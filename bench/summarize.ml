(* summarize.ml — Turn a batch of coqc .out files into a long-form CSV.

   Invoked by the bench/bench.mk %.csv summary rule:

     ocaml -I $(ocamlfind query csv) csv.cma bench/summarize.ml \
       -dim <name> <build>/<dim>/<v>-<r>.out ...

   Each input file is the captured stdout of a single coqc invocation
   on a benchmark .v file; gen_bench.ml sprinkles `idtac "BENCH: ..."`
   commands before each `Time Definition`, so the output looks like:

     BENCH: simpl hasDecEq T0
     Finished transaction in 0.123 secs (0.120u,0.003s)
     ...

   We pair each BENCH label with the next `Finished transaction in X`
   line and emit one CSV row per pair.  Value and rep are recovered
   from the filename stem, e.g. `bench/build/types/3-1.out` → value=3,
   rep=1. *)

let dim = ref ""
let files = ref []

let has_prefix s p =
  String.length s >= String.length p
  && String.sub s 0 (String.length p) = p

let strip_prefix s p =
  String.sub s (String.length p) (String.length s - String.length p)

let read_lines path =
  let ic = open_in path in
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  loop []

let parse_output lines =
  let label = ref None in
  let acc = ref [] in
  List.iter (fun raw ->
    let line = String.trim raw in
    if has_prefix line "BENCH: " then
      label := Some (strip_prefix line "BENCH: ")
    else if has_prefix line "Finished transaction in " then begin
      let rest = strip_prefix line "Finished transaction in " in
      match String.index_opt rest ' ' with
      | None -> ()
      | Some i ->
        (try
          let t = float_of_string (String.sub rest 0 i) in
          (match !label with
           | Some l -> acc := (l, t) :: !acc; label := None
           | None -> ())
        with _ -> ())
    end
  ) lines;
  List.rev !acc

(* Recover (value, rep) from "<anything>/v<value>-<rep>.out".  The
   leading "v" is a prefix added by gen_mk.awk so the file name is a
   legal Rocq module identifier. *)
let parse_stem path =
  let base = Filename.chop_extension (Filename.basename path) in
  let base =
    if String.length base > 0 && base.[0] = 'v'
    then String.sub base 1 (String.length base - 1)
    else base
  in
  match String.index_opt base '-' with
  | None -> failwith ("bad .out filename: " ^ path)
  | Some i ->
    let value = String.sub base 0 i in
    let rep = String.sub base (i + 1) (String.length base - i - 1) in
    (value, rep)

let () =
  Arg.parse
    [ "-dim", Arg.Set_string dim, "NAME dimension label emitted in the CSV" ]
    (fun f -> files := f :: !files)
    "summarize.ml -dim NAME FILE.out ...";
  if !dim = "" then (prerr_endline "summarize.ml: -dim is required"; exit 2);
  let files = List.rev !files in
  let rows = ref [
    [ "dimension"; "value"; "rep"; "step"; "seconds" ]
  ] in
  List.iter (fun path ->
    let value, rep = parse_stem path in
    let pairs = parse_output (read_lines path) in
    List.iter (fun (step, secs) ->
      rows := [
        !dim; value; rep; step; Printf.sprintf "%.6f" secs
      ] :: !rows
    ) pairs
  ) files;
  Csv.output_all (Csv.to_channel stdout) (List.rev !rows)
