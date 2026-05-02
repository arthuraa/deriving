(* plot.ml — Aggregate one long-form summary CSV and draw a PNG.

   Invoked by the bench/bench.mk %.png recipe:

     ocaml -I $(ocamlfind query csv) csv.cma unix.cma \
       bench/plot.ml <summary.csv> <output.png>

   The summary CSV is in the format emitted by bench/summarize.ml: columns
   `dimension,value,rep,step,seconds`, one row per `Time Definition`
   transaction.  Step labels like "simpl hasDecEq T0" carry a trailing per-type
   " T<digits>" suffix which we strip so multi-type sweeps collapse to a single
   line per derivation step.  For each (value, rep, step) we sum across types to
   show total work, then take the median across reps so the final plot has one
   point per (value, step).  The aggregated table is dumped to a sibling .dat
   file and fed to gnuplot as wide-format columns. *)

let dim_xlabels = [
  "types",  "number of mutually inductive types";
  "nonrec", "nonrecursive arguments per constructor";
  "rec",    "recursive arguments per constructor";
  "args",   "arguments per constructor (rec = nonrec)";
  "ctors",  "constructors per type";
]

let step_order = [
  "indDef"; "IndType";
  "nored hasDecEq"; "simpl hasDecEq";
  "hasChoice"; "isCountable";
  "nored isOrder"; "simpl isOrder";
]

(* Strip a trailing " T<digits>" suffix from a step label. *)
let base_step step =
  let n = String.length step in
  let rec digits_from i =
    if i >= n then true
    else if step.[i] >= '0' && step.[i] <= '9' then digits_from (i + 1)
    else false
  in
  let rec scan i =
    if i + 2 > n then step
    else if step.[i] = ' ' && step.[i + 1] = 'T'
         && i + 2 < n && digits_from (i + 2) then
      String.sub step 0 i
    else scan (i + 1)
  in
  scan 0

let median xs =
  let a = Array.of_list xs in
  Array.sort compare a;
  let n = Array.length a in
  if n = 0 then nan
  else if n mod 2 = 1 then a.(n / 2)
  else (a.(n / 2 - 1) +. a.(n / 2)) /. 2.0

let load_sums path =
  let rows = Csv.load path in
  match rows with
  | [] -> failwith ("empty CSV: " ^ path)
  | header :: rows ->
    let idx name =
      let rec find i = function
        | [] -> failwith ("missing column: " ^ name)
        | c :: _ when c = name -> i
        | _ :: rest -> find (i + 1) rest
      in
      find 0 header
    in
    let i_val = idx "value" in
    let i_rep = idx "rep" in
    let i_step = idx "step" in
    let i_secs = idx "seconds" in
    (* (value, rep, base_step) -> total seconds across types *)
    let sums = Hashtbl.create 128 in
    List.iter (fun row ->
      let row = Array.of_list row in
      if Array.length row > i_secs then begin
        let v = int_of_string row.(i_val) in
        let r = int_of_string row.(i_rep) in
        let step = base_step row.(i_step) in
        let secs = float_of_string row.(i_secs) in
        let key = (v, r, step) in
        let prev = try Hashtbl.find sums key with Not_found -> 0.0 in
        Hashtbl.replace sums key (prev +. secs)
      end
    ) rows;
    sums

let group_by_step sums =
  let by_step = Hashtbl.create 16 in
  Hashtbl.iter (fun (v, _rep, step) s ->
    let vmap =
      match Hashtbl.find_opt by_step step with
      | Some m -> m
      | None   -> let m = Hashtbl.create 16 in Hashtbl.add by_step step m; m
    in
    let prev = try Hashtbl.find vmap v with Not_found -> [] in
    Hashtbl.replace vmap v (s :: prev)
  ) sums;
  by_step

let sorted_values by_step =
  let s = ref [] in
  Hashtbl.iter (fun _step vmap ->
    Hashtbl.iter (fun v _ ->
      if not (List.mem v !s) then s := v :: !s
    ) vmap
  ) by_step;
  List.sort compare !s

let ordered_steps by_step =
  let known = List.filter (fun s -> Hashtbl.mem by_step s) step_order in
  let extras =
    Hashtbl.fold (fun k _ acc ->
      if List.mem k step_order then acc else k :: acc
    ) by_step []
  in
  known @ List.sort compare extras

let write_dat path values steps by_step =
  let oc = open_out path in
  output_string oc "# value";
  List.iter (fun s ->
    output_char oc ' ';
    String.iter (fun c ->
      output_char oc (if c = ' ' then '_' else c)
    ) s
  ) steps;
  output_char oc '\n';
  List.iter (fun v ->
    Printf.fprintf oc "%d" v;
    List.iter (fun s ->
      let vmap = Hashtbl.find by_step s in
      match Hashtbl.find_opt vmap v with
      | Some xs -> Printf.fprintf oc " %.6f" (median xs)
      | None    -> output_string oc " NaN"
    ) steps;
    output_char oc '\n'
  ) values;
  close_out oc

let run_gnuplot ~dat ~png ~title ~xlabel steps =
  let ic, oc = Unix.open_process "gnuplot" in
  let p fmt = Printf.fprintf oc fmt in
  p "set terminal pngcairo size 900,600 enhanced font 'sans,11'\n";
  p "set output '%s'\n" png;
  p "set title \"deriving timings vs %s\\n{/*0.8 (per step, summed across mutual types)}\"\n" title;
  p "set xlabel '%s'\n" xlabel;
  p "set ylabel 'seconds (median over reps)'\n";
  p "set key outside right top\n";
  p "set grid\n";
  p "set logscale y\n";
  p "set yrange [0.001:*]\n";
  p "plot ";
  List.iteri (fun i step ->
    if i > 0 then p ", ";
    p "'%s' using 1:%d with linespoints title '%s'" dat (i + 2) step
  ) steps;
  p "\n";
  close_out oc;
  (try while true do ignore (input_line ic) done
   with End_of_file -> ());
  ignore (Unix.close_process (ic, oc))

let () =
  let csv_path, png_path =
    match Sys.argv with
    | [| _; a; b |] -> a, b
    | _ ->
      prerr_endline "usage: plot.ml <summary.csv> <output.png>";
      exit 2
  in
  let dim =
    Filename.chop_extension (Filename.basename csv_path)
  in
  let xlabel =
    try List.assoc dim dim_xlabels with Not_found -> dim
  in
  let dat_path =
    Filename.concat (Filename.dirname png_path) (dim ^ ".dat")
  in
  let sums = load_sums csv_path in
  let by_step = group_by_step sums in
  let values = sorted_values by_step in
  let steps = ordered_steps by_step in
  write_dat dat_path values steps by_step;
  run_gnuplot ~dat:dat_path ~png:png_path ~title:xlabel ~xlabel steps;
  Printf.printf "wrote %s\n" png_path
