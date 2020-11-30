let re = Str.regexp "Hint Unfold \\([^ ]+\\) : deriving."

let read_file acc file =
  let ic = open_in file in
  let rec loop acc =
    try
      let s = input_line ic in
      let acc = if Str.string_match re s 0 then
                  Str.replace_matched "\\1" s :: acc
                else acc in
      loop acc
    with End_of_file -> close_in ic; acc in
  loop acc

let read_files files =
  List.rev @@ Array.fold_left read_file [] files

let print_db prefix db =
  Printf.printf "  %s [" prefix;
  List.iter (Printf.printf "    %s\n") db;
  print_endline "]."

let _ =
  print_endline "From mathcomp Require Import ssreflect ssrfun.";
  print_endline "From deriving Require Import base ind.";
  print_endline "Declare Reduction deriving_compute :=";
  let db = read_files Sys.argv in
  print_db "cbv" db;
  print_endline "Declare Reduction deriving_lazy :=";
  print_db "lazy" db;
  print_endline "Ltac deriving_compute :=";
  print_db "cbv" db
