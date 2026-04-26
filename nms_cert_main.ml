(* nms_cert_main.ml

   OCaml CLI driver for the extracted nms-verified certifier.

   Reads a detection list from stdin and emits one of:
     CERTIFIED <slack>          if Separated holds at the given slack
     REJECTED                   if no candidate covers the data

   Each input line is whitespace-separated:
       score x1 y1 x2 y2

   where (x1, y1, x2, y2) is the detection's integer bounding box.

   IoU is computed as percent-scale (0..100) intersection-over-union
   over integer rectangles, matching the [ibox_iou] semantics in nms.v.

   Build:
     rocq compile nms.v
     ocamlfind ocamlopt nms_cert.ml nms_cert_main.ml -o nms_cert

   Usage:
     ./nms_cert TAU THETA SLACK < detections.txt
*)

open Nms_cert

type ibox = { x1 : int; y1 : int; x2 : int; y2 : int }

let area b =
  let w = max 0 (b.x2 - b.x1) in
  let h = max 0 (b.y2 - b.y1) in
  w * h

let inter_area a b =
  let x1 = max a.x1 b.x1 in
  let y1 = max a.y1 b.y1 in
  let x2 = min a.x2 b.x2 in
  let y2 = min a.y2 b.y2 in
  let w = if x1 <= x2 then x2 - x1 else 0 in
  let h = if y1 <= y2 then y2 - y1 else 0 in
  w * h

let iou a b =
  let i = inter_area a b in
  let u = area a + area b - i in
  if u = 0 then 0 else (i * 100) / u

let box_eq (a : ibox) (b : ibox) = a = b

let parse_line line : ibox det =
  Scanf.sscanf line " %d %d %d %d %d"
    (fun s x1 y1 x2 y2 -> { score = s; box = { x1; y1; x2; y2 } })

let read_dets () =
  let dets = ref [] in
  (try
     while true do
       let line = input_line stdin in
       if String.trim line <> "" then
         dets := parse_line line :: !dets
     done
   with End_of_file -> ());
  List.rev !dets

let usage () =
  Printf.eprintf "usage: nms_cert TAU THETA SLACK < detections.txt\n";
  exit 2

let () =
  let argv = Sys.argv in
  if Array.length argv <> 4 then usage ();
  let tau =
    try int_of_string argv.(1) with _ -> usage () in
  let theta =
    try int_of_string argv.(2) with _ -> usage () in
  let slack =
    try int_of_string argv.(3) with _ -> usage () in
  let dets = read_dets () in
  Printf.printf "input: %d detections, tau=%d, theta=%d, slack=%d\n"
    (List.length dets) tau theta slack;
  let ok = separated_check iou tau theta box_eq slack dets in
  if ok then begin
    Printf.printf "CERTIFIED: Separated at slack %d\n" slack;
    exit 0
  end else begin
    Printf.printf "REJECTED: not Separated at slack %d\n" slack;
    exit 1
  end
