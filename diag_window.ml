(* diag_window.ml *)
open Tsdl
let or_die = function Ok v -> v | Error (`Msg e) -> Sdl.log "SDL error: %s" e; exit 1
let () =
  Sdl.log "Starting";
  Sdl.init Sdl.Init.video |> or_die;
  Sdl.log "SDL video init OK";
  let win = Sdl.create_window ~w:640 ~h:480 "Diag - Tsdl" Sdl.Window.shown |> or_die in
  Sdl.log "Window created OK. Will wait 3000 ms";
  let t0 = Sdl.get_ticks () in
  let rec wait () =
    Sdl.pump_events ();
    if Int32.sub (Sdl.get_ticks ()) t0 < 3000l then (Sdl.delay 16l; wait ())
  in
  wait ();
  Sdl.log "Done. Cleaning up.";
  Sdl.destroy_window win; Sdl.quit (); Sdl.log "Quit OK"
