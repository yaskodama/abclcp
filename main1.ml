(* main.ml *)
open Tsdl

let or_die = function
  | Ok v -> v
  | Error (`Msg e) -> Sdl.log "SDL error: %s" e; exit 1

let () =
  Sdl.init Sdl.Init.video |> or_die;
  let window =
    Sdl.create_window ~w:640 ~h:480 "OCaml + SDL2" Sdl.Window.shown |> or_die
  in
  let renderer =
    Sdl.create_renderer
      ~index:(-1)
      ~flags:Sdl.Renderer.(accelerated + presentvsync)
      window |> or_die
  in
  (* 背景を青で塗る *)
  Sdl.set_render_draw_color renderer 0 0 255 255 |> ignore;
  Sdl.render_clear renderer |> ignore;
  Sdl.render_present renderer;

  (* イベントループ: 閉じるボタン or ESC で終了 *)
  let rec loop () =
    let e = Sdl.Event.create () in
    (* 16ms ごとにイベントをポーリングして画面を維持 *)
    if Sdl.poll_event (Some e) then begin
      match Sdl.Event.(get e typ) with
      | t when t = Sdl.Event.quit -> ()
      | t when t = Sdl.Event.key_down ->
          let key = Sdl.Event.(get e keyboard_keycode) in
          if key = Sdl.Scancode.escape then () else (Sdl.delay 16l; loop ())
      | _ -> Sdl.delay 16l; loop ()
    end else (Sdl.delay 16l; loop ())
  in
  loop ();

  Sdl.destroy_renderer renderer;
  Sdl.destroy_window window;
  Sdl.quit ()
