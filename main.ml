(* main.ml *)
open Tsdl

let () =
  match Sdl.init Sdl.Init.video with
  | Error (`Msg e) ->
      Sdl.log "SDL init error: %s" e; exit 1
  | Ok () ->
      match Sdl.create_window ~w:640 ~h:480 "OCaml SDL Example" Sdl.Window.shown with
      | Error (`Msg e) ->
          Sdl.log "Window creation error: %s" e;
          Sdl.quit (); exit 1
      | Ok window ->
          match Sdl.create_renderer
                  ~index:(-1)
                  ~flags:Sdl.Renderer.(accelerated + presentvsync)
                  window with
          | Error (`Msg e) ->
              Sdl.log "Renderer creation error: %s" e;
              Sdl.destroy_window window; Sdl.quit (); exit 1
          | Ok renderer ->
              Sdl.set_render_draw_color renderer 0 0 255 255 |> ignore;
              Sdl.render_clear renderer;
              Sdl.render_present renderer;
              Sdl.delay 3000l;
              Sdl.destroy_renderer renderer;
              Sdl.destroy_window window;
              Sdl.quit ()
