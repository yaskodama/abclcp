open Tsdl

let draw_line renderer (x1,y1) (x2,y2) =
  Sdl.render_draw_line renderer x1 y1 x2 y2 |> ignore

(* Universityという文字のワイヤーフレーム座標 *)
let draw_university renderer x y scale =
  let s n = n * scale in
  let ox, oy = x, y in

  (* U *)
  draw_line renderer (ox, oy) (ox, oy + s 40);
  draw_line renderer (ox, oy + s 40) (ox + s 20, oy + s 40);
  draw_line renderer (ox + s 20, oy + s 40) (ox + s 20, oy);

  let ox = ox + s 30 in
  (* n *)
  draw_line renderer (ox, oy + s 20) (ox, oy + s 40);
  draw_line renderer (ox, oy + s 20) (ox + s 15, oy + s 20);
  draw_line renderer (ox + s 15, oy + s 20) (ox + s 15, oy + s 40);

  let ox = ox + s 25 in
  (* i *)
  draw_line renderer (ox, oy + s 20) (ox, oy + s 40);
  draw_line renderer (ox, oy + s 15) (ox, oy + s 17);

  let ox = ox + s 10 in
  (* v *)
  draw_line renderer (ox, oy + s 20) (ox + s 7, oy + s 40);
  draw_line renderer (ox + s 7, oy + s 40) (ox + s 14, oy + s 20);

  let ox = ox + s 20 in
  (* e *)
  draw_line renderer (ox + s 15, oy + s 25) (ox, oy + s 25);
  draw_line renderer (ox, oy + s 25) (ox, oy + s 35);
  draw_line renderer (ox, oy + s 35) (ox + s 15, oy + s 35);
  draw_line renderer (ox + s 15, oy + s 35) (ox + s 15, oy + s 40);
  draw_line renderer (ox + s 15, oy + s 40) (ox, oy + s 40);

  let ox = ox + s 20 in
  (* r *)
  draw_line renderer (ox, oy + s 25) (ox, oy + s 40);
  draw_line renderer (ox, oy + s 25) (ox + s 10, oy + s 25);
  draw_line renderer (ox + s 10, oy + s 25) (ox + s 10, oy + s 30);
  draw_line renderer (ox, oy + s 30) (ox + s 10, oy + s 40);

  let ox = ox + s 15 in
  (* s *)
  draw_line renderer (ox + s 15, oy + s 25) (ox, oy + s 25);
  draw_line renderer (ox, oy + s 25) (ox, oy + s 32);
  draw_line renderer (ox, oy + s 32) (ox + s 15, oy + s 32);
  draw_line renderer (ox + s 15, oy + s 32) (ox + s 15, oy + s 40);
  draw_line renderer (ox + s 15, oy + s 40) (ox, oy + s 40);

  let ox = ox + s 20 in
  (* i *)
  draw_line renderer (ox, oy + s 20) (ox, oy + s 40);
  draw_line renderer (ox, oy + s 15) (ox, oy + s 17);

  let ox = ox + s 10 in
  (* t *)
  draw_line renderer (ox, oy + s 20) (ox, oy + s 40);
  draw_line renderer (ox - s 5, oy + s 20) (ox + s 5, oy + s 20);

  let ox = ox + s 15 in
  (* y *)
  draw_line renderer (ox, oy + s 20) (ox + s 7, oy + s 30);
  draw_line renderer (ox + s 14, oy + s 20) (ox + s 7, oy + s 30);
  draw_line renderer (ox + s 7, oy + s 30) (ox + s 7, oy + s 40)

let () =
  match Sdl.init Sdl.Init.video with
  | Error (`Msg e) -> Sdl.log "Error: %s" e; exit 1
  | Ok () ->
    match Sdl.create_window ~w:640 ~h:200 "University Wireframe" Sdl.Window.windowed with
    | Error (`Msg e) -> Sdl.log "Window error: %s" e; exit 1
    | Ok window ->
      match Sdl.create_renderer window ~index:(-1) ~flags:Sdl.Renderer.accelerated with
      | Error (`Msg e) -> Sdl.log "Renderer error: %s" e; exit 1
      | Ok renderer ->
        (* 背景を白 *)
        Sdl.set_render_draw_color renderer 255 255 255 255 |> ignore;
        Sdl.render_clear renderer |> ignore;

        (* 描画色を赤に *)
        Sdl.set_render_draw_color renderer 255 0 0 255 |> ignore;

        (* University を描画 (位置:x=50,y=50, スケール:3倍) *)
        draw_university renderer 50 50 3;

        (* 表示 *)
        Sdl.render_present renderer;
        Sdl.delay 5000l;

        (* クリーンアップ *)
        Sdl.destroy_renderer renderer;
        Sdl.destroy_window window;
        Sdl.quit ()
