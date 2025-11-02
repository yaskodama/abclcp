open Tsdl

type point3d = {x:float; y:float; z:float}

(* 3D点を2D座標へ透視投影 *)
let project p =
  let focal_length = 300.0 in
  let scale = focal_length /. (focal_length +. p.z) in
  let x2d = int_of_float (p.x *. scale) in
  let y2d = int_of_float (p.y *. scale) in
  (x2d, y2d)

let draw_line renderer p1 p2 =
  let (x1, y1) = project p1 in
  let (x2, y2) = project p2 in
  Sdl.render_draw_line renderer x1 y1 x2 y2 |> ignore

(* 3D文字 U を定義 *)
let draw_university renderer ox oy =
  let oxf = float_of_int ox and oyf = float_of_int oy in
  let s = 40.0 in (* 文字サイズ *)
  let d = 15.0 in (* 奥行き *)
  
  (* U *)
  let u = [
    {x=0.;y=0.;z=0.}; {x=0.;y=s;z=0.};
    {x=0.;y=s;z=0.}; {x=s/.2.;y=s;z=0.};
    {x=s/.2.;y=s;z=0.}; {x=s/.2.;y=0.;z=0.};
    (* 奥行き *)
    {x=0.;y=0.;z=d}; {x=0.;y=s;z=d};
    {x=0.;y=s;z=d}; {x=s/.2.;y=s;z=d};
    {x=s/.2.;y=s;z=d}; {x=s/.2.;y=0.;z=d};
    (* 接続 *)
    {x=0.;y=0.;z=0.}; {x=0.;y=0.;z=d};
    {x=0.;y=s;z=0.}; {x=0.;y=s;z=d};
    {x=s/.2.;y=s;z=0.}; {x=s/.2.;y=s;z=d};
    {x=s/.2.;y=0.;z=0.}; {x=s/.2.;y=0.;z=d};
  ] in

  let draw_char points offset =
    let ox, oy, oz = offset in
    let len = List.length points in
    let rec draw idx =
      if idx < len then begin
        let p1 = List.nth points idx in
        let p2 = List.nth points (idx+1) in
        draw_line renderer
          {x=p1.x+.ox;y=p1.y+.oy;z=p1.z+.oz}
          {x=p2.x+.ox;y=p2.y+.oy;z=p2.z+.oz};
        draw (idx+2)
      end
    in
    draw 0
  in

  (* U を描画 *)
  draw_char u (oxf, oyf, 100.)

(* メイン処理 *)
let () =
  match Sdl.init Sdl.Init.video with
  | Error (`Msg e) -> Sdl.log "Error: %s" e; exit 1
  | Ok () ->
    match Sdl.create_window ~w:800 ~h:600 "University 3D" Sdl.Window.windowed with
    | Error (`Msg e) -> Sdl.log "Window error: %s" e; exit 1
    | Ok window ->
      match Sdl.create_renderer window ~index:(-1) ~flags:Sdl.Renderer.accelerated with
      | Error (`Msg e) -> Sdl.log "Renderer error: %s" e; exit 1
      | Ok renderer ->
        begin
          (* 背景を白 *)
          Sdl.set_render_draw_color renderer 255 255 255 255 |> ignore;
          Sdl.render_clear renderer |> ignore;

          (* 描画色を青 *)
          Sdl.set_render_draw_color renderer 0 0 255 255 |> ignore;

          (* 描画位置を中央付近に設定 *)
          Sdl.render_set_scale renderer 1. 1. |> ignore;
          Sdl.render_set_logical_size renderer 800 600 |> ignore;
          Sdl.render_set_viewport renderer None |> ignore;

          (* 中央付近に表示 *)
          draw_university renderer 350 250;

          (* 表示 *)
          Sdl.render_present renderer;
          Sdl.delay 5000l;

          (* クリーンアップ *)
          Sdl.destroy_renderer renderer;
          Sdl.destroy_window window;
          Sdl.quit ()
        end
