(* sdl_helper.ml *)
open Tsdl

type cmd =
  | Init of int * int * string
  | Line of int * int * int * int
  | Clear
  | Present
  | Quit
  | EraseLine of int * int * int * int

let q = Queue.create ()
let m = Mutex.create ()
let c = Condition.create ()
let running = ref true
let log s = prerr_endline ("[SDL] " ^ s)
let post cmd =
  Mutex.lock m; Queue.add cmd q; Condition.signal c; Mutex.unlock m;
  log "posted cmd"

(* 外部公開 API：他スレッドからはこれだけ呼ぶ *)
let sdl_init ~w ~h ~title = post (Init (w,h,title))
let sdl_draw_line x1 y1 x2 y2 = post (Line (x1,y1,x2,y2))
let sdl_clear () = post Clear
let sdl_present () = post Present
let sdl_quit () = post Quit
let sdl_erase_line x1 y1 x2 y2 = post (EraseLine (x1, y1, x2, y2))

let self_test_boot () =
  log "self_test_boot: posting Init/Clear/Present";
  post (Init (640, 480, "SelfTest"));
  post Clear;
  post Present

let ev = Sdl.Event.create ()

let rec idle () =
  ignore (Sdl.poll_event (Some ev));
  (match Sdl.Event.(enum (get ev typ)) with
   | `Quit -> running := false
   | _ -> ());
  if Queue.is_empty q && !running then (Sdl.delay 5l; idle ())

let ev = Sdl.Event.create ()

let log s = prerr_endline ("[SDL] " ^ s)

(* メインスレッドで動かすループ *)

let rec main_loop () =
  log "main_loop: started on main thread";
  let window = ref None in
  let renderer = ref None in

  let rec loop () =
    (* 1) イベントを捌く（macOSでは必須） *)
    ignore (Sdl.poll_event (Some ev));
    (match Sdl.Event.(enum (get ev typ)) with
     | `Quit -> running := false
     | _ -> ());

    if not !running then (
      (* 終了処理 *)
      (match !renderer with Some r -> Sdl.destroy_renderer r | None -> ());
      (match !window with Some w -> Sdl.destroy_window w | None -> ());
      Sdl.quit ();
      ()
    ) else (
      (* 2) キューから1件だけ非ブロッキングで取り出して処理 *)
      let cmd_opt =
        Mutex.lock m;
        let res =
          if Queue.is_empty q then None else Some (Queue.take q)
        in
        Mutex.unlock m;
        res
      in

      (match cmd_opt with
       | None ->
           (* 何も無ければ 5ms スリープして次フレームへ *)
           Sdl.delay 5l;


           in
           let ren =
             match Sdl.create_renderer win ~index:(-1) ~flags:Sdl.Renderer.accelerated with
             | Ok r -> r | Error (`Msg e) -> failwith ("create_renderer failed: " ^ e)
           in
           window := Some win; renderer := Some ren;
           ignore (Sdl.set_render_draw_color ren 0 0 0 255);
           ignore (Sdl.render_clear ren);
           Sdl.render_present ren;
           ignore (Sdl.set_render_draw_color ren 255 255 255 255);

       | Some (Line (x1,y1,x2,y2)) ->
           log (Printf.sprintf "Line %d,%d -> %d,%d" x1 y1 x2 y2);
           (match !renderer with
            | None -> ()
            | Some r -> ignore (Sdl.render_draw_line r x1 y1 x2 y2));

       | Some Clear ->
           log "Clear";
           (match !renderer with
            | None -> ()
            | Some r ->
                ignore (Sdl.set_render_draw_color r 0 0 0 255);
                ignore (Sdl.render_clear r));

       | Some Present ->
           log "Present";
           (match !renderer with
            | None -> () | Some r -> Sdl.render_present r);

       | Some (EraseLine (x1,y1,x2,y2)) ->
           (match !renderer with
            | None -> ()
            | Some r ->
                ignore (Sdl.set_render_draw_color r 0 0 0 255);
                ignore (Sdl.render_draw_line r x1 y1 x2 y2));

       | Some Quit ->
           running := false
      );
      (* 3) 次フレーム *)
      loop ()
    )
  in
  loop ()



  let rec loop () =
    (* ★ 追加：キューが空なら idle を回す *)
    if Queue.is_empty q then idle ();

    (* キュー待ち *)
    Mutex.lock m;
    while Queue.is_empty q && !running do Condition.wait c m done;
    let cmd_opt = if !running then Some (Queue.take q) else None in
    Mutex.unlock m;

    match cmd_opt with
    | None -> () (* running=false *)
    | Some (Init (w,h,title)) ->
      log (Printf.sprintf "Init %dx%d %s" w h title);

    (* 1) SDL 初期化の result を確認 *)
      (match Sdl.init Sdl.Init.video with
       | Ok () -> ()
       | Error (`Msg e) -> failwith ("Sdl.init failed: " ^ e));

    (* 2) High-DPI を許可して作成（macOS で見えやすく） *)
      let flags = Sdl.Window.(shown + allow_highdpi) in
        let win =
          match Sdl.create_window ~w ~h title flags with
          | Ok w -> w
          | Error (`Msg e) -> failwith ("create_window failed: " ^ e)
        in

    (* 3) レンダラー生成の result 確認 *)
      let ren =
        match Sdl.create_renderer win ~index:(-1) ~flags:Sdl.Renderer.accelerated with
        | Ok r -> r
        | Error (`Msg e) -> failwith ("create_renderer failed: " ^ e)
      in
        window := Some win;
        renderer := Some ren;

    (* 4) 描画色を白に、いったん黒でクリア → present で“ウィンドウを確実に見せる” *)
        ignore (Sdl.set_render_draw_color ren 0 0 0 255);   (* 背景: 黒 *)
        ignore (Sdl.render_clear ren);
        Sdl.render_present ren;
        ignore (Sdl.set_render_draw_color ren 255 255 255 255);  (* 線の色: 白 *)
        loop ()
     | Some (Line (x1,y1,x2,y2)) ->
        log (Printf.sprintf "Line %d,%d -> %d,%d" x1 y1 x2 y2);
        (match !renderer with
         | None -> ()
         | Some r ->
            (match Sdl.render_draw_line r x1 y1 x2 y2 with
             | Ok () -> ()
             | Error (`Msg e) -> failwith e));
         loop ()
     | Some Clear ->
         log "Clear";
         (match !renderer with
         | None -> ()
         | Some r ->
            (* 色設定も result を返す *)
            (match Sdl.set_render_draw_color r 0 0 0 255 with
             | Ok () -> ()
             | Error (`Msg e) -> failwith e);
            (match Sdl.render_clear r with
             | Ok () -> ()
             | Error (`Msg e) -> failwith e));
         loop ()
     | Some Present ->
        log "Present";
        (match !renderer with
        | None -> ()
        | Some r ->
            (* present は unit を返す（Tsdl 0.9.10 時点） *)
            Sdl.render_present r);
         loop ()
     | Some (EraseLine (x1, y1, x2, y2)) ->
       (match !renderer with
        | None -> ()
        | Some r ->
            (* 背景色(例:黒)で上書き描画 *)
            ignore (Sdl.set_render_draw_color r 0 0 0 255);
            ignore (Sdl.render_draw_line r x1 y1 x2 y2));
         loop ()
    | Some Quit ->
        running := false;
        (match !renderer with Some r -> Sdl.destroy_renderer r | None -> ());
        (match !window with Some w -> Sdl.destroy_window w | None -> ());
        Sdl.quit ()
  in
  loop ()
