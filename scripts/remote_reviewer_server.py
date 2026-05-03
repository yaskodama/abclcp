#!/usr/bin/env python3
import json
import os
from http.server import BaseHTTPRequestHandler, HTTPServer


class Handler(BaseHTTPRequestHandler):
    def do_POST(self):
        if self.path != "/review":
            self.send_response(404)
            self.end_headers()
            self.wfile.write(b"not found")
            return

        length = int(self.headers.get("Content-Length", "0"))
        try:
            payload = json.loads(self.rfile.read(length).decode("utf-8"))
            problem = str(payload.get("problem", ""))
            answer = str(payload.get("answer", ""))
            lang = str(payload.get("lang", "")).lower()
            ok = "12" in answer or "12個" in answer
            if lang == "ja":
                review = "リモートレビューア承認: 回答は正しいです" if ok else "リモートレビューア差し戻し: 回答の修正が必要です"
            else:
                review = "remote reviewer accepted: answer is correct" if ok else "remote reviewer rejected: answer needs correction"
            body = json.dumps({
                "actor": "remote-reviewer",
                "problem": problem,
                "answer": answer,
                "review": review,
            }).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except Exception as exc:
            body = str(exc).encode("utf-8")
            self.send_response(500)
            self.send_header("Content-Type", "text/plain")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

    def log_message(self, fmt, *args):
        return


def main() -> int:
    host = os.environ.get("REMOTE_REVIEWER_HOST", "127.0.0.1")
    port = int(os.environ.get("REMOTE_REVIEWER_PORT", "18080"))
    server = HTTPServer((host, port), Handler)
    print(f"remote reviewer listening on {host}:{port}", flush=True)
    server.serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
