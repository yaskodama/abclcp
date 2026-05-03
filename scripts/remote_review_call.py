#!/usr/bin/env python3
import json
import sys
import urllib.error
import urllib.request


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print("usage: remote_review_call.py host:port [--ja]", file=sys.stderr)
        return 2

    hostport = sys.argv[1]
    raw = sys.stdin.read()
    marker = "\n---ANSWER---\n"
    if marker not in raw:
        print("input must contain ---ANSWER--- marker", file=sys.stderr)
        return 2
    problem, answer = raw.split(marker, 1)

    lang = "ja" if len(sys.argv) >= 3 and sys.argv[2] == "--ja" else ""
    body = json.dumps({"problem": problem.strip(), "answer": answer.strip(), "lang": lang}).encode("utf-8")
    req = urllib.request.Request(
        f"http://{hostport}/review",
        data=body,
        method="POST",
        headers={"Content-Type": "application/json"},
    )
    try:
        with urllib.request.urlopen(req, timeout=20) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        print(f"remote reviewer HTTP error {exc.code}: {detail}", file=sys.stderr)
        return 1
    except Exception as exc:
        print(f"remote reviewer request failed: {exc}", file=sys.stderr)
        return 1

    review = payload.get("review", "")
    if not review:
        print("remote reviewer response did not contain review", file=sys.stderr)
        return 1
    print(review)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
