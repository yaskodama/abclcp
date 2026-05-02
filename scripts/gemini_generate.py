#!/usr/bin/env python3
import json
import os
import sys
import time
import urllib.error
import urllib.request


def retry_delay_seconds(detail: str) -> float:
    try:
        payload = json.loads(detail)
        for item in payload.get("error", {}).get("details", []):
            if item.get("@type") == "type.googleapis.com/google.rpc.RetryInfo":
                delay = item.get("retryDelay", "")
                if delay.endswith("s"):
                    return max(1.0, float(delay[:-1]))
    except Exception:
        pass
    return 2.0


def main() -> int:
    api_key = os.environ.get("GEMINI_API_KEY", "").strip()
    if not api_key:
        print("GEMINI_API_KEY is not set", file=sys.stderr)
        return 2

    model = os.environ.get("GEMINI_MODEL", "gemini-2.5-flash").strip() or "gemini-2.5-flash"
    prompt = sys.stdin.read()
    if not prompt.strip():
        print("prompt is empty", file=sys.stderr)
        return 2

    url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
    body = {
        "contents": [
            {
                "role": "user",
                "parts": [{"text": prompt}],
            }
        ]
    }
    data = json.dumps(body).encode("utf-8")
    req = urllib.request.Request(
        url,
        data=data,
        method="POST",
        headers={
            "Content-Type": "application/json",
            "x-goog-api-key": api_key,
        },
    )

    retries = int(os.environ.get("GEMINI_RETRIES", "2").strip() or "2")
    payload = None
    for attempt in range(retries + 1):
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                payload = json.loads(resp.read().decode("utf-8"))
                break
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            if exc.code == 429 and attempt < retries:
                time.sleep(retry_delay_seconds(detail))
                continue
            print(f"Gemini HTTP error {exc.code}: {detail}", file=sys.stderr)
            return 1
        except Exception as exc:
            print(f"Gemini request failed: {exc}", file=sys.stderr)
            return 1

    if payload is None:
        print("Gemini response was empty", file=sys.stderr)
        return 1

    texts = []
    for cand in payload.get("candidates", []):
        content = cand.get("content", {})
        for part in content.get("parts", []):
            text = part.get("text")
            if text:
                texts.append(text)

    if not texts:
        print("Gemini response did not contain text", file=sys.stderr)
        return 1

    print("\n".join(texts).strip())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
