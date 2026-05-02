#!/usr/bin/env python3
import json
import os
import sys
import urllib.error
import urllib.request


def collect_text(payload):
    texts = []

    output_text = payload.get("output_text")
    if isinstance(output_text, str) and output_text:
        texts.append(output_text)

    for item in payload.get("output", []):
        for content in item.get("content", []):
            if content.get("type") == "output_text" and content.get("text"):
                texts.append(content["text"])

    return "\n".join(texts).strip()


def main() -> int:
    api_key = os.environ.get("OPENAI_API_KEY", "").strip()
    if not api_key:
        print("OPENAI_API_KEY is not set", file=sys.stderr)
        return 2

    model = os.environ.get("OPENAI_MODEL", "gpt-4.1").strip() or "gpt-4.1"
    prompt = sys.stdin.read()
    if not prompt.strip():
        print("prompt is empty", file=sys.stderr)
        return 2

    body = {
        "model": model,
        "input": prompt,
    }
    data = json.dumps(body).encode("utf-8")
    req = urllib.request.Request(
        "https://api.openai.com/v1/responses",
        data=data,
        method="POST",
        headers={
            "Content-Type": "application/json",
            "Authorization": f"Bearer {api_key}",
        },
    )

    try:
        with urllib.request.urlopen(req, timeout=90) as resp:
            payload = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        print(f"OpenAI HTTP error {exc.code}: {detail}", file=sys.stderr)
        return 1
    except Exception as exc:
        print(f"OpenAI request failed: {exc}", file=sys.stderr)
        return 1

    text = collect_text(payload)
    if not text:
        print("OpenAI response did not contain output text", file=sys.stderr)
        return 1

    print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
