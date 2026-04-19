document.addEventListener("DOMContentLoaded", () => {
  const out = document.getElementById("out");
  const log = document.getElementById("log");
  const events = document.getElementById("events");
  const replies = document.getElementById("replies");
  const tree = document.getElementById("tree");

  const SID_KEY = "abcl_sid";
  let sid = localStorage.getItem(SID_KEY);
  if (!sid) {
    sid = "s-" + Math.random().toString(16).slice(2) + "-" + Date.now();
    localStorage.setItem(SID_KEY, sid);
  }

  let afterId = -1;
  let afterEvt = -1;
  const msgNodes = new Map();

  function extractId(line) {
    const m = line.match(/id=([^\s]+)/);
    return m ? m[1] : null;
  }

  function ensureNode(id, title) {
    if (msgNodes.has(id)) return msgNodes.get(id);
    if (!tree) return null;

    const root = document.createElement("div");
    root.style.border = "1px solid #333";
    root.style.borderRadius = "8px";
    root.style.padding = "6px";
    root.style.margin = "6px 0";

    const head = document.createElement("div");
    head.textContent = title;
    head.style.color = "#55ff55";
    head.style.fontWeight = "700";

    const body = document.createElement("div");
    body.style.marginTop = "4px";
    body.style.paddingLeft = "10px";

    root.appendChild(head);
    root.appendChild(body);
    tree.appendChild(root);

    const node = { root, head, body };
    msgNodes.set(id, node);
    return node;
  }

  function addChild(id, text, kind) {
    const node = ensureNode(id, "id=" + id);
    if (!node) return;
    const row = document.createElement("div");
    row.textContent = text;
    row.style.whiteSpace = "pre-wrap";
    if (kind === "reply") row.style.color = "#66ccff";
    else if (kind === "failed") {
      row.style.color = "#ff5555";
      row.style.fontWeight = "700";
    } else {
      row.style.color = "#ffff66";
    }
    node.body.appendChild(row);
  }

  function parseAtom(s) {
    s = s.trim();
    if (!s) return null;
    if (
      (s.startsWith("\"") && s.endsWith("\"")) ||
      (s.startsWith("'") && s.endsWith("'"))
    ) {
      return s.substring(1, s.length - 1);
    }
    if (s === "true") return true;
    if (s === "false") return false;
    if (s === "null") return null;
    const n = Number(s);
    if (Number.isFinite(n)) return n;
    return s;
  }

  async function pollLogs() {
    try {
      const r = await fetch("/api/log?sid=" + encodeURIComponent(sid) + "&after=" + afterId);
      if (r.ok) {
        const j = await r.json();
        if (typeof j.next === "number") afterId = j.next;
        if (j.lines && j.lines.length && log) {
          const NL = String.fromCharCode(10);
          log.textContent += j.lines.join(NL) + NL;
          log.scrollTop = log.scrollHeight;
        }
      }
    } catch (e) {
      if (out) out.textContent = "poll log error: " + e;
    }
    setTimeout(pollLogs, 500);
  }

  async function pollEvents() {
    try {
      const r = await fetch("/api/events?after=" + afterEvt);
      if (r.ok) {
        const j = await r.json();
        if (typeof j.next === "number") afterEvt = j.next;
        if (j.lines && j.lines.length) {
          for (const line of j.lines) {
            if (events) {
              const row = document.createElement("div");
              row.textContent = line;
              row.style.whiteSpace = "pre-wrap";
              if (line.startsWith("[FAILED]")) {
                row.style.color = "#ff5555";
                row.style.fontWeight = "700";
              } else if (line.startsWith("[ACCEPTED]")) {
                row.style.color = "#55ff55";
              } else if (line.startsWith("[REPLY]")) {
                row.style.color = "#66ccff";
              } else {
                row.style.color = "#ffff66";
              }
              events.appendChild(row);
              events.scrollTop = events.scrollHeight;
            }

            const id = extractId(line);
            if (id) {
              if (line.startsWith("[ACCEPTED]")) {
                const node = ensureNode(id, line);
                if (node) {
                  node.head.textContent = line;
                  node.head.style.color = "#55ff55";
                }
              } else if (line.startsWith("[FAILED]")) {
                addChild(id, line, "failed");
              } else if (line.startsWith("[REPLY]")) {
                addChild(id, line, "reply");
              } else {
                addChild(id, line, "event");
              }
            }
          }
        }
      }
    } catch (e) {
      if (out) out.textContent = "poll events error: " + e;
    }
    setTimeout(pollEvents, 500);
  }

  async function sendMessage() {
    const to = document.getElementById("to")?.value || "";
    const method = document.getElementById("method")?.value || "";
    const argsRaw = document.getElementById("args")?.value || "";
    const unsafe = document.getElementById("unsafe")?.checked || false;

    const payload = {
      sid,
      to,
      method,
      args: argsRaw
        .split(",")
        .map((s) => s.trim())
        .filter((s) => s.length > 0)
        .map(parseAtom),
      from: "browser",
      unsafe
    };

    try {
      if (out) out.textContent = "sending...";
      const r = await fetch("/api/json/send", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload)
      });
      const t = await r.text();
      if (out) out.textContent = "send: " + t;
    } catch (e) {
      if (out) out.textContent = "send error: " + e;
    }
  }

  window.send = sendMessage;

  if (out) out.textContent = "JS loaded, sid=" + sid;
  pollLogs();
  pollEvents();
});
