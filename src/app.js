document.addEventListener("DOMContentLoaded", () => {
  const SID_KEY = "abcl_sid";
  let sid = localStorage.getItem(SID_KEY);
  if (!sid) {
    sid = "s-" + Math.random().toString(16).slice(2) + "-" + Date.now();
    localStorage.setItem(SID_KEY, sid);
  }

  let afterEvt = -1;
  let afterLog = -1;
  const out = document.getElementById("out");
  const logBox = document.getElementById("log");
  const eventsBox = document.getElementById("events");
  const repliesBox = document.getElementById("replies");
  const treeBox = document.getElementById("tree");
  const msgNodes = new Map();

  function text(id) {
      return document.getElementById(id);
  }

  function extractId(line) {
    const m = line.match(/id=([^\s]+)/);
    return m ? m[1] : null;
  }

  function ensureNode(id, title) {
    if (msgNodes.has(id)) return msgNodes.get(id);
    if (!treeBox) return null;
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
    treeBox.appendChild(root);
    const node = { root, head, body };
    msgNodes.set(id, node);
    return node;
  }

  function addTreeChild(id, text, kind) {
    const node = ensureNode(id, "id=" + id);
    if (!node) return;
    const row = document.createElement("div");
    row.textContent = text;
    row.style.whiteSpace = "pre-wrap";

    if (kind === "reply") {
      row.style.color = "#66ccff";
    } else if (kind === "failed") {
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
    
  function appendEventLine(line) {
    if (!eventsBox) return;

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

    eventsBox.appendChild(row);
    eventsBox.scrollTop = eventsBox.scrollHeight;

    const id = extractId(line);
      if (!id) return;

      
    if (line.startsWith("[ACCEPTED]")) {
      const node = ensureNode(id, line);
      if (node) {
        node.head.textContent = line;
        node.head.style.color = "#55ff55";
      }
    } else if (line.startsWith("[FAILED]")) {
      addTreeChild(id, line, "failed");
    } else if (line.startsWith("[REPLY]")) {
      addTreeChild(id, line, "reply");
    } else {
      addTreeChild(id, line, "event");
    }
  }

  async function pollLogs() {
    try {
      const r = await fetch("/api/log?sid=" + encodeURIComponent(sid) + "&after=" + afterLog);
      if (r.ok) {
        const j = await r.json();
        if (typeof j.next === "number") afterLog = j.next;

        if (j.lines && j.lines.length && logBox) {
          const NL = String.fromCharCode(10);
          logBox.textContent += j.lines.join(NL) + NL;
          logBox.scrollTop = logBox.scrollHeight;
        }
      }
    } catch (e) {
      if (out) out.textContent = "poll log error: " + e;
    }
    setTimeout(pollLogs, 700);
  }

  async function pollEvents() {
    try {
      const r = await fetch("/api/events?after=" + afterEvt);
      if (r.ok) {
        const j = await r.json();
        if (typeof j.next === "number") afterEvt = j.next;

        if (j.lines && j.lines.length) {
          for (const line of j.lines) {
            appendEventLine(line);

            if (line.startsWith("[REPLY]") && repliesBox) {
              repliesBox.textContent += line + "\n";
              repliesBox.scrollTop = repliesBox.scrollHeight;
            }
          }
        }
      }
    } catch (e) {
      if (out) out.textContent = "poll events error: " + e;
    }
    setTimeout(pollEvents, 700);
      }

  async function sendJsonMessage() {
    const to = text("to")?.value || "";
    const method = text("method")?.value || "";
    const argsRaw = text("args")?.value || "";
    const unsafe = text("unsafe")?.checked || false;

    const payload = {
      sid,
      to,
      method,
      args: argsRaw
        .split(",")
        .map(s => s.trim())
        .filter(s => s.length > 0)
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

  function openServerConsole() {
    const w = window.open("", "_blank", "width=1000,height=700");
    if (!w) {
      if (out) out.textContent = "Popup blocked";
      return;
    }

    w.document.open();
    w.document.write(`
<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <title>ABCL Server Console</title>
  <style>
    body { margin: 0; background: #111; color: #ddd; }
  </style>
</head>
<body>
  <script src="/console_server.js"></script>
</body>
</html>
`);
    w.document.close();
  }

  function openBrowserConsole() {
    const w = window.open("", "_blank", "width=1000,height=700");
    if (!w) {
      if (out) out.textContent = "Popup blocked";
      return;
    }

    w.document.open();
    w.document.write(`
<!doctype html>
<html>
<head>
  <meta charset="utf-8">
  <title>ABCL Browser Console</title>

 <style>
    body { margin: 0; background: #111; color: #ddd; }
  </style>
</head>
<body>
  <script src="/console_browser.js"></script>
</body>
</html>
`);
    w.document.close();
  }

  function installButtons() {
    const host = document.body;
    const wrap = document.createElement("div");
    wrap.style.marginTop = "12px";
    wrap.style.padding = "8px";
    wrap.style.border = "1px solid #ccc";
    wrap.style.background = "#fafafa";

    const title = document.createElement("div");
    title.textContent = "Console / Quick Operations";
    title.style.fontWeight = "700";
    title.style.marginBottom = "8px";
    wrap.appendChild(title);

    const openBtn = document.createElement("button");
    openBtn.textContent = "Open Console (Server)";
    openBtn.style.marginRight = "8px";
    openBtn.onclick = openServerConsole;
    wrap.appendChild(openBtn);

    const browserBtn = document.createElement("button");
    browserBtn.textContent = "Open Browser Console";
    browserBtn.style.marginRight = "8px";
    browserBtn.onclick = openBrowserConsole;
    wrap.appendChild(browserBtn);

    const sendBtn = document.createElement("button");
    sendBtn.textContent = "Send Message";
    sendBtn.style.marginRight = "8px";
    sendBtn.onclick = sendJsonMessage;
    wrap.appendChild(sendBtn);

    const refreshBtn = document.createElement("button");
    refreshBtn.textContent = "Refresh Events";
    refreshBtn.onclick = pollEvents;
    wrap.appendChild(refreshBtn);

    host.insertBefore(wrap, host.firstChild);
  }

  window.send = sendJsonMessage;
  window.openServerConsole = openServerConsole;
  window.openBrowserConsole = openBrowserConsole;
  installButtons();

  if (out) out.textContent = "JS loaded, sid=" + sid;

  pollLogs();
  pollEvents();
});
