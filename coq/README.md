# AIPL⁻ / ABCM の Coq 形式化

AIPL（ABCL/c+）の、型健全性と型安全性が証明できる範囲 **AIPL⁻** の形式化。

再開・全体像は **[HANDOFF.md](HANDOFF.md)** を参照。

## ビルド

```bash
export PATH="$HOME/.opam/5.1.1/bin:$PATH"   # Coq / Rocq Prover 9.1.0
make          # すべてビルド
make check    # 主定理 14 個の Print Assumptions を確認
```

## ファイル

| ファイル | 内容 |
|---|---|
| `AIPLSoundness.v` | AIPL⁻ の型健全性・型安全性（progress は三択） |
| `AIPLDining.v` | 哲学者の食事問題のデッドロック自由、優先度規律の必要十分 |
| `ABCMEmbedding.v` | ABCM ⊂ AIPL⁻ の埋め込み |
| `ABCMEmbedding_simulation_WIP.v` | **未完**。構成レベルのシミュレーション。`make` からは除外 |
| `AbclSoundness.v` | 旧レポートの形式化（閉じた式のみ。参考） |

レポート: [`../docs/aipl_soundness_ja.pdf`](../docs/aipl_soundness_ja.pdf)（28 頁）

## ABCM.v について

`ABCMEmbedding.v` は ABCM の形式化 `ABCM.v` を `Require` する。原本は別リポジトリ
（`yaskodama/abcm-soundness`、非公開）にあり、**この公開リポジトリには含めていない**。
ビルドするには次のいずれかで用意する。

```bash
ln -s /path/to/abcm-soundness/ABCM.v ABCM.v     # 推奨（原本は一つ）
# または
cp /path/to/abcm-soundness/ABCM.v ABCM.v
```

`ABCM.v` が無い場合、`AIPLSoundness.v` と `AIPLDining.v` は問題なくビルドできる
（埋め込みだけがビルドできない）。
