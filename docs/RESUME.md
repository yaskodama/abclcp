# ABCL/c+ AIOS 作業再開メモ

次回この作業を再開するときは、まずリポジトリに移動します。

```sh
cd /Users/kodamay/aios/abclcp
```

作業ツリーの状態確認:

```sh
git status
```

ビルド確認:

```sh
cd src
opam exec -- make
```

セッション型サンプルの実行:

```sh
cd /Users/kodamay/aios/abclcp
sh scripts/run_session_protocol.sh
```

AIOS スモークテスト:

```sh
sh scripts/aios_smoke.sh
```

Codex に続きから依頼する例:

```text
/Users/kodamay/aios/abclcp で、ABCL/c+ の AIOS セッション型実装の続きを進めて下さい。
まず git status と scripts/run_session_protocol.sh を確認して下さい。
```

現在の主な作業内容:

- ABCL/c+ にセッション型プロトコルの実行時検査を追加
- `protocol_define`, `protocol_start`, `protocol_state`, `protocol_end`, `protocol_events` を追加
- 協調 AIOS サンプルへセッション型を導入
- `scripts/run_session_protocol.sh` で基本サンプルを実行可能

区切りとして保存する場合は、次回または終了前に「ここまでをチェックインして下さい」と依頼してください。
