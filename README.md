# 書籍「プログラミング言語の基礎概念」の Prolog による実装

『プログラミング言語の基礎概念』（五十嵐淳著、サイエンス社）を勉強するにあたり、各章で定義される言語（OCamlのサブセット）を Prolog で実装したものです。

## 使い方

1. SWI-Prolog をインストールする
2. 各章に対応したプログラムを起動する

例）EvalML4
```
$ swipl EvalML4.pl
```
3. プロンプトで以下のようにコードを実行する
```
?- test("let x = 1 in x + 2", W).
let x = 1 in x + 2 => 3
W = 3.
```
4. またはテスト一式を実行する
```
?- tests.
..
let x = 1 in x + 2 => 3
let rec fib = fun n -> if n < 2 then n else fib (n - 1) + fib (n - 2) in fib 10 => 55
..
true
```

## Nat.pl

第一章の Nat の実装です。ペアノ自然数の足し算と掛け算を行います。

例）
```s(z) plus s(z) is s(s(z))```