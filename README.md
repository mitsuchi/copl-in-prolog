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

第1章の Nat の実装です。ペアノ自然数の足し算と掛け算を行います。

例）
```s(z) plus s(z) is s(s(z))```

## CompareNat[1-3].pl

第1章の CompareNat1 から 3 までの実装です。ペアノ自然数どうしの大小を比較します。

例）
```s(z) isLessThan s(s(z))```

## EvalNatExp.pl

第1章の EvalNatExp の実装です。足し算と掛け算からなる式を評価します。

例）
```s(s(z)) + z ⇓ s(s(z))```

## ReduceNatExp.pl

第1章の ReduceNatExp の実装です。足し算と掛け算からなる式を簡約します。

例）
```s(z) * s(z) + s(z) * s(z) --> s(z) * s(z) + s(z)```

## EvalNat1.pl

第3章の NatExp の実装です。整数とif式を評価します。

例）
```if 1 < 2 then 3 else 4```