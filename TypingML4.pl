:- set_prolog_flag(double_quotes, chars).

:- op(990,xfx, ⱶ).
:- op(900,xfx, in).
:- op(900,xfx, with).
:- op(900,xfx, then).
:- op(890,xfx, else).
:- op(600,xfy, ->).
:- op(590,yfx, ::).

% tokenize
tokens(Ts) --> " ", tokens(Ts).
tokens([T|Ts]) --> tok(T), !, tokens(Ts).
tokens([]) --> "".

tok(int(I)) --> digits(Cs), { number_chars(I, Cs) }.
tok(bool(true)) --> "true".
tok(bool(false)) --> "false".
tok(+) --> "+".
tok(->) --> "->".
tok(-) --> "-".
tok(*) --> "*".
tok(<) --> "<".
tok('(') --> "(".
tok(')') --> ")".
tok('[') --> "[".
tok(']') --> "]".
tok('|') --> "|".
tok(=) --> "=".
tok(::) --> "::".
tok(if) --> "if".
tok(then) --> "then".
tok(else) --> "else".
tok(let) --> "let".
tok(in) --> "in".
tok(fun) --> "fun".
tok(rec) --> "rec".
tok(match) --> "match".
tok(with) --> "with".
tok(var(Cs)) --> alpha_alnums(Cs).

digits([C|Cs]) --> digit(C), digits(Cs).
digits([C])    --> digit(C).

alpha_alnums([C|Cs]) --> alpha(C), alnums(Cs).
alpha_alnums([C]) --> alpha(C).

alnums([C|Cs]) --> (alpha(C) | digit(C)), alnums(Cs).
alnums([C])    --> alpha(C) | digit(C).

digit(C) --> [C], { code_type(C, digit) }.
alpha(C) --> [C], { code_type(C, alpha) }.

% parse
expr(E)      --> term(T), expr1(T, E).
expr(T :: E) --> term(T), ['::'], expr(E).
expr1(E1, E) --> "<", term(T), expr1(E1 < T, E).
expr1(E1, E) --> "+", term(T), expr1(E1 + T, E).
expr1(E1, E) --> "-", term(T), expr1(E1 - T, E).
expr1(E, E)  --> [].

term(T) --> factor(F), term1(F, T).
term1(E1, E) --> "*", term(T), expr1(E1 * T, E).
term1(E, E)  --> [].

factor(F) --> farg(A), factor1(A, F).
factor1(F1, F) --> farg(A), factor1(app(F1,A), F).
factor1(E, E) --> [].

farg(int(N)) --> [int(N)].
farg(bool(B)) --> [bool(B)].
farg(var(X)) --> [var(X)].
farg(E) --> "(", expr(E), ")".
farg(nil) --> "[", "]".
farg(if(E1, E2, E3)) --> ['if'], expr(E1), ['then'], expr(E2), ['else'], expr(E3).
farg(let(X = E1 in E2)) --> ['let', var(X), '='], expr(E1), ['in'], expr(E2).                        
farg(letrec(X = E1 in E2)) --> ['let', 'rec', var(X), '='], expr(E1), ['in'], expr(E2).
farg(fun(X -> E)) --> ['fun', var(X), '->'], expr(E).
farg(match(E1 with [] -> E2, X :: Y -> E3)) -->
    ['match'], expr(E1), ['with', '[', ']', '->'], expr(E2),
    ['|', var(X), '::', var(Y), '->'], expr(E3).

% type check

% -----------
% C ⱶ i : int    ただし i は 整数
_ ⱶ int(_) : int.

% ------------
% C ⱶ b : bool   ただし b は true または false
_ ⱶ bool(_) : bool.

% C ⱶ e1 : bool   C ⱶ e2 : t   C ⱶ e3 : t
% ---------------------------------------
% C ⱶ if e1 then e2 else e3 : t
C ⱶ if(E1, E2, E3) : T :-
    C ⱶ E1 : bool, C ⱶ E2 : T, C ⱶ E3 : T.

% C ⱶ e1 : int   C ⱶ e2 : int
% ---------------------------
% C ⱶ e1 + e2 : int
C ⱶ E1 + E2 : int :-
    C ⱶ E1 : int, C ⱶ E2 : int.

% C ⱶ e1 : int   C ⱶ e2 : int
% ---------------------------
% C ⱶ e1 - e2 : int
C ⱶ E1 - E2 : int :-
    C ⱶ E1 : int, C ⱶ E2 : int.

% C ⱶ e1 : int   C ⱶ e2 : int
% ---------------------------
% C ⱶ e1 * e2 : int
C ⱶ E1 * E2 : int :-
    C ⱶ E1 : int, C ⱶ E2 : int.

% C ⱶ e1 : int   C ⱶ e2 : int
% ---------------------------
% C ⱶ e1 < e2 : bool
C ⱶ (E1 < E2) : bool :-
    C ⱶ E1 : int, C ⱶ E2 : int.

% (C (x) = t)
% ----------- T-Var
% C ⱶ x : t
C ⱶ var(X) : T :-
    first(X:T,C).

% C, x : t1 ⱶ e : t2
% ------------------------- T-Fun
% C ⱶ fun x -> e : t1 -> t2
C ⱶ fun(X -> E) : (T1 -> T2) :-
    [X : T1 | C] ⱶ E : T2.


% C ⱶ e1 : t1 -> t2   C ⱶ e2 : t1
% ------------------------------- T-App
% C ⱶ e1 e2 : t1
C ⱶ app(E1, E2) : T2 :-
    C ⱶ E1 : T1 -> T2,
    C ⱶ E2 : T1.

% C ⱶ e1 : t1   C, x : t1 ⱶ e2 : t2
% --------------------------------- T-Let
% C ⱶ let x = e1 in e2 : t2
C ⱶ let(X = E1 in E2) : T2 :-
    C ⱶ E1 : T1,
    [X : T1 | C] ⱶ E2 : T2.

% C, x : t1 -> t2, y : t1 ⱶ e1 : t2
% C, y : t1 -> t2 ⱶ e2 : t
% ------------------------------------ T-LetRec
% C ⱶ letrec x = fun y -> e1 in e2 : t
C ⱶ letrec(X = fun(Y -> E1) in E2) : T :-
   [Y : T1, X : (T1 -> T2) | C] ⱶ E1 : T2,
   [X : (T1 -> T2) | C] ⱶ E2 : T.

% C ⱶ e1 : t   C ⱶ e2 : t list
% ----------------------------- T-Cons
% C ⱶ e1 :: e2 : t list
C ⱶ (E1 :: E2) : list(T) :-
    C ⱶ E1 : T, C ⱶ E2 : list(T).

% ---------------- T-Nil
% C ⱶ [] :: t list
_ ⱶ nil : list(_).                  

% C, x : t1, y : t2 list ⱶ e3 : t
% C ⱶ e2 : t   C ⱶ e1 : t1 list
% -------------------------------------------- T-Match
% C ⱶ match e1 with [] -> e2, x :: y -> e3 : t
C ⱶ match(E1 with [] -> E2, X :: Y -> E3) : T :-
    C ⱶ E1 : list(T1), C ⱶ E2 : T,
    [Y : list(T1), X : T1 | C] ⱶ E3 : T.

first(K:V,[K1:V1|_]) :- K = K1, V=V1.
first(K:V,[K1:_|Xs]) :- K\==K1, first(K:V, Xs).

% UI
code_result(String, Type) :-
    phrase(tokens(Tokens), String),
    phrase(expr(E), Tokens),
    [] ⱶ E : Type.

code_expr(String, Ast) :-
    phrase(tokens(Tokens), String),
    phrase(expr(Ast), Tokens).

code_tokens(String, Tokens) :-
    phrase(tokens(Tokens), String).

test(Code, Expected) :-
    code_result(Code, Actual),
    ((Expected = Actual) -> writef('%s => %w\n', [Code, Actual]);
    writef('%s => %w expected, but got %w\n', [Code, Expected, Actual]), fail).

tests :-
    test("42", int),
    test("3 + 5", int),
    test("let x = 3 < 2 in let y = 5 in if x then y else 2", int),
    test("fun f -> f 0 + f 1", (int -> int) -> int),
    test("let k = fun x -> fun y -> x in k 3 true", int),
    test("let k = fun x -> fun y -> x in k (1 :: []) 3", list(int)),
    test("let rec fact = fun n -> if n < 2 then 1 else n * fact (n - 1) in fact 3", int),
    test("let l = (fun x -> x) :: (fun y -> 2) :: (fun z -> z + 3) :: [] in 2", int),
    test("let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in length", list(int) -> int),
    test("let compose = fun f -> fun g -> fun x -> f (g x) in let p = fun x -> x * x in let q = fun x -> x + 4 in compose p q", int -> int),
    test("let l = (fun x -> x) :: (fun y -> 2) :: (fun z -> z + 3) :: [] in 2", int),
    test("let rec length = fun l -> match l with [] -> 0 | x :: y -> 1 + length y in length ((fun x -> x) :: (fun y -> y + 3) :: [])", int),
    test("1", int), !.

