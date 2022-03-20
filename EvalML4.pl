:- set_prolog_flag(double_quotes, chars).
:- op(590,yfx, ::).
:- op(600,xfy, ⇩).
:- op(800,xfx, plus).
:- op(800,xfx, minus).
:- op(800,xfx, times).
:- op(800,xfx, lessThan).
:- op(900,xfx, in).
:- op(900,xfx, with).
:- op(990,xfx, ⱶ).

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

digit(C)   --> [C], { code_type(C, digit) }.

alpha_alnums([C|Cs]) --> alpha(C), alnums(Cs).
alpha_alnums([C]) --> alpha(C).

alnums([C|Cs]) --> (alpha(C) | digit(C)), alnums(Cs).
alnums([C])    --> alpha(C) | digit(C).

alpha(C) --> [C], { code_type(C, alpha) }.

% parse
% expr ::= term | expr + term | expr - term | expr < term | term :: expr
expr(E)      --> term(T), expr1(T, E).
expr(T :: E) --> term(T), [::], expr(E).
expr1(E1, E) --> "<", term(T), expr1(E1 < T, E).
expr1(E1, E) --> "+", term(T), expr1(E1 + T, E).
expr1(E1, E) --> "-", term(T), expr1(E1 - T, E).
expr1(E, E)  --> [].

% term ::= factor | term * factor
term(T) --> factor(F), term1(F, T).
term1(E1, E) --> "*", term(T), expr1(E1 * T, E).
term1(E, E)  --> [].

% factor ::= farg         -- function body or argument
%          | factor farg  -- function application
factor(F) --> farg(A), factor1(A, F).
factor1(F1, F) --> farg(A), factor1(app(F1,A), F).
factor1(E, E) --> [].

% farg ::= int | bool | var | '(' expr ')' | '[' ']''
%        | 'if' expr 'then' expr 'else' expr
%        | 'let' var '=' expr 'in' expr
%        | 'letrec' var '=' fun var '->' expr 'in' expr
%        | 'fun' var '->' expr
%        | 'match' expr 'with' '[' ']' '->' expr '|' var '::' var '->' expr
farg(int(I)) --> [int(I)].
farg(bool(B)) --> [bool(B)].
farg(var(X)) --> [var(X)].
farg(E) --> "(", expr(E), ")".
farg(nil) --> "[]".
% if e1 then e2 else e3
farg(if(E1, E2, E3)) -->
    [if], expr(E1), [then], expr(E2), [else], expr(E3).
% let x = e1 in e2
farg(let(X = E1 in E2)) -->
    [let, var(X), =], expr(E1), [in], expr(E2).
% let rec x = fun y -> e1 in e2
farg(letrec(X = fun(Y -> E1) in E2)) -->
    [let, rec, var(X), =, fun, var(Y), ->], expr(E1), [in], expr(E2).
% fun x -> e
farg(fun(X -> E)) -->
    [fun, var(X), ->], expr(E).
% match e1 with [] -> e2 | x :: y -> e3
farg(match(E1 with [] -> E2, X :: Y -> E3)) -->
    [match], expr(E1), [with, '[', ']', ->], expr(E2),
    ['|', var(X), ::, var(Y), ->], expr(E3).

% eval

% --------- E-Int
% C ⱶ i ⇩ i
_ ⱶ int(I) ⇩ I.

% --------- E-Bool
% C ⱶ b ⇩ b
_ ⱶ bool(B) ⇩ B.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   i1 plus i2 is i3
% -------------------------------------------- E-Plus
% C ⱶ e1 + e2 ⇩ i3
C ⱶ E1 + E2 ⇩ I3 :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 plus I2 is I3.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   i1 minus i2 is i3
% --------------------------------------------- E-Minus
% C ⱶ e1 - e2 ⇩ i3
C ⱶ (E1 - E2) ⇩ I3 :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 minus I2 is I3.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   i1 times i2 is i3
% ------------------------------------------------- E-Times
% C ⱶ e1 * e2 ⇩ i3
C ⱶ E1 * E2 ⇩ I3 :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 times I2 is I3.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   i1 less than i2 is i3
% ----------------------------------------------------- E-LessThan
% C ⱶ e1 < e2 ⇩ i3
C ⱶ (E1 < E2) ⇩ B :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 lessThan I2 is B.

% C ⱶ e1 ⇩ true   C ⱶ e2 ⇩ v
% ----------------------------- E-IfT
% C ⱶ if e1 then e2 else e3 ⇩ v
C ⱶ if(E1, E2, _) ⇩ V :-
    C ⱶ E1 ⇩ true, C ⱶ E2 ⇩ V.

% C ⱶ e1 ⇩ false    C ⱶ e3 ⇩ v
% ----------------------------- E-IfF
% C ⱶ if e1 then e2 else e3 ⇩ v
C ⱶ if(E1, _, E3) ⇩ V :-
    C ⱶ E1 ⇩ false, C ⱶ E3 ⇩ V.

% C ⱶ e1 ⇩ v1   C, x = v1 ⱶ e2 ⇩ v
% -------------------------------- E-Let
% C ⱶ let x = e1 in e2 ⇩ v
C ⱶ let(X = E1 in E2) ⇩ V :-
    C ⱶ E1 ⇩ V1, [X = V1 | C] ⱶ E2 ⇩ V. 

% C, x = (ε)[rec x = fun y -> e1] ⱶ e2 ⇩ v 
% ---------------------------------------- E-LetRec
% C ⱶ let rec x = fun y -> e1 in e2 ⇩ v
C ⱶ letrec(X = fun(Y -> E1) in E2) ⇩ V :-
    [X = cls(C, X = fun(Y -> E1)) | C] ⱶ E2 ⇩ V.

% ---------------- E-Var1
% C, x = v ⱶ x ⇩ v
[X = V | _] ⱶ var(X) ⇩ V.

% (y != x)   C ⱶ x ⇩ v2
% --------------------- E-Var2
% C, y = v1 ⱶ x ⇩ v2
[Y = _ | C] ⱶ var(X) ⇩ V :-
    Y \== X, C ⱶ var(X) ⇩ V.

% --------------------------------- E-Fun
% C ⱶ fun x -> e ⇩ (C) [fun x -> e]
C ⱶ fun(X -> E) ⇩ cls(C, fun(X -> E)).

% C ⱶ e1 ⇩ (C2) [fun x -> e0]   
% C ⱶ e2 ⇩ v2   C2, x = v2 ⱶ e0 ⇩ v
% --------------------------------- E-App
% C ⱶ e1 e2 ⇩ v
C ⱶ app(E1, E2) ⇩ V :-
    C ⱶ E1 ⇩ cls(C2, fun(X -> E0)),
    C ⱶ E2 ⇩ V2,
    [X = V2 | C2] ⱶ E0 ⇩ V.

% C ⱶ e1 ⇩ (C2) [rec x = fun y -> e0]   C ⱶ e2 ⇩ v2 
% C2, x = (C2) [rec x = fun y -> e0], y = v2 ⱶ e0 ⇩ v
% --------------------------------------------------- E-AppRec
% C ⱶ e1 e2 ⇩ v
C ⱶ app(E1, E2) ⇩ V :-
    C ⱶ E1 ⇩ cls(C2, X = fun(Y -> E0)),
    C ⱶ E2 ⇩ V2,
    [Y = V2, X = cls(C2, X = fun(Y -> E0)) | C2] ⱶ E0 ⇩ V.

% ----------- E-Nil
% C ⱶ [] ⇩ []
_ ⱶ nil ⇩ [].

% C ⱶ e1 ⇩ v1   C ⱶ e2 ⇩ v2
% ------------------------ E-Cons
% C ⱶ e1 :: e2 ⇩ v1 :: v2
C ⱶ E1 :: E2 ⇩ [V1 | V2] :-
    C ⱶ E1 ⇩ V1, C ⱶ E2 ⇩ V2.

% C ⱶ e1 ⇩ []    C ⱶ e2 ⇩ v
% --------------------------------------------- E-MatchNil
% C ⱶ match e1 with [] -> e2 | x :: y -> e3 ⇩ v
C ⱶ match(E1 with [] -> E2, _ :: _ -> _) ⇩ V :-
    C ⱶ E1 ⇩ [], C ⱶ E2 ⇩ V.

% C ⱶ e1 ⇩ v1 :: v2    C, y = v2, x = v1 ⱶ e3 ⇩ v
% ----------------------------------------------- E-MatchCons
% C ⱶ match e1 with [] -> e2 | x :: y -> e3 ⇩ v
C ⱶ match(E1 with [] -> _, X :: Y -> E3) ⇩ V :-
    C ⱶ E1 ⇩ [V1 | V2],
    [X = V1, Y = V2 | C] ⱶ E3 ⇩ V.

% (i3 = i1 + i2)
% ---------------- B-Plus
% i1 plus i2 is i3
I1 plus I2 is I3 :-
    I3 is I1 + I2.

% (i3 = i1 - i2)
% ---------------- B-Minus
% i1 minus i2 is i3
I1 minus I2 is I3 :-
     I3 is I1 - I2.

% (i3 = i1 * i2)
% ---------------- B-Times
% i1 times i2 is i3
I1 times I2 is I3 :-
     I3 is I1 * I2.

% (b3 = i1 < i2)
% ---------------- B-LessThan
% i1 less than i2 is b3
I1 lessThan I2 is B :-
     I1 < I2 -> B = true; B = false.

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(Expr), Tokens),
    [] ⱶ Expr ⇩ Result, !.

code_expr(Code, Expr) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(Expr), Tokens).

code_tokens(Code, Tokens) :-
    phrase(tokens(Tokens), Code).

% test
test(Code, Expected) :-
    code_result(Code, Actual),
    (Expected = Actual -> writef('%s => %w\n', [Code, Actual]);
    writef('%s => %w expected, but got %w\n', [Code, Expected, Actual]), fail).

tests :-
    test("42", 42),
    test("1 + 2", 3),
    test("3 + 4 - 2", 5),
    test("10 - 1 - 2", 7),
    test("1 + 2 * 3", 7),
    test("(1 + 2) * 3", 9),
    test("1 < 2", true),
    test("2 < 1", false),    
    test("if 1 < 2 then 3 else 4", 3),
    test("if 2 < 1 then 3 else 4", 4),
    test("if true then 1 else 2", 1),
    test("if false then 1 else 2", 2),
    test("let x = 1 in x + 2", 3),
    test("let x = 1 in let y = 2 in x + y", 3),
    test("let x = 1 in let x = 2 in x + x", 4),
    test("let double = fun x -> x + x in double 1", 2),
    test("(fun x -> fun y -> x + y) 1 2", 3),
    test("let rec fact = fun n -> if n < 2 then 1 else n * fact (n - 1) in fact 5", 120),
    test("let rec fib = fun n -> if n < 2 then n else fib (n - 1) + fib (n - 2) in fib 10", 55),
    test("match [] with [] -> 1 | a :: b -> a", 1),
    test("let x = [] in match x with [] -> 1 | a :: b -> a", 1),
    test("match 1 :: 2 :: 3 :: [] with [] -> 4 | a :: b -> a", 1),
    test("match 1 :: 2 :: 3 :: [] with [] -> 4 | a :: b -> b", [2, 3]),
    test("let rec length = fun x -> match x with [] -> 0 | a :: b -> 1 + length b in length (10 :: 20 :: 30 :: [])", 3),
    test("1", 1).    