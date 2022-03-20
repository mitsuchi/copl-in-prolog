:- set_prolog_flag(double_quotes, chars).
:- op(700,xfx,is).
:- op(800,xfx,⇩).
:- op(800,xfx,plus).
:- op(800,xfx,minus).
:- op(800,xfx,times).
:- op(800,xfx,lessThan).
:- op(900,xfx,in).
:- op(990,xfx,ⱶ).

% tokenize
tokens(Ts) --> " ", tokens(Ts).
tokens([T|Ts]) --> tok(T), !, tokens(Ts).
tokens([]) --> "".

tok(int(I)) --> digits(Cs), { number_chars(I, Cs) }.
tok(bool(true)) --> "true".
tok(bool(false)) --> "false".
tok(+) --> "+".
tok(-) --> "-".
tok(*) --> "*".
tok(<) --> "<".
tok('(') --> "(".
tok(')') --> ")".
tok(=) --> "=".
tok(if) --> "if".
tok(then) --> "then".
tok(else) --> "else".
tok(let) --> "let".
tok(in) --> "in".
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
expr(E)      --> term(T), expr1(T, E).
expr1(E1, E) --> "<", term(T), expr1(E1 < T, E).
expr1(E1, E) --> "+", term(T), expr1(E1 + T, E).
expr1(E1, E) --> "-", term(T), expr1(E1 - T, E).
expr1(E, E)  --> [].

term(T) --> factor(F), term1(F, T).
term1(E1, E) --> "*", term(T), expr1(E1 * T, E).
term1(E, E)  --> [].

factor(int(I)) --> [int(I)].
factor(bool(B)) --> [bool(B)].
factor(var(X)) --> [var(X)].
factor(E) --> "(", expr(E), ")".
factor(if(E1, E2, E3)) -->
    [if], expr(E1), [then], expr(E2), [else], expr(E3).
factor(let(X = E1 in E2)) --> [let, var(X), =], expr(E1), [in], expr(E2).

% eval

% 以下では環境を C とする (Context)
% C ⱶ i ⇩ i
_ ⱶ int(I) ⇩ I.

% C ⱶ b ⇩ b
_ ⱶ bool(B) ⇩ B.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   C ⱶ i1 plus i2 is i3
% ------------------------------------------------
% C ⱶ e1 + e2 ⇩ i3
C ⱶ E1 + E2 ⇩ I3 :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 plus I2 is I3.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   C ⱶ i1 minus i2 is i3
% -------------------------------------------------
% C ⱶ e1 - e2 ⇩ i3
C ⱶ E1 - E2 ⇩ I3 :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 minus I2 is I3.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   C ⱶ i1 times i2 is i3
% -------------------------------------------------
% C ⱶ e1 * e2 ⇩ i3
C ⱶ E1 * E2 ⇩ I3 :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 times I2 is I3.

% C ⱶ e1 ⇩ i1   C ⱶ e2 ⇩ i2   C ⱶ i1 less than i2 is i3
% -----------------------------------------------------
% C ⱶ e1 < e2 ⇩ i3
C ⱶ E1 < E2 ⇩ B :-
    C ⱶ E1 ⇩ I1, C ⱶ E2 ⇩ I2, I1 lessThan I2 is B.

% C ⱶ e1 ⇩ true   C ⱶ e2 ⇩ v
% --------------------------
% C ⱶ if e1 then e2 else e3 ⇩ v
C ⱶ if(E1, E2, _) ⇩ V :-
        C ⱶ E1 ⇩ true, C ⱶ E2 ⇩ V.

% C ⱶ e1 ⇩ false   C ⱶ e3 ⇩ v
% -----------------------------
% C ⱶ if e1 then e2 else e3 ⇩ v
C ⱶ if(E1, _, E3) ⇩ V :-
    C ⱶ E1 ⇩ false, C ⱶ E3 ⇩ V.

% C ⱶ e1 ⇩ v1   x = v1, C ⱶ e3 ⇩ v
% --------------------------------
% C ⱶ let x = e1 in e2 ⇩ v
C ⱶ let(X = E1 in E2) ⇩ V :-
    C ⱶ E1 ⇩ V1, [X = V1 | C] ⱶ E2 ⇩ V.

% C, x = v ⱶ x ⇩ v
[X = V | _] ⱶ var(X) ⇩ V.

% (y != x)   C ⱶ x ⇩ v2
% ---------------------
% C, y = v1 ⱶ x ⇩ v2
[Y = _ | C] ⱶ var(X) ⇩ V :-
    Y \== X, C ⱶ var(X) ⇩ V.

I1 plus I2 is I3 :- I3 is I1 + I2.
I1 minus I2 is I3 :- I3 is I1 - I2.
I1 times I2 is I3 :- I3 is I1 * I2.
I1 lessThan I2 is B :- I1 < I2 -> B = true; B = false.

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
    test("1", 1).    