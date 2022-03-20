:- set_prolog_flag(double_quotes, chars).
:- op(600,xfy,⇓).
:- op(700,xfx,is).
:- op(800,xfx,plus).
:- op(800,xfx,minus).
:- op(800,xfx,times).
:- op(800,xfx,lessThan).

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
tok(if) --> "if".
tok(then) --> "then".
tok(else) --> "else".

digits([C|Cs]) --> digit(C), digits(Cs).
digits([C])    --> digit(C).

digit(C)   --> [C], { code_type(C, digit) }.

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
factor(E) --> "(", expr(E), ")".
factor(if(E1, E2, E3)) -->
    [if], expr(E1), [then], expr(E2), [else], expr(E3).

% eval

% i ⇓ i
int(I) ⇓ I.

% b ⇓ b
bool(B) ⇓ B.

% e1 ⇓ i1   e2 ⇓ i2   i1 plus i2 is i3
% --------------------------------------
% e1 + e2 ⇓ i3
E1 + E2 ⇓ I3 :-
    E1 ⇓ I1, E2 ⇓ I2, I1 plus I2 is I3.

% e1 ⇓ i1   e2 ⇓ i2   i1 minus i2 is i3
% ---------------------------------------
% e1 - e2 ⇓ i3
E1 - E2 ⇓ I3 :-
    E1 ⇓ I1, E2 ⇓ I2, I1 minus I2 is I3.

% e1 ⇓ i1   e2 ⇓ i2   i1 times i2 is i3
% ---------------------------------------
% e1 * e2 ⇓ i3
E1 * E2 ⇓ I3 :-
    E1 ⇓ I1, E2 ⇓ I2, I1 times I2 is I3.

% e1 ⇓ i1   e2 ⇓ i2   i1 less than i2 is b
% ------------------------------------------
% e1 < e2 ⇓ b
(E1 < E2) ⇓ B :-
    E1 ⇓ I1, E2 ⇓ I2, I1 lessThan I2 is B.

% e1 ⇓ true   e2 ⇓ v
% -------------------------
% if e1 then e2 else e3 ⇓ v
if(E1, E2, _) ⇓ V :-
    E1 ⇓ true, E2 ⇓ V.

% e1 ⇓ false   e3 ⇓ v
% -------------------------
% if e1 then e2 else e3 ⇓ v
if(E1, _, E3) ⇓ V :-
    E1 ⇓ false, E3 ⇓ V.

I1 plus I2 is I3 :- I3 is I1 + I2.
I1 minus I2 is I3 :- I3 is I1 - I2.
I1 times I2 is I3 :- I3 is I1 * I2.
I1 lessThan I2 is B :- I1 < I2 -> B = true; B = false.

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    E ⇓ Result, !.

% test
test(Code, Expected) :-
    code_result(Code, Actual),
    (Expected = Actual -> writef('%s ⇓ %w\n', [Code, Actual]);
    writef('%s ⇓ %w expected, but got %w\n', [Code, Expected, Actual]), fail).

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
    test("1", 1).