:- set_prolog_flag(double_quotes, chars).
:- op(585,xfy,>>).
:- op(590,xfx,=>).
:- op(600,xfx,evalto).
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

% i => k evalto v
% ---------------
% i >> k evalto v
int(I) >> K evalto V :-
    I => K evalto V.

% b => k evalto v
% ---------------
% b >> k evalto v
bool(B) >> K evalto V :-
    B => K evalto V.

% -----------------
% v => '_' evalto v
V => '_' evalto V.

% e1 >> {_ op e2} >> k evalto v
% ------------------------
% e1 op e2 >> k evalto v
E1 + E2 >> K evalto V :-
    E1 >> {'_' + E2} >> K evalto V.
E1 - E2 >> K evalto V :-
    E1 >> {'_' - E2} >> K evalto V.
E1 * E2 >> K evalto V :-
    E1 >> {'_' * E2} >> K evalto V.
(E1 < E2) >> K evalto V :-
    E1 >> {'_' < E2} >> K evalto V.

% e >> {v1 op _} >> k evalto v2
% ------------------------
% v1 => {_ op e} >> k evalto v2
V1 => {'_' + E} >> K evalto V2 :-
    E >> {V1 + '_'} >> K evalto V2.
V1 => {'_' - E} >> K evalto V2 :-
    E >> {V1 - '_'} >> K evalto V2.
V1 => {'_' * E} >> K evalto V2 :-
    E >> {V1 * '_'} >> K evalto V2.
V1 => {'_' < E} >> K evalto V2 :-
    E >> {V1 < '_'} >> K evalto V2.

% i1 plus i2 is i3   i3 ⇒ k evalto v
% -----------------------------
% i2 ⇒ {i1 + _} ≫ k evalto v
I2 => {I1 + '_'} >> K evalto V :-
    I1 plus I2 is I3, I3 => K evalto V.

% i1 minus i2 is i3   i3 ⇒ k ⇓ v
% ----------------------------
% i2 ⇒ {i1 - _} >> k ⇓ v
I2 => {I1 - '_'} >> K evalto V :-
    I1 minus I2 is I3, I3 => K evalto V.

% i1 times i2 is i3   i3 ⇒ k ⇓ v
% ----------------------------
% i2 ⇒ {i1 * _} >> k ⇓ v
I2 => {I1 * '_'} >> K evalto V :-
    I1 times I2 is I3, I3 => K evalto V.

% i1 less than i2 is b3   b3 ⇒ k ⇓ v
% ----------------------------------
% i2 ⇒ {i1 < _} >> k ⇓ v
I2 => {I1 < '_'} >> K evalto V :-
    I1 lessThan I2 is B3, B3 => K evalto V.

% e1 >> {if _ then e2 else e3} >> k ⇓ v
%------------------------------------
% if e1 then e2 else e3 >> k ⇓ v
if(E1, E2, E3) >> K evalto V :-
    E1 >> {if('_', E2, E3)} >> K evalto V.

% e1 >> k ⇓ v
% --------------------------------------
% true ⇒ {if _ then e1 else e2} >> k ⇓ v
true => {if('_', E1, _)} >> K evalto V :-
    E1 >> K evalto V.

% e2 >> k ⇓ v
% ---------------------------------------
% false ⇒ {if _ then e1 else e2} >> k ⇓ v
false => {if('_', _, E2)} >> K evalto V :-
    E2 >> K evalto V.

I1 plus I2 is I3 :-
    I3 is I1 + I2.
I1 minus I2 is I3 :-
    I3 is I1 - I2.
I1 times I2 is I3 :-
    I3 is I1 * I2.
I1 lessThan I2 is B :-
    I1 < I2 -> B = true; B = false.

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    E >> _ evalto Result, !.

code_expr(Code, E) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens).

% test
test(Code, Expected) :-
    code_result(Code, Actual),
    (Expected = Actual -> writef('%s evalto %w\n', [Code, Actual]);
    writef('%s evalto %w expected, but got %w\n', [Code, Expected, Actual]), fail).

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