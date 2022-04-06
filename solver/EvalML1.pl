:- set_prolog_flag(double_quotes, chars).
:- op(590,xfx,~>).
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

tok(int(-I)) --> "-", digits(Cs), { number_chars(I, Cs) }.
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
factor(paren(E)) --> "(", expr(E), ")".
factor(if(E1, E2, E3)) -->
    [if], expr(E1), [then], expr(E2), [else], expr(E3).

% eval

paren(E) ⇓ V ~> (D, W) :-
    E ⇓ V ~> (D, W).

% i ⇓ i -- E-Int
int(I) ⇓ I ~> (D, W) :-
    pp('%w evalto %w by E-Int', [I, I], [], D, W).

% b ⇓ b -- E-Bool
bool(B) ⇓ B ~> (D, W) :-
    pp('%w evalto %w by E-Bool', [B, B], [], D, W).

% e1 ⇓ i1   e2 ⇓ i2   i1 plus i2 is i3
% -------------------------------------- E-Plus
% e1 + e2 ⇓ i3
E1 + E2 ⇓ I3 ~> (D, W) :-
    E1 ⇓ I1 ~> (D1, s(W)),
    E2 ⇓ I2 ~> (D2, s(W)),
    I1 plus I2 is I3 ~> (D3, s(W)),
    pp('%w + %w evalto %w by E-Plus', [E1, E2, I3], [D1, D2, D3], D, W).

% e1 ⇓ i1   e2 ⇓ i2   i1 minus i2 is i3
% --------------------------------------- E-Minus
% e1 - e2 ⇓ i3
E1 - E2 ⇓ I3 ~> (D, W) :-
    E1 ⇓ I1 ~> (D1, s(W)),
    E2 ⇓ I2 ~> (D2, s(W)),
    I1 minus I2 is I3 ~> (D3, s(W)),
    pp('%w - %w evalto %w by E-Minus', [E1, E2, I3], [D1, D2, D3], D, W).

% e1 ⇓ i1   e2 ⇓ i2   i1 times i2 is i3
% ------------------------------------- E-Times
% e1 * e2 ⇓ i3
E1 * E2 ⇓ I3 ~> (D, W) :-
    E1 ⇓ I1 ~> (D1, s(W)),
    E2 ⇓ I2 ~> (D2, s(W)),
    I1 times I2 is I3 ~> (D3, s(W)),
    pp('%w * %w evalto %w by E-Times', [E1, E2, I3], [D1, D2, D3], D, W).

% e1 ⇓ i1   e2 ⇓ i2   i1 less than i2 is b
% ---------------------------------------- E-Lt
% e1 < e2 ⇓ b
(E1 < E2) ⇓ B ~> (D, W) :-
    E1 ⇓ I1 ~> (D1, s(W)),
    E2 ⇓ I2 ~> (D2, s(W)),
    I1 lessThan I2 is B ~> (D3, s(W)),
    pp('%w < %w evalto %w by E-Lt', [E1, E2, B], [D1, D2, D3], D, W).

% e1 ⇓ true   e2 ⇓ v
% ------------------------- E-IfT
% if e1 then e2 else e3 ⇓ v
if(E1, E2, E3) ⇓ V ~> (D, W) :-
    E1 ⇓ true ~> (D1, s(W)),
    E2 ⇓ V ~> (D2, s(W)),
    pp('if %w then %w else %w evalto %w by E-IfT', [E1, E2, E3, V], [D1, D2], D, W).

% e1 ⇓ false   e3 ⇓ v
% ------------------------- E-IfF
% if e1 then e2 else e3 ⇓ v
if(E1, E2, E3) ⇓ V ~> (D, W) :-
    E1 ⇓ false ~> (D1, s(W)),
    E3 ⇓ V ~> (D2, s(W)),
    pp('if %w then %w else %w evalto %w by E-IfF', [E1, E2, E3, V], [D1, D2], D, W).

I1 plus I2 is I3 ~> (D, W) :-
    I3 is I1 + I2,
    pp('%w plus %w is %w by B-Plus', [I1, I2, I3], [], D, W).

I1 minus I2 is I3 ~> (D, W) :-
    I3 is I1 - I2,
    pp('%w minus %w is %w by B-Minus', [I1, I2, I3], [], D, W).

I1 times I2 is I3 ~> (D, W):-
    I3 is I1 * I2,
    pp('%w times %w is %w by B-Times', [I1, I2, I3], [], D, W).

I1 lessThan I2 is B ~> (D, W) :-
    (I1 < I2 ->
    B = true;
    B = false),
    pp('%w less than %w is %w by B-Lt', [I1, I2, B], [], D, W).

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    E ⇓ Result ~> (_, _), !.

derive(Code) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    E ⇓ _ ~> (Derived, _),
    write(Derived), !.

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

% pretty print
indent(z, '').
indent(s(N), S) :-
    indent(N, S1), swritef(S, '  %w', [S1]).

unparse(int(N), N).
unparse(bool(B), B).
unparse(paren(E), U) :-
    unparse(E, U1), swritef(U, '(%w)', [U1]).
unparse(E1 + E2, U1 + U2) :-
    unparse(E1, U1), unparse(E2, U2).
unparse(E1 - E2, U1 - U2) :-
    unparse(E1, U1), unparse(E2, U2).
unparse(E1 * E2, U1 * U2) :-
    unparse(E1, U1), unparse(E2, U2).
unparse(E1 < E2, U1 < U2) :-
    unparse(E1, U1), unparse(E2, U2).
unparse(if(E1, E2, E3), U) :-
    unparse(E1, U1), unparse(E2, U2), unparse(E3, U3),
    swritef(U, 'if %w then %w else %w', [U1, U2, U3]).
unparse(E, E).

pp(Format, Vars, Inners, Derivation, W) :-
    indent(W, Indent),
    maplist(unparse, Vars, UnParsedVars),
    swritef(D1, Format, UnParsedVars),
    reverse(Inners, Rs),
    foldl(concat, Rs, '', InnersStr),
    swritef(Derivation, '%w%w {\n%w%w};\n', [Indent, D1, InnersStr, Indent]).