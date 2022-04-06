:- set_prolog_flag(double_quotes, chars).
:- op(590,xfx, ~>).
:- op(700,xfx, is).
:- op(800,xfx, evalto).
:- op(800,xfx, plus).
:- op(800,xfx, minus).
:- op(800,xfx, times).
:- op(800,xfx, lessThan).
:- op(900,xfx, in).
:- op(990,xfx, ⱶ).

% tokenize
tokens(Ts) --> " ", tokens(Ts).
tokens([T|Ts]) --> tok(T), !, tokens(Ts).
tokens([]) --> "".

tok(num(I)) --> "#", digits(Cs), { number_chars(I, Cs) }.
tok(int(-I)) --> "-", digits(Cs), { number_chars(I, Cs) }.
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
tok(=) --> "=".
tok(dot) --> ".".
tok(if) --> "if".
tok(then) --> "then".
tok(else) --> "else".
tok(let) --> "let".
tok(in) --> "in".
tok(fun) --> "fun".
tok(rec) --> "rec".

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

factor(F) --> farg(A), factor1(A, F).
factor1(F1, F) --> farg(A), factor1(app(F1,A), F).
factor1(E, E) --> [].

farg(int(I)) --> [int(I)].
farg(bool(B)) --> [bool(B)].
farg(num(X)) --> [num(X)].
farg(paren(E)) --> "(", expr(E), ")".
farg(if(E1, E2, E3)) -->
    [if], expr(E1), [then], expr(E2), [else], expr(E3).
farg(let(dot = E1 in E2)) --> [let, dot, =], expr(E1), [in], expr(E2).  
farg(letrec(dot = fun(dot -> E1) in E2)) -->
    [let, rec, dot, =, fun, dot, ->], expr(E1), [in], expr(E2).
farg(fun(dot -> E)) --> [fun, dot, ->], expr(E).

% eval
% 以下では環境を C とする (Context)

%C ⱶ A evalto B ~> D :-
%    write('C = '), write(C), write(', A = '), writeln(A), fail.

C ⱶ paren(E) evalto V ~> (D, W) :-
    C ⱶ E evalto V ~> (D, W).

% C ⱶ i evalto i
C ⱶ int(I) evalto I ~> (D, W) :-
    pp('%w|- %w evalto %w by E-Int', C, [I, I], [], D, W), !.

% C ⱶ b evalto b
C ⱶ bool(B) evalto B ~> (D, W) :-
    pp('%w|- %w evalto %w by E-Bool', C, [B, B], [], D, W), !.

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 plus i2 is i3
% ------------------------------------------------
% C ⱶ e1 + e2 evalto i3
C ⱶ E1 + E2 evalto I3 ~> (D, W) :-
    C ⱶ E1 evalto I1 ~> (D1, s(W)),
    C ⱶ E2 evalto I2 ~> (D2, s(W)),
    I1 plus I2 is I3 ~> (D3, s(W)),
    pp('%w|- %w + %w evalto %w by E-Plus', C, [E1, E2, I3], [D1, D2, D3], D, W).

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 minus i2 is i3
% -------------------------------------------------
% C ⱶ e1 - e2 evalto i3
C ⱶ E1 - E2 evalto I3 ~> (D, W) :-
    C ⱶ E1 evalto I1 ~> (D1, s(W)),
    C ⱶ E2 evalto I2 ~> (D2, s(W)),
    I1 minus I2 is I3 ~> (D3, s(W)),
    pp('%w|- %w - %w evalto %w by E-Minus', C, [E1, E2, I3], [D1, D2, D3], D, W).

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 times i2 is i3
% -------------------------------------------------
% C ⱶ e1 * e2 evalto i3
C ⱶ E1 * E2 evalto I3 ~> (D, W) :-
    C ⱶ E1 evalto I1 ~> (D1, s(W)),
    C ⱶ E2 evalto I2 ~> (D2, s(W)),
    I1 times I2 is I3 ~> (D3, s(W)),
    pp('%w|- %w * %w evalto %w by E-Times', C, [E1, E2, I3], [D1, D2, D3], D, W).

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 less than i2 is i3
% -----------------------------------------------------
% C ⱶ e1 < e2 evalto i3
C ⱶ E1 < E2 evalto I3 ~> (D, W) :-
    C ⱶ E1 evalto I1 ~> (D1, s(W)),
    C ⱶ E2 evalto I2 ~> (D2, s(W)),
    I1 lessThan I2 is I3 ~> (D3, s(W)),
    pp('%w|- %w < %w evalto %w by E-Lt', C, [E1, E2, I3], [D1, D2, D3], D, W).

% C ⱶ e1 evalto true   C ⱶ e2 evalto v
% --------------------------
% C ⱶ if e1 then e2 else e3 evalto v
C ⱶ if(E1, E2, E3) evalto V ~> (D, W) :-
    C ⱶ E1 evalto true ~> (D1, s(W)),
    C ⱶ E2 evalto V ~> (D2, s(W)),
    pp('%w|- if %w then %w else %w evalto %w by E-IfT', C, [E1, E2, E3, V], [D1, D2], D, W).

% C ⱶ e1 evalto false   C ⱶ e3 evalto v
% -----------------------------
% C ⱶ if e1 then e2 else e3 evalto v
C ⱶ if(E1, E2, E3) evalto V ~> (D, W) :-
    C ⱶ E1 evalto false ~> (D1, s(W)),
    C ⱶ E3 evalto V ~> (D2, s(W)),
    pp('%w|- if %w then %w else %w evalto %w by E-IfF', C, [E1, E2, E3, V], [D1, D2], D, W).

% C ⱶ e1 evalto v1   C, x = v1 ⱶ e3 evalto v
% --------------------------------
% C ⱶ let x = e1 in e2 evalto v
C ⱶ let(dot = E1 in E2) evalto V ~> (D, W) :-
    C ⱶ E1 evalto V1 ~> (D1, s(W)),
    [V1 | C] ⱶ E2 evalto V ~> (D2, s(W)),
    pp('%w|- let . = %w in %w evalto %w by E-Let', C, [E1, E2, V], [D1, D2], D, W).

% C, x = (C)[rec x = fun y -> e1] ⱶ e2 evalto v
% ----------------------------------------
% C ⱶ let rec x = fun y -> e1 in e2 evalto v
C ⱶ letrec(dot = fun(dot -> E1) in E2) evalto V ~> (D, W) :-
    [cls(C, dot = fun(dot -> E1)) | C] ⱶ E2 evalto V ~> (D1, s(W)),
    pp('%w|- let rec . = fun . -> %w in %w evalto %w by E-LetRec', C, [E1, E2, V], [D1], D, W).

% C, v ⱶ x evalto v
C ⱶ num(X) evalto V ~> (D, W) :-
    nth1(X, C, V),
    pp('%w|- #%w evalto %w by E-Var', C, [X, V], [], D, W), !.

% C ⱶ fun x -> e evalto (C) [fun x -> e]
C ⱶ fun(dot -> E) evalto cls(C, fun(dot -> E)) ~> (D, W):-
    pp('%w|- fun . -> %w evalto (%w)[fun . -> %w] by E-Fun', C, [E, C, E], [], D, W).

% C ⱶ e1 evalto (C2) [fun x -> e0]
% C ⱶ e2 evalto v2   C2, x = v2 ⱶ e0 evalto v
% ---------------------------------
% C ⱶ e1 e2 evalto v
C ⱶ app(E1, E2) evalto V ~> (D, W) :-
    C ⱶ E1 evalto cls(C2, fun(dot -> E0)) ~> (D1, s(W)),
    C ⱶ E2 evalto V2 ~> (D2, s(W)),
    [V2 | C2] ⱶ E0 evalto V ~> (D3, s(W)),
    pp('%w|- %w %w evalto %w by E-App', C, [E1, E2, V], [D1, D2, D3], D, W).

% C ⱶ e1 evalto (C2) [rec x = fun y -> e0]
% C ⱶ e2 evalto v2
% C2, x = (C2) [rec x = fun y -> e0], y = v2 ⱶ e0 evalto v
% ---------------------------------------------------
% C ⱶ e1 e2 evalto v
C ⱶ app(E1, E2) evalto V ~> (D, W) :-
    C ⱶ E1 evalto cls(C2, dot = fun(dot -> E0)) ~> (D1, s(W)),
    C ⱶ E2 evalto V2 ~> (D2, s(W)),
    [V2, cls(C2, dot = fun(dot -> E0)) | C2] ⱶ E0 evalto V ~> (D3, s(W)),
    pp('%w|- %w %w evalto %w by E-AppRec', C, [E1, E2, V], [D1, D2, D3], D, W).

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
    [] ⱶ E evalto Result ~> (_, _), !.

derive(Code) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E evalto _ ~> (Derived, _),
    write(Derived), !.

derive(C, Code) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    reverse(C, RC),
    RC ⱶ E evalto _ ~> (Derived, _),
    write(Derived), !.

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
    test("let fact = fun self -> fun n -> if n < 2 then 1 else n * self self (n - 1) in fact fact 3", 6),
    test("1", 1).    

% pretty print
indent(z, '').
indent(s(N), S) :-
    indent(N, S1), swritef(S, '  %w', [S1]).

unparse([], '').
unparse([E], U) :-
    unparse(E, UE), swritef(U, '%w', [UE]).
unparse([E | C], U) :-
    unparse(E, UE), unparse(C, UC), swritef(U, '%w, %w', [UC, UE]).
unparse(int(N), N).
unparse(bool(B), B).
unparse(num(X), UX) :-
    swritef(UX, '#%w', [X]).
unparse(paren(E), U) :-
    unparse(E, U1), swritef(U, '(%w)', [U1]).
unparse(E1 + E2, U) :-
    unparse(E1, U1), unparse(E2, U2), swritef(U, '%w + %w', [U1, U2]).
unparse(E1 - E2, U) :-
    unparse(E1, U1), unparse(E2, U2), swritef(U, '%w - %w', [U1, U2]).
unparse(E1 * E2, U) :-
    unparse(E1, U1), unparse(E2, U2), swritef(U, '%w * %w', [U1, U2]).
unparse(E1 < E2, U) :-
    unparse(E1, U1), unparse(E2, U2), swritef(U, '%w < %w', [U1, U2]).
unparse(fun(dot -> E), S) :-
    unparse(E, UE), swritef(S, 'fun . -> %w', [UE]).
unparse(cls(C, dot = E), S) :-
    unparse(C, UC), unparse(E, UE), swritef(S, '(%w)[rec . = %w]', [UC, UE]).
unparse(cls(C, E), S) :-
    unparse(C, UC), unparse(E, UE), swritef(S, '(%w)[%w]', [UC, UE]).
unparse(if(E1, E2, E3), U) :-
    unparse(E1, U1), unparse(E2, U2), unparse(E3, U3),
    swritef(U, 'if %w then %w else %w', [U1, U2, U3]).
unparse(app(E1, E2), U) :-
    unparse(E1, U1), unparse(E2, U2),
    swritef(U, '%w %w', [U1, U2]).
unparse(let(dot = E1 in E2), U) :-
    unparse(E1, U1), unparse(E2, U2),
    swritef(U, 'let . = %w in %w', [U1, U2]).
unparse(letrec(dot = E1 in E2), U) :-
    unparse(E1, U1), unparse(E2, U2),
    swritef(U, 'let rec . = %w in %w', [U1, U2]).
unparse(E, E).

pp(Format, Vars, Inners, Derivation, W) :-
    indent(W, Indent),
    maplist(unparse, Vars, UnParsedVars),
    swritef(D1, Format, UnParsedVars),
    (Inners = [] -> swritef(Derivation, '%w%w {};\n', [Indent, D1, Indent]);
    reverse(Inners, Rs),
    foldl(concat, Rs, '', InnersStr),
    swritef(Derivation, '%w%w {\n%w%w};\n', [Indent, D1, InnersStr, Indent])).

pp(Format, Context, Vars, Inners, Derivation, W) :-
    indent(W, Indent),
    unparse(Context, UnParsedContext),
    maplist(unparse, Vars, UnParsedVars),
    swritef(D1, Format, [UnParsedContext | UnParsedVars]),
    (Inners = [] -> swritef(Derivation, '%w%w {};\n', [Indent, D1, Indent]);
    reverse(Inners, Rs),
    foldl(concat, Rs, '', InnersStr),
    swritef(Derivation, '%w%w {\n%w%w};\n', [Indent, D1, InnersStr, Indent])).

