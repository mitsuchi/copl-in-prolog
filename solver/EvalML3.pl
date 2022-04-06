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
tok(if) --> "if".
tok(then) --> "then".
tok(else) --> "else".
tok(let) --> "let".
tok(in) --> "in".
tok(fun) --> "fun".
tok(rec) --> "rec".
tok(var(Atom)) --> alpha_alnums(Cs), {atom_string(Atom, Cs)}.

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
farg(var(X)) --> [var(X)].
farg(paren(E)) --> "(", expr(E), ")".
farg(if(E1, E2, E3)) -->
    [if], expr(E1), [then], expr(E2), [else], expr(E3).
farg(let(X = E1 in E2)) --> [let, var(X), =], expr(E1), [in], expr(E2).  
farg(letrec(X = fun(Y -> E1) in E2)) -->
    [let, rec, var(X), =, fun, var(Y), ->], expr(E1), [in], expr(E2).
farg(fun(X -> E)) --> [fun, var(X), ->], expr(E).

% eval
% 以下では環境を C とする (Context)

%C ⱶ A evalto B ~> D :-
%    write('C = '), write(C), write(', A = '), writeln(A), fail.

C ⱶ paren(E) evalto V ~> D :-
    C ⱶ E evalto V ~> D.

% C ⱶ i evalto i
C ⱶ int(I) evalto I ~> D :-
    D = dd('E-Int', C ⱶ int(I) evalto I, []), !.

% C ⱶ b evalto b
C ⱶ bool(B) evalto B ~> D :-
    D = dd('E-Bool', C ⱶ bool(B) evalto B, []), !.

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 plus i2 is i3
% ------------------------------------------------
% C ⱶ e1 + e2 evalto i3
C ⱶ E1 + E2 evalto I3 ~> D :-
    C ⱶ E1 evalto I1 ~> D1,
    C ⱶ E2 evalto I2 ~> D2,
    I1 plus I2 is I3 ~> D3,
    D = dd('E-Plus', C ⱶ E1 + E2 evalto I3, [D1, D2, D3]).

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 minus i2 is i3
% -------------------------------------------------
% C ⱶ e1 - e2 evalto i3
C ⱶ E1 - E2 evalto I3 ~> D :-
    C ⱶ E1 evalto I1 ~> D1,
    C ⱶ E2 evalto I2 ~> D2,
    I1 minus I2 is I3 ~> D3,
    D = dd('E-Minus', C ⱶ E1 - E2 evalto I3, [D1, D2, D3]).

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 times i2 is i3
% -------------------------------------------------
% C ⱶ e1 * e2 evalto i3
C ⱶ E1 * E2 evalto I3 ~> D :-
    C ⱶ E1 evalto I1 ~> D1,
    C ⱶ E2 evalto I2 ~> D2,
    I1 times I2 is I3 ~> D3,
    D = dd('E-Times', C ⱶ E1 * E2 evalto I3, [D1, D2, D3]).

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 less than i2 is i3
% -----------------------------------------------------
% C ⱶ e1 < e2 evalto i3
C ⱶ E1 < E2 evalto I3 ~> D :-
    C ⱶ E1 evalto I1 ~> D1,
    C ⱶ E2 evalto I2 ~> D2,
    I1 lessThan I2 is I3 ~> D3,
    D = dd('E-Lt', C ⱶ E1 < E2 evalto I3, [D1, D2, D3]).

% C ⱶ e1 evalto true   C ⱶ e2 evalto v
% --------------------------
% C ⱶ if e1 then e2 else e3 evalto v
C ⱶ if(E1, E2, E3) evalto V ~> D :-
    C ⱶ E1 evalto true ~> D1,
    C ⱶ E2 evalto V ~> D2,
    D = dd('E-IfT', C ⱶ if(E1, E2, E3) evalto V, [D1, D2]).

% C ⱶ e1 evalto false   C ⱶ e3 evalto v
% -----------------------------
% C ⱶ if e1 then e2 else e3 evalto v
C ⱶ if(E1, E2, E3) evalto V ~> D :-
    C ⱶ E1 evalto false ~> D1,
    C ⱶ E3 evalto V ~> D2,
    D = dd('E-IfF', C ⱶ if(E1, E2, E3) evalto V, [D1, D2]).

% C ⱶ e1 evalto v1   C, x = v1 ⱶ e3 evalto v
% --------------------------------
% C ⱶ let x = e1 in e2 evalto v
C ⱶ let(X = E1 in E2) evalto V ~> D :-
    C ⱶ E1 evalto V1 ~> D1,
    [X = V1 | C] ⱶ E2 evalto V ~> D2,
    D = dd('E-Let', C ⱶ let(X = E1 in E2) evalto V, [D1, D2]).

% C, x = (C)[rec x = fun y -> e1] ⱶ e2 evalto v
% ----------------------------------------
% C ⱶ let rec x = fun y -> e1 in e2 evalto v
C ⱶ letrec(X = fun(Y -> E1) in E2) evalto V ~> D :-
    [X = cls(C, X = fun(Y -> E1)) | C] ⱶ E2 evalto V ~> D1,
    D = dd('E-LetRec', C ⱶ letrec(X = fun(Y -> E1) in E2) evalto V, [D1]).

% C, x = v ⱶ x evalto v
[X = V | C] ⱶ var(X) evalto V ~> D :-
    D = dd('E-Var1', [X = V | C] ⱶ var(X) evalto V, []).

% (y != x)   C ⱶ x evalto v2
% --------------------------
% C, y = v1 ⱶ x evalto v2
[Y = V1 | C] ⱶ var(X) evalto V ~> D :-
    Y \== X, C ⱶ var(X) evalto V ~> D1,
    D = dd('E-Var2', [Y = V1 | C] ⱶ var(X) evalto V, [D1]).

% C ⱶ fun x -> e evalto (C) [fun x -> e]
C ⱶ fun(X -> E) evalto cls(C, fun(X -> E)) ~> D :-
    D = dd('E-Fun', C ⱶ fun(X -> E) evalto cls(C, fun(X -> E)), []).

% C ⱶ e1 evalto (C2) [fun x -> e0]
% C ⱶ e2 evalto v2   C2, x = v2 ⱶ e0 evalto v
% ---------------------------------
% C ⱶ e1 e2 evalto v
C ⱶ app(E1, E2) evalto V ~> D :-
    C ⱶ E1 evalto cls(C2, fun(X -> E0)) ~> D1,
    C ⱶ E2 evalto V2 ~> D2,
    [X = V2 | C2] ⱶ E0 evalto V ~> D3,
    D = dd('E-App', C ⱶ app(E1, E2) evalto V, [D1, D2, D3]).

% C ⱶ e1 evalto (C2) [rec x = fun y -> e0]
% C ⱶ e2 evalto v2
% C2, x = (C2) [rec x = fun y -> e0], y = v2 ⱶ e0 evalto v
% ---------------------------------------------------
% C ⱶ e1 e2 evalto v
C ⱶ app(E1, E2) evalto V ~> D :-
    C ⱶ E1 evalto cls(C2, X = fun(Y -> E0)) ~> D1,
    C ⱶ E2 evalto V2 ~> D2,
    [Y = V2, X = cls(C2, X = fun(Y -> E0)) | C2] ⱶ E0 evalto V ~> D3,
    D = dd('E-AppRec', C ⱶ app(E1, E2) evalto V, [D1, D2, D3]).

I1 plus I2 is I3 ~> D :-
    I3 is I1 + I2,
    D = dd('B-Plus', I1 plus I2 is I3, []).

I1 minus I2 is I3 ~> D :-
    I3 is I1 - I2,
    D = dd('B-Minus', I1 minus I2 is I3, []).

I1 times I2 is I3 ~> D :-
    I3 is I1 * I2,
    D = dd('B-Times', I1 times I2 is I3, []).

I1 lessThan I2 is B ~> D :-
    (I1 < I2 ->
    B = true;
    B = false),
    D = dd('B-Lt', I1 lessThan I2 is B, []).

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E evalto Result ~> _, !.

derive(Code) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E evalto _ ~> Derived,
    ppp(Derived, z), !.

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
% pretty print
ppp(dd(Rule, P, SubDerivs), W) :-
    unparse(P, UP), indent(W, Indent),
    writef('%w%w by %w {\n', [Indent, UP, Rule]), !, 
    ppp(SubDerivs, s(W)),
    writef('%w};\n', [Indent]).

ppp([], _).
ppp([D], W) :-
    ppp(D, W).
ppp([D | Ds], W) :-
    ppp(D, W),
    ppp(Ds, W).

indent(z, '').
indent(s(N), S) :-
    indent(N, S1), swritef(S, '  %w', [S1]).

unparse(C ⱶ P, U) :-
    unparse(C, UC), unparse(P, UP), swritef(U, '%w|- %w', [UC, UP]).
unparse(E evalto V, U) :-
    unparse(E, UE), unparse(V, UV), swritef(U, '%w evalto %w', [UE, UV]).
unparse(I1 lessThan I2 is B, U) :-
    swritef(U, '%w less than %w is %w', [I1, I2, B]).
unparse([], '').
unparse([X = E], U) :-
    unparse(X, UX), unparse(E, UE), swritef(U, '%w = %w', [UX, UE]).
unparse([X = E | C], U) :-
    unparse(X, UX), unparse(E, UE), unparse(C, UC), swritef(U, '%w, %w = %w', [UC, UX, UE]).
unparse(int(N), N).
unparse(bool(B), B).
unparse(var(X), X).
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
unparse(fun(X -> E), S) :-
    unparse(X, UX), unparse(E, UE), swritef(S, 'fun %w -> %w', [UX, UE]).
unparse(cls(C, X = E), S) :-
    unparse(C, UC), unparse(E, UE), swritef(S, '(%w)[rec %w = %w]', [UC, X, UE]).
unparse(cls(C, E), S) :-
    unparse(C, UC), unparse(E, UE), swritef(S, '(%w)[%w]', [UC, UE]).
unparse(if(E1, E2, E3), U) :-
    unparse(E1, U1), unparse(E2, U2), unparse(E3, U3),
    swritef(U, 'if %w then %w else %w', [U1, U2, U3]).
unparse(app(E1, E2), U) :-
    unparse(E1, U1), unparse(E2, U2),
    swritef(U, '%w %w', [U1, U2]).
unparse(let(X = E1 in E2), U) :-
    unparse(E1, U1), unparse(E2, U2),
    swritef(U, 'let %w = %w in %w', [X, U1, U2]).
unparse(letrec(X = E1 in E2), U) :-
    unparse(E1, U1), unparse(E2, U2),
    swritef(U, 'let rec %w = %w in %w', [X, U1, U2]).
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

