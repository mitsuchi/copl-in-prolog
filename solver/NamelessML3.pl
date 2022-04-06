:- set_prolog_flag(double_quotes, chars).
:- op(590,xfx, ~>).
:- op(700,xfx, is).
:- op(800,xfx, ==>).
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

%C ⱶ A ==> B ~> D :-
%    write('C = '), write(C), write(', A = '), writeln(A), fail.

C ⱶ paren(E) ==> T ~> (D, W) :-
    C ⱶ E ==> T ~> (D, W).

% C ⱶ i ==> i
C ⱶ int(I) ==> I ~> (D, W) :-
    pp('%w|- %w ==> %w by Tr-Int', C, [I, I], [], D, W), !.

% C ⱶ b ==> b
C ⱶ bool(B) ==> B ~> (D, W) :-
    pp('%w|- %w ==> %w by Tr-Bool', C, [B, B], [], D, W), !.

% C ⱶ e1 ==> i1   C ⱶ e2 ==> i2 
% ------------------------------------------------
% C ⱶ e1 + e2 ==> i1 + i2
C ⱶ E1 + E2 ==> T1 + T2  ~> (D, W) :-
    C ⱶ E1 ==> T1 ~> (D1, s(W)),
    C ⱶ E2 ==> T2 ~> (D2, s(W)),
    pp('%w|- %w + %w ==> %w + %w by Tr-Plus', C, [E1, E2, T1, T2], [D1, D2], D, W).

% C ⱶ e1 ==> i1   C ⱶ e2 ==> i2 
% -------------------------------------------------
% C ⱶ e1 - e2 ==> i3
C ⱶ E1 - E2 ==> T1 - T2 ~> (D, W) :-
    C ⱶ E1 ==> T1 ~> (D1, s(W)),
    C ⱶ E2 ==> T2 ~> (D2, s(W)),
    pp('%w|- %w - %w ==> %w - %w by Tr-Minus', C, [E1, E2, T1, T2], [D1, D2], D, W).

% C ⱶ e1 ==> i1   C ⱶ e2 ==> i2 
% -------------------------------------------------
% C ⱶ e1 * e2 ==> i3
C ⱶ E1 * E2 ==> T1 * T2 ~> (D, W) :-
    C ⱶ E1 ==> T1 ~> (D1, s(W)),
    C ⱶ E2 ==> T2 ~> (D2, s(W)),
    pp('%w|- %w * %w ==> %w * %w by Tr-Times', C, [E1, E2, T1, T2], [D1, D2], D, W).

% C ⱶ e1 ==> i1   C ⱶ e2 ==> i2  
% -----------------------------------------------------
% C ⱶ e1 < e2 ==> i3
C ⱶ (E1 < E2) ==> (T1 < T2) ~> (D, W) :-
    C ⱶ E1 ==> T1 ~> (D1, s(W)),
    C ⱶ E2 ==> T2 ~> (D2, s(W)),
    pp('%w|- %w < %w ==> %w < %w by Tr-Lt', C, [E1, E2, T1, T2], [D1, D2], D, W).

% C ⱶ e1 ==> true   C ⱶ e2 ==> v
% -------------------------------
% C ⱶ if e1 then e2 else e3 ==> v
C ⱶ if(E1, E2, E3) ==> if(T1, T2, T3) ~> (D, W) :-
    C ⱶ E1 ==> T1 ~> (D1, s(W)),
    C ⱶ E2 ==> T2 ~> (D2, s(W)),
    C ⱶ E3 ==> T3 ~> (D3, s(W)),
    pp('%w|- if %w then %w else %w ==> if %w then %w else %w by Tr-If', C, [E1, E2, E3, T1, T2, T3], [D1, D2, D3], D, W).

% C ⱶ e1 ==> v1   C, x = v1 ⱶ e3 ==> v
% --------------------------------
% C ⱶ let x = e1 in e2 ==> v
C ⱶ let(X = E1 in E2) ==> let('.' = T1 in T2) ~> (D, W) :-
    C ⱶ E1 ==> T1 ~> (D1, s(W)),
    [X | C] ⱶ E2 ==> T2 ~> (D2, s(W)),
    pp('%w|- let %w = %w in %w ==> let . = %w in %w by Tr-Let', C, [X, E1, E2, T1, T2], [D1, D2], D, W).

% C, x = (C)[rec x = fun y -> e1] ⱶ e2 ==> v
% ----------------------------------------
% C ⱶ let rec x = fun y -> e1 in e2 ==> v
C ⱶ letrec(X = fun(Y -> E1) in E2) ==> letrec('.' = fun('.' -> T1) in T2) ~> (D, W) :-
    [Y, X | C] ⱶ E1 ==> T1 ~> (D1, s(W)),
    [X | C] ⱶ E2 ==> T2 ~> (D2, s(W)),
    pp('%w|- let rec %w = fun %w -> %w in %w ==> let rec . = fun . -> %w in %w by Tr-LetRec', C, [X, Y, E1, E2, T1, T2], [D1, D2], D, W).

% C, x = v ⱶ x ==> v
[X | C] ⱶ var(X) ==> num(1) ~> (D, W) :-
    pp('%w|- %w ==> #1 by Tr-Var1', [X | C], [X], [], D, W), !.

% (y != x)   C ⱶ x ==> v2
% --------------------------
% C, y = v1 ⱶ x ==> v2
[Y | C] ⱶ var(X) ==> num(N2) ~> (D, W):-
    Y \== X, C ⱶ var(X) ==> num(N1) ~> (D1, s(W)),
    N2 is N1 + 1,
    pp('%w|- %w ==> #%w by Tr-Var2', [Y | C], [X, N2], [D1], D, W).

% C ⱶ fun x -> e ==> (C) [fun x -> e]
C ⱶ fun(X -> E) ==> fun('.' -> T) ~> (D, W) :-
    [X | C] ⱶ E ==> T ~> (D1, s(W)),
    pp('%w|- fun %w -> %w ==> fun . -> %w by Tr-Fun', C, [X, E, T], [D1], D, W).

% C ⱶ e1 ==> (C2) [fun x -> e0]
% C ⱶ e2 ==> v2   C2, x = v2 ⱶ e0 ==> v
% ---------------------------------
% C ⱶ e1 e2 ==> v
C ⱶ app(E1, E2) ==> app(T1, T2) ~> (D, W) :-
    C ⱶ E1 ==> T1 ~> (D1, s(W)),
    C ⱶ E2 ==> T2 ~> (D2, s(W)),
    pp('%w|- %w %w ==> %w %w by Tr-App', C, [E1, E2, T1, T2], [D1, D2], D, W).

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E ==> Result ~> (_, _), !.

derive(Code) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E ==> _ ~> (Derived, _),
    write(Derived), !.

derive(C, Code) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    C ⱶ E ==> _ ~> (Derived, _),
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

unparse(num(N), UN) :-
    swritef(UN, '#%w', [N]).
unparse([], '').
unparse([X], U) :-
    unparse(X, UX), swritef(U, '%w', [UX]).
unparse([X | C], U) :-
    unparse(X, UX), unparse(C, UC), swritef(U, '%w, %w', [UC, UX]).
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
unparse(fun(X -> E), U) :-
    unparse(E, U1),
    swritef(U, 'fun %w -> %w', [X, U1]).
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

