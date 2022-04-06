:- set_prolog_flag(double_quotes, chars).
:- op(590,xfx, ~>).
:- op(595,yfx, ::).
:- op(700,xfx, is).
:- op(800,xfx, :).
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
expr(T :: E) --> term(T), [::], expr(E).
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
farg(nil) --> "[]".
farg(if(E1, E2, E3)) -->
    [if], expr(E1), [then], expr(E2), [else], expr(E3).
farg(let(X = E1 in E2)) --> [let, var(X), =], expr(E1), [in], expr(E2).  
farg(letrec(X = fun(Y -> E1) in E2)) -->
    [let, rec, var(X), =, fun, var(Y), ->], expr(E1), [in], expr(E2).
farg(fun(X -> E)) --> [fun, var(X), ->], expr(E).
% match e1 with [] -> e2 | x :: y -> e3
farg(match(E1 with [] -> E2, X :: Y -> E3)) -->
    [match], expr(E1), [with, '[', ']', ->], expr(E2),
    ['|', var(X), ::, var(Y), ->], expr(E3).

% eval
% 以下では環境を C とする (Context)

%C ⱶ A : B ~> D :-
%    write('C = '), write(C), write(', A = '), writeln(A), fail.

C ⱶ paren(E) : V ~> D :-
    C ⱶ E : V ~> D, !.

% C ⱶ i : i
C ⱶ int(I) : int ~> D :-
    D = dd('T-Int', C ⱶ I : int, []), !.

% C ⱶ b : b
C ⱶ bool(B) : bool ~> D :-
    D = dd('T-Bool', C ⱶ bool(B) : bool, []), !.

% C ⱶ e1 : i1   C ⱶ e2 : i2   i1 plus i2 is i3
% ------------------------------------------------
% C ⱶ e1 + e2 : i3
C ⱶ E1 + E2 : int ~> D :-
    C ⱶ E1 : int ~> D1,
    C ⱶ E2 : int ~> D2,
    D = dd('T-Plus', C ⱶ E1 + E2 : int, [D1, D2]), !.

C ⱶ E1 - E2 : int ~> D :-
    C ⱶ E1 : int ~> D1,
    C ⱶ E2 : int ~> D2,
    D = dd('T-Minus', C ⱶ E1 - E2 : int, [D1, D2]), !.

C ⱶ E1 * E2 : int ~> D :-
    C ⱶ E1 : int ~> D1,
    C ⱶ E2 : int ~> D2,
    D = dd('T-Mult', C ⱶ E1 * E2 : int, [D1, D2]), !.

C ⱶ E1 < E2 : bool ~> D :-
    C ⱶ E1 : int ~> D1,
    C ⱶ E2 : int ~> D2,
    D = dd('T-Lt', C ⱶ E1 < E2 : bool, [D1, D2]), !.

C ⱶ var(X) : T ~> D:-
    first(X : S, C),
    instantiate(S, T),
    D = dd('T-Var', C ⱶ var(X) : T, []), !.

C ⱶ if(E1, E2, E3) : T ~> D :-
    C ⱶ E1 : bool ~> D1,
    C ⱶ E2 : T ~> D2,
    C ⱶ E3 : T ~> D3,
    D = dd('T-If', C ⱶ if(E1, E2, E3) : T, [D1, D2, D3]), !.

C ⱶ fun(X -> E) : (T1 -> T2) ~> D :-
    [X : mono(T1) | C] ⱶ E : T2 ~> D1,
    D = dd('T-Abs', C ⱶ fun(X -> E) : (T1 -> T2), [D1]), !.

C ⱶ app(E1, E2) : T2 ~> D :-
    C ⱶ E1 : (T1 -> T2) ~> D1,
    C ⱶ E2 : T1 ~> D2,
    D = dd('T-App', C ⱶ app(E1, E2) : T2, [D1, D2]), !.

C ⱶ let(X = E1 in E2) : T2 ~> D :-
    C ⱶ E1 : T1 ~> D1,
    [X : poly(C, T1) | C] ⱶ E2 : T2 ~> D2,
    D = dd('T-Let', C ⱶ let(X = E1 in E2) : T2, [D1, D2]), !.

C ⱶ letrec(X = fun(Y -> E1) in E2) : T ~> D :-
    [Y : mono(T1), X : mono(T1 -> T2) | C] ⱶ E1 : T2 ~> D1,
    [X : poly(C, T1 -> T2) | C] ⱶ E2 : T ~> D2,
    D = dd('T-LetRec', C ⱶ letrec(X = fun(Y -> E1) in E2) : T, [D1, D2]).

C ⱶ (E1 :: E2) : list(T) ~> D:-
    C ⱶ E1 : T ~> D1,
    C ⱶ E2 : list(T) ~> D2,
    D = dd('T-Cons', C ⱶ (E1 :: E2) : list(T), [D1, D2]), !.

C ⱶ nil : list(T) ~> D :-
    D = dd('T-Nil', C ⱶ nil : list(T), []), !.

C ⱶ match(E1 with [] -> E2, X :: Y -> E3) : T ~> D :-
    C ⱶ E1 : list(T1) ~> D1,
    C ⱶ E2 : T ~> D2,
    [Y : mono(list(T1)), X : mono(T1) | C] ⱶ E3 : T ~> D3,
    D = dd('T-Match', C ⱶ match(E1 with [] -> E2, X :: Y -> E3) : T, [D1, D2, D3]).

first(K:V,[K1:V1|_]) :- K = K1, V=V1.
first(K:V,[K1:_|Xs]) :- K\==K1, first(K:V, Xs).

instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).
instantiate(mono(T),T).

start :-
    derive("fun x -> x").

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E : Result ~> _, !.

derive(Code) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E : _ ~> Derivation,
    ppp(Derivation, z), !.

derive(Code, Type) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(E), Tokens),
    [] ⱶ E : Type ~> Derivation,
    ppp(Derivation, z), !.

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
ppp(dd(Rule, C ⱶ E : T, SubDerivs), W) :-
    Term = f(C ⱶ E : T, SubDerivs),
    numbervars(Term, 0, _),
    unparse(C, UC), unparse(E, UE), unparse(T, UT), indent(W, Indent),
    writef('%w%w|- %w : %w by %w {\n', [Indent, UC, UE, UT, Rule]),
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

%unparse(E, E).
unparse(V, V) :-
    var(V).
unparse(mono(T), UT) :-
    unparse(T, UT).
unparse(poly(_, T), U) :-
    unparse(T, UT),
    swritef(U, 'alpha.%w', [UT]).

unparse([], '').
unparse([X : E], U) :-
    unparse(X, UX), unparse(E, UE), swritef(U, '%w : %w', [UX, UE]).
unparse([X : E | C], U) :-
    unparse(X, UX), unparse(E, UE), unparse(C, UC), swritef(U, '%w, %w : %w', [UC, UX, UE]).
unparse([E], UE) :-
    unparse(E, UE).
unparse([E | Es], U) :-
    unparse(E, UE), unparse(Es, UEs), swritef(U, '%w :: %w', [UE, UEs]).
unparse(int(N), N).
unparse(bool(B), B).
unparse(var(X), X).
unparse(list(T), U) :-
    unparseP(T, UT, ->), swritef(U, '%w list', [UT]).
unparse(nil, []).
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
unparse(E1 :: E2, U) :-
    unparseP(E1, U1, ::), unparse(E2, U2), swritef(U, '%w :: %w', [U1, U2]).
unparse(E1 -> E2, U) :-
    unparseP(E1, U1, ->), unparse(E2, U2), swritef(U, '%w -> %w', [U1, U2]).
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
unparse(match(E1 with [] -> E2, X :: Y -> E3), U) :-
    unparse(E1, U1), unparse(E2, U2), unparse(E3, U3),
    swritef(U, 'match %w with [] -> %w | %w :: %w -> %w', [U1, U2, X, Y, U3]).

unparse(E, E).

unparseP(E, U, OP) :-
    E =.. [OP, _, _],
    unparse(E, UE),
    swritef(U, '(%w)', [UE]), !.
unparseP(E, U, _) :-
    unparse(E, U).

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

hoge(V, V) :-
    var(V).
hoge(E, E).