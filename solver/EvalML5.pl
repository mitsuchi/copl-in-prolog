:- set_prolog_flag(double_quotes, chars).
:- op(590,xfx, ~>).
:- op(595,yfx, ::).
:- op(700,xfx, is).
:- op(800,xfx, evalto).
:- op(800,xfx, plus).
:- op(800,xfx, minus).
:- op(800,xfx, times).
:- op(800,xfx, lessThan).
:- op(800,xfx, matches).
:- op(800,xfx, doesntMatch).
:- op(900,xfx, when).
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
tok('_') --> "_".
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
alnums([C])    --> alpha(C) | digit(C) | apos(C).

alpha(C) --> [C], { code_type(C, alpha) }.

apos('\'') --> "\'".

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
% match e with clauses
farg(match(E with Cs)) -->
    [match], expr(E), [with], clauses(Cs).

% clauses ::= pattern '->'' e ('|' clauses)
clauses([C|Cs]) --> clause(C), ['|'], clauses(Cs).
clauses([C]) --> clause(C).

clause(P -> E) --> pat(P), [->], expr(E).

% pattern ::= (var | '[]' | '_') ('::' pattern)
pat(P1 :: P2) --> pat1(P1), [::], pat(P2).
pat(P) --> pat1(P).

pat1(paren(P)) --> "(", pat(P), ")".
pat1(var(X)) --> [var(X)].
pat1(nil) --> "[]".
pat1(wildcard) --> "_".

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
    pp('%w|- %w + %w evalto %w by E-Plus', C, [E1, E2, I3], [D1, D2, D3], D, W), !.

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 minus i2 is i3
% -------------------------------------------------
% C ⱶ e1 - e2 evalto i3
C ⱶ E1 - E2 evalto I3 ~> (D, W) :-
    C ⱶ E1 evalto I1 ~> (D1, s(W)),
    C ⱶ E2 evalto I2 ~> (D2, s(W)),
    I1 minus I2 is I3 ~> (D3, s(W)),
    pp('%w|- %w - %w evalto %w by E-Minus', C, [E1, E2, I3], [D1, D2, D3], D, W), !.

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 times i2 is i3
% -------------------------------------------------
% C ⱶ e1 * e2 evalto i3
C ⱶ E1 * E2 evalto I3 ~> (D, W) :-
    C ⱶ E1 evalto I1 ~> (D1, s(W)),
    C ⱶ E2 evalto I2 ~> (D2, s(W)),
    I1 times I2 is I3 ~> (D3, s(W)),
    pp('%w|- %w * %w evalto %w by E-Times', C, [E1, E2, I3], [D1, D2, D3], D, W), !.

% C ⱶ e1 evalto i1   C ⱶ e2 evalto i2   i1 less than i2 is i3
% -----------------------------------------------------
% C ⱶ e1 < e2 evalto i3
C ⱶ E1 < E2 evalto I3 ~> (D, W) :-
    C ⱶ E1 evalto I1 ~> (D1, s(W)),
    C ⱶ E2 evalto I2 ~> (D2, s(W)),
    I1 lessThan I2 is I3 ~> (D3, s(W)),
    pp('%w|- %w < %w evalto %w by E-Lt', C, [E1, E2, I3], [D1, D2, D3], D, W), !.

% C ⱶ e1 evalto true   C ⱶ e2 evalto v
% --------------------------
% C ⱶ if e1 then e2 else e3 evalto v
C ⱶ if(E1, E2, E3) evalto V ~> (D, W) :-
    C ⱶ E1 evalto true ~> (D1, s(W)),
    C ⱶ E2 evalto V ~> (D2, s(W)),
    pp('%w|- if %w then %w else %w evalto %w by E-IfT', C, [E1, E2, E3, V], [D1, D2], D, W), !.

% C ⱶ e1 evalto false   C ⱶ e3 evalto v
% -----------------------------
% C ⱶ if e1 then e2 else e3 evalto v
C ⱶ if(E1, E2, E3) evalto V ~> (D, W) :-
    C ⱶ E1 evalto false ~> (D1, s(W)),
    C ⱶ E3 evalto V ~> (D2, s(W)),
    pp('%w|- if %w then %w else %w evalto %w by E-IfF', C, [E1, E2, E3, V], [D1, D2], D, W), !.

% C ⱶ e1 evalto v1   C, x = v1 ⱶ e3 evalto v
% --------------------------------
% C ⱶ let x = e1 in e2 evalto v
C ⱶ let(X = E1 in E2) evalto V ~> (D, W) :-
    C ⱶ E1 evalto V1 ~> (D1, s(W)),
    [X = V1 | C] ⱶ E2 evalto V ~> (D2, s(W)),
    pp('%w|- let %w = %w in %w evalto %w by E-Let', C, [X, E1, E2, V], [D1, D2], D, W), !.

% C, x = (C)[rec x = fun y -> e1] ⱶ e2 evalto v
% ----------------------------------------
% C ⱶ let rec x = fun y -> e1 in e2 evalto v
C ⱶ letrec(X = fun(Y -> E1) in E2) evalto V ~> (D, W) :-
    [X = cls(C, X = fun(Y -> E1)) | C] ⱶ E2 evalto V ~> (D1, s(W)),
    pp('%w|- let rec %w = fun %w -> %w in %w evalto %w by E-LetRec', C, [X, Y, E1, E2, V], [D1], D, W), !.

% C, x = v ⱶ x evalto v
C ⱶ var(X) evalto V ~> (D, W) :-
    member(X = V, C),
    pp('%w|- %w evalto %w by E-Var', C, [X, V], [], D, W), !.

% C ⱶ fun x -> e evalto (C) [fun x -> e]
C ⱶ fun(X -> E) evalto cls(C, fun(X -> E)) ~> (D, W):-
    pp('%w|- fun %w -> %w evalto (%w)[fun %w -> %w] by E-Fun', C, [X, E, C, X, E], [], D, W), !.

% C ⱶ e1 evalto (C2) [fun x -> e0]
% C ⱶ e2 evalto v2   C2, x = v2 ⱶ e0 evalto v
% ---------------------------------
% C ⱶ e1 e2 evalto v
C ⱶ app(E1, E2) evalto V ~> (D, W) :-
    C ⱶ E1 evalto cls(C2, fun(X -> E0)) ~> (D1, s(W)),
    C ⱶ E2 evalto V2 ~> (D2, s(W)),
    [X = V2 | C2] ⱶ E0 evalto V ~> (D3, s(W)),
    pp('%w|- %w %w evalto %w by E-App', C, [E1, E2, V], [D1, D2, D3], D, W), !.

% C ⱶ e1 evalto (C2) [rec x = fun y -> e0]
% C ⱶ e2 evalto v2
% C2, x = (C2) [rec x = fun y -> e0], y = v2 ⱶ e0 evalto v
% ---------------------------------------------------
% C ⱶ e1 e2 evalto v
C ⱶ app(E1, E2) evalto V ~> (D, W) :-
    C ⱶ E1 evalto cls(C2, X = fun(Y -> E0)) ~> (D1, s(W)),
    C ⱶ E2 evalto V2 ~> (D2, s(W)),
    [Y = V2, X = cls(C2, X = fun(Y -> E0)) | C2] ⱶ E0 evalto V ~> (D3, s(W)),
    pp('%w|- %w %w evalto %w by E-AppRec', C, [E1, E2, V], [D1, D2, D3], D, W), !.

C ⱶ nil evalto '[]' ~> (D, W) :-
    pp('%w|- [] evalto [] by E-Nil', C, [], [], D, W), !.

C ⱶ E1 :: E2 evalto [V1 | V2] ~> (D, W):-
    C ⱶ E1 evalto V1 ~> (D1, s(W)),
    C ⱶ E2 evalto V2 ~> (D2, s(W)),
    %pp('%w|- %w :: %w evalto %w :: %w by E-Cons', C, [E1, E2, V1, V2], [D1, D2], D, W), !.
    pp('%w|- %w evalto %w by E-Cons', C, [[E1 | E2], [V1 | V2]], [D1, D2], D, W), !.

C ⱶ match(E0 with [P -> E]) evalto V1 ~> (D, W) :-
    C ⱶ E0 evalto V ~> (D1, s(W)),
    P matches V when C1 ~> (D2, s(W)),
    append(C1, C, C2),    % (C2 = C ; C1) , 左が先頭なので C と C1 は逆順になる
    C2 ⱶ E evalto V1 ~> (D3, s(W)),  % E2 |- e ⇩ v'
    pp('%w|- match %w with %w -> %w evalto %w by E-MatchM1', C, [E0, P, E, V1], [D1, D2, D3], D, W), !.

C ⱶ match(E0 with [(P -> E) | Clause]) evalto  V1 ~> (D, W) :-
    C ⱶ E0 evalto V ~> (D1, s(W)),
    P matches V when C1 ~> (D2, s(W)),   
    append(C1, C, C2),    % (E2 = E ; E1) , 左が先頭なので E と E1 は逆順になる
    C2 ⱶ E evalto V1 ~> (D3, s(W)),  % E2 |- e ⇩ v'
    pp('%w|- match %w with %w -> %w | %w evalto %w by E-MatchM2', C, [E0, P, E, Clause, V1], [D1, D2, D3], D, W), !.

C ⱶ match(E0 with [(P -> E) | Cs]) evalto V1 ~> (D, W) :-
    C ⱶ E0 evalto V ~> (D1, s(W)),    
    P doesntMatch V ~> (D2, s(W)),
    C ⱶ match(E0 with Cs) evalto V1 ~> (D3, s(W)),
    pp('%w|- match %w with %w -> %w | %w evalto %w by E-MatchN', C, [E0, P, E, Cs, V1], [D1, D2, D3], D, W), !.

paren(P) matches V when C ~> (D, W) :- 
    P matches V when C ~> (D1, W),
    swritef(D, '(%w)', [D1]).

var(X) matches V when [X = V] ~> (D, W) :- % X matches V when [X = V]
    pp('%w matches %w when (%w = %w) by M-Var', [X, V, X, V], [], D, W), !.

nil matches '[]' when [] ~> (D, W) :-        % [] matches [] when []
    pp('[] matches [] when () by M-Nil', [], [], D, W), !.

wildcard matches V when [] ~> (D, W) :-    % _ matches v when []
    pp('_ matches %w when () by M-Wild', [V], [], D, W), !.

P1 :: P2 matches [V1 | V2] when C ~> (D, W) :-
    P1 matches V1 when C1 ~> (D1, s(W)),
    P2 matches V2 when C2 ~> (D2, s(W)), 
    xunion(C2, C1, C),
    %pp('%w :: %w matches %w :: %w when (%w) by M-Cons', [P1, P2, V1, V2, C], [D1, D2], D, W), !.
    pp('%w matches %w when (%w) by M-Cons', [[P1 | P2], [V1 | V2], C], [D1, D2], D, W), !.

nil doesntMatch [V1|V2] ~> (D, W) :- % [] doesn't match V1 :: V2
    %pp('[] doesn\'t match %w :: %w by NM-ConsNil', [V1, V2], [], D, W), !.
    pp('[] doesn\'t match %w by NM-ConsNil', [[V1 | V2]], [], D, W), !.
P1 :: P2 doesntMatch '[]' ~> (D, W) :- % P1 :: P2 doesn't match []
    %pp('%w :: %w doesn\'t match [] by NM-NilCons', [P1, P2], [], D, W), !.
    pp('%w doesn\'t match [] by NM-NilCons', [[P1 | P2]], [], D, W), !.
P1 :: P2 doesntMatch [V1 | V2] ~> (D, W) :-
    P1 doesntMatch V1 ~> (D1, s(W)),
    %pp('%w :: %w doesn\'t match %w :: %w by NM-ConsConsL', [P1, P2, V1, V2], [D1], D, W), !.
    pp('%w doesn\'t match %w by NM-ConsConsL', [[P1 | P2], [V1 |V2 ]], [D1], D, W), !.    
P1 :: P2 doesntMatch [V1 | V2] ~> (D, W):-
    P2 doesntMatch V2 ~> (D1, s(W)),
    %pp('%w :: %w doesn\'t match %w :: %w by NM-ConsConsR', [P1, P2, V1, V2], [D1], D, W), !.
    pp('%w doesn\'t match %w by NM-ConsConsR', [[P1 | P2], [V1 | V2]], [D1], D, W), !.

xunion(E1, E2, E3) :-
    append(E1, E2, E3),
    env_vars(E1, V1), env_vars(E2, V2), intersection(V1, V2, []).

env_vars([], []).
env_vars([X = _|E], [X | Vars]) :- env_vars(E, Vars), !.

I1 plus I2 is I3 ~> (D, W) :-
    I3 is I1 + I2,
    pp('%w plus %w is %w by B-Plus', [I1, I2, I3], [], D, W), !.

I1 minus I2 is I3 ~> (D, W) :-
    I3 is I1 - I2,
    pp('%w minus %w is %w by B-Minus', [I1, I2, I3], [], D, W), !.

I1 times I2 is I3 ~> (D, W):-
    I3 is I1 * I2,
    pp('%w times %w is %w by B-Times', [I1, I2, I3], [], D, W), !.

I1 lessThan I2 is B ~> (D, W) :-
    (I1 < I2 ->
    B = true;
    B = false),
    pp('%w less than %w is %w by B-Lt', [I1, I2, B], [], D, W), !.

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
unparse([X = E], U) :-
    unparse(X, UX), unparse(E, UE), swritef(U, '%w = %w', [UX, UE]).
unparse([X = E | C], U) :-
    unparse(X, UX), unparse(E, UE), unparse(C, UC), swritef(U, '%w, %w = %w', [UC, UX, UE]).
unparse([X -> E], U) :-
    unparse(X, UX), unparse(E, UE), swritef(U, '%w -> %w', [UX, UE]).
unparse([X -> E | C], U) :-
    unparse(X, UX), unparse(E, UE), unparse(C, UC), swritef(U, '%w -> %w | %w', [UX, UE, UC]).
unparse([E], UE) :-
    unparse(E, UE).
unparse([E | Es], U) :-
    unparse(E, UE),
    unparse(Es, UEs),
    (E = [_ | _] -> swritef(U, '(%w) :: %w', [UE, UEs]);
    swritef(U, '%w :: %w', [UE, UEs])).
unparse(int(N), N).
unparse(bool(B), B).
unparse(var(X), X).
unparse(wildcard, '_').
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
    unparse(E1, U1), unparse(E2, U2), swritef(U, '%w :: %w', [U1, U2]).
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
unparse(match(E1 with Cs), U) :-
    unparse(E1, U1), unparse(Cs, UCs),
    swritef(U, 'match %w with %w', [U1, UCs]).
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

