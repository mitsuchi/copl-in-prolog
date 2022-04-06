:- set_prolog_flag(double_quotes, chars).
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
:- op(994,xfy, >>).
:- op(995,xfx, =>).
:- op(997,xfx, evalto).
:- op(998,xfx, ~>).


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
tok('{') --> "{".
tok('}') --> "}".
tok('[') --> "[".
tok(']') --> "]".
tok('|') --> "|".
tok(>>) --> ">>".
tok(=>) --> "=>".
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
alnums([C])    --> alpha(C) | digit(C).

alpha(C) --> [C], { code_type(C, alpha) }.

% parse

% program := expr conts?
program(P) --> expr(P).
program(E >> C) --> expr(E), [>>], conts(C).

% conts := '>>' cont | conts
conts(C) --> cont(C).
conts(C1 >> C2) --> cont(C1), [>>], conts(C2).

% cont := '_'
cont('_') --> "_".
%cont({E}) --> "{", expr(E), "}".
cont({I + '_'}) --> "{", [int(I), +, '_'], "}".
cont({I - '_'}) --> "{", [int(I), -, '_'], "}".
cont({I * '_'}) --> "{", [int(I), *, '_'], "}".
cont({I < '_'}) --> "{", [int(I), <, '_'], "}".
cont({'_' + E}) --> "{", ['_', +], expr(E), "}".
cont({'_' - E}) --> "{", ['_', -], expr(E), "}".
cont({'_' * E}) --> "{", ['_', *], expr(E), "}".
cont({'_' < E}) --> "{", ['_', <], expr(E), "}".
cont({if('_', E1, E2)}) --> "{", [if], "_", [then], expr(E1), [else], expr(E2), "}".

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
farg('_') --> "_".
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
paren(E) >> K evalto V ~> D :-
    E >> K evalto V ~> D, !.

% i >> k evalto v by E-Int { // 式 i の値を得たい
%     i => k evalto v         // i はすでに値なのでそれを使え
% }
int(I) >> K evalto V ~> D :-
    I => K evalto V ~> D1,
    D = dd('E-Int', int(I) >> K evalto V, [D1]), !.

% b >> k evalto v by E-Bool {  // 式 b の値を得たい
%     b => k evalto v          // b はすでに値なのでそれを使え
% }
bool(B) >> K evalto V ~> D :-
    B => K evalto V ~> D1,
    D = dd('E-Bool', bool(B) >> K evalto V, [D1]), !.

% e1 op e2 >> k evalto v by E-BinOp { // e1 op e2 の値を得たい
%     e1 >> {_ op e2} >> k evalto v   // まず e1 を評価せよ。右側の評価とopの演算は継続に追加せよ。
% }
E1 + E2 >> K evalto V ~> D :-
    E1 >> {'_' + E2} >> K evalto V ~> D1,
    D = dd('E-BinOp', E1 + E2 >> K evalto V, [D1]), !.

E1 - E2 >> K evalto V ~> D :-
    E1 >> {'_' - E2} >> K evalto V ~> D1,
    D = dd('E-BinOp', E1 - E2 >> K evalto V, [D1]), !.

E1 * E2 >> K evalto V ~> D :-
    E1 >> {'_' * E2} >> K evalto V ~> D1,
    D = dd('E-BinOp', E1 * E2 >> K evalto V, [D1]), !.

E1 < E2 >> K evalto V ~> D :-
    E1 >> {'_' < E2} >> K evalto V ~> D1,
    D = dd('E-BinOp', E1 < E2 >> K evalto V, [D1]), !.

% if e1 then e2 else e3 >> k evalto v by E-If {  // if 式の値を得たい
%     e1 >> {if _ then e2 else e3} >> k evalto v // e1 を評価せよ。then か else の評価は継続に追加せよ。
% }
if(E1, E2, E3) >> K evalto V ~> D :-
    E1 >> {if('_', E2, E3)} >> K evalto V ~> D1,
    D = dd('E-If', if(E1, E2, E3) >> K evalto V, [D1]).

% v => _ evalto v by C-Ret { // 得た値は v で、残りの作業はない
%                            // おめでとう、もうすることはない
% }
V => '_' evalto V ~> D :-
    D = dd('C-Ret', V => '_' evalto V, []).

% v1 => {_ op e} >> k evalto v2 by C-EvalR { // 得た値は v1 で、残りは二項演算の右側の評価と、二項演算。
%     e >> {v1 op _} >> k evalto v2          // 右側を評価せよ。その結果との二項演算は継続に追加せよ。
% }
V1 => {'_' + E} >> K evalto V2 ~> D :-
    E >> {V1 + '_'} >> K evalto V2 ~> D1,
    D = dd('C-EvalR', V1 => {'_' + E} >> K evalto V2, [D1]).

V1 => {'_' - E} >> K evalto V2 ~> D :-
    E >> {V1 - '_'} >> K evalto V2 ~> D1,
    D = dd('C-EvalR', V1 => {'_' - E} >> K evalto V2, [D1]).

V1 => {'_' * E} >> K evalto V2 ~> D :-
    E >> {V1 * '_'} >> K evalto V2 ~> D1,
    D = dd('C-EvalR', V1 => {'_' * E} >> K evalto V2, [D1]).

V1 => {'_' < E} >> K evalto V2 ~> D :-
    E >> {V1 < '_'} >> K evalto V2 ~> D1,
    D = dd('C-EvalR', V1 => {'_' < E} >> K evalto V2, [D1]).

% i2 => {i1 + _} >> k evalto v by C-Plus { // 得た値は i2 で、残りはそれを右側とする足し算。
%     i1 plus i2 is i3                     // まず足し算せよ
%     i3 => k evalto v                     // その値に残りの作業をせよ
% }
I2 => {I1 + '_'} >> K evalto V ~> D :-
    I1 plus I2 is I3 ~> D1,
    I3 => K evalto V ~> D2,
    D = dd('C-Plus', I2 => {I1 + '_'} >> K evalto V, [D1, D2]).

I2 => {I1 - '_'} >> K evalto V ~> D :-
    I1 minus I2 is I3 ~> D1,
    I3 => K evalto V ~> D2,
    D = dd('C-Minus', I2 => {I1 - '_'} >> K evalto V, [D1, D2]).

I2 => {I1 * '_'} >> K evalto V ~> D :-
    I1 times I2 is I3 ~> D1,
    I3 => K evalto V ~> D2,
    D = dd('C-Times', I2 => {I1 * '_'} >> K evalto V, [D1, D2]).

I2 => {I1 < '_'} >> K evalto V ~> D :-
    I1 lessThan I2 is I3 ~> D1,
    I3 => K evalto V ~> D2,
    D = dd('C-Lt', I2 => {I1 < '_'} >> K evalto V, [D1, D2]).

% i1 plus i2 is i3 by B-Plus {} // 足し算はふつうにやれ
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

% true => {if _ then e1 else e2} >> k evalto v by C-IfT { // 得た値は true で、残りは if の評価
%    e1 >> k evalto v                                    // e1 を評価せよ
% }
true => {if('_', E1, E2)} >> K evalto V ~> D :-
    E1 >> K evalto V ~> D1,
    D = dd('C-IfT', true => {if('_', E1, E2)} >> K evalto V, [D1]).

false => {if('_', E1, E2)} >> K evalto V ~> D :-
    E2 >> K evalto V ~> D1,
    D = dd('C-IfF', false => {if('_', E1, E2)} >> K evalto V, [D1]).

paren(E) => K evalto V ~> D :-
    E => K evalto V ~> D, !.

% UI
code_result(Code, Result) :-
    phrase(tokens(Tokens), Code),
    phrase(program(P), Tokens),
    P evalto Result ~> _, !.

derive(Code) :-
    phrase(tokens(Tokens), Code),
    phrase(program(P), Tokens),
    P evalto _ ~> Derivation,
    ppp(Derivation, z), !.

derive(Code, Value) :-
    phrase(tokens(Tokens), Code),
    phrase(program(P), Tokens),
    P evalto Value ~> Derivation,
    ppp(Derivation, z), !.

code_expr(Code, Expr) :-
    phrase(tokens(Tokens), Code),
    phrase(expr(Expr), Tokens).

code_conts(Code, K) :-
    phrase(tokens(Tokens), Code),
    phrase(conts(K), Tokens).

code_program(Code, P) :-
    phrase(tokens(Tokens), Code),
    phrase(program(P), Tokens).

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

%unparse(E, E).
unparse(V, V) :-
    var(V).
unparse(mono(T), UT) :-
    unparse(T, UT).
unparse(poly(_, T), U) :-
    unparse(T, UT),
    swritef(U, 'alpha.%w', [UT]).

unparse(E evalto V, U) :-
    unparse(E, UE), unparse(V, UV), swritef(U, '%w evalto %w', [UE, UV]).
unparse(I1 lessThan I2 is B, U) :-
    swritef(U, '%w less than %w is %w', [I1, I2, B]).
unparse([], '').
unparse({Cont}, U) :-
    unparse(Cont, UCont), swritef(U, '{%w}', [UCont]).
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
unparse(E1 => E2, U) :-
    unparseP(E1, U1, =>), unparse(E2, U2), swritef(U, '%w => %w', [U1, U2]).
unparse(E1 >> E2, U) :-
    unparseP(E1, U1, >>), unparse(E2, U2), swritef(U, '%w >> %w', [U1, U2]).
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