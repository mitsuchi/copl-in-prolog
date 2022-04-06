:- set_prolog_flag(double_quotes, chars).
:- op(1,fx, !).
:- op(700,xfx, is).
:- op(800,xfx, :=).
:- op(800,yfx, &&).
:- op(800,yfx, '||').
:- op(800,xfx, <=).
:- op(800,xfx, evalto).
:- op(800,xfx, plus).
:- op(800,xfx, minus).
:- op(800,xfx, times).
:- op(800,xfx, lessThan).
:- op(900,xfx, in).
:- op(980,xfx, to).
:- op(980,xfx, do).
:- op(990,xfx, >-).
:- op(990,xfx, changes).
:- op(995,xfx, ~>).

% tokenize
tokens(Ts) --> " ", tokens(Ts).
tokens([T|Ts]) --> tok(T), !, tokens(Ts).
tokens([]) --> "".

tok(int(-I)) --> "-", digits(Cs), { number_chars(I, Cs) }.
tok(int(I)) --> digits(Cs), { number_chars(I, Cs) }.
tok(bool(true)) --> "true".
tok(bool(false)) --> "false".
tok(<=) --> "<=".
tok(&&) --> "&&".
tok(:=) --> ":=".
tok('||') --> "||".
tok(;) --> ";".
tok(,) --> ",".
tok(+) --> "+".
tok(->) --> "->".
tok(-) --> "-".
tok(*) --> "*".
tok(<) --> "<".
tok('(') --> "(".
tok(')') --> ")".
tok(=) --> "=".
tok(!) --> "!".
tok(if) --> "if".
tok(then) --> "then".
tok(else) --> "else".
tok(let) --> "let".
tok(in) --> "in".
tok(fun) --> "fun".
tok(rec) --> "rec".
tok(changes) --> "changes".
tok(to) --> "to".
tok(skip) --> "skip".
tok(while) --> "while".
tok(do) --> "do".
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
program(C changes S1 to S2) -->
    com(C), [changes], store(S1), [to], store(S2).

com(C1) --> com1(C1).
com(C1 ; C2) --> com1(C1), ";", com(C2).

com1(skip) --> [skip].
com1(X := A) --> [var(X)], [:=], aexp(A).
com1(if(B, C1, C2)) --> [if], bexp(B), [then], com(C1), [else], com(C2).
com1(while(B do C)) --> [while], "(", bexp(B), ")", [do], com(C).

bexp(BT && B) --> bterm(BT), [&&], bexp(B).
bexp(BT '||' B) --> bterm(BT), ['||'], bexp(B).
bexp(BT) --> bterm(BT).

bterm(bool(B)) --> [bool(B)].
bterm(!B) --> "!", bterm(B).
bterm(A1 < A2) --> aexp(A1), "<", aexp(A2).
bterm(A1 = A2) --> aexp(A1), "=", aexp(A2).
bterm(A1 <= A2) --> aexp(A1), [<=], aexp(A2).
bterm(paren(E)) --> "(", bexp(E), ")".

aexp(A)  --> aterm(AT), aexp1(AT, A).
aexp1(A1, A) --> "+", aterm(AT), aexp1(A1 + AT, A).
aexp1(A1, A) --> "-", aterm(AT), aexp1(A1 - AT, A).
aexp1(A1, A) --> "*", aterm(AT), aexp1(A1 * AT, A).
aexp1(A, A) --> [].

aterm(int(I)) --> [int(I)].
aterm(var(X)) --> [var(X)].
aterm(paren(E)) --> "(", aexp(E), ")".

store([X = I]) --> [var(X), '=', int(I)].
store([X = I | S]) --> [var(X), '=', int(I)], ",", store(S).

% eval
% 以下では環境を C とする (Context)

%C >- A evalto B ~> D :-
%    write('C = '), write(C), write(', A = '), writeln(A), fail.

% skip changes s to s by C-Skip {}
skip changes S to S ~> D :-
    D = dd('C-Skip', skip changes S to S, []).

% x := a changes s1 to s2 by C-Assign {
%    s1 ⊢ a evalto i      (s2 = s1[i/x])
% }
X := A changes S1 to S2 ~> D :-
    S1 >- A evalto I ~> D1,
    update(S1, X = I, S2),
    D = dd('C-Assign', X := A changes S1 to S2, [D1]).

% c1;c2 changes s1 to s3 by C-Seq {
%     c1 changes s1 to s2   c2 changes s2 to s3
% }
(C1;C2) changes S1 to S3 ~> D :-
    C1 changes S1 to S2 ~> D1,
    C2 changes S2 to S3 ~> D2,
    D = dd('C-Seq', (C1;C2) changes S1 to S3, [D1, D2]).

% if b then c1 else c2 changes s1 to s2 by C-IfT {
%    s1 ⊢ b evalto true   c1 changes s1 to s2
% }
if(B, C1, C2) changes S1 to S2 ~> D :-
    S1 >- B evalto true ~> D1,
    C1 changes S1 to S2 ~> D2,
    D = dd('C-IfT', if(B, C1, C2) changes S1 to S2, [D1, D2]).

if(B, C1, C2) changes S1 to S2 ~> D :-
    S1 >- B evalto false ~> D1,
    C2 changes S1 to S2 ~> D2,
    D = dd('C-IfF', if(B, C1, C2) changes S1 to S2, [D1, D2]).

% while (b) do c changes σ1 to σ3 by C-WhileT {
%    σ1 ⊢ b ⇓ true   c changes σ1 to σ2   while (b) do c changes σ2 to σ3
% }
while(B do C) changes S1 to S3 ~> D :-
    S1 >- B evalto true ~> D1,
    C changes S1 to S2 ~> D2,
    while(B do C) changes S2 to S3 ~> D3,
    D = dd('C-WhileT', while(B do C) changes S1 to S3, [D1, D2, D3]).

% while (b) do c changes σ to σ by C-WhileF {
%   σ ⊢ b ⇓ false
% }
while(B do C) changes S to S ~> D :-
    S >- B evalto false ~> D1,
    D = dd('C-WhileF', while(B do C) changes S to S, [D1]).

C >- paren(E) evalto V ~> D :-
    C >- E evalto V ~> D.

% s ⊢ i evalto i by A-Const {}
S >- int(I) evalto I ~> D :-
    D = dd('A-Const', S >- int(I) evalto I, []).

% s ⊢ x evalto i by A-Var {
%    (σ(x) = i)
% }
S >- var(X) evalto I ~> D :-
    member(X = I, S),
    D = dd('A-Var', S >- var(X) evalto I, []).

% s ⊢ a1 + a2 evalto i3 by A-Plus {
%   s ⊢ a1 evalto i1,  s ⊢ a2 evalto i2   (i3 = i1 + i2)
% }
S >- A1 + A2 evalto I3 ~> D :-
    S >- A1 evalto I1 ~> D1,
    S >- A2 evalto I2 ~> D2,
    I3 is I1 + I2,
    D = dd('A-Plus', S >- A1 + A2 evalto I3, [D1, D2]).

S >- A1 - A2 evalto I3 ~> D :-
    S >- A1 evalto I1 ~> D1,
    S >- A2 evalto I2 ~> D2,
    I3 is I1 - I2,
    D = dd('A-Minus', S >- A1 - A2 evalto I3, [D1, D2]).

S >- A1 * A2 evalto I3 ~> D :-
    S >- A1 evalto I1 ~> D1,
    S >- A2 evalto I2 ~> D2,
    I3 is I1 * I2,
    D = dd('A-Times', S >- A1 * A2 evalto I3, [D1, D2]).

% s ⊢ bv evalto bv by B-Const {}
S >- bool(B) evalto B ~> D :-
    D = dd('B-Const', S >- bool(B) evalto B, []).

% s ⊢ a1 < a2 ⇓ bv by B-Lt {
%    σ ⊢ a1 ⇓ i1   σ ⊢ a2 ⇓ i2   (bv = (i1 ≤ i2))
% }
S >- (A1 < A2) evalto BV ~> D :-
    S >- A1 evalto I1 ~> D1,
    S >- A2 evalto I2 ~> D2,
    (I1 < I2 ->
    BV = true;
    BV = false),
    D = dd('B-Lt', S >- (A1 < A2) evalto BV, [D1, D2]).

S >- (A1 <= A2) evalto BV ~> D :-
    S >- A1 evalto I1 ~> D1,
    S >- A2 evalto I2 ~> D2,
    (I1 =< I2 ->
    BV = true;
    BV = false),
    D = dd('B-Le', S >- (A1 <= A2) evalto BV, [D1, D2]).

% σ ⊢ b1 && b2 ⇓ bv3 by B-And {
%    σ ⊢ b1 ⇓ bv1    σ ⊢ b2 ⇓ bv2   (bv3 = (bv1 ∧ bv2))
% }
S >- (B1 && B2) evalto BV3 ~> D :-
    S >- B1 evalto BV1 ~> D1,
    S >- B2 evalto BV2 ~> D2,
    and(BV1, BV2, BV3),
    D = dd('B-And', S >- (B1 && B2) evalto BV3, [D1, D2]).

and(true, true, true).
and(false, _, false).
and(_, false, false).

update([], _ = _, []).
update([L = _ | S], L = V, [L = V | S]).
update([L1 = V1 | S1], L2 = V2, S3) :-
    not(L1 = L2),
    update(S1, L2 = V2, S2),
    S3 = [L1 = V1 | S2].

% UI
derive(Code) :-
    phrase(tokens(Tokens), Code),
    phrase(program(P), Tokens),
    P ~> Derived,
    ppp(Derived, z), !.

code_program(Code, P) :-
    phrase(tokens(Tokens), Code),
    phrase(program(P), Tokens).

code_tokens(Code, Tokens) :-
    phrase(tokens(Tokens), Code).  

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

unparse(C && P, U) :-
    unparse(C, UC), unparse(P, UP), swritef(U, '%w && %w', [UC, UP]).
unparse(while(B do C), U) :-
    unparse(B, UB), unparse(C, UC), swritef(U, 'while (%w) do %w', [UB, UC]).
unparse(C ; P, U) :-
    unparse(C, UC), unparse(P, UP), swritef(U, '%w ; %w', [UC, UP]).
unparse(C := P, U) :-
    unparse(C, UC), unparse(P, UP), swritef(U, '%w := %w', [UC, UP]).
unparse(C >- P, U) :-
    unparseS(C, UC), unparse(P, UP), swritef(U, '%w|- %w', [UC, UP]).
unparse(E changes V, U) :-
    unparse(E, UE), unparse(V, UV), swritef(U, '%w changes %w', [UE, UV]).
unparse(E to V, U) :-
    unparseS(E, UE), unparseS(V, UV), swritef(U, '%w to %w', [UE, UV]).
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

unparseS([X = E], U) :-
    unparse([X = E], U).
unparseS([X = E | C], U) :-
    unparse(X, UX), unparse(E, UE), unparse(C, UC), swritef(U, '%w = %w, %w', [UX, UE, UC]).

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

