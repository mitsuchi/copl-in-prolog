:- op(700,xfx,is).
:- op(800,xfx,plus).
:- op(800,xfx,times).
:- op(600,xfx,~>).

% ------------- P-Zero
% Z plus n is n
z plus N is N ~> (D, W) :-
    pp(D, "Z plus %w is %w by P-Zero", [N, N], [], W).

% n1 plus n2 is n
% --------------------- P-Succ
% S(n1) plus n2 is S(n)
s(N1) plus N2 is s(N) ~> (D, W) :-
    N1 plus N2 is N ~> (D1, s(W)),
    pp(D, "%w plus %w is %w by P-Succ", [s(N1), N2, s(N)], [D1], W).
    
% --------------- T-Zero
% Z times n1 is Z
z times N1 is z ~> (D, W) :-
    pp(D, "Z times %w is Z by T-Zero", [N1], [], W).

% n1 times n2 is n3    n2 plus n3 is n4
% ------------------------------------- T-Succ
% S(n1) times n2 is n4
s(N1) times N2 is N4 ~> (D, W) :-
    N1 times N2 is N3 ~> (D1, s(W)),
    N2 plus N3 is N4 ~> (D2, s(W)),
    pp(D, "%w times %w is %w by T-Succ", [s(N1), N2, N4], [D1, D2], W).

% test
test(Expr) :-
    (Expr -> writef('%w\n', [Expr]);
    writef('%w failed\n', [Expr]), fail).

tests :-
    % 1 + 1 = 2
    test( s(z) plus s(z) is s(s(z)) ~> D ), 
    % 2 * 3 = 6
    test( s(s(z)) times s(s(s(z))) is s(s(s(s(s(s(z)))))) ~> D).

% pretty print
indent(z, "").
indent(s(N), S) :-
    indent(N, S1), swritef(S, "  %w", [S1]).

upper(z, 'Z').
upper(s(N), Up) :-
    upper(N, Up1), swritef(Up, "S(%w)", [Up1]).

pp(Derivation, Format, Vars, Inners, W) :-
    indent(W, Indent),
    maplist(upper, Vars, UpVars),
    swritef(D1, Format, UpVars),
    reverse(Inners, Rs),
    foldl(concat, Rs, "", InnersStr),
    swritef(Derivation, '%w%w {\n%w%w};\n', [Indent, D1, InnersStr, Indent]).