:- op(800,xfx,isLessThan).
:- op(600,yfx,~>).

% ------------------- L-Succ
% n is less than S(n)
N isLessThan s(N) ~> (D, W) :-
    pp(D, "%w is less than %w by L-Succ", [N, s(N)], [], W).

% n1 is less than n2    n2 is less than n3
% ---------------------------------------- L-Trans
% n1 is less than n3
N1 isLessThan N3 ~> (D, W) :-
    N1 isLessThan N2, N2 isLessThan N3,
    pp(D, "%w is less than %w by L-Trans", [N1, N3], [], W).

% test
test(Expr) :-
    (Expr -> writef('%w\n', [Expr]);
    writef('%w failed\n', [Expr]), fail).

tests :-
    % 1 < 2
    test( s(z) isLessThan s(s(z)) ), 
    % 2 < 3
    test( s(s(z)) isLessThan s(s(s(z))) ).

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