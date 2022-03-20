:- op(800,xfx,isLessThan).

% ------------------- L-Succ
% n is less than S(n)
N isLessThan s(N).

% n1 is less than n2
% ------------------ L-SuccR
% n1 is less than S(n2)
N1 isLessThan s(N2) :-
    N1 isLessThan N2.

% test
test(Expr) :-
    (Expr -> writef('%w\n', [Expr]);
    writef('%w failed\n', [Expr]), fail).

tests :-
    % 1 < 2
    test( s(z) isLessThan s(s(z)) ), 
    % 2 < 3
    test( s(s(z)) isLessThan s(s(s(z))) ).
