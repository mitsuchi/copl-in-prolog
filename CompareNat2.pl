:- op(800,xfx,isLessThan).

% ------------------- L-Zero
% z is less than S(n)
z isLessThan s(N).

% n1 is less than n2
% ------------------ L-SuccSucc
% S(n1) is less than S(n2)
s(N1) isLessThan s(N2) :-
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
