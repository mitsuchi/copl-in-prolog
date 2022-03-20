:- op(700,xfx,is).
:- op(800,xfx,plus).
:- op(800,xfx,times).

% ------------- P-Zero
% Z plus n is n
z plus N is N.

% n1 plus n2 is n
% --------------------- P-Succ
% S(n1) plus n2 is S(n)
s(N1) plus N2 is s(N) :-
    N1 plus N2 is N.

% --------------- T-Zero
% Z times n1 is Z
z times _ is z.

% n1 times n2 is n3    n2 plus n3 is n4
% ------------------------------------- T-Succ
% S(n1) times n2 is n4
s(N1) times N2 is N4 :-
    N1 times N2 is N3, N2 plus N3 is N4.

% test
test(Expr) :-
    (Expr -> writef('%w\n', [Expr]);
    writef('%w failed\n', [Expr]), fail).

tests :-
    % 1 + 1 = 2
    test( s(z) plus s(z) is s(s(z)) ), 
    % 2 * 3 = 6
    test( s(s(z)) times s(s(s(z))) is s(s(s(s(s(s(z)))))) ).
