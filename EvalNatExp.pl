:- op(600,xfx,⇓).
:- op(700,xfx,is).
:- op(800,xfx,plus).
:- op(800,xfx,times).

% -------------- E-Const
% n ⇓ n
N ⇓ N.

% e1 ⇓ n1   e2 ⇓ n2   n1 plus n2 is n
% ------------------------------------- E-Plus
% e1 + e2 ⇓ n
E1 + E2 ⇓ N :-
    E1 ⇓ N1, E2 ⇓ N2, N1 plus N2 is N.

% e1 ⇓ n1   e2 ⇓ n2   n1 times n2 is n
% ------------------------------------- E-Times
% e1 * e2 ⇓ n
E1 * E2 ⇓ N :-
    E1 ⇓ N1, E2 ⇓ N2, N1 times N2 is N.

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
    % 0 + 2 ⇓ 2
    test( z + s(s(z)) ⇓ s(s(z)) ),
    % 2 + 0 ⇓ 2
    test( s(s(z)) + z ⇓ s(s(z)) ),
    % 3 + 2 * 1 ⇓ 5
    test( s(s(s(z))) + s(s(z)) * s(z) ⇓ s(s(s(s(s(z))))) ).