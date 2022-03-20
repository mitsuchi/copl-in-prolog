
:- op(590,xfy,-->). % ⟶
:- op(590,xfx,->*). % ⟶*
:- op(590,xfx,->>). % ⟶d
:- op(700,xfx,is).
:- op(800,xfx,plus).
:- op(800,xfx,times).

peano(z).
peano(s(N)) :-
    peano(N).

% n1 plus n2 is n3
% ---------------- R-Plus
% n1 + n2 -> n3
N1 + N2 --> N3 :-
    N1 plus N2 is N3.

% n1 times n2 is n3
% ---------------- R-Times
% n1 * n2 -> n3
N1 * N2 --> N3 :-
    N1 times N2 is N3.

% e1 -> e1'
% ------------------- R-PlusL
% e1 + e2 -> e1' + e2
E1 + E2 --> E1_ + E2 :-
    E1 --> E1_.

% e2 -> e2'
% ------------------- R-PlusR
% e1 + e2 -> e1 + e2'
E1 + E2 --> E1 + E2_ :-
    E2 --> E2_.

% e1 -> e1'
% ------------------- R-TimesL
% e1 * e2 -> e1' * e2
E1 * E2 --> E1_ * E2 :-
    E1 --> E1_.

% e2 -> e2'
% ------------------- R-TimesR
% e1 * e2 -> e1 * e2'
E1 * E2 --> E1 * E2_ :-
    E2 --> E2_.

% ------- MR-Zero
% e ->* e
E ->* E.

% e -> e'
% ------- MR-One
% e ->* e'
E ->* E_ :-
    E --> E_.

% e -> e'   e' ->* e''
% --------------------- MR-Multi'
% e ->* e''
E ->* E__ :-
    E --> E_, E_ ->* E__.

% DR-Plus
N1 + N2 ->> N3 :-
    peano(N1), peano(N2), peano(N3),
    N1 plus N2 is N3.

% DR-Times
N1 * N2 ->> N3 :-
    peano(N1), peano(N2), peano(N3),
    N1 times N2 is N3.

% DR-PlusL
E1 + E2 ->> E1_ + E2 :-
    E1 ->> E1_.

% DR-PlusR
N1 + E2 ->> N1 + E2_ :-
    peano(N1), E2 ->> E2_.

% DR-TimesL
E1 * E2 ->> E1_ * E2 :-
    E1 ->> E1_.

% DR-TimesR
N1 * E2 ->> N1 * E2_ :-
    peano(N1), E2 ->> E2_.

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
    % 0 + 2 -> 2
    test( z + s(s(z)) --> s(s(z)) ),
    % 2 + 0 -> 2
    test( s(s(z)) + z --> s(s(z)) ),
    % 2 * 0 -> 0
    test( s(s(z)) * z --> z ),
    % 2 * 1 -> 2
    test( s(s(z)) * s(z) --> s(s(z)) ),
    % 1 * 1 + 1 * 1 -> 1 * 1 + 1
    test( s(z) * s(z) + s(z) * s(z) --> s(z) * s(z) + s(z) ),
    % 0 + 2 ->* 2
    test( z + s(s(z)) ->* s(s(z)) ),
    % 1 * 1 + 1 * 1 ->d 1 + 1 * 1
    test( s(z) * s(z) + s(z) * s(z) ->> s(z) + s(z) * s(z) ),
    % 1 * 1 + 1 * 1 ->* 2
    test( s(z) * s(z) + s(z) * s(z) ->* s(s(z)) ).
