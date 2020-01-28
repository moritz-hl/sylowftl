[read praktikum/main_theorems/lagrange.ftl]

Let G denote a group.

Let a *^{G} b denote Mul(G)[(a, b)]. 

Let M denote a set.


Signature.
a finite group is a group.

Signature.
a pSubgroup of G is a subgroup of G.

Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
conj(g, U, G) = {(Mul(G)[(g, Mul(G)[(u, Inv(G)[g])])])| u is an element of U}.

Definition.
Let U be a subgroup of G.
Let M be a set.
A groupaction from G res U on M is a function f
such that f is from Prod(U, M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of U
f[(Mul(G)[(a, b)], x)] = f[(a, f[(b, x)])].


Definition.
Let U be a subgroup of G.
Let f be a groupaction from G res U on M.
A fixedpoint on M on G res U of f is an element y of M such that
for every element a of U f[(a, y)] = y.

Definition.
Let U be a subgroup of G.
Let f be a groupaction from G res U on M.
fixedPoints(M, G, U, f) = {y | y is a fixedpoint on M on G res U of f}.

Definition.
Let p be a prime number.
Syl(p, G) = {P | P is a subgroup of G and not (p | Index(G, P))}.

Definition.
Let p be a prime number.
Let P be an element of Syl(p, G).
Let U be a subgroup of G.
Op(p, U, P, G) is a groupaction f from G res U  on LCosets(P, G) such that
for all elements u of U for all elements x of El(G) 
f[(u, LCos(x, P, G))] = LCos(Mul(G)[(u, x)],P, G).

Axiom.
Let M be a set.
If card(M) != 0 then there is an element x of M such that x = x.

Theorem Sylow2.
Let p be a prime.
Let G be a finite group.
Let U be a pSubgroup of G.
Let P be an element of Syl(p, G).
Then there is an element g of El(G) such that conj(g, U, G) is a subset of P.
Proof.
  card(fixedPoints(LCosets(P, G), G, U, Op(p, U, P, G))) = Index(G, P) (mod p).
  
  Not Index(G, P) = 0 (mod p).
  
  Hence card(fixedPoints(LCosets(P, G), G, U, Op(p, U, P, G))) != 0.
  
  Take an element x of fixedPoints(LCosets(P, G), G, U, Op(p, U, P, G)).
  Take an element y of El(G) such that x = LCos(y, P, G).
  
  Let us show that conj(Inv(G)[y], U, G) is a subset of P.
    Let h be an element of U.
    x = Op(p, U, P, G)[(h, x)].
    LCos(y, P, G) = Op(p, U, P, G)[(h, LCos(y, P, G))]  =  LCos((h *^{G} y) ,P, G).
    
    Hence h *^{G} y is an element of LCos(y, P, G).
  
    Take an element w of P such that h *^{G} y = y *^{G} w.

    Then we have w = Inv(G)[y] *^{G} (y *^{G} w) =  Inv(G)[y] *^{G} (h *^{G} y).
    Therefore  Inv(G)[y] *^{G} (h *^{G}  y) is an element of P.
  end.
Qed.