[read praktikum/main_theorems/lagrange.ftl]
Let G denote a group.

Let a *^{G} b denote Mul(G)[(a, b)]. 

Let M denote a set.

Signature.
a finite group is a group.

Signature.
Let p be a prime number.
A subgroup of order p of G is a subgroup of G such that
(there is a natural number n such that card(El(G)) = p ^ n).

Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
conj(g, U, G) = {(Mul(G)[(g, Mul(G)[(u, Inv(G)[g])])])| u is an element of U}.

Definition.
Let p be a prime number.
Syl(p, G) = {P | P is a subgroup of G and not (p | Index(G, P))}.

Axiom.
Let p be a prime number.
Let U, P be elements of Syl(p, G).
card(U) = card(P).

Definition.
Let p be a prime number.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(p, U, P, G) is a groupaction f from Gr(U, G)  on LCosets(P, G) such that
for all elements u of U for all elements x of El(G) 
f[(u, LCos(x, P, G))] = LCos(Mul(G)[(u, x)],P, G).

Theorem Sylow2.
Let p be a prime number.
Let G be a finite group.
Let P, U be an element of Syl(p, G).
Then there is an element g of El(G) such that conj(g, U, G) is a subset of P.
Proof.
  card(fixedPoints(LCosets(P, G), Gr(U, G), Op(p, U, P, G))) = Index(G, P) (mod p).
  
  Index(G, P) != 0  (mod p).
  
  Hence card(fixedPoints(LCosets(P, G), Gr(U, G),  Op(p, U, P, G))) != 0.
  
  Take an element x of fixedPoints(LCosets(P, G), Gr(U, G),  Op(p, U, P, G)).
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