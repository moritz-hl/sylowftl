### Group action of Sylow 2

Let M, N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
Let f be a function. Let M,N be sets. f is from M to N iff Dom(f) = M and for every element x of M f[x] is an element of N.

Definition.
Let f be a function. f is injective iff for all elements x,y of Dom(f) we have (x!=y => f[x] != f[y]).

Definition.
Let f be a function. f is surjective onto M iff (f is from Dom(f) to M and for every y << M there is an element x of Dom(f) such that f[x]=y).

Definition.
Let f be a function. f is bijection from M to N iff (f is injective and f is from M to N) and (f is surjective onto M).

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

[synonym group/-s]

##Definition von Gruppen

Signature.
A group is a notion.

Signature.
a finite group is a group.

Let G denote a group.

Signature.
El(G) is a  set.

Lemma.
Let x, y be elements of El(G).
(x, y) is an element of Prod(El(G), El(G)).

Signature.
One(G) is an object.

Axiom.
One(G) << El(G).

Signature.
Let a, b be elements of El(G).
a *^{G} b is an element of El(G).

Signature.
Inv(G) is an function from El(G) to El(G).

Axiom Assoc.
Let x, y, z be elements of El(G). x *^{G} ( y *^{G} z) = (x *^{G} y) *^{G} z. 

Axiom InvOne.
Let x be an element of El(G). Then x *^{G} Inv(G)[x] = One(G) =  Inv(G)[x] *^{G} x.

Axiom MulOne.
Let x be an element of El(G). Then x *^{G} One(G) = x =  One(G) *^{G} x.

Axiom.
Let x, y be elements of El(G).
If x *^{G} y = One(G) then y = Inv(G)[x].

Axiom.
Let x, y be elements of El(G).
If x *^{G} y = x then y = One(G).

Definition.
A subgroup of G is set H such that
(H is a subset of El(G))
and (One(G) << H)
and (for every x << H Inv(G)[x] << H)
and (for all elements x, y of H x *^{G} y << H).

Definition.
Let U be a subgroup of G.
Gr(U, G) is a group H such that
(El(H) = U)
and (One(H) = One(G))
and (for every x << U Inv(H)[x] = Inv(G)[x])
and (for all elements x, y of U x *^{Gr(U, G)} y = x *^{G} y).

Axiom.
Let G be a group.
Let H be a subset of El(G).
Assume ((There is a x << H such that x = x) and (for all elements  y, z of H  z *^{G} Inv(G)[y] << H)).
Then H is a subgroup of G.


Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
LeftCoset(g, H, G) = {g *^{G} h | h << H}.



Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then Inv(G)[g2] *^{G} g1 << H.

Let Mul(G)[(a, b)] stand for a *^{G} b.

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Inv(G)[g2] *^{G} g1 << H.
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).



Axiom CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(G)[g2]*^{G}  g1 << H Iff LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Axiom.
Let H be a subgroup of G.
Let g be an element of El(G).
Let h be an element of El(G).
Assume g is an element of LeftCoset(h, H, G).
Then LeftCoset(g, H, G) = LeftCoset(h, H, G).

Definition.
Let H be a subgroup of G.
LeftCosets(H, G) = {LeftCoset(g, H, G) | g << El(G)}.

Definition.
Let M be a set.
Let G be a group.
A groupaction from G on M is a function f
such that f is from Prod(El(G), M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of El(G)
f[((a *^{G}  b), x)] = f[(a, f[(b, x)])].

Lemma.
Let P be a subgroup of G.
Let U be a subgroup of G.
Let u be an element of U.
Let x, y be elements of El(G) such that LeftCoset(x, P, G) = LeftCoset(y, P, G). 
Then LeftCoset(u *^{G} x, P, G) = LeftCoset(u *^{G} y, P, G).
Proof.
  Let us show that every element of LeftCoset(u *^{G} x, P, G) is an element of  LeftCoset(u *^{G} y, P, G).
    Let i be an element of LeftCoset(u *^{G} x, P, G).
    Take an element p of P such that i =  (u *^{G} x) *^{G} p.
    Then we have Inv(G)[u] *^{G} i =  x *^{G} p.
    Inv(G)[u] *^{G} i is an element of LeftCoset(x, P, G).
    Therefore Inv(G)[u] *^{G} i is an element of LeftCoset(y, P, G)
    and i is an element of LeftCoset(u *^{G} y, P, G).
  end.
qed.


###Welldefined by the previous Lemma.
Definition.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(U, P, G) is a function f 
such that f is from Prod(El(Gr(U, G)), LeftCosets(P, G)) to LeftCosets(P, G) and
for all elements u of U for all elements x of El(G) 
f[(u, LeftCoset(x, P, G))] = LeftCoset(u *^{G}  x,P, G).



Lemma.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(U, P, G) is a groupaction from Gr(U, G) on LeftCosets(P, G).
Proof.
Take a function f such that f = Op(U, P, G).
Take a group H such that  H = Gr(U, G).
Take a set M such that M = LeftCosets(P, G).

For every element x of M we have f[(One(H), x)] = x.

Let us show that for every element x of M for all elements a, b of El(H)
 f[(a *^{H} b, x)] =  f[(a,  f[(b, x)])].
  Let x be an element of M.
  Let a, b be elements of El(H).

  Take an element g of El(G) such that x = LeftCoset(g, P, G).

  We have f[(b, x)] = LeftCoset(b *^{G} g,P, G).

  f[(a, f[(b, x)])] = LeftCoset(a *^{G} (b *^{G} g),P, G).

  f[(a *^{H}  b, x)] = LeftCoset((a *^{G} b)*^{G} g,P, G).

  Thus f[(a, f[(b, x)])] = f[(a *^{H} b, x)].
end.

Therefore the thesis.
Qed.