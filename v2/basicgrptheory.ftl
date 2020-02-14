###Basic group theory

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

Lemma.
Let x, y be elements of El(G).
If x *^{G} y = One(G) then y = Inv(G)[x].

Lemma.
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

Lemma.
Let G be a group.
Let H be a subset of El(G).
Assume ((There is a x << H such that x = x) and (for all elements  y, z of H  z *^{G} Inv(G)[y] << H)).
Then H is a subgroup of G.
Proof.
  One(G) << H.
    Proof.
      Take x << H.
      Then One(G) = x *^{G} Inv(G)[x].
      Thus One(G) << H.
    end.

  For every x << H Inv(G)[x] << H.
    Proof.
      Let x be an element of H.
      Then Inv(G)[x] = One(G) *^{G} Inv(G)[x].
      Thus Inv(G)[x] << H.
    end.

  For all elements x, y of H x *^{G} y << H.
  Proof.
    Let x, y be elements of H.
    Then Inv(G)[x] << H.
    x *^{G} y = x *^{G}  Inv(G)[Inv(G)[y]].
    Hence x *^{G} y << H.
    end.
Qed.


Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
LeftCoset(g, H, G) = {g *^{G} h | h << H}.



Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then Inv(G)[g2] *^{G} g1 << H.
Proof.
  Take y << El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
  Take b << H such that y = g1 *^{G} b.
  Take c << H such that y = g2 *^{G} c.

  g1 = y *^{G} Inv(G)[b].
  g2 = y *^{G} Inv(G)[c].
  Inv(G)[g2] = c *^{G} Inv(G)[y].

  Inv(G)[g2] *^{G} g1 = (c *^{G} Inv(G)[y]) *^{G}  g1.


  Inv(G)[y] *^{G} g1 = Inv(G)[y] *^{G} (y *^{G} Inv(G)[b])
  = (Inv(G)[y] *^{G} y) *^{G} Inv(G)[b].

  (Inv(G)[g2] *^{G}  g1) = c *^{G} (Inv(G)[y] *^{G} g1).
qed.


Let Mul(G)[(a, b)] stand for a *^{G} b.

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Inv(G)[g2] *^{G} g1 << H.
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).
Proof.
LeftCoset(g1, H, G) is a subset of LeftCoset(g2, H, G).
Proof.
  Let y be an element of LeftCoset(g1, H, G).
  Take a << H such that y = g1 *^{G} a.
  (Inv(G)[g2] *^{G}  g1) *^{G}  a << H.



  Then y = g1 *^{G}  a = g2 *^{G} ((Inv(G)[g2] *^{G}  g1) *^{G}  a).
end.

LeftCoset(g2, H, G) is a subset of LeftCoset(g1, H, G).
Proof.
  Let y be an element of LeftCoset(g2, H, G).
  Take a << H such that y = g2 *^{G} a.

  Then y = g2 *^{G} a =g1 *^{G} ((Inv(G)[g1]*^{G} g2)*^{G} a).
end.
Qed.



Lemma CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(G)[g2]*^{G}  g1 << H Iff LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Lemma.
Let H be a subgroup of G.
Let g be an element of El(G).
Let h be an element of El(G).
Assume g is an element of LeftCoset(h, H, G).
Then LeftCoset(g, H, G) = LeftCoset(h, H, G).