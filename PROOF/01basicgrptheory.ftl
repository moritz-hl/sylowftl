Let M, N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
Let M be a set.
M is empty iff there is no element x of M such that x = x.

Definition.
Let M be a set such that for all elements N of M N is a set.
\-/ M = {x | There is an element N of M such that x is an element of N}.

Definition.
Let N1, N2 be sets.
N1 \-/ N2 = {x | x is an element of N1 or x is  an element of N2}.

Definition.
Let N1 be a set.
Let N2 be a subset of N1.
N1 \\ N2 = {x | x is an element of N1 and (x is not an element of N2)}.

Definition.
Let N1, N2 be a sets.
N1 and N2 are disjunct iff there is no element x of N1 such that x is an element of N2.

Definition.
A disjunct collection is a set M such that 
(for all elements N of M N is a set) and for all elements N1, N2 of M (N1 = N2 or ( N1 and N2 are disjunct)).

Definition.
Let f be a function. Let M,N be sets. f is from M to N iff Dom(f) = M and for every element x of M f[x] is an element of N.

Definition.
Let f be a function. Range(f) = {f[x] | x << Dom(f)}.

Definition.
Let f be a function. f is injective iff for all elements x,y of Dom(f) we have (x!=y => f[x] != f[y]).

Definition.
Let f be a function. f is surjective onto M iff (f is from Dom(f) to M and for every y << M there is an element x of Dom(f) such that f[x]=y).
[synonym group/-s]
[synonym subgroup/-s]



##Definition von Gruppen

Signature.
A group is a notion.

Let G denote a group.

Signature.
El(G) is a  set.

Signature.
One(G) is an object.

Axiom.
One(G) << El(G).

Signature.
Let a, b be elements of El(G).
a *^{G} b is an element of El(G).

Signature.
Let a be an element of El(G).
Inv(a, G) is an element of El(G).

Axiom Assoc.
Let x, y, z be elements of El(G). x *^{G} ( y *^{G} z) = (x *^{G} y) *^{G} z. 

Axiom InvOne.
Let x be an element of El(G). x *^{G} Inv(x, G) = One(G) = Inv(x, G) *^{G} x.

Axiom MulOne.
Let x be an element of El(G). x *^{G} One(G) = x =  One(G) *^{G} x.

Lemma InvUniq.
Let x, y be elements of El(G).
If x *^{G} y = One(G) then y = Inv(x, G).

Lemma OneUniq.
Let x, y be elements of El(G).
If x *^{G} y = x then y = One(G).

Definition.
A subgroup of G is set H such that
(H is a subset of El(G))
and (One(G) << H)
and (for every x << H Inv(x, G) << H)
and (for all elements x, y of H x *^{G} y << H).

Definition.
Let U be a subgroup of G.
Gr(U, G) is a group H such that
(El(H) = U)
and (One(H) = One(G))
and (for every x << U Inv(x, H) = Inv(x, G))
and (for all elements x, y of U x *^{Gr(U, G)} y = x *^{G} y).

Lemma.
Let G be a group.
Let H be a subset of El(G).
Assume ((There is a x << H such that x = x) and (for all elements  y, z of H  z *^{G} Inv(y, G) << H)).
H is a subgroup of G.
Proof.
  One(G) << H.
    Proof.
      Take x << H.
      Then One(G) = x *^{G} Inv(x, G).
      Thus One(G) << H.
    end.

  For every x << H Inv(x, G) << H.
    Proof.
      Let x be an element of H.
      Then Inv(x, G) = One(G) *^{G} Inv(x, G).
      Thus Inv(x, G) << H.
    end.

  For all elements x, y of H x *^{G} y << H.
  Proof.
    Let x, y be elements of H.
    Then Inv(x, G) << H.
    x *^{G} y = x *^{G}  Inv(Inv(y, G), G).
    Hence x *^{G} y << H.
    end.
Qed.

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
Coset(g, H, G) = {g *^{G} h | h << H}.

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Coset(g1, H, G) and Coset(g2, H, G) are not disjunct.
Inv(g2, G) *^{G} g1 << H.
Proof.
  Take y << El(G) such that (y << Coset(g1, H, G) and y << Coset(g2, H, G)).
  Take b << H such that y = g1 *^{G} b.
  Take c << H such that y = g2 *^{G} c.

  We have g1 = y *^{G} Inv(b, G).
          g2 = y *^{G} Inv(c, G).
          Inv(g2, G) = c *^{G} Inv(y, G).
          Inv(y, G) *^{G} g1 = Inv(b, G).

  Therefore Inv(g2, G) *^{G}  g1 = c *^{G} (Inv(b, G)).
qed.


Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
If Inv(g2, G) *^{G} g1 << H
Then Coset(g1, H, G) = Coset(g2, H, G).
Proof.
Assume Inv(g2, G) *^{G} g1 << H.

Every element of Coset(g1, H, G) is an element of Coset(g2, H, G).
Proof.
  Let y be an element of Coset(g1, H, G).
  Take a << H such that y = g1 *^{G} a.
  (Inv(g2, G) *^{G}  g1) *^{G}  a << H.
  Then y = g1 *^{G}  a = g2 *^{G} ((Inv(g2, G) *^{G}  g1) *^{G}  a).
end.

Every element of Coset(g2, H, G) is an element of  Coset(g1, H, G).
Proof.
  Let y be an element of Coset(g2, H, G).
  Take a << H such that y = g2 *^{G} a.
  (Inv(g2, G) *^{G}  g1) *^{G}  a << H.
  Then y = g2 *^{G} a =g1 *^{G} ((Inv(g1, G)*^{G} g2)*^{G} a).
end.

Therefore Coset(g1, H, G) = Coset(g2, H, G).
Qed.

Lemma CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
If Coset(g1, H, G) and  Coset(g2, H, G) are not disjunct
then Coset(g1, H, G) = Coset(g2, H, G).

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(g2, G)*^{G} g1 << H iff Coset(g1, H, G) = Coset(g2, H, G).

Definition.
Let H be a subgroup of G.
Cosets(H, G) = {Coset(g, H, G) | g << El(G)}.

[synonym coset/-s]
Let a coset of H in G denote an element of Cosets(H, G).

Lemma.
Let U be a subgroup of G.
El(G) = \-/ Cosets(U, G).
Proof.
Let us show that every element of El(G) is an element of \-/ Cosets(U, G).
  Let g be an element of El(G).
  g is an element of Coset(g, U, G).
end.

Let us show that every element of \-/ Cosets(U, G) is an element of El(G).
  Let h be an element of \-/ Cosets(U, G).
  Take an element k of El(G) such that h is an element of Coset(k, U, G).
  Coset(k, U, G) is a subset of El(G).
  Hence h is an element of El(G).
end.

Therefore El(G) = \-/ Cosets(U, G).
Qed.

Lemma.
Let G be a group.
Let U be a subgroup of G.
Cosets(U, G) is a disjunct collection.
Proof.
Let us show that for every elements N1, N2 of Cosets(U, G) N1 = N2 or (N1 and N2 are disjunct).
  Let N1, N2 be cosets of U in G.
  Take elements g1, g2 of El(G) such that N1 = Coset(g1, U, G) and N2 = Coset(g2, U, G).
  If N1 and N2 are not disjunct then N1 = N2 (by CosEq).
  Therefore the thesis.
end.
Qed.

Lemma.
Let G be a group.
Let U be a subgroup of G.
U is a coset of U in G.
Proof.
  We have U = Coset(One(G), U, G).
  Therefore the thesis.
Qed.

Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
Conjugate(g, U, G) = {(g *^{G} (u *^{G} Inv(g, G)))| u is an element of U}.

Definition.
Let U, V be subgroups of G.
U and V are conjugates in G iff there is an element g of El(G) such that U = Conjugate(g, V, G).