##Lagrange

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

[synonym integer/-s]

Signature Integers. An integer is a notion.

Let a,b,c,n, m stand for integers.

Signature IntZero.  0 is an integer.
Signature IntOne.   1 is an integer.
Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.
Signature.          a ^ b is an integer.

Signature. a < b is an atom.

Let a - b stand for a + (-b).

Axiom AddAsso.      a + (b + c) = (a + b) + c.
Axiom AddComm.      a + b = b + a.
Axiom AddZero.      a + 0 = a = 0 + a.
Axiom AddNeg.       a - a = 0 = -a + a.

Axiom MulAsso.      a * (b * c) = (a * b) * c.
Axiom MulComm.      a * b = b * a.
Axiom MulOne.       a * 1 = a = 1 * a.


Axiom Distrib.      a * (b + c) = (a*b) + (a*c) and
                    (a + b) * c = (a*c) + (b*c).

Axiom MulZero.      a * 0 = 0 = 0 * a.

Axiom MulMinOne.    (-1) * a = -a = a * -1.

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Axiom.
If q | a and q | b then q | (a + b).

Definition EquMod.  a = b (mod q) iff q | a-b.

Definition NeqMod.  a != b (mod q) iff not (a = b (mod q)).

Axiom EquModRef.    a = a (mod q).

Axiom EquModSym.    a = b (mod q) => b = a (mod q).

Axiom EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).

Axiom EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).

Signature Prime.    a is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom PrimeDivisor. n has a prime divisor iff n != 1 /\ n != -1.


[synonym number/-s]

Signature.
Let y be a integer.
y is nonnegative is an atom.

Signature.
A natural number is a nonnegative integer.

Signature.
A finite set is a set.

Signature.
Let M be a set.
card(M) is a natural number.


Definition.
Let M be a set such that for all elements N of M N is a set.
Union(M) = {x | There is an element N of M such that x is an element of N}.

Definition.
Let N1, N2 be a sets.
N1 and N2 are disjunct iff there is no element x of N1 such that x is an element of N2.

Definition.
Let N1, N2 be sets.
N1 \-/ N2 = {x | x is an element of N1 or x is an element of N2}.

Definition.
Let N1 be a set.
Let N2 be a subset of N1.
N1 \\ N2 = {x | x is an element of N1 and (x is not an element of N2)}.

Axiom.
Let N1, N2 be sets.
If N1 and N2 are disjunct then card(N1 \-/ N2) = card(N1) + card(N2).


Definition.
Let M be a set such that for all elements N of M N is a set.
M is disjunct collection iff for all elements N1, N2 of M (N1 = N2 or ( N1 and N2 are disjunct)).

Axiom cardUnion.
Let M be a set such that for all elements N of M N is a set.
Assume M is disjunct collection.
Assume that for all elements N1, N2 of M card(N1) = card(N2).
Let N be an element of M.
card(Union(M)) = card(N)*card(M).

Axiom.
Let N1, N2 be sets.
card(N1) = card(N2) iff there is a function f such that (f is from N1 to N2 and f is injective and f is surjective onto N2).

Axiom.
Let M be a set.
If card(M) != 0 then there is an element x of M such that x = x.

Axiom.
Let M be a set.
card(M) = 1 iff there is an element y of M such that for all elements x of M x = y.

Axiom.
Let M be a set.
Assume 1 < card(M).
Let x be an element of M.
Then there is an element y of M such that x != y.

Axiom.
Let M be a set.
Let N be a subset of M.
If card(M) = card(N) then M = N.


Definition.
Let U be a subgroup of G.
Index(G, U) = card(LeftCosets(U, G)).


Lemma.
Let U be a subgroup of G.
El(G) = Union(LeftCosets(U, G)).
Proof.
Let us show that El(G) is a subset of Union(LeftCosets(U, G)).
  Let g be an element of El(G).
  Then g is an element of LeftCoset(g, U, G).
end.

Let us show that Union(LeftCosets(U, G)) is a subset of El(G).
  Let h be an element of Union(LeftCosets(U, G)).
  Take an element k of El(G) such that h is an element of LeftCoset(k, U, G).
h is an element of El(G).
end.

Therefore El(G) = Union(LeftCosets(U, G)).
Qed.

Lemma.
Let G be a group.
Let U be a subgroup of G.
LeftCosets(U, G) is disjunct collection.
Proof.
Let N1, N2 be elements of LeftCosets(U, G).
Assume that not (N1 and  N2 are disjunct).
Take elements g1, g2  of El(G) such that N1 = LeftCoset(g1, U, G) and N2 = LeftCoset(g2, U, G).
Then g1 << N1 and g1 << N2.
Hence N1 = N2 (by CosEq).
Qed.

Definition.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is a function f
such that Dom(f) = U
and  for all elements u of U f[u] = (g *^{G} u).

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is from U to LeftCoset(g, U, G).

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is injective.

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is surjective onto LeftCoset(g, U, G).

Theorem Lagrange.
Let G be a group.
Let U be a subgroup of G.
card(El(G)) = card(U)*card(LeftCosets(U, G)).
Proof.
  card(El(G)) = card(Union(LeftCosets(U, G))).
  Let N1, N2 be elements of LeftCosets(U, G).
  Take elements g1, g2 of El(G) such that N1 = LeftCoset(g1, U, G) and N2 = LeftCoset(g2, U, G).
  card(N1) = card(U) = card(N2).
  Thus for all elements N11, N12 of LeftCosets(U, G) card(N11) = card(N12).
  U is an element of LeftCosets(U, G).
  LeftCosets(U, G) is disjunct collection.
  card(El(G)) = card(Union(LeftCosets(U, G))) = card(N1)*card(LeftCosets(U, G)) (by cardUnion).
Qed.