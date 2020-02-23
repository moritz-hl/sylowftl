###Fixed Points mod p
[synonym set/-s]
Let M, N denote sets.
Let x << M stand for x is an element of M.
Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
Let M be a set such that every element of M is a set.
Union(M) = {x | There is an element N of M such that x is an element of N}.

Definition.
Let N1, N2 be a sets.
N1 and N2 are disjunct iff there is no element of N1 that is an element of N2.

Definition.
A disjunct collection is a set M such that 
(every element of M is a set) and for all elements N1, N2 of M (N1 = N2 or ( N1 and N2 are disjunct)).

Definition.
Let N1, N2 be sets.
N1 \-/ N2 = {x | x is an element of N1 or x is  an element of N2}.

Definition.
Let N1 be a set.
Let N2 be a subset of N1.
N1 \\ N2 = {x | x is an element of N1 and (x is not an element of N2)}.

Definition.
Let f be a function. Let M,N be sets. f is from M to N iff Dom(f) = M and for every element x of M f[x] is an element of N.

Definition.
Let f be a function. Range(f) = {f[x] | x << Dom(f)}.

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

[synonym group/-s]

Signature.
A group is a notion.

Let G denote a group.

Signature.
El(G) is a  set.

Lemma.
Let x, y be elements of El(G).
(x, y) is an element of Prod(El(G), El(G)).

Signature.
One(G) is a set.

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

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
Coset(g, H, G) = {g *^{G} h | h << H}.

Definition.
Let H be a subgroup of G.
Cosets(H, G) = {Coset(g, H, G) | g << El(G)}.

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
Definition Divisor. A divisor of b is a integer a
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

Signature NNeg. a is nonnegative is an atom.

Let a prime stand for a prime nonzero integer.

[synonym number/-s]

Let a natural number stand for a nonnegative integer.

Axiom.
Let n be a natural number.
Let p be a prime number.
Let k be a natural number.
If k | p^n then k = 1 or p | k.

Signature.
A finite set is a set.

Axiom.
Let M be a finite set.
Let N be a subset of M.
N is a finite set.

Axiom RanFin.
Let f be a function such that Dom(f) is a finite set.
Range(f) is a finite set.

Axiom.
Let M, N be finite set.
Prod(M, N) is a finite set.

Axiom.
Let M be a finite set such that for all elements N of M N is a finite set.
Union(M) is a finite set.

Axiom.
Let N1, N2 be finite sets.
N1 \-/ N2 is a finite set.

Signature.
Let M be a finite set.
card(M) is a natural number.

Axiom.
Let N1, N2 be finite sets.
If N1 and N2 are disjunct then card(N1 \-/ N2) = card(N1) + card(N2).

Definition.
a finite group is a group G such that El(G) is a finite set.


Axiom cardUnion.
Let M be a finite set such that every element of M is a finite set.
Let N be an element of M.
If M is disjunct collection and for all elements N1, N2 of M card(N1) = card(N2)
then card(Union(M)) = card(N)*card(M).

Axiom cardUnion2.
Let M be a finite set such that every element of M is a finite set.
Let k be an integer.
If M is disjunct collection and  for all elements N of M  k | card(N) then
k | card(Union(M)).

Axiom.
Let M be a finite set.
If card(M) != 0 then there is an element x of M such that x = x.

Axiom.
Let M be a finite set.
card(M) = 1 iff there is an element y of M such that for all elements x of M x = y.

Axiom.
Let M be a finite set.
Assume 1 < card(M).
Let x be an element of M.
Then there is an element y of M such that x != y.

Axiom.
Let M be a finite set.
Let N be a subset of M.
If card(M) = card(N) then M = N.

Axiom.
Let G be a finite group.
Let U be a subgroup of G.
Cosets(U, G) is a finite set.

Definition.
Let G be a finite group.
Let U be a subgroup of G.
Index(G, U) = card(Cosets(U, G)).

Definition.
Let M be a set.
Let G be a group.
A groupaction from G on M is a function f
such that f is from Prod(El(G), M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of El(G)
f[((a *^{G}  b), x)] = f[(a, f[(b, x)])].

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
Let x be an element of M.
Orbit(x, f, G, M) = { f[(a, x)] | a << El(G)}.

Axiom. #05, 360
Let G be a finite group.
Let f be a groupaction from G on M.
Let x << M.
Orbit(x,f, G, M) is a finite set.

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
A fixedpoint on M on G of f is an element y of M such that
for every element a of El(G) f[(a, y)] = y.

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
fixedPoints(M, G, f) = {y | y is a fixedpoint on M on G of f}.

Lemma.
Let M be a set.
Let G be a finite group.
Let f be a groupaction from G on M.
Let x be an element of M.
x is a fixedpoint on M on G of f iff card(Orbit(x, f, G, M)) = 1.

Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) = {y | y << El(G) and f[(y, x)] = x}.

Axiom.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) is a subgroup of G.

Axiom.
Let M be a set.
Let G be a finite group.
Let f be a groupaction from G on M.
Let x << M.
Index(G, Stab(x, f, G, M)) = card(Orbit(x, f, G, M)).

Axiom Lagrange. #pr04
Let G be a finite group.
Let U be a subgroup of G.
card(El(G)) = card(U)*card(Cosets(U, G)).

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x1, x2 be elements of M.
Assume that Orbit(x1, f, G, M) and Orbit(x2, f, G, M) are not disjunct.
Then Orbit(x1, f, G, M) = Orbit(x2, f, G, M).
Proof.
Let us show that every element of Orbit(x1, f, G, M) is an element of Orbit(x2, f, G, M).
  Let x3 be an element of Orbit(x1, f, G, M).
  x1 is an element of Orbit(x2, f, G, M).
  Thus x3 is an element of Orbit(x2, f, G, M).
end.
Let us show that every element of Orbit(x2, f, G, M) is an element of Orbit(x1, f, G, M).
  Let x3 be an element of Orbit(x2, f, G, M).
  x2 is an element of Orbit(x1, f, G, M).
  Thus x3 is an element of Orbit(x1, f, G, M).
end.
Qed.

Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) = {Orbit(x, f, G, M) | x is an element of M and x is not an element of fixedPoints(M, G, f)}.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Every element of OrbitsNotTriv(f, G, M) is a set.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) is a disjunct collection.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) = M \\ fixedPoints(M, G, f).
Proof.
Let us show that every element of Union(OrbitsNotTriv(f, G, M)) is an element of  M \\ fixedPoints(M, G, f).
  Let x be an element of Union(OrbitsNotTriv(f, G, M)).
  Take an element y of M such that x is an element of Orbit(y, f, G, M) and y is not an element of fixedPoints(M, G, f).
  x is an element of M.
  x is not an element of fixedPoints(M, G, f).
  fixedPoints(M , G, f) is a subset of M.
  Hence x is an element of M \\ fixedPoints(M, G, f).
end.

Let us show that every element of M \\ fixedPoints(M, G, f) is an element of Union(OrbitsNotTriv(f, G, M)).
  Let x be an element of M \\ fixedPoints(M , G, f).
  x is an element of M.
  x is not an element of fixedPoints(M , G, f).
  Orbit(x, f, G, M) is an element of OrbitsNotTriv(f, G, M).
  x is an element of Orbit(x, f, G, M).
  Thus x is an element of Union(OrbitsNotTriv(f, G, M)).
end.
qed.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) and fixedPoints(M, G, f) are disjunct.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) \-/ fixedPoints(M, G, f) = M.

Lemma.
Let M be a finite set.
Let G be a group.
Let f be a groupaction from G on M.
fixedPoints(M, G, f) is a finite set.
Proof.
  Let us show that  every element of fixedPoints(M, G, f) is an element of M.
    Let x be an element of fixedPoints(M, G, f).
    Then x is an element of M.
  end.

   fixedPoints(M, G, f) is a subset of M.

   Therefore the thesis.
Qed.

Signature.
Let p be a prime number.
A group of order p is a finite group H such that
(there is a natural number n such that card(El(H)) = p ^ n).

Axiom cardUnion3.
Let M be a set.
Let k be an integer.
If M is a finite set such that every element of M is a finite set
and M is disjunct collection
and for all elements N of M k | card(N)
then k | card(Union(M)).

Lemma.
Let M be a finite set.
Let p be a prime number.
Let G be a group of order p.
Let f be a groupaction from G on M.
card(fixedPoints(M, G, f)) = card(M) (mod p).
Proof.

Union(OrbitsNotTriv(f, G, M)) is a subset of M.

Let us show that p | card(Union(OrbitsNotTriv(f, G, M))).
  [prove off]
  OrbitsNotTriv(f, G, M) is a finite set.
  [/prove]

  Every element of OrbitsNotTriv(f, G, M) is a finite set.

  p is an integer.

  Let us show that for all elements N1 of OrbitsNotTriv(f, G, M) p | card(N1).
    Let N be an element of OrbitsNotTriv(f, G, M).

    Take an element x of M such that N = Orbit(x, f, G, M).
    
    Let us show that card(N) != 1.
      Assume the contrary.
       
      x is not a fixedPoint on M on G of f.

      x is an element of N.
      Thus x is a fixedPoint on M on G of f.

      Contradiction.
    end.

    We have card(N) = Index(G, Stab(x, f, G, M)).
    Hence card(El(G)) = card(Stab(x, f, G, M))*card(N) and card(N) | card(El(G)).
    Therefore p | card(N).
  end.

  (1) OrbitsNotTriv(f, G, M) is a finite set such that every element of OrbitsNotTriv(f, G, M) is a finite set.
  (3) OrbitsNotTriv(f, G, M) is a disjunct collection and for all elements N of OrbitsNotTriv(f, G, M) p | card(N).

  Therefore  p | card(Union(OrbitsNotTriv(f, G, M))) (by cardUnion3, 1, 3).
end.
 
We have card(M) = card(fixedPoints(M, G, f)) + card(Union(OrbitsNotTriv(f, G, M))).

Therefore  card(M) = card(fixedPoints(M, G, f)) (mod p).
qed.