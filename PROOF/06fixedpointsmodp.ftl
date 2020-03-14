[synonym set/-s]

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

### BEGIN 01

[synonym group/-s]
[synonym subgroup/-s]

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
Let x be an element of El(G). Then x *^{G} Inv(x, G) = One(G) = Inv(x, G) *^{G} x.

Axiom MulOne.
Let x be an element of El(G). Then x *^{G} One(G) = x =  One(G) *^{G} x.

Axiom InvUniq.
Let x, y be elements of El(G).
If x *^{G} y = One(G) then y = Inv(x, G).

Axiom OneUniq.
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

Axiom.
Let G be a group.
Let H be a subset of El(G).
Assume ((There is a x << H such that x = x) and (for all elements  y, z of H  z *^{G} Inv(y, G) << H)).
Then H is a subgroup of G.

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
Coset(g, H, G) = {g *^{G} h | h << H}.

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Coset(g1, H, G) and Coset(g2, H, G) are not disjunct.
Then Inv(g2, G) *^{G} g1 << H.

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
If Inv(g2, G) *^{G} g1 << H
Then Coset(g1, H, G) = Coset(g2, H, G).

Axiom CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
If Coset(g1, H, G) and  Coset(g2, H, G) are not disjunct
then Coset(g1, H, G) = Coset(g2, H, G).

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(g2, G)*^{G} g1 << H iff Coset(g1, H, G) = Coset(g2, H, G).

Definition.
Let H be a subgroup of G.
Cosets(H, G) = {Coset(g, H, G) | g << El(G)}.

[synonym coset/-s]
Let a coset of H in G denote an element of Cosets(H, G).

Axiom.
Let U be a subgroup of G.
El(G) = \-/ Cosets(U, G).

Axiom.
Let G be a group.
Let U be a subgroup of G.
Cosets(U, G) is a disjunct collection.

Axiom.
Let G be a group.
Let U be a subgroup of G.
U is a coset of U in G.

Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
Conjugate(g, U, G) = {(g *^{G} (u *^{G} Inv(g, G)))| u is an element of U}.

Definition.
Let U, V be subgroups of G.
U and V are conjugates in G iff there is an element g of El(G) such that U = Conjugate(g, V, G).

## END 01



### BEGIN 02

[synonym integer/-s]
[synonym number/-s]

Signature Integers. An integer is a notion.

Signature Naturals. A natural number is an integer.

Let a,b,c,d,e,n,m stand for integers.

Signature NatZero.  0 is a natural number.
Signature NatOne.   1 is a natural number.

Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.

Signature NatPot. Let b be a natural number.  a ^ b is an integer.

Axiom NatPlus. If a and b are natural numbers then a + b is a natural number.
Axiom NatMult. If a and b are natural numbers then a * b is a natural number.


Signature NatLT. a < b is an atom.

Let a is smaller than b stand for a < b.

Axiom TriCh.
a = b \/ a < b \/ b < a.

Axiom.
If a < b then a != b.


Let a - b stand for a + (-b).

Axiom NatSub.
If a < b then b - a is natural number.

Axiom AddAsso.      a + (b + c) = (a + b) + c.
Axiom AddComm.      a + b = b + a.
Axiom AddZero.      a + 0 = a = 0 + a.
Axiom AddNeg.       a - a = 0 = -a + a.

Axiom MulAsso.      a * (b * c) = (a * b) * c.
Axiom MulComm.      a * b = b * a.
Axiom MulOne.       a * 1 = a = 1 * a.

Axiom Distrib.      a * (b + c) = (a*b) + (a*c) and
                    (a + b) * c = (a*c) + (b*c).

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Axiom PotInj.   Let p be an integer. Let n,m be natural numbers. (p ^ n = p ^  m) => n = m.
Axiom PotAdd. Let p be an integer. Let n, m be natural numbers. p ^ (n + m) = (p ^ n) * (p  ^ m).
Axiom PotNotZero. Let p be an integer. Let k be a natural number. p ^ k  != 0.


Axiom MulZero.      a * 0 = 0 = 0 * a.

Axiom MulMinOne.    (-1) * a = -a = a * -1.

Axiom IntCanc.
c != 0 /\ a * c = b * c => a = b.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Axiom DivPlus.
q | a /\ q | b =>  q | (a + b).

Definition EquMod.  a = b (mod q) iff q | a-b.

Definition NeqMod.  a != b (mod q) iff not (a = b (mod q)).

Axiom EquModRef.    a = a (mod q).

[ontored on]
Axiom EquModSym.    a = b (mod q) => b = a (mod q).

Axiom EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).

Axiom EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
[/ontored]

Signature Prime.    a is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom.
Let n be a natural number.
Let p be a prime number.
Let k be a natural number.
If k | p^n then k = 1 or p | k.

Axiom.
Let k be a natural number.
k != 0 => p | p^k.

Axiom.
Let p be a prime.
Let a, b be natural numbers.
If n = (p^a)*c /\ n = (p^b)*d and p does not divide c and p does not divide d then a = b.

## END 02

###BEGIN 03

Signature.
A finite set is a set.

Axiom.
Let M be a finite set.
Let N be a subset of M.
N is a finite set.

Axiom.
Let f be a function such that Dom(f) is a finite set.
Range(f) is a finite set.

Axiom.
Let M, N be finite set.
Prod(M, N) is a finite set.

Signature.
Let M be a finite set.
card(M) is a natural number.

Axiom.
Let M be a finite set.
Let N be a subset of M.
If card(M) = card(N) then M = N.

Axiom.
Let M be a set such that for all elements N of M N is a finite set.
\-/ M is a finite set.

Axiom.
Let N1, N2 be finite sets.
N1 \-/ N2 is a finite set.

Axiom.
Let N1, N2 be finite sets.
If N1 and N2 are disjunct then card(N1 \-/ N2) = card(N1) + card(N2).

Axiom cardUnion.
Let  M be a finite set such that for all elements N of M N is a finite set.
Assume M is a disjunct collection.
Assume that for all elements N1, N2 of M card(N1) = card(N2).
Let N be an element of M.
card(\-/M) = card(N)*card(M).

Axiom cardUnion2.
Let M be a set.
Let k be an integer.
If M is a finite set such that every element of M is a finite set
and M is disjunct collection
and for all elements N of M k | card(N)
then k | card(\-/ M).

Axiom.
Let N1, N2 be finite sets.
card(N1) = card(N2) iff there is a function f such that (f is from N1 to N2 and f is injective and f is surjective onto N2).

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

### END 03

### BEGIN 04

Definition.
A finite group is a group G such that El(G) is a finite set.

Axiom.
Let U be a subgroup of G.
El(G) = \-/ Cosets(U, G).

Axiom.
Let G be a finite group.
Let U be a subgroup of G.
Cosets(U, G) is a finite set.

Definition.
Let G be a finite group.
Let U be a subgroup of G.
Index(G, U) = card(Cosets(U, G)).

Axiom.
Let G be a finite group.
Let U, V be subgroups of G such that V and U are conjugates in G.
Then card(U) = card(V).

Axiom Lagrange.
Let G be a finite group.
Let U be a subgroup of G.
card(El(G)) = card(U)*card(Cosets(U, G)).

### END 04

### BEGIN 05

Definition.
Let M be a set.
Let G be a group.
A group action from G on M is a function f
such that f is from Prod(El(G), M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of El(G)
f[((a *^{G}  b), x)] = f[(a, f[(b, x)])].

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
Let x be an element of M.
Orbit(x, f, M, G) = { f[(a, x)] | a << El(G)}.


Definition.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
Let x << M.
Stab(x,f, M, G) = {y | y << El(G) and f[(y, x)] = x}.

Axiom.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
Let x << M.
Stab(x,f,M, G) is a subgroup of G.

##"Welldefined" by the previous Lemma.
Axiom.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
Let x << M.
There is a function h such that
h is from Cosets(Stab(x, f, M, G), G) to Orbit(x, f, M, G)
and (for all elements i of El(G) h[Coset(i,Stab(x, f, M, G),G)] = f[(i, x)]).

Axiom.
Let G be a finite group.
Let f be a group action from G on M.
Let x << M.
Orbit(x,f, M, G) is a finite set.

Axiom.
Let M be a set.
Let G be a finite group.
Let f be a group action from G on M.
Let x << M.
Index(G, Stab(x, f, M, G)) = card(Orbit(x, f, M, G)).

### END 05

###############################################################

Definition.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
A fixed point of f on M on G is an element y of M such that
for every element a of El(G) f[(a, y)] = y.

Definition.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
fixedPoints(f, M, G) = {y | y is a fixed point of f on M on G}.

Lemma.
Let M be a finite set.
Let G be a group.
Let f be a group action from G on M.
fixedPoints(f, M, G) is a finite set.
Proof.
  Let us show that  every fixed point of f on M on G is an element of M.
    Let x be a fixed point of f on M on G.
    Then x is an element of M.
  end.

   fixedPoints(f, M, G) is a subset of M.

   Therefore the thesis.
Qed.

Lemma.
Let M be a set.
Let G be a finite group.
Let f be a group action from G on M.
Let x be an element of M.
x is a fixed point of f on M on G iff card(Orbit(x, f, M, G)) = 1.


Lemma OrbitsIntersect.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
Let x1, x2 be elements of M such that Orbit(x1, f, M, G) and Orbit(x2, f, M ,G) are not disjunct.
x1 is an element of Orbit(x2,  f, M, G).
Proof.
Take y <<  M such that y << Orbit(x1, f, M, G) and y << Orbit(x2, f, M, G).
Take g1 << El(G) such that f[(g1, x1)] = y.
Take g2 << El(G) such that f[(g2, x2)] = y.

x1 = f[(Inv(g1, G) *^{G} g1, x1)] = f[(Inv(g1, G), y)] = f[(Inv(g1, G) *^{G} g2, x2)].

Therefore the thesis.
Qed.

Lemma.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
Let x1, x2 be elements of M such that Orbit(x1,  f, M, G) and Orbit(x2,  f, M, G) are not disjunct.
Orbit(x1,  f, M, G) = Orbit(x2, f, M, G).
Proof.
Let us show that every element of Orbit(x1,  f, M, G) is an element of Orbit(x2,  f, M, G).
  Let x3 be an element of Orbit(x1,  f, M, G).
  x1 is an element of Orbit(x2,  f, M, G) (by OrbitsIntersect).
  Thus x3 is an element of Orbit(x2,  f, M, G).
end.
Let us show that every element of Orbit(x2, f, M, G) is an element of Orbit(x1,  f, M, G).
  Let x3 be an element of Orbit(x2, f, M, G).
  x2 is an element of Orbit(x1,  f, M, G) (by OrbitsIntersect).
  Thus x3 is an element of Orbit(x1,  f, M, G).
end.
Qed.

Definition.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
OrbitsNotFix(f, M, G) = {Orbit(x,  f, M, G) | x is an element of M and x is not a fixed point of f on M on G}.

Lemma.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
OrbitsNotFix(f, M, G) is a disjunct collection.

Lemma.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
\-/ OrbitsNotFix( f, M, G) = M \\ fixedPoints(f, M, G).
Proof.
Let us show that every element of \-/ OrbitsNotFix( f, M, G) is an element of  M \\ fixedPoints(f, M, G).
  Let x be an element of  \-/ OrbitsNotFix( f, M, G).
  Take an element y of M such that x is an element of Orbit(y,  f, M, G) and y is not an element of fixedPoints(f, M, G).
  x is an element of M.
  x is not a fixed point of f on M on G.
  fixedPoints(f, M , G) is a subset of M.
  Therefore  x is an element of M \\ fixedPoints(f, M, G).
end.

Let us show that every element of M \\ fixedPoints(f, M, G) is an element of  \-/ OrbitsNotFix( f, M, G).
  Let x be an element of M \\ fixedPoints(f, M , G).
  x is an element of M.
  x is not a fixed point of f on M on G.
  Orbit(x, f, M, G) is an element of OrbitsNotFix( f, M, G).
  x is an element of Orbit(x,  f, M, G).
  Therefore  x is an element of  \-/ OrbitsNotFix( f, M, G).
end.
qed.

Lemma.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
 \-/  OrbitsNotFix( f, M, G) and fixedPoints(f, M, G) are disjunct.

Lemma.
Let M be a set.
Let G be a group.
Let f be a group action from G on M.
( \-/ OrbitsNotFix( f, M, G)) \-/ fixedPoints( f, M, G) = M.

Lemma.
Let M be a finite set.
Let G be a finite group.
Let f be a group action from G on M.
OrbitsNotFix( f, M, G) is a finite set.
Proof.
Define h[x] = Orbit(x,  f, M, G) for x in M.

OrbitsNotFix( f, M, G) is a subset of Range(h).
Qed.

Lemma.
Let M be a finite set.
Let G be a finite group.
Let f be a group action from G on M.
card(M) = card(( \-/ OrbitsNotFix( f, M, G)) \-/ fixedPoints( f, M, G)) 
= card(fixedPoints(f, M, G)) + card(\-/ OrbitsNotFix( f, M, G)).

Signature.
Let p be a prime.
A group of order p is a finite group H such that
(there is a natural number n such that card(El(H)) = p ^ n).

Lemma.
Let M be a finite set.
Let p be a prime.
Let G be a group of order p.
Let f be a group action from G on M.
card(fixedPoints(f, M, G)) = card(M) (mod p).
Proof.

\-/ OrbitsNotFix(f, M, G) is a subset of M.

Let us show that p | card( \-/  OrbitsNotFix( f, M, G)).

  Let us show that for all elements N1 of OrbitsNotFix( f, M, G) p | card(N1).

    Let N be an element of OrbitsNotFix( f, M, G).

    Take an element x of M such that N = Orbit(x, f, M, G).
    
    Let us show that card(N) != 1.
      Assume the contrary.
       
      x is not a fixed point of f on M on G .
      x is an element of N.
      Thus x is a fixed point of f on M on G.

      Contradiction.
    end.

    We have card(N) = Index(G, Stab(x, f, M, G)).
    Hence card(El(G)) = card(Stab(x,  f, M, G))*card(N) and card(N) | card(El(G)).
    Therefore p | card(N).
  end.

  (1) OrbitsNotFix( f, M, G) is a finite set such that every element of OrbitsNotFix( f, M, G) is a finite set.
  (2) OrbitsNotFix( f, M, G) is a disjunct collection and for all elements N of OrbitsNotFix( f, M, G) p | card(N).

  Therefore  p | card(\-/ OrbitsNotFix( f, M, G)) (by cardUnion2, 1, 2).
end.

We have card(M) = card(fixedPoints(f, M, G)) + card(\-/ OrbitsNotFix( f, M, G)).

Therefore  card(M) = card(fixedPoints(f, M, G)) (mod p).
qed.