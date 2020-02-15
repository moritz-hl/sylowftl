Let M, N denote sets.
Let x << M stand for x is an element of M.
Let x !<< M stand for x is not an element of M.

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

Definition.
Let f be a function. Ran(f) = {f[x] | x << Dom(f)}.

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

Axiom.
Let f be a function.
Assume f is bijection from M to N.
There is a function g such that (g is bijection from N to M and for every x << M g[f[x]] = x).

[synonym group/-s]

##Definition von Gruppen

Signature.
A group is a notion.

Signature.
A finite group is a group.

Let G denote a group.

Signature.
El(G) is a set.

Axiom Lemma.
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
Inv(G) is a function from El(G) to El(G).

Axiom Assoc.
Let x, y, z be elements of El(G). x *^{G} ( y *^{G} z) = (x *^{G} y) *^{G} z. 

Axiom InvOne.
Let x be an element of El(G). Then x *^{G} Inv(G)[x] = One(G) =  Inv(G)[x] *^{G} x.

Axiom MulOne.
Let x be an element of El(G). Then x *^{G} One(G) = x =  One(G) *^{G} x.

Axiom Lemma.
Let x, y be elements of El(G).
If x *^{G} y = One(G) then y = Inv(G)[x].

Axiom Lemma.
Let x, y be elements of El(G).
If x *^{G} y = x then y = One(G).

Definition. #Warum nicht El(H)?
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

Axiom Lemma.
Let G be a group.
Let H be a subset of El(G).
Assume ((There is a x << H such that x = x) and (for all elements  y, z of H  z *^{G} Inv(G)[y] << H)).
Then H is a subgroup of G.

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
LeftCoset(g, H, G) = {g *^{G} h | h << H}.

Axiom Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then Inv(G)[g2] *^{G} g1 << H.

Let Mul(G)[(a, b)] stand for a *^{G} b.

Axiom Ext.
Let D, E be sets.
If E is a subset of D and D is a subset of E then D = E.

Axiom Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Inv(G)[g2] *^{G} g1 << H.
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Axiom CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Axiom Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(G)[g2]*^{G}  g1 << H Iff LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Axiom Lemma.
Let H be a subgroup of G.
Let g,h be elements of El(G).
Assume g is an element of LeftCoset(h, H, G).
Then LeftCoset(g, H, G) = LeftCoset(h, H, G).

Definition.
Let H be a subgroup of G.
LeftCosets(H, G) = {LeftCoset(g, H, G) | g << El(G)}.

[synonym integer/-s]

Signature Integers. An integer is a notion.

Let a,b,c,n,m stand for integers.

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
#Proof. a*(1+(-1)) = (a*1)+(a*(-1))=0. Qed.

Axiom MulMinOne.    (-1) * a = -a = a * -1.

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b. #Definiert Let eine Relation?

Axiom Lemma.
Assume q | a and q | b.
q | (a + b).

Definition EquMod.  a = b (mod q) iff q | a-b.

Definition NeqMod.  a != b (mod q) iff not (a = b (mod q)).

Axiom EquModRef.    a = a (mod q).
Axiom EquModSym.    a = b (mod q) => b = a (mod q).
Axiom EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).
Axiom EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).

Signature Prime. a is prime is an atom.

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
Let N1, N2 be sets.
#Let N2 be a subset of N1.
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
card(N1) = card(N2) iff there is a function f such that 
(f is from N1 to N2 and f is injective and f is surjective onto N2).

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


Axiom Lemma.
Let U be a subgroup of G.
El(G) = Union(LeftCosets(U, G)).


Axiom Lemma.
Let G be a group.
Let U be a subgroup of G.
LeftCosets(U, G) is disjunct collection.


Definition.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is a function f
such that Dom(f) = U
and  for all elements u of U f[u] = (g *^{G} u).

Axiom Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is from U to LeftCoset(g, U, G).

Axiom Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is injective.

Axiom Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is surjective onto LeftCoset(g, U, G).

Axiom Lagrange.
Let G be a group.
Let U be a subgroup of G.
card(Union(LeftCosets(U, G))) = card(U)*card(LeftCosets(U, G)).

Definition.
Let M be a set.
Let G be a group.
A groupaction from G on M is a function f
such that f is from Prod(El(G), M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of El(G)
f[((a *^{G}  b), x)] = f[(a, f[(b, x)])].

Definition.
Let p be a prime number.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(p, U, P, G) is a function f such that f is from Prod(El(Gr(U, G)), LeftCosets(P, G)) to LeftCosets(P, G) and
for all elements u of U for all elements k of El(G)
f[(u, LeftCoset(k, P, G))] = LeftCoset(u *^{G} k,P, G).

Axiom Lemma.
Let p be a prime number.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(p, U, P, G) is a groupaction from Gr(U, G) on LeftCosets(P, G).

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
Let x be an element of M.
Orbit(x, f, G, M) = { f[(a, x)] | a << El(G)}.

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

Axiom Lemma. 
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x be an element of M.
x << Orbit(x, f, G, M).

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x be an element of M.
x is a fixedpoint on M on G of f iff card(Orbit(x, f, G, M)) = 1.


Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) = {y | y << El(G) and f[(y, x)] = x}.

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) is a subgroup of G.


Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
fStabOrb(x, f, G, M) is a function h such that
h is from LeftCosets(Stab(x, f, G, M), G) to Orbit(x, f, G, M)
and (for all elements i of El(G) h[LeftCoset(i,Stab(x, f, G, M),G)] = f[(i, x)]).

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
fStabOrb(x, f, G, M) is injective and surjective onto Orbit(x, f, G, M).


Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Index(G, Stab(x, f, G, M)) = card(Orbit(x, f, G, M)).

Axiom.
Let n be a natural number.
Let p be a prime number.
Let k be a natural number.
If k | p^n then k = 1 or p | k.

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x1, x2 be elements of M.
Assume that Orbit(x1, f, G, M) and Orbit(x2, f, G, M) are not disjunct.
Then Orbit(x1, f, G, M) = Orbit(x2, f, G, M).


Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) = {Orbit(x, f, G, M) | x << M and x !<< fixedPoints(M, G, f)}.

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) is a set such that for all elements N of OrbitsNotTriv(f, G, M) N is a set.


Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) is disjunct collection.

###
Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
For all y << M Orbit(y, f, G, M) is a subset of M.  

###
Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
fixedPoints(M , G, f) is a subset of M.

###
Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let y << M.
Assume y is not an element of fixedPoints(M, G, f).
card(Orbit(y, f, G, M)) != 1.

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) = M \\ fixedPoints(M, G, f).

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) and fixedPoints(M, G, f) are disjunct.

Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) \-/ fixedPoints(M, G, f) = M.

Signature.
Let p be a prime number.
A group of order p is a group H  such that
(there is a natural number n such that card(El(H)) = p ^ n).

Axiom cardUnion2.
Let M be a set such that for all elements N of M N is a set.
Let k be an integer.
If M is disjunct collection and for all elements N of M  k | card(N) then
k | card(Union(M)).


Axiom Lemma.
Let M be a set.
Let p be a prime number.
Let G be a group of order p.
Let f be a groupaction from G on M.
card(fixedPoints(M, G, f)) = card(M) (mod p).


Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
ConjugateSet(g, U, G) = {(g *^{G} (u *^{G} Inv(G)[g]))| u is an element of U}.

##lemma conjugatesets same size


Definition.
#Let G be a finite group?
Let p be a prime number.
Syl(p, G) = {P | P is a subgroup of G and not (p | Index(G, P)) and Gr(P, G) is a group of order p}.

Axiom.
#Let G be a finite group?
Let p be a prime number.
Let U, P be elements of Syl(p, G).
card(U) = card(P).


Theorem Sylow2.
Let G be a finite group.
Let p be a prime number.
Let P, U be an element of Syl(p, G).
Then there is an element g of El(G) such that ConjugateSet(g, U, G) is a subset of P.
Proof.
  Let us show that Index(G, P) != 0  (mod p).
   not (p | -Index(G, P)).
  end.

  card(fixedPoints(LeftCosets(P, G), Gr(U, G), Op(p, U, P, G))) = Index(G, P) (mod p).
  
  Hence card(fixedPoints(LeftCosets(P, G), Gr(U, G),  Op(p, U, P, G))) != 0.
  
  Take an element x of fixedPoints(LeftCosets(P, G), Gr(U, G),  Op(p, U, P, G)).
  Take an element y of El(G) such that x = LeftCoset(y, P, G).
  
  Let us show that ConjugateSet(Inv(G)[y], U, G) is a subset of P.
    Let h be an element of U.
    x is a fixedpoint on LeftCosets(P, G) on Gr(U, G) of Op(p, U, P, G).
    x = Op(p, U, P, G)[(h, x)].
    LeftCoset(y, P, G) = Op(p, U, P, G)[(h, LeftCoset(y, P, G))]  =  LeftCoset((h *^{G} y) ,P, G).
    
    Hence h *^{G} y is an element of LeftCoset(y, P, G).
  
    Take an element w of P such that h *^{G} y = y *^{G} w.

    Then we have w = Inv(G)[y] *^{G} (y *^{G} w) =  Inv(G)[y] *^{G} (h *^{G} y).
    Therefore  Inv(G)[y] *^{G} (h *^{G}  y) is an element of P.
  end.
Qed.

