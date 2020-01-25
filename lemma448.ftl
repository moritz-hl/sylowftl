Let M,N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

###Functions

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

Definition.
Let f, g be functions.
Assume g is from Dom(g) to Dom(f).
comp(f, g) is a function h such that Dom(h) = Dom(g)
and for every x << Dom(g) comp(f, g)[x] = f[g[x]].

Axiom.
Let f be a function.
Assume f is bijection from M to N.
There is a function g such that (g is bijection from N to M and for every x << M g[f[x]] = x).


[synonym group/-s]
Signature.
A group is a notion.

Let G denote a group.

Signature.
El(G) is a  set.

Signature.
One(G) is a set.

Axiom.
One(G) << El(G).

Signature.
Mul(G) is a function from  Prod(El(G), El(G)) to El(G).

Let a *^{G} b denote Mul(G)[(a, b)]. 

Signature.
Inv(G) is an function from El(G) to El(G).


Axiom Assoc.
Let x, y, z be elements of El(G).
Mul(G)[(x, Mul(G)[(y, z)])]
= Mul(G)[(Mul(G)[(x, y)], z)].

Axiom InvOne.
Let x be an element of El(G). Then Mul(G)[(x, Inv(G)[x])] = One(G) =  Mul(G)[( Inv(G)[x], x)].

Axiom MulOne.
Let x be an element of El(G). Then Mul(G)[(x,One(G))] = x =  Mul(G)[(One(G), x)].

Lemma OneUni.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = x.
then y = One(G).

Lemma InvUni.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = One(G).
Then y = Inv(G)[x].

Lemma InvOne.
Inv(G)[One(G)] = One(G).

Lemma MulInv.
Let x, y be elements of El(G).
Then Inv(G)[Mul(G)[(x, y)]] = Mul(G)[(Inv(G)[y],Inv(G)[x])].
Proof.
Mul(G)[(Mul(G)[(x, y)], Mul(G)[(Inv(G)[y],Inv(G)[x])])] = One(G).
Qed.

Lemma.
Let x be an element of El(G).
Then Inv(G)[Inv(G)[x]] = x.

Definition.
A subgroup of G is set H such that
(H is a subset of El(G))
and (One(G) << H)
and (for every x << H Inv(G)[x] << H)
and (for all elements x, y of H Mul(G)[(x, y)] << H).

[synonym integer/-s]

Signature Integers. An integer is a notion.

Let a,b,c,d,i,j,k,l,m,n stand for integers.

Signature IntZero.  0 is an integer.
Signature IntOne.   1 is an integer.
Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.
Signature IntPow. a ^^ b is an integer.


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

Lemma MulZero.      a * 0 = 0 = 0 * a.
Proof. a * 0 = a * (1 + (-1)). Qed.


Lemma MulMinOne.    -1 * a = -a = a * -1.
Proof. a + ((-1)*a) = 0. Qed.

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Definition EquMod.  a = b (mod q) iff q | a-b.

Lemma EquModRef.    a = a (mod q).
[ontored on]
Lemma EquModSym.    a = b (mod q) => b = a (mod q).
Proof.
    Assume that a = b (mod q).
    (1) Take n such that q * n = a - b.
    q * -n .= (-1) * (q * n) (by MulMinOne, MulAsso,MulComm,MulBubble)
                   .= (-1) * (a - b) (by 1).
qed.
[/ontored]
Lemma EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).
Proof.
    Assume that a = b (mod q) /\ b = c (mod q).
    Take n such that q * n = a - b.
    Take m such that q * m = b - c.
    We have q * (n + m) = a - c.
qed.

Lemma EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
Proof.
    Assume that a = b (mod p * q).
    Take m such that (p * q) * m = a - b.
    We have p * (q * m) = a - b = q * (p * m).
qed.

Signature Prime.    a is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom PrimeDivisor. n has a prime divisor iff n != 1 /\ n != -1.

Signature.
a finite group is a group.

Signature.
a pSubgroup of G is a subgroup of G.

Signature.
Let M be a set.
card(M) is an integer.

Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
conj(g, U, G) = {(Mul(G)[(g, Mul(G)[(u, Inv(G)[g])])])| u is an element of U}.

Definition.
Let U be a subgroup of G.
A groupaction from G res U  on M is a function f
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
Let g be an element of El(G).
Let H be a subgroup of G.
LCos(g, H, G) = {Mul(G)[(g, h)] | h << H}.

Definition.
Let H be a subgroup of G.
LCosets(H, G) = {LCos(g, H, G) | g << El(G)}.

Definition.
Let U be a subgroup of G.
Index(G, U) = card(LCosets(U, G)).

Axiom.
Let G be a finite group.
Let U be a subgroup of G.
Let M be a set.
Let f be a groupaction from G res U on M.
card(fixedPoints(M, G, U, f)) = card(M) (mod p).

Definition.
Let p be a prime.
Syl(p, G) = {P | P is a subgroup of G and not (p divides Index(G, P))}.

Definition.
Let p be a prime.
Let P be an element of Syl(p, G).
Let U be a subgroup of G.
Op(p, U, P, G) is a groupaction f from G res U  on LCosets(P, G) such that
for all elements u of U for all elements x of El(G) 
f[(u, LCos(x, P, G))] = LCos(Mul(G)[(u, x)],P, G).

Axiom.
Let M be a set.
If card(M) != 0 then there is an element x of M such that x = x.

Definition.
Let H be a subgroup of G.
Normalizer(H, G) = {g | (g is an element of El(G)) and conj(g, H, G) is a subset of H}.

Axiom.
Let H be a subgroup of G.
Normalizer(H, G) is a subgroup of G.

Signature.
Let H be a subgroup of G.
Gr(H, G) is a group.

Axiom.
Let H be a subgroup of G.
H is a subgroup of Gr(Normalizer(H, G), G).

Lemma.
Let h be a prime.
Let G be a finite group.
Let U be a pSubgroup of G.
Index(Gr(Normalizer(U, G), G), U) = Index(G, U) (mod h).