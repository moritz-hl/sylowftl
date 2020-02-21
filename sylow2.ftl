##Sylow2

Let M, N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
Let f be a function. Let M,N be sets. f is from M to N iff Dom(f) = M and for every element x of M f[x] is an element of N.

Definition.
Let f be a function. Range(f) = {f[x] | x << Dom(f)}.

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

Definition.
Let M be a set.
M is empty iff there is no element x of M such that x = x.

Lemma.
M is not empty iff there is an element x of M such that x = x.

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
One(G) is an element of  El(G).

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
LeftCoset(g, H, G) = {g *^{G} h | h << H}.

Axiom CosetEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(G)[g2]*^{G}  g1 << H iff LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Definition.
Let H be a subgroup of G.
LeftCosets(H, G) = {LeftCoset(g, H, G) | g << El(G)}.


Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
Conjugate(g, U, G) = {(g *^{G} (u *^{G} Inv(G)[g]))| u is an element of U}.

Definition.
Let U, V be subgroups of G.
U and V are conjugates in G iff there is an element g of El(G) such that U = Conjugate(g, V, G).

[synonym integer/-s]
[synonym number/-s]

Signature Integers. An integer is a notion.

Signature Naturals. A natural number is an integer.

Let a,b,c,n, m stand for integers.

Signature IntZero.  0 is a natural number.
Signature IntOne.   1 is a natural number.

Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.

Signature. Let b be a natural number.  a ^ b is an integer.

Axiom. If a and b are natural numbers then a + b is a natural number.
Axiom. If a and b are natural numbers then a * b is a natural number.

##Natural Numbers
Signature. a < b is an atom.

Axiom TriCh.
a = b \/ a < b \/ b < a.

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

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Axiom PotInj.   Let p be an integer. Let n,m be natural numbers. (p ^ n = p ^  m) => n = m.

Axiom MulZero.      a * 0 = 0 = 0 * a.
Axiom MulMinOne.    (-1) * a = -a = a * -1.

Axiom.
c != 0 /\ a * c = b * c => a = b.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Axiom.
q | a /\ q | b =>  q | (a + b).

Definition EquMod.  a = b (mod q) iff q | a-b.

Definition NeqMod.  a != b (mod q) iff not (a = b (mod q)).

Axiom EquModRef.    a = a (mod q).

[ontored on]
Axiom EquModSym.    a = b (mod q) => b = a (mod q).

Axiom EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).

Axiom EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).

Signature Prime.    a is prime is an atom.

Let a prime stand for a prime nonzero integer.

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


Definition.
Let M be a set such that for all elements N of M N is a set.
Union(M) = {x | There is an element N of M such that x is an element of N}.

Axiom.
Let M be a set such that for all elements N of M N is a finite set.
Union(M) is a finite set.

Signature.
Let M be a finite set.
card(M) is a natural number.

Axiom.
Let M be a finite set.
If card(M) != 0 then M is not empty.

Axiom.
Let M be a finite set.
Let N be a subset of M.
If card(M) = card(N) then M = N.


Definition.
a finite group is a group G such that El(G) is a finite set.

Lemma.
Let G be a finite group.
Let U be a subgroup of G.
U is a finite set.


###
Axiom.
Let G be a finite group.
Let U be a subgroup of G.
LeftCosets(U, G) is a finite set.

Definition.
Let G be a finite group.
Let U be a subgroup of G.
Index(G, U) = card(LeftCosets(U, G)).

Axiom.
Let U be a subgroup of G.
El(G) = Union(LeftCosets(U, G)).

Axiom Lagrange.
Let G be a finite group.
Let U be a subgroup of G.
card(El(G)) = card(U)*card(LeftCosets(U, G)).

###Groupactions
Definition.
Let M be a set.
Let G be a group.
A groupaction from G on M is a function f
such that f is from Prod(El(G), M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of El(G)
f[((a *^{G}  b), x)] = f[(a, f[(b, x)])].

Definition.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(U, P, G) is a function f 
such that f is from Prod(El(Gr(U, G)), LeftCosets(P, G)) to LeftCosets(P, G) and
for all elements u of U for all elements x of El(G) 
f[(u, LeftCoset(x, P, G))] = LeftCoset(u *^{G}  x,P, G).

Axiom.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(U, P, G) is a groupaction from Gr(U, G) on LeftCosets(P, G).

Definition.
Let f be a function from Prod(El(G), M) to M.
Let x be an element of M.
Orbit(x, f, G, M) = { f[(a, x)] | a << El(G)}.

Definition.
Let f be a groupaction from G on M.
A fixedpoint on M on G of f is an element y of M such that
for every element a of El(G) f[(a, y)] = y.

Definition.
Let G be a group.
Let f be a groupaction from G on M.
fixedPoints(M, G, f) = {y | y is a fixedpoint on M on G of f}.

Definition.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) = {y | y << El(G) and f[(y, x)] = x}.

Axiom.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) is a subgroup of G.

Lemma.
Let G be a finite group.
Let f be a groupaction from G on M.
Let x << M.
Orbit(x,f, G, M) is a finite set.
Proof.
  Define h[g] = f[(g, x)] for g in El(G).
  Dom(h) is a finite set.
  Orbit(x, f, G, M) is a subset of Range(h).
  Proof.
    Let us show that every element of Orbit(x, f, G, M) is an element of Range(h).
       (1) Let y be an element of Orbit(x, f, G, M).

       We can take an element g1 of El(G) such that y = f[(g1, x)] (by 1).

       Thus y is an element of Range(h).
    end.
  end.
  Therefore Orbit(x, f, G, M) is a finite set.
Qed.
             
Lemma.
Let M be a finite set.
Let G be a group.
Let f be a groupaction from G on M.
fixedPoints(M, G, f) is a finite set.
Proof.
  Let us show that (1) every element of fixedPoints(M, G, f) is an element of M.
    Let x be an element of fixedPoints(M, G, f).
    Then x is an element of M.
  end.

   fixedPoints(M, G, f) is a subset of M (by 1).

   Therefore the thesis.
Qed.

Axiom.
Let G be a finite group.
Let f be a groupaction from G on M.
Let x << M.
Index(G, Stab(x, f, G, M)) = card(Orbit(x, f, G, M)).

Signature.
A group of order p is a finite group H such that
(there is a natural number n such that card(El(H)) = p ^ n).

Signature.
A subgroup of G of order p is a subgroup U of G such that
(Gr(U, G) is a group of order p).


###Fixed Points Lemma.

[prove off]
Theorem FixPointsMod.
Let M be a finite set.
Let G be a group of order p.
Let f be a groupaction from G on M.
card(fixedPoints(M, G, f)) = card(M) (mod p).

Theorem ConjSize.
Let G be a finite group.
Let g be an element of El(G).
Let U be a subgroup of G.
card(Conjugate(g, U, G)) = card(U).
[/prove]

Definition.
Let G be a finite group.
Syl(p, G) = {P | P is a subgroup of G of order p and  not (p | Index(G, P))}.


Lemma SylSize.
Let G be a finite group.
Let P, U be elements of Syl(p, G).
card(U) = card(P).
Proof.
Take natural numbers n, m such that card(U) = p^n and card(P) = p^m.
Let us show that n = m.
Assume the contrary.
Case m < n.
n-m is a natural number.
p^n = (p^(n-m))*(p^m).

(p^n)*Index(G, U) = card(El(G)).

(Index(G, U)*(p^(n-m)))*(p^m) = card(El(G)) = Index(G, P)*(p^m).

Hence (Index(G, U)*(p^(n-m))) = Index(G, P).

p | (Index(G, U)*(p^(n-m))).

contradiction.
end.
Case n < m.


end.
end.
Qed.

Theorem Sylow2a.
Let G be a finite group.
Let P be an element of Syl(p, G).
Let U be a subgroup of G of order p.
Then there is an element g of El(G) such that Conjugate(g, U, G) is a subset of P.
Proof.
  Take a groupaction f from Gr(U, G) on LeftCosets(P, G) such that f = Op(U, P, G).
  
  Let us show that card(fixedPoints(LeftCosets(P, G), Gr(U, G),  f)) != 0.
     card(fixedPoints(LeftCosets(P, G), Gr(U, G), f)) = Index(G, P) (mod p).
     
     p does not divide Index(G, P).
     
     Therefore Index(G, P) != 0 (mod p).
  end.
  
  We can take an element x of fixedPoints(LeftCosets(P, G), Gr(U, G),  f)
  and an element g of El(G) such that x = LeftCoset(g, P, G).
  
  Let us show that every element of Conjugate(Inv(G)[g], U, G) is an element of P.
    Let h  be an element of Conjugate(Inv(G)[g], U, G).

    Take an element u of U such that h = Inv(G)[g] *^{G} (u *^{G}  g).

    We have LeftCoset(g, P, G) = f[(u,x)] =  LeftCoset((u *^{G} g) ,P, G).

    Therefore Inv(G)[g] *^{G} (u *^{G}  g) is an element of P (By CosetEq).
  end.
Qed.

Theorem Sylow2b.
Let G be a finite group.
Let P, U be elements of Syl(p, G).
P and U are conjugates in G.
Proof.
  Take an element g of El(G) such that Conjugate(g, U, G) is a subset of P.

  card(Conjugate(g, U, G)) = card(U) = card(P) (by SylSize, ConjSize).

  Hence Conjugate(g, U, G) = P.
qed.