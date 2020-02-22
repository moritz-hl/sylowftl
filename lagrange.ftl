##Lagrange
###Finite Sets
Let M, N denote sets.
Let x << M stand for x is an element of M.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
Let M be a set such that for all elements N of M N is a set.
Union(M) = {x | There is an element N of M such that x is an element of N}.

Definition.
Let N1, N2 be a sets.
N1 and N2 are disjunct iff there is no element x of N1 such that x is an element of N2.

Definition.
A disjunct collection is a set M such that 
(for all elements N of M N is a set) and for all elements N1, N2 of M (N1 = N2 or ( N1 and N2 are disjunct)).


Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

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


Definition.
Let f be a function. Range(f) = {f[x] | x << Dom(f)}.


[synonym group/-s]


[synonym set/-s]

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

[synonym subgroup/-s]
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
(g, H, G) = {g *^{G} h | h << H}.

Definition.
Let H be a subgroup of G.
s(H, G) = {(g, H, G) | g << El(G)}.

Axiom.
Let U be a subgroup of G.
El(G) = Union(s(U, G)).

Axiom.
Let G be a group.
Let U be a subgroup of G.
s(U, G) is a disjunct collection.

Axiom.
Let G be a group.
Let U be a subgroup of G.
U is an element of s(U, G).

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
If  q | a and q | b then q | (a + b).

Definition EquMod.  a = b (mod q) iff q | a-b.

Definition NeqMod.  a != b (mod q) iff not (a = b (mod q)).

Lemma EquModRef.    a = a (mod q).

[ontored on]
Axiom EquModSym.    a = b (mod q) => b = a (mod q).

Axiom EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).

Axiom EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
[/ontored]

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

Axiom.
Let M be a finite set such that for all elements N of M N is a finite set.
Union(M) is a finite set.

Signature.
Let M be a finite set.
card(M) is a natural number.

Definition.
a finite group is a group G such that El(G) is a finite set.



Axiom cardUnion.
Let M be a finite set such that for all elements N of M N is a finite set.
Let N be an element of M.
If M is disjunct collection and for all elements N1, N2 of M card(N1) = card(N2)
then card(Union(M)) = card(N)*card(M).


Axiom.
Let N1, N2 be finite sets.
card(N1) = card(N2) iff there is a function f such that (f is from N1 to N2 and f is injective and f is surjective onto N2).

Axiom.
Let U be a subgroup of G.
El(G) = Union(s(U, G)).

###
Axiom.
Let G be a finite group.
Let U be a subgroup of G.
s(U, G) is a finite set such that for all elements N of s(U, G)  N is a finite set.
###

Definition.
Let G be a finite group.
Let U be a subgroup of G.
Index(G, U) = card(s(U, G)).

Lemma.
Let G be a finite group.
Let U, V be subgroups of G such that V and U are conjugates in G.
Then card(U) = card(V).
Proof.
Take an element g of El(G) such that V = Conjugate(g, U, G).
Define f[u] = g *^{G} (u *^{G} Inv(G)[g] ) for u in U.
Let us show that f is from U to V.
  Dom(f) = U.
  Let us show that for all elements u of U f[u] is an element of V.
    Let u be an element of U.
    f[u] is an element of V.
  end.
end.

Let us show that f is injective.
  Let us show that for all elements u1, u2 of U if f[u1] = f[u2] then u1 = u2.
     Let u1, u2 be elements of U such that f[u1] = f[u2].
     We have u1 = (Inv(G)[g] *^{G}  (g *^{G} (u1 *^{G} Inv(G)[g]))) *^{G} g.
     We have u2 = (Inv(G)[g] *^{G}  (g *^{G} (u2 *^{G} Inv(G)[g]))) *^{G} g.
     Therefore u1 = (Inv(G)[g] *^{G}  f[u1]) *^{G} g = (Inv(G)[g] *^{G}  f[u2]) *^{G} g = u2.
  end.
end.

Let us show that f is surjective onto V.
  Let us show that for every element v of V there is an element u of U such that f[u] = v.
    Let v be an element of V.
    We can take an element u of U such that v = (g *^{G} u) *^{G} Inv(G)[g].
    Hence v = f[u].
  end.
end.
qed.



Theorem Lagrange.
Let G be a finite group.
Let U be a subgroup of G.
card(El(G)) = card(U)*card(s(U, G)).
Proof.
Let us show that for all elements g of El(G) card((g, U, G)) = card(U).
  Let g be an element of El(G).
  Define f[u] = g *^{G} u for u in U.
  f is from U to (g, U, G).
  f is injective.
  Proof.
    Let us show that for all  elements u1, u2 of U If f[u1] = f[u2] then u1 = u2.
      Let u1, u2 be elements of U such that f[u1] = f[u2].
      We have u1 = Inv(G)[g] *^{G} (g *^{G} u1) = Inv(G)[g] *^{G} (g *^{G} u2) = u2.
      Thus u1 = u2.
    end.

    Therefore the thesis.
  end.

  f is surjective onto (g, U, G).
  Proof.
    Let us show that for every element y of (g, U, G) there is an element u of U such that f[u] = y.
      Let y be an element of (g, U, G).
      Take an element u of U such that y = g*^{G} u.
      Then f[u] = y.
    end.

    Therefore the thesis.
  end.
end.

(1) s(U, G) is a disjunct collection and for all elements N1, N2 of s(U, G) card(N1) = card(N2).
(2) s(U, G) is a finite set such that for all element N1 of s(U, G) N1 is a finite set.
(3) U is an element of s(U, G).

Therefore card(Union(s(U, G))) = card(U)*card(s(U, G)) (by cardUnion, 1, 2, 3).
Qed.