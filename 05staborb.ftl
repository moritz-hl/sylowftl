###Stabilizer and Orbit
[synonym set/-s]
Let M, N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

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
Let N1, N2 be sets.
N1 \-/ N2 = {x | x is an element of N1 or x is an element of N2}.

Definition.
Let N1 be a set.
Let N2 be a subset of N1.
N1 \\ N2 = {x | x is an element of N1 and (x is not an element of N2)}.



Definition.
Let f be a function. Let M,N be sets. f is from M to N iff Dom(f) = M and for every element x of M f[x] is an element of N.

Definition.
Let f be a function. f is injective iff for all elements x,y of Dom(f) we have (x!=y => f[x] != f[y]).

Definition.
Let f be a function. f is surjective onto M iff (f is from Dom(f) to M and for every y << M there is an element x of Dom(f) such that f[x]=y).

Definition.
Let f be a function. f is bijection from M to N iff (f is injective and f is from M to N) and (f is surjective onto M).

Definition.
Let f be a function. Range(f) = {f[x] | x << Dom(f)}.

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

[synonym group/-s]

##Definition von Gruppen

Signature.
A group is a notion.

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
Coset(g, H, G) = {g *^{G} h | h << H}.



Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << Coset(g1, H, G) and y << Coset(g2, H, G)).
Then Inv(G)[g2] *^{G} g1 << H.

Let Mul(G)[(a, b)] stand for a *^{G} b.

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Inv(G)[g2] *^{G} g1 << H.
Then Coset(g1, H, G) = Coset(g2, H, G).



Axiom CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << Coset(g1, H, G) and y << Coset(g2, H, G)).
Then Coset(g1, H, G) = Coset(g2, H, G).

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(G)[g2]*^{G}  g1 << H Iff Coset(g1, H, G) = Coset(g2, H, G).

Axiom.
Let H be a subgroup of G.
Let g be an element of El(G).
Let h be an element of El(G).
Assume g is an element of Coset(h, H, G).
Then Coset(g, H, G) = Coset(h, H, G).



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



[synonym number/-s]

Signature.
Let y be a integer.
y is nonnegative is an atom.

Signature.
A natural number is a nonnegative integer.

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
Let M be a finite set such that for all elements N of M N is a finite set.
Let N be an element of M.
If M is disjunct collection and for all elements N1, N2 of M card(N1) = card(N2)
then card(Union(M)) = card(N)*card(M).

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

Axiom.
Let U be a subgroup of G.
El(G) = Union(Cosets(U, G)).

Axiom.
Let G be a group.
Let U be a subgroup of G.
Cosets(U, G) is disjunct collection.

Axiom Lagrange.
Let G be a finite group.
Let U be a subgroup of G.
card(Union(Cosets(U, G))) = card(U)*card(Cosets(U, G)).


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


Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) = {y | y << El(G) and f[(y, x)] = x}.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) is a subgroup of G.
Proof.

One(G) is an element of Stab(x, f, G, M).

Let us show that for all elements y, z of Stab(x, f, G, M)  z *^{G} Inv(G)[y] << Stab(x, f, G, M).
  Let y, z be elements of Stab(x, f, G, M).
  We have f[(z *^{G} Inv(G)[y], x)] = x.
  Therefore z *^{G} Inv(G)[y] is an element of Stab(x, f, G, M).
end.

Therefore the thesis.
Qed.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Let g, h be elements of El(G).
If Coset(g, Stab(x, f, G, M), G) = Coset(h, Stab(x, f, G, M), G) then f[(g, x)] = f[(h, x)].

##"Welldefined" by the previous Lemma.
Axiom.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
There is a function h such that
h is from Cosets(Stab(x, f, G, M), G) to Orbit(x, f, G, M)
and (for all elements i of El(G) h[Coset(i,Stab(x, f, G, M),G)] = f[(i, x)]).

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
Let M be a set.
Let G be a finite group.
Let f be a groupaction from G on M.
Let x << M.
Index(G, Stab(x, f, G, M)) = card(Orbit(x, f, G, M)).
Proof.

Take a function h such that
h is from Cosets(Stab(x, f, G, M), G) to Orbit(x, f, G, M)
and (for all elements i of El(G) h[Coset(i,Stab(x, f, G, M),G)] = f[(i, x)]).

h is surjective onto Orbit(x, f, G, M).
Proof.
  Let us show that for every element y of Orbit(x, f, G, M) there is an element z of Dom(f) such that f[z] = y.
    Let y be an element of Orbit(x, f, G, M).
    Take an element i of El(G) such that f[(i, x)] = y.
    Then we have h[Coset(i,Stab(x, f, G, M),G)] = y.
  end.
end.

h is injective.
Proof.
  Let us show that for all elements h1, h2 of Cosets(Stab(x, f, G, M), G) if h[h1] = h[h2] then h1 = h2.
    Let h1, h2 be elements of Cosets(Stab(x, f, G, M), G) such that h[h1] =h[h2].
    
    Take elements g1, g2 of El(G) such that h1 = Coset(g1,Stab(x, f, G, M),G) and h2 = Coset(g2, Stab(x, f, G, M),G).
  
    Then f[(g1, x)] = f[(g2, x)].
    f[((Inv(G)[g2] *^{G} g1), x)] = f[((Inv(G)[g2]*^{G} g2), x)] = x.
    
    Thus Inv(G)[g2] *^{G} g1 is an element of Stab(x, f, G, M).
    Therefore h1 = h2.
  end.
end.
qed.
