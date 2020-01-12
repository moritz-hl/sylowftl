Let M,N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

###Funktionen

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
##Definition von Gruppen

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

Signature.
Inv(G) is an function from El(G) to El(G).

Axiom Assoc.
Let x, y, z be elements of El(G). Mul(G)[(x, Mul(G)[(y, z)])] = Mul(G)[(Mul(G)[(x, y)], z)].

Axiom InvOne.
Let x be an element of El(G). Then Mul(G)[(x, Inv(G)[x])] = One(G) =  Mul(G)[( Inv(G)[x], x)].

Axiom MulOne.
Let x be an element of El(G). Then Mul(G)[(x,One(G))] = x =  Mul(G)[(One(G), x)].

##Einfache Eigenschaften

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

##Definition für Untergruppen

Definition.
A subgroup of G is set H such that
(H is a subset of El(G))
and (One(G) << H)
and (for every x << H Inv(G)[x] << H)
and (for all elements x, y of H Mul(G)[(x, y)] << H).


##Untergruppenkriterium

Lemma.
Let H be a subset of El(G).
Assume ((There is a x << H such that x = x) and (for all elements  y, z of H  Mul(G)[(z, Inv(G)[y])] << H)).
Then H is a subgroup of G.
Proof.
  One(G) << H.
    Proof.
      Take x << H.
      Then One(G) = Mul(G)[(x, Inv(G)[x])].
      Thus One(G) << H.
    end.

  For every x << H Inv(G)[x] << H.
    Proof.
      Let x be an element of H.
      Then Inv(G)[x] = Mul(G)[(One(G), Inv(G)[x])].
      Thus Inv(G)[x] << H.
    end.

  For all elements x, y of H Mul(G)[(x, y)] << H.
  Proof.
    Let x, y be elements of H.
    Then Inv(G)[x] << H.
    Mul(G)[(x, y)] = Mul(G)[(x, Inv(G)[Inv(G)[y]])].
    Hence Mul(G)[(x, y)] << H.
    end.
Qed.

##Definition von Linksnebenklassen

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
LCos(g, H, G) = {Mul(G)[(g, h)] | h << H}.

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LCos(g1, H, G) and y << LCos(g2, H, G)).
Then Mul(G)[(Inv(G)[g2], g1)] << H.
Proof.
  Take y << El(G) such that (y << LCos(g1, H, G) and y << LCos(g2, H, G)).
  Take b << H such that y = Mul(G)[(g1, b)].
  Take c << H such that y = Mul(G)[(g2, c)].

  g1 = Mul(G)[(y, Inv(G)[b])].
  g2 = Mul(G)[(y, Inv(G)[c])].
  Inv(G)[g2] = Mul(G)[(c, Inv(G)[y])].

  Mul(G)[(Inv(G)[g2], g1)] = Mul(G)[(Mul(G)[(c, Inv(G)[y])], g1)].

  Mul(G)[(Inv(G)[y], g1)] = Mul(G)[(Inv(G)[y], Mul(G)[(y, Inv(G)[b])])]
  = Mul(G)[(Mul(G)[(Inv(G)[y],y)], Inv(G)[b])].

  Hence Mul(G)[(Inv(G)[g2], g1)] = Mul(G)[(c, Inv(G)[b])].
qed.

Axiom.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Mul(G)[(Inv(G)[g2], g1)] << H.
Then LCos(g1, H, G) = LCos(g2, H, G).
###Beweis sehr rechnerintensi

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Mul(G)[(Inv(G)[g2], g1)] << H Iff LCos(g1, H, G) = LCos(g2, H, G).

###TODO: G ist die disjunkte Vereinigung der Nebenklassen und alle Nebenklassen haben die gleiche Kardinalität

Lemma.
Let H be a subgroup of G.
Let g be an element of El(G).
Let h be an element of El(G).
Assume g is an element of LCos(h, H, G).
Then LCos(g, H, G) = LCos(h, H, G).

###TODO: Satz von Lagrange

##Definition von Normalteilern

Definition.
A normal subgroup of G is a subgroup H of G such that
for every g << El(G) for every h << H
Mul(G)[(g, Mul(G)[(h, Inv(G)[g])])] << H.

##Homomorphismen

Let G1, G2, G3 denote groups.

##Definition von Gruppenhomomorphismen

Definition.
A grphom from G1 to G2 is a function f such that f is from El(G1) to El(G2)
and forall x,y << El(G1)  Mul(G2)[(f[x], f[y])] = f[Mul(G1)[(x, y)]].

##Einfache Eigenschaften

Lemma.
Let f be a grphom from G1 to G2.
f[One(G1)] = One(G2).

Lemma.
Let f be a grphom from G1 to G2.
Let x << El(G1).
Inv(G2)[f[x]] = f[Inv(G1)[x]].
Proof.
  Mul(G2)[(f[x],f[Inv(G1)[x]])]=One(G2).
  f[Inv(G1)[x]] = Inv(G2)[f[x]] (by InvUni).
Qed.

##Komposition

Lemma.
Let f be a grphom from G2 to G3.
Let g be a grphom from G1 to G2.
Then comp(f, g) is grphom from G1 to G3.
Proof.
  comp(f, g) is from El(G1) to El(G3).
  Let  x, y << El(G1). 
  comp(f, g)[Mul(G1)[(x, y)]] = f[g[Mul(G1)[(x, y)]]].
  g[Mul(G1)[(x, y)]] = Mul(G2)[(g[x], g[y])].
  g[x], g[y] << El(G2).
  f[Mul(G2)[(g[x], g[y])]] = Mul(G3)[(f[g[x]], f[g[y]])].
  Mul(G3)[(f[g[x]], f[g[y]])] = Mul(G3)[(comp(f, g)[x], comp(f, g)[y])].
  comp(f, g)[Mul(G1)[(x, y)]] = Mul(G3)[(comp(f, g)[x], comp(f, g)[y])].
Qed.

##Definition des Kerns

Definition.
Let f be a grphom from G1 to G2.
Ker(f, G1, G2) = {z | z << El(G1) and f[z]=One(G2)}.

##Einfache Eigenschaften

Lemma.
Let f be a grphom from G1 to G2.
One(G1) << Ker(f, G1, G2).



Lemma.
Let f be a grphom from G1 to G2.
Ker(f, G1, G2) is a subgroup of G1.
Proof.
  One(G1) << Ker(f, G1, G2).
  Let x, y be elements of Ker(f, G1, G2).
  Then f[Mul(G1)[(x, y)]] = Mul(G2)[(f[x], f[y])] = One(G2).
  f[Inv(G1)[x]] = Inv(G2)[f[x]] = Inv(G2)[One(G2)] = One(G2).
Qed.

Lemma.
Let f be a grphom from G1 to G2.
Ker(f, G1, G2) is a normal subgroup of G1.
Proof.
  Let g be an element of El(G1).
  Let h be an element of Ker(f, G1, G2).
  f[h] = One(G2).
  f[Mul(G1)[(g, Mul(G1)[(h, Inv(G1)[g])])]] = Mul(G2)[(f[g], Mul(G2)[(f[h], f[Inv(G1)[g]])])] = One(G2).
  Hence Mul(G1)[(g, Mul(G1)[(h, Inv(G1)[g])])] << Ker(f, G1, G2).
Qed.

##Injektivitätskriterium

Lemma.
Let f be a grphom from G1 to G2.
Assume f is injective.
Then Ker(f, G1, G2) = {One(G1)}.

Lemma.
Let f be a grphom from G1 to G2.
Assume Ker(f, G1, G2) = {One(G1)}.
Then f is injective.
Proof.
  Let x, y << El(G1).
  Assume f[x]=f[y].
  Then One(G2) = f[Mul(G1)[(x, Inv(G1)[y])]].
  Mul(G1)[(x, Inv(G1)[y])] << Ker(f, G1, G2).
  Mul(G1)[(x, Inv(G1)[y])] = One(G1).
  Hence x = Inv(G1)[Inv(G1)[y]] = y.
qed.

Lemma.
Let f be a grphom from G1 to G2.
f is injective iff Ker(f, G1, G2) = {One(G1)}.

##Faktorgruppe

Definition.
Let H be a subgroup of G.
LCosets(H, G) = {LCos(g, H, G) | g << El(G)}.


Lemma.
Let H be a normal subgroup of G.
Let x << El(G).
Then LCos(x, H, G) << LCosets(H, G).

##Definition der Faktorgruppe

Definition.
Let H be a normal subgroup of G.
FactGrp(H, G) is a group F such that
(El(F) = LCosets(H, G)
and forall x, y << El(G) 
(Mul(F)[(LCos(x, H, G), LCos(y, H, G))] = LCos(Mul(G)[(x, y)], H, G)
and Inv(F)[LCos(x, H, G)] = LCos(Inv(G)[x], H, G))).

##Projektion

Definition.
Let H be a normal subgroup of G.
p(H, G) is a function f such that
(Dom(f) = El(G) and
forall x << El(G) f[x] = LCos(x, H, G)).

##Eigenschaften der Projektion

Lemma.
Let H be a normal subgroup of G.
p(H, G) is from El(G) to El(FactGrp(H, G)).

Lemma.
Let H be a normal subgroup of G.
p(H, G) is surjective onto El(FactGrp(H, G)).

Lemma.
Let H be a normal subgroup of G.
p(H, G) is grphom from G to FactGrp(H, G).

##Normale Untergruppen sind Kerne

Lemma.
Let H be a normal subgroup of G.
Ker(p(H, G), G, FactGrp(H, G)) = H.

Lemma.
Let H be a normal subgroup of G.
Then there is a Group G2 such that there is a function f such that
(f is a grphom from G to G2 and Ker(f, G, G2) = H).

Lemma.
Let f be a grphom from G1 to G2.
Let H be a normal subgroup of G1.
Assume Ker(f, G1, G2) is a subset of H.
Let g be a grphom g from FactGrp(H, G1) to G2.
Then comp(g, p(H, G1)) is from El(G1) to El(G2).

##Universelle Eigenschaft
Axiom.
Let f be a grphom from G1 to G2.
Let H be a normal subgroup of G1.
Assume Ker(f, G1, G2) is a subset of H.
Then there is a grphom g from FactGrp(H, G1) to G2 such that
comp(g, p(H, G1))=f.
##Problem: Definition von Funktion aus der Faktorgruppe?



##Natürliche Zahlen

[synonym number/-s]

Signature.
a number is a notion.

Signature.
Nat is the set of numbers.

Signature.
0 is a number.

Let n, m denote numbers.

Signature.
Succ(n) is a number.

Definition.
1 = Succ(0).

Definition.
2 = Succ(1).

Definition.
3 = Succ(2).

Definition.
4 = Succ(3).

Definition.
5 = Succ(4).


Axiom.
Succ(n) != 0.

Axiom.
If Succ(n) = Succ(m) then n = m.

Axiom.
let M be a set.
If (0 is an element of M and for each element x of Nat (If x is an element of M then Succ(x) is an element of M))
Then Nat is a subset of M.


Lemma.
Nat = {x| x = 0 or there is a number k such that x = Succ(k)}.
Proof.
Define M2 = {x|x = 0 or there is a number k such that x = Succ(k)}.
Qed.

Signature.
n+m is a number.

Axiom.
n+0=n.

Axiom.
n+Succ(m)=Succ(n+m).

Signature.
n*m is a number.

Axiom.
n*0 = 0.

Axiom.
n*Succ(m) = (n*m)+n.


Signature.
n < m is an atom.

Axiom.
n < m iff (m = Succ(n) or Succ(n) < m).


Definition.
MN(n) = {x|x is a number and  x<n}.


Axiom.
Let x, y, z be numbers.
If x < y and y < z then x < z.

Axiom.
If n < m then not m < n.

Axiom.
If Succ(n) < Succ(m) then n < m.


Lemma.
Nat = {x| x is a number and (x = 0 or 0 < x)}.
Proof.
  Define HN = {x| x is a number and (x = 0 or 0 < x)}.
  0 is an element of HN.

  let x be an element of HN.
  If x = 0 then (0 < Succ(x) and Succ(x) is an element of HN).
  If x != 0 then (0 < x and 0 < Succ(x) and Succ(x) is an element of HN).
Qed.

Lemma.
MN(0) = {x|x!=x}.

Lemma.
MN(5) = {0, 1, 2, 3, 4}.

Lemma.
MN(Succ(n)) = {x | x is an element of MN(n) or x = n}.


Lemma.
Let x be an element of Prod(El(G), El(G)).
Mul(G)[(One(G), One(G))] is an element of El(G).

###Zyklische Gruppen (vllt Ganze Zahlen).


