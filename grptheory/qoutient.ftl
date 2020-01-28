Let G denote a group.

Let G1, G2, G3 denote groups.


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


###Funktion aus Faktorgruppe in Irgendwas angeben?
###Über Homomorphiesatz?