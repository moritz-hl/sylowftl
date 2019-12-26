
Let M,N denote sets.
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


Definition.
Let f, g be functions.
Assume g is from Dom(g) to Dom(f).
comp(f, g) is a function h such that Dom(h) = Dom(g)
and for every x << Dom(g) comp(f, g)[x] = f[g[x]].

[synonym group/-s]
###ToDo Definition-Checker for Groups.
Signature.
A group is a notion.


Let G denote a group.

Signature.
El(G) is a  set.

Definition.
A associative function on G is a function f
such that f is from  Prod(El(G), El(G)) to El(G).

Signature.
One(G) is a set.

Axiom.
One(G) << El(G).

Signature.
Mul(G) is a associative function on G.

Signature.
Inv(G) is an function from El(G) to El(G).

Axiom InvOne.
Let x be an element of El(G). Then Mul(G)[(x, Inv(G)[x])] = One(G) =  Mul(G)[( Inv(G)[x], x)].

Axiom MulOne.
Let x be an element of El(G). Then Mul(G)[(x,One(G))] = x =  Mul(G)[(One(G), x)].

Axiom MulInv.
Let x, y be elements of El(G).
Then Inv(G)[Mul(G)[(x, y)]] = Mul(G)[(Inv(G)[y],Inv(G)[x])].

Axiom.
Let x be an element of El(G).
Then Inv(G)[Inv(G)[x]] = x.

Axiom.
Inv(G)[One(G)] = One(G).

Definition.
A subgroup of G is set H such that
(H is a subset of El(G))
and (One(G) << H)
and (for every x << H Inv(G)[x] << H)
and (for all elements x, y of H Mul(G)[(x, y)] << H).

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

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
LCos(g, H, G) = {Mul(G)[(g, h)] | h << H}.

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
RCos(g, H, G) = {Mul(G)[(h, g)] | h << H}.

Definition.
A normal subgroup of G is a subgroup H of G such that
for every g << El(G) for every h << H
Mul(G)[(g, Mul(G)[(h, Inv(G)[g])])] << H.


Definition.
An abelian group is a group G such that
for all elements x, y of El(G) Mul(G)[(x, y)] = Mul(G)[(y, x)].

Axiom.
Let x, y, z be elements of El(G).
Mul(G)[(x, Mul(G)[(y, z)])]
= Mul(G)[(Mul(G)[(x, y)], z)].


Lemma.
Let G be an abelian Group.
Let H be a subgroup of G.
Then H is a normal subgroup of G.
Proof.
Let g be an element of El(G).
Let h be an element of H.
Mul(G)[(g, Mul(G)[(h, Inv(G)[g])])] = h.
Proof.
Mul(G)[(g, Mul(G)[(h, Inv(G)[g])])]
=Mul(G)[(g, Mul(G)[(Inv(G)[g], h)])]
=Mul(G)[(Mul(G)[(g, Inv(G)[g])], h)] = 
Mul(G)[(One(G), h)] = h.
end.
Qed.


Lemma.
Let H be a subgroup of G.
Let a, g be elements of El(G).
Assume g << LCos(a, H, G).
Then Inv(G)[g] << RCos(Inv(G)[a], H, G).
Proof.
Take h << H such that g = Mul(G)[(a, h)].
Then Inv(G)[g] = Inv(G)[Mul(G)[(a, h)]].
Inv(G)[g] .= Inv(G)[Mul(G)[(a, h)]] .= Mul(G)[(Inv(G)[h], Inv(G)[a])].
h is an element of H.
Therefore Inv(G)[h] << H.
Inv(G)[g] << RCos(Inv(G)[a], H, G).
Qed.

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

Mul(G)[(Inv(G)[g2], g1)] = Mul(G)[(c, Inv(G)[b])]. 
qed.

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Mul(G)[(Inv(G)[g2], g1)] << H.
Then LCos(g1, H, G) = LCos(g2, H, G).
Proof.
LCos(g1, H, G) is a subset of LCos(g2, H, G).
Proof.
Let y be an element of LCos(g1, H, G).
Take a << H such that y = Mul(G)[(g1, a)].
Mul(G)[(Mul(G)[(Inv(G)[g2], g1)], a)] << H.
Then y = Mul(G)[(g1, a)]=Mul(G)[(g2, Mul(G)[(Mul(G)[(Inv(G)[g2], g1)], a)])].
end.

LCos(g2, H, G) is a subset of LCos(g1, H, G).
Proof.
Let y be an element of LCos(g2, H, G).
Take a << H such that y = Mul(G)[(g2, a)].
Mul(G)[(Mul(G)[(Inv(G)[g1], g2)], a)] << H.
Then y = Mul(G)[(g2, a)]=Mul(G)[(g1, Mul(G)[(Mul(G)[(Inv(G)[g1], g2)], a)])].
end.
Qed.

Lemma.
El(G) is a subgroup of G.

Lemma.
El(G) is a normal subgroup of G.

Definition.
OneGr(G)= {One(G)}.

Lemma.
OneGr(G) is a subgroup of G.

Lemma.
OneGr(G) is a normal subgroup of G.

Definition.
Let H be a subgroup of G.
Let g << El(G).
FLCos(g, G, H) is function f such that
Dom(f) = H and
for every x << H f[x] = Mul(G)[(g, x)].

Lemma.
Let H be a subgroup of G.
Let g << El(G).
Then FLCos(g, G, H) is injective.
Proof.
Let x, y << H.
Assume  FLCos(g, G, H)[x]= FLCos(g, G, H)[y].
FLCos(g, G, H)[x] = Mul(G)[(g, x)].
FLCos(g, G, H)[y] = Mul(G)[(g, y)].
Then x = Mul(G)[(Inv(G)[g], Mul(G)[(g, x)])].
y = Mul(G)[(Inv(G)[g], Mul(G)[(g, y)])].
Hence x = y.
Qed.

Lemma.
Let H be a subgroup of G.
Let g << El(G).
Then FLCos(g, G, H) is from H to LCos(g, H, G).
Proof.
Dom(FLCos(g, G, H)) = H.

Let x << H.
Then FLCos(g, G, H)[x] = Mul(G)[(g, x)].
Hence FLCos(g, G, H)[x] <<  LCos(g, H, G).
Qed.

Definition.
Let H be a subgroup of G.
LCosets(H, G) = {LCos(g, H, G) | g << El(G)}.

###Homomorphismen

Let G1, G2 denote groups.

Definition.
A grphom from G1 to G2 is a function f such that f is from El(G1) to El(G2)
and forall x,y << El(G1)  Mul(G2)[(f[x], f[y])] = f[Mul(G1)[(x, y)]].


Axiom InvUni.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = One(G).
Then y = Inv(G)[x].

Axiom OneUni.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = x.
Then y = One(G).


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

Definition.
Let f be a grphom from G1 to G2.
Ker(f, G1, G2) = {z | z << El(G1) and f[z]=One(G2)}.

Lemma.
Let f be a grphom from G1 to G2.
One(G1) << Ker(f, G1, G2).

Lemma.
Let f be a grphom from G1 to G2.
Assume f is injective.
Then Ker(f, G1, G2) = {One(G1)}.

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


Let G3 denote a group.

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

Definition.
Symm(M) is a group G such that
El(G) = {f|f is a function and f is bijection from M to M}
And for every f, g << El(G) Mul(G)[(f, g)] = comp(f, g).


Definition.
Let g be an element of El(G).
gact(g, G) is a function f such that
Dom(f) = El(G)
and forall x << El(G) f[x] = Mul(G)[(g, x)].

Lemma.
Let g be an element of El(G).
Then gact(g, G) is injective.

Lemma.
Let g be an element of El(G).
Then gact(g, G) is from El(G) to El(G).

Lemma.
Let g be an element of El(G).
Then gact(g, G) is surjective onto El(G).

Lemma.
Let g be an element of El(G).
Then gact(g, G) is bijection from El(G) to El(G).

Lemma.
Let g be an element of El(G).
Then gact(g, G) is an element of El(Symm(El(G))).
###Quotienten.

Definition.
Let H be a normal subgroup of G.
FactGrp(H, G) is a group F such that
(El(F) = LCosets(H, G)
and forall x, y << El(G) 
(Mul(F)[(LCos(x, H, G), LCos(y, H, G))] = LCos(Mul(G)[(x, y)], H, G)
and Inv(F)[LCos(x, H, G)] = LCos(Inv(G)[x], H, G))).

Definition.
Let H be a normal subgroup of G.
p(H, G) is a function f such that
(Dom(f) = El(G) and
forall x << El(G) f[x] = LCos(x, H, G)).

Lemma.
Let H be a normal subgroup of G.
p(H, G) is from El(G) to El(FactGrp(H, G)).

Lemma.
Let H be a normal subgroup of G.
p(H, G) is surjective onto El(FactGrp(H, G)).

Lemma.
Let H be a normal subgroup of G.
p(H, G) is grphom from G to FactGrp(H, G).

Lemma.
Let H be a normal subgroup of G.
Ker(p(H, G), G, FactGrp(H, G)) = H.

Lemma.
Let H be a normal subgroup of G.
Then there is a Group G2 such that there is a function f such that
(f is a grphom from G to G2 and Ker(f, G, G2) = H).


###Zyklische Gruppen.
###...