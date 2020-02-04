[read praktikum/grptheory/functions.ftl]
[read praktikum/grptheory/groupdef.ftl]
[read praktikum/grptheory/subgroups.ftl]
[read praktikum/grptheory/groupaction.ftl]
[read praktikum/grptheory/cardsnumbers.ftl]
[read praktikum/grptheory/cosets.ftl]

Lemma.
Let G be a group.
Let U be a subgroup of G.
El(G) = Union(LCosets(U, G)).
Proof.
Let us show that El(G) is a subset of Union(LCosets(U, G)).
  Let g be an element of El(G).
  Then g is an element of LCos(g, U, G).
end.

Let us show that Union(LCosets(U, G)) is a subset of El(G).
  Let h be an element of Union(LCosets(U, G)).
  Take an element k of El(G) such that h is an element of LCos(k, U, G).
  h is an element of El(G).
end.

Therefore El(G) = Union(LCosets(U, G)).
Qed.

Lemma.
Let G be a group.
Let U be a subgroup of G.
LCosets(U, G) is disjunct collection.
Proof.
Let N1, N2 be elements of LCosets(U, G).
Assume that not (N1 and  N2 are disjunct).
Take an element y of N1 such that y is an element of N2.
Then N1 = N2 (by CosEq).
Qed.

Definition.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCos(g, U, G) is a function f
such that Dom(f) = U
and  for all elements u of U f[u] = Mul(G)[(g, u)].

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCos(g, U, G) is from U to LCos(g, U, G).

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCos(g, U, G) is injective.

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCos(g, U, G) is surjective onto LCos(g, U, G).




Lemma Lagrange.
Let G be a group.
Let U be a subgroup of G.
card(U) | card(El(G)) and Index(G, U) | card(El(G)).
Proof.
  card(El(G)) = card(Union(LCosets(U, G))).
  Let N1, N2 be elements of LCosets(U, G).
  Take elements g1, g2 of El(G) such that N1 = LCos(g1, U, G) and N2 = LCos(g2, U, G).
  card(N1) = card(U) = card(N2).
  U is an element of LCosets(U, G).
  LCosets(U, G) is disjunct collection.
Qed.



Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
fStabOrb(x, f, G, M) is a function h such that
h is from LCosets(Stab(x, f, G, M), G) to Orbit(x, f, G, M)
and (for all elements i of El(G) h[LCos(i,Stab(x, f, G, M),G)] = f[(i, x)]).

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
fStabOrb(x, f, G, M) is injective and surjective onto Orbit(x, f, G, M).
Proof.

fStabOrb(x, f, G, M) is from LCosets(Stab(x, f, G, M), G) to Orbit(x, f, G, M).

fStabOrb(x, f, G, M) is surjective onto Orbit(x, f, G, M).
Proof. Obvious.

Let us show that fStabOrb(x, f, G, M) is injective.
  Let h1, h2 be elements of LCosets(Stab(x, f, G, M), G).
  Take elements g1, g2 of El(G) such that
  h1 = LCos(g1,Stab(x, f, G, M),G) and h2 = LCos(g2, Stab(x, f, G, M),G).
  Assume fStabOrb(x, f, G, M)[h1] = fStabOrb(x, f, G, M)[h2].
  Then f[(g1, x)] = f[(g2, x)].
  Mul(G)[(Inv(G)[g2], g1)] is an element of El(G).
  Hence f[(Mul(G)[(Inv(G)[g2], g1)], x)] = f[(Mul(G)[(Inv(G)[g2], g2)], x)] = x.
  
  Thus Mul(G)[(Inv(G)[g2], g1)] is an element of Stab(x, f, G, M).
  
  Therefore h1 = h2.
end.
qed.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Index(G, Stab(x, f, G, M)) = card(Orbit(x, f, G, M)).