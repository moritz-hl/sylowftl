[read praktikum/grptheory/functions.ftl]
[read praktikum/grptheory/groupdef.ftl]
[read praktikum/grptheory/subgroups.ftl]

Let G denote a group.

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
###Beweis sehr rechnerintensiv

Lemma CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LCos(g1, H, G) and y << LCos(g2, H, G)).
Then LCos(g1, H, G) = LCos(g2, H, G).

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Mul(G)[(Inv(G)[g2], g1)] << H Iff LCos(g1, H, G) = LCos(g2, H, G).

Lemma.
Let H be a subgroup of G.
Let g be an element of El(G).
Let h be an element of El(G).
Assume g is an element of LCos(h, H, G).
Then LCos(g, H, G) = LCos(h, H, G).

Definition.
Let H be a subgroup of G.
LCosets(H, G) = {LCos(g, H, G) | g << El(G)}.

