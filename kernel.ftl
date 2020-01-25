
Let G denote a group.

Let G1, G2, G3 denote groups.

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