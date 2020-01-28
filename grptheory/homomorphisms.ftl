Let G denote a group.

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