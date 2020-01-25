Let G denote a group.

Definition.
A subgroup of G is set H such that
(H is a subset of El(G))
and (One(G) << H)
and (for every x << H Inv(G)[x] << H)
and (for all elements x, y of H Mul(G)[(x, y)] << H).


##Untergruppenkriterium

Lemma.
Let G be a group.
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