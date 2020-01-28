
Lemma OneUni.
Let G be a group.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = x.
then y = One(G).

Lemma InvUni.
Let G be a group.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = One(G).
Then y = Inv(G)[x].

Lemma InvOne.
Let G be a group.
Inv(G)[One(G)] = One(G).

Lemma MulInv.
Let G be a group.
Let x, y be elements of El(G).
Then Inv(G)[Mul(G)[(x, y)]] = Mul(G)[(Inv(G)[y],Inv(G)[x])].
Proof.
Mul(G)[(Mul(G)[(x, y)], Mul(G)[(Inv(G)[y],Inv(G)[x])])] = One(G).
Qed.

Lemma.
Let G be a group.
Let x be an element of El(G).
Then Inv(G)[Inv(G)[x]] = x.