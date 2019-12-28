Let M,N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

###Functions

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
###ToDo Definition-Check for Groups.
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

Axiom assoc.
Let x, y, z be elements of El(G).
Mul(G)[(x, Mul(G)[(y, z)])]
= Mul(G)[(Mul(G)[(x, y)], z)].

Axiom InvOne.
Let x be an element of El(G). Then Mul(G)[(x, Inv(G)[x])] = One(G) =  Mul(G)[( Inv(G)[x], x)].

Axiom MulOne.
Let x be an element of El(G). Then Mul(G)[(x,One(G))] = x =  Mul(G)[(One(G), x)].

Lemma.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = x.
then y = One(G).

Lemma InvUni.
Let x, y be elements of El(G).
Assume Mul(G)[(x, y)] = One(G).
Then y = Inv(G)[x].

Lemma.
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

Signature.
A number is a notion.

Let n denote a number.

Signature.
MN(n) is a set.

Definition.
A vector on G of length n is a function f such that
f is from MN(n) to El(G).

###TODO
Definition.
Let v be a vector on G of length n.
VMul(v, G, n) = One(G).

Definition.
Vecs(G, n)  = {v | v is a vector on G of length n}.

###TODO
###rotation
Definition.
Let v be a vector on G of length n.
Let i be a number.
Rot(v, G, n, i)  is a function.