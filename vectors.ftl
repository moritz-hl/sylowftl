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
Let M,N denote sets.
Let x << M stand for x is an element of M.

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

Definition.
A vector on G of length n is a function f such that
f is from MN(n) to El(G).

###TODO
Definition.
Let v be a vector on G of length n.
VMul(v, G, n) = One(G).

Definition.
Vecs(G, n)  = {v | v is a vector on G of length n}.


Lemma.
Inv(G)[One(G)] = One(G).

Lemma.
(One(G), One(G)) is an element of Prod(El(G), El(G)).

Lemma.
Mul(G) is a function from Prod(El(G), El(G)) to El(G).

Lemma.
Dom(Mul(G)) = Prod(El(G), El(G)).

Lemma.
Let x be an element of Prod(El(G), El(G)).
Mul(G)[(One(G), One(G))] is an element of El(G).





