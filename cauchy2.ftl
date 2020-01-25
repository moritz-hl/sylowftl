[read praktikum/functions.ftl]
[read praktikum/groupdef.ftl]
[read praktikum/subgroups.ftl]
[synonym number/-s]

Signature.
a number is a notion.

Signature.
NN is the set of numbers.

Signature.
0 is a number.

Let n, m denote numbers.

Signature.
Succ(n) is a number.

Axiom.
Succ(n) != 0.

Axiom.
If Succ(n) = Succ(m) then n = m.

Axiom Induct.
let M be a set.
If (0 is an element of M and for each element x of NN (If x is an element of M then Succ(x) is an element of M))
Then NN is a subset of M.

Lemma.
NN = {x| x = 0 or there is a number k such that x = Succ(k)}.
Proof.
Define M2 = {x|x = 0 or there is a number k such that x = Succ(k)}.
Qed.

Signature.
n < m is an atom.

Axiom.
n < m iff (m = Succ(n) or Succ(n) < m).

Axiom.
Let x, y, z be numbers.
If x < y and y < z then x < z.

Axiom.
If n < m then not m < n.

Axiom.
If Succ(n) < Succ(m) then n < m.

Definition.
\MN(n) = {x|x is a number and  x<n}.

Lemma.
NN = {x| x is a number and (x = 0 or 0 < x)}.
Proof.
  Define HN = {x| x is a number and (x = 0 or 0 < x)}.
  0 is an element of HN.

  let x be an element of HN.
  If x = 0 then (0 < Succ(x) and Succ(x) is an element of HN).
  If x != 0 then (0 < x and 0 < Succ(x) and Succ(x) is an element of HN).
Qed.

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

Signature.
let n,m be numbers.
n|m is an atom.

Signature.
let n,m be numbers.
n-m is a number.

Axiom.
Let n, m be number.
If n < m then n != m.

Signature.
A prime number is a number.

Axiom.
Let p be a prime number.
then 1 < p.

Axiom.
Let p be a prime number.
Let n be a number.
Assume n | p.
Then n = 1 or n = p.


Signature.
Let M be a set.
card(M) is a number.

Let G denote a group.

Let x +^{G} y stand for  Mul(G)[(x, y)].

Let -^{G} x stand for Inv(G)[x].


Signature.
Let x be an element of El(G).
ord(x, G) is a number.

Axiom.
Let x be an element of El(G).
Assume x != One(G).
Then 1 < ord(x, G).

Definition.
Let n be a number such that n != 0.
Pre(n) is number such that Succ(Pre(n)) = n.

Lemma.
Pre(1) = 0.

Definition.
Let n be a number.
Assume 1 < n.
ZZ(n) is a group H such that
El(H) = \MN(n)
and One(H) = 0
and (Pre(n), 1) is an element of Prod(El(H), El(H))
and (1, Pre(n)) is an element of Prod(El(H), El(H))
and Pre(n) +^{H} 1 = 0 = 1 +^{H} Pre(n)
and for all elements x, y, z of El(H)
((If x != Pre(n) then x +^{H} 1 = Succ(x) = 1 +^{H} x)).
###and Mul(H)[(x, Mul(H)[(y, z)])] = Mul(H)[(Mul(H)[(x, y)], z)] and Mul(H)[(x, Inv(H)[x])] = One(H) =  Mul(H)[( Inv(H)[x], x)] and Mul(H)[(x,One(H))] = x =  Mul(H)[(One(H), x)] ).

Lemma.
El(ZZ(2)) = {0, 1}.

Let M denote a set.

Definition.
A groupaction from G on M is a function f
such that f is from Prod(El(G), M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of El(G)
f[(Mul(G)[(a, b)], x)] = f[(a, f[(b, x)])].

Definition.
Let f be a function from Prod(El(G), M) to M.
Let x be an element of M.
Orbit(G, M, f, x) = { f[(a, x)] | a << El(G)}.

Definition.
Let f be a function from Prod(El(G), M) to M.
A fixedpoint on M on G of f is an element y of M such that
for every element a of El(G) f[(a, y)] = y.

Definition.
Let f be a function from Prod(El(G), M) to M.
fixedPoints(M, G, f) = {y | y is a fixedpoint on M on G of f}.

Definition.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) = {y | y << El(G) and f[(y, x)] = x}.

Lemma.
Let f be a groupaction from G on M.
Let x << M.
Stab(x, f, G, M) is a subgroup of G.


Signature.
let n be a number such that 1 < n.
A vector of G of length n is a function f from El(ZZ(n)) to El(G).

Signature.
let n be a number such that 1 < n.
Let i be an element of El(ZZ(n)).
Let v be a vector of G of length n.
Rot(v, i, n, G) is a vector of G of length n.

Signature.
let n be a number such that 1 < n.
VMul(v, G, n) is an element of El(G).

Definition.
let n be a number such that 1 < n.
Om(G, n) = {v | v is a vector of G of length n and VMul(v, G, n) = One(G)}.

Definition.
let p be a prime number.
Op(p, G) is a groupaction f from ZZ(p) on Om(G, p) such that
for all elements i of El(ZZ(p)) for all elements v of Om(G, p)
f[(i, v)] = Rot(v, i, p, G).


Signature.
Let n be a number such that 1 < n.
OneV(G, n) is a vector of G of length n.

Signature.
Let n be a number.
Let x be a number.
PotZ(x, n) is a number.

Signature.
let n be a number such that 1 < n.
Let v be a vector of G of length n.
v is constant on G of length n is an atom.

Axiom.
Let p be a prime number.
card(Om(G, p)) = PotZ(card(El(G)), p-1).


Axiom.
Let x,n,m  be numbers.
If x < n and n | m then x < m.

Axiom.
Let M be a set.
Let x be an element of M.
Assume 1 < card(M).
There is an element y of M such that y != x.

Axiom.
Let n be a number such that 1 < n.
Let v be a vector of G of length n.
Assume v is constant on G of length n.
If VMul(v, G, n) = One(G) then ord(v[0], G) | n.



Axiom.
Let n be a number such that 1 < n.
Let v be vector of G of length n.
Assume v is constant on G of length n.
v[0] = One(G) iff v = OneV(G, n).

Lemma Cauchy.
Let p be a prime number.
Assume p | card(El(G)).
Then there is an element x of El(G) such that ord(x, G) = p.
Proof.
  card(Om(G, p)) = PotZ(card(El(G)), p-1).

  ##FixP(Op(G, p)) = {v | v is an element of Om(G, p) and v is constant on G of length p}.

  ##OneV(G, p) is an element of FixP(Op(G, p)).

  ##p | card(FixP(Op(G, p))).
  1 < p.

  ##Hence 1 < card(FixP(Op(G, p))).

  ##Take an element v of FixP(Op(G, p)) such that v != OneV(G, p).

  ##ord(v[0], G) | p.
 ## v[0] != One(G).
  ##1 < ord(v[0], G).
  ##ord(v[0], G) = p.
Qed.