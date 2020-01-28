Let M,N denote sets.
Let x << M stand for x is an element of M.

###There are no proofs in this file

[synonym number/-s]
Signature.
A group is a notion.

Let G denote a group.

Signature.
El(G) is a set.

Signature.
One(G) is a notion.

Signature.
A number is a notion.

Signature.
0 is a number.

Signature.
1 is a number.

Signature.
A prime number is a number.

Signature.
let n,m be numbers.
n|m is an atom.

Signature.
Let n, m be numbers.
n < m is an atom.

Signature.
Let M be a set.
card(M) is a number.

Signature.
Let x be an element of El(G).
ord(x, G) is a number.

Signature.
let n,m be numbers.
n-m is a number.


Signature.
let n be a number.
A vector of G of length n is a function f such that 0 is an element of Dom(f) and for every x << Dom(f) f[x] is an element of El(G).

Signature.
Let n be a number.
VMul(v, G, n) is an element of El(G).

Definition.
Let n be a number.
Om(G, n) = {v | v is a vector of G of length n and VMul(v, G, n) = One(G)}.

Signature.
Let n be a number.
OneV(G, n) is a vector of G of length n.

Signature.
Let n be a number.
Let x be a number.
PotZ(x, n) is a number.

Signature.
A groupoperation is a function.

Signature.
Let f be a groupoperation.
FixP(f) is a Set.

Signature.
Let n be a number.
Op(G, n) is a groupoperation.

Signature.
let n be a number.
Let v be a vector of G of length n.
v is constant on G of length n is an atom.

Axiom.
Let p be a prime number.
card(Om(G, p)) = PotZ(card(El(G)), p-1).

Axiom.
Let p be a prime number.
FixP(Op(G, p)) = {v | v is an element of Om(G, p) and v is constant on G of length p}.

Axiom.
Let p be a prime number.
OneV(G, p) is an element of FixP(Op(G, p)).

Axiom DivFixForOp.
Let p be a prime number.
p | card(FixP(Op(G, p))).

Axiom PrimeGT1.
Let p be a prime number.
1 < p.

Axiom.
Let x,n,m  be numbers.
If x < n and n | m then x < m.

Axiom.
Let M be a set.
Let x be an element of M.
Assume 1 < card(M).
There is an element y of M such that y != x.

Axiom.
Let n be a number.
Let v be a vector of G of length n.
Assume v is constant on G of length n.
If VMul(v, G, n) = One(G) then ord(v[0], G) | n.

Axiom.
Let x be an element of El(G).
Assume x != One(G).
Then 1 < ord(x, G).

Axiom.
Let n be a number.
Let v be vector of G of length n.
Assume v is constant on G of length n.
v[0] = One(G) iff v = OneV(G, n).

Axiom.
Let p be a prime number.
Let n be a number.
Assume n | p.
Then n = 1 or n = p.

Axiom.
Let n, m be number.
If n < m then n != m.

Lemma Cauchy.
Let p be a prime number.
Assume p | card(El(G)).
Then there is an element x of El(G) such that ord(x, G) = p.
Proof.
  card(Om(G, p)) = PotZ(card(El(G)), p-1).

  FixP(Op(G, p)) = {v | v is an element of Om(G, p) and v is constant on G of length p}.

  OneV(G, p) is an element of FixP(Op(G, p)).

  p | card(FixP(Op(G, p))).
  1 < p.

  Hence 1 < card(FixP(Op(G, p))).

  Take an element v of FixP(Op(G, p)) such that v != OneV(G, p).

  ord(v[0], G) | p.
  v[0] != One(G).
  1 < ord(v[0], G).
  ord(v[0], G) = p.
Qed.