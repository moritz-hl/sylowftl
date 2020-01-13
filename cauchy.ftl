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
A vector of G of length n is a function.

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
A groupoperation is a function f such that 0 is an element of Dom(f).

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
  1 < ord(v[0], G).
  ord(v[0], G) = p.
Qed.