[read praktikum/grptheory/functions.ftl]
[synonym number/-s]

Signature.
a natural number is a notion.

Signature.
NN is the set of natural numbers.

Signature.
0 is a natural number.

Let n, m denote natural numbers.

Signature.
Succ(n) is a natural number.

Axiom.
Succ(n) != 0.

Axiom.
If Succ(n) = Succ(m) then n = m.

Axiom Induct.
let M be a set.
If (0 is an element of M and for each element x of NN (If x is an element of M then Succ(x) is an element of M))
Then NN is a subset of M.

Lemma.
NN = {x| x = 0 or there is a natural number k such that x = Succ(k)}.
Proof.
Define M2 = {x|x = 0 or there is a natural number k such that x = Succ(k)}.
Qed.


Signature.
n < m is an atom.

Axiom.
n < m iff (m = Succ(n) or Succ(n) < m).

Axiom.
Let x, y, z be natural numbers.
If x < y and y < z then x < z.

Axiom.
If n < m then not m < n.

Axiom.
If Succ(n) < Succ(m) then n < m.

Definition.
\MN(n) = {x|x is a natural number and  x<n}.

Lemma.
NN = {x| x is a natural number and (x = 0 or 0 < x)}.
Proof.
  Define HN = {x| x is a natural number and (x = 0 or 0 < x)}.
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
let n,m be natural numbers.
n|m is an atom.

Signature.
let n,m be natural numbers.
n-m is a natural number.

Signature.
let n,m be natural numbers.
n+m is a natural number.

Signature.
Let n,m be natural numbers.
n*m is a natural number.

Axiom.
Let n, m be natural number.
If n < m then n != m.

Signature.
A prime number is a natural number.

Signature.
Let p, n be natural numbers.
p ^ n is a natural number.

Definition EquMod.  
Let a, b, q be natural numbers.
a = b (mod q) iff q | a-b.

Definition NotEquMod.
Let a, b, q be natural numbers.
a != b (mod q) iff not (q | a-b).

Axiom.
Let a, b, q be natural numbers.
a = a (mod q).

Axiom.
Let a, b, q be natural numbers.
If a = b (mod q) then b = a (mod q).

Axiom.
Let a, b, c, q be natural numbers.
If a = b (mod q) and b = c (mod q) then a = c (mod q).

Axiom.
Let a, q be natural numbers.
If a != 0 (mod q) then a != 0.

Axiom.
Let p be a prime number.
Let n be a natural number.
Assume n | p.
Then n = 1 or n = p.

Signature.
Let M be a set.
card(M) is a natural number.


Definition.
Let M be a set such that for all elements N of M N is a set.
Union(M) = {x | There is an element N of M such that x is an element of N}.

Definition.
Let N1, N2 be a sets.
N1 and N2 are disjunct iff there is no element x of N1 such that x is an element of N2.

Definition.
Let N1, N2 be sets.
N1 \-/ N2 = {x | x is an element of N1 or x is an element of N2}.

Axiom.
Let N1, N2 be sets.
If N1 and N2 are disjunct then card(N1 \-/ N2) = card(N1) + card(N2).


Definition.
Let M be a set such that for all elements N of M N is a set.
M is disjunct collection iff for all elements N1, N2 of M (N1 = N2 or ( N1 and N2 are disjunct)).

Axiom cardUnion.
Let M be a set such that for all elements N of M N is a set.
Assume M is disjunct collection.
Assume that for all elements N1, N2 of M card(N1) = card(N2).
Let N be an element of M.
card(N) | card(Union(M)) and card(M) | card(Union(M)).

Axiom.
Let N1, N2 be sets.
card(N1) = card(N2) iff there is a function f such that (f is from N1 to N2 and f is injective and f is surjective onto N2).

Axiom.
Let M be a set.
If card(M) != 0 then there is an element x of M such that x = x.

Axiom.
Let M be a set.
Assume 1 < card(M).
Let x be an element of M.
Then there is an element y of M such that x != y.

Axiom.
Let M be a set.
Let N be a subset of M.
If card(M) = card(N) then M = N.