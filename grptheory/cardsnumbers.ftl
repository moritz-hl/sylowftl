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

Signature.
let n,m be numbers.
n+m is a number.

Signature.
Let n,m be numbers.
n*m is a number.

Axiom.
Let n, m be number.
If n < m then n != m.

Signature.
A prime number is a number.

Axiom.
Let p be a prime number.
Let n be a number.
Assume n | p.
Then n = 1 or n = p.

Signature.
Let M be a set.
card(M) is a number.

Definition.
Let M be a set such that for all elements N of M N is a set.
Union(M) = {x | There is an element N of M such that x is an element of N}.

Definition.
Let N1, N2 be a sets.
N1 and N2 are disjunct iff there is no element x of N1 such that x is an element of N2.

Lemma.
Let N1, N2 be sets.
N1 and N2 are disjunct iff N2 and N1 are disjunct.

Definition.
Let N1, N2 be sets.
N1 \-/ N2 = {x | x is an element of N1 or x is an element of N2}.

Definition.
Let N1 be set.
Let N2 be a subset of N1.
N1 \\ N2 = {x | x is an element of N1 and x is not an element of N2}.

Axiom.
Let N1, N2 be sets.
If N1 and N2 are disjunct then card(N1 \-/ N2) = card(N1) + card(N2).

Axiom.
Let N1 be a set.
Let N2 be a subset of N1.
Then card(N1 \\ N2) = card(N1) - card(N2).

Definition.
Let M be a set such that for all elements N of M N is a set.
M is disjunct collection iff for all elements N1, N2 of M (N1 = N2 or ( N1 and N2 are disjunct)).

Axiom.
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
Assume card(M) > 1.
Let x be an element of M.
Then there is an element y of M such that x != y.