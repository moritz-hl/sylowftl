[read praktikum/functions.ftl]
[read praktikum/groupdef.ftl]

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

Signature.
Let M be a set such that for all elements N of M N is a set.
Union(M) is a set.

Definition.
Let M be a set such that for all elements N of M N is a set.
M is disjunct iff for all elements N1, N2 of M there is no element of N1 that is an element of N2.

