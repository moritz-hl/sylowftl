Let M,N denote sets.
Let x << M stand for x is an element of M.

Definition.
Prod(M,N) = { (x,y) | x << M and y << N }.

Definition.
A subset of M is a set N such that every element of N is an element of M.

Definition.
Let f be a function. Let M,N be sets. f is from M to N iff Dom(f) = M and for every element x of M f[x] is an element of N.

Definition.
Let f be a function. f is injective iff for all elements x,y of Dom(f) we have (x!=y => f[x] != f[y]).

Definition.
Let f be a function. f is surjective onto M iff (f is from Dom(f) to M and for every y << M there is an element x of Dom(f) such that f[x]=y).

Definition.
Let f be a function. f is bijection from M to N iff (f is injective and f is from M to N) and (f is surjective onto N).

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

Axiom.
Let f be a function.
Assume f is bijection from M to N.
There is a function g such that (g is bijection from N to M and for every x << M g[f[x]] = x).


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
If (0 is an element of M and for each element x of NN (If x is an element of M then Succ(x) is an element of M))
Then NN is a subset of M.


Lemma.
NN = {x| x = 0 or there is a number k such that x = Succ(k)}.
Proof.
Define M2 = {x|x = 0 or there is a number k such that x = Succ(k)}.
Qed.

Signature.
n+m is a number.

Axiom.
n+0=n.

Axiom.
n+Succ(m) = Succ(n+m).

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

###TODO: Proof.

Axiom.
Let x, y, z be numbers.
If x < y and y < z then x < z.

Axiom.
If n < m then not m < n.

Axiom.
If Succ(n) < Succ(m) then n < m.

Definition.
MN(n) = {x|x is a number and  x<n}.

Lemma.
NN = {x| x is a number and (x = 0 or 0 < x)}.
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

Signature.
A FSet is a set.

Let F, G denote FSet.

Signature.
card(F) is a number.

Axiom.
card(F) = n iff there is a function f such that f is bijection from MN(n) to F.

Definition.
test is a FSet such that
test = {1, 2}.

Lemma.
card(test) = 2.
Proof.
  Define testf[i] = Succ(i) for i in MN(2).
  Dom(testf) = MN(2).
  testf is injective.
  testf is from MN(2) to test.
  testf is surjective onto test.
  Therefore  the thesis.
Qed.