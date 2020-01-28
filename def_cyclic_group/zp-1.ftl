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

Let G denote a group.

Let x +^{G} y stand for  Mul(G)[(x, y)].

Let -^{G} x stand for Inv(G)[x].

[read praktikum/notation_helper.ftl]

Lemma.
Let x, y be elements of El(G).
x +^{G} y is an element of El(G).

Lemma.
\MN(2) = {0, 1}.

Definition.
Let n be a number.
Assume 1 < n.
ZZ(n) is a group H such that
El(H) = \MN(Succ(n))
and One(H) = 0
and (n, 1) is an element of Prod(El(H), El(H))
and (1, n) is an element of Prod(El(H), El(H))
and n +^{H} 1 = 0 = 1 +^{H} n
and for all elements x, y, z of El(H)
((If x != n then x +^{H} 1 = Succ(x) = 1 +^{H} x)).
###and Mul(H)[(x, Mul(H)[(y, z)])] = Mul(H)[(Mul(H)[(x, y)], z)] and Mul(H)[(x, Inv(H)[x])] = One(H) =  Mul(H)[( Inv(H)[x], x)] and Mul(H)[(x,One(H))] = x =  Mul(H)[(One(H), x)] ).

Lemma.
El(ZZ(2)) = {0, 1, 2}.

Lemma.
Let n be a number.
Assume 1 < n.
ZZ(n) is abelian.
Proof.  
  Let y be an element of El(ZZ(n)).
  
  Define M2 = {x|x is a number and 
    if x is an element of El(ZZ(n)) then Mul(ZZ(n))[(x, y)]=Mul(ZZ(n))[(y, x)]
  }.
  
  0 is an element of M2.
  for each element p of NN (If p is an element of M2 then Succ(p) is an element of M2).
  Proof.
    Let k be an element of NN.
    Assume k is an element of M2.
    Then Succ(k) is an element of M2.
    Proof.
      If not k < n then Succ(k) is not an element of El(ZZ(n)).
      
      Assume k is an element of El(ZZ(n)) and k <  n.
      Then Succ(k) is an element of El(ZZ(n)).
      Succ(k) +^{ZZ(n)} y = 
      ((k +^{ZZ(n)} 1) +^{ZZ(n)} y) = ((1 +^{ZZ(n)} k) +^{ZZ(n)} y)
       = (1 +^{ZZ(n)} (k +^{ZZ(n)} y))
       = (1 +^{ZZ(n)} (y +^{ZZ(n)} k))
      = ((y +^{ZZ(n)} k) +^{ZZ(n)} 1)
      = (y +^{ZZ(n)} (k +^{ZZ(n)} 1))
      = (y+^{ZZ(n)} Succ(k)).
    end.
  end.

  Hence NN is a subset of M2.
Qed.

Definition.
GG3 = {0, 2}.

[read praktikum/subgroups.ftl]

Lemma.
GG3 is a subgroup of ZZ(3).

Lemma.
Let N, M be sets.
If N is a subset of M and M is a subset of N then M = N.

Lemma.
Let n be a number.
assume 1 < n.
Let H be a subgroup of ZZ(n).
Assume 1 is an element of H.
Then H = El(ZZ(n)).
Proof.
 Define M2 = {x|x is a number and If x is an element of El(ZZ(n)) then x is an element of H}.
 0 is an element of M2.
 For each element p of NN (If p is an element of M2 then Succ(p) is an element of M2).
 Proof.
    let k be an element of NN.
    Assume k is an element of M2.
    Then Succ(k) is an element of M2.
    Proof.
      If not k < n then Succ(k) is not an element of El(ZZ(n)).
      Assume k < n.
      Succ(k) = k +^{ZZ(n)} 1.
      Therefore Succ(k) is an element of H.
    end.
 end.
 Hence El(ZZ(n)) is a subset of H.
 Therefore the thesis.
Qed.