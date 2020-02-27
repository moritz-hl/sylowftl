[synonym integer/-s]
[synonym number/-s]

Signature Integers. An integer is a notion.

Signature Naturals. A natural number is an integer.

Let a,b,c,d,e,n,m stand for integers.

Signature NatZero.  0 is a natural number.
Signature NatOne.   1 is a natural number.

Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.

Signature NatPot. Let b be a natural number.  a ^ b is an integer.

Axiom NatPlus. If a and b are natural numbers then a + b is a natural number.
Axiom NatMult. If a and b are natural numbers then a * b is a natural number.

Signature NatLT. a < b is an atom.

Let a is smaller than b stand for a < b.

Axiom TriCh.
a = b \/ a < b \/ b < a.

Axiom.
a < b iff a != b.

Let a - b stand for a + (-b).

Axiom NatSub.
If a < b then b - a is natural number.

Axiom AddAsso.      a + (b + c) = (a + b) + c.
Axiom AddComm.      a + b = b + a.
Axiom AddZero.      a + 0 = a = 0 + a.
Axiom AddNeg.       a - a = 0 = -a + a.

Axiom MulAsso.      a * (b * c) = (a * b) * c.
Axiom MulComm.      a * b = b * a.
Axiom MulOne.       a * 1 = a = 1 * a.

Axiom Distrib.      a * (b + c) = (a*b) + (a*c) and
                    (a + b) * c = (a*c) + (b*c).

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Axiom PotInj.   Let p be an integer. Let n,m be natural numbers. (p ^ n = p ^  m) => n = m.
Axiom PotAdd. Let p be an integer. Let n, m be natural numbers. p ^ (n + m) = (p ^ n) * (p  ^ m).
Axiom PotNotZero. Let p be an integer. Let k be a natural number. p ^ k  != 0.


Lemma MulZero.      a * 0 = 0 = 0 * a.
Proof.
  a*(1+(-1)) = (a*1)+(a*(-1))=0.
Qed.

Lemma MulMinOne.    (-1) * a = -a = a * -1.
Proof.
  a+(-1 * a)= (1*a)+(-1 * a) = 0.
Qed.

Lemma IntCanc.
c != 0 /\ a * c = b * c => a = b.
Proof.
  Assume c != 0 /\ a * c = b * c.
  
  (1) (a+ (-b))*c = (a * c) + ((-b) * c) = 0.
  
  Therefore a - b = 0 (by ZeroDiv, 1).
Qed.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Lemma DivPlus.
q | a /\ q | b =>  q | (a + b).

Definition EquMod.  a = b (mod q) iff q | a-b.

Definition NeqMod.  a != b (mod q) iff not (a = b (mod q)).

Lemma EquModRef.    a = a (mod q).

[ontored on]
Lemma EquModSym.    a = b (mod q) => b = a (mod q).
Proof.
    Assume that a = b (mod q).
    (1) Take n such that q * n = a - b.
    q * -n .= (-1) * (q * n) (by MulMinOne, MulAsso,MulComm,MulBubble)
                   .= (-1) * (a - b) (by 1).
    Therefore q | b-a.
qed.

Lemma EquModTrn.    a = b (mod q) /\ b = c (mod q) => a = c (mod q).
Proof.
    Assume that a = b (mod q) /\ b = c (mod q).
    Take n such that q * n = a - b.
    Take m such that q * m = b - c.
    We have q * (n + m) = a - c.
qed.

Lemma EquModMul. a = b (mod p * q) => a = b (mod p) /\ a = b (mod q).
Proof.
    Assume that a = b (mod p * q).
    Take m such that (p * q) * m = a - b.
    We have p * (q * m) = a - b = q * (p * m).
qed.
[/ontored]

Signature Prime.    a is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom.
Let n be a natural number.
Let p be a prime.
Let k be a natural number.
If k | p^n then k = 1 or p | k.

Axiom.
Let k be a natural number.
k != 0 => p | p^k.

Lemma DLogN.
Let p be a prime.
Let a, b be natural numbers.
If n = (p^a)*c /\ n = (p^b)*d and p does not divide c and p does not divide d then a = b.
Proof.
Assume n = (p^a)*c and n = (p^b)*d and p does not divide c and p does not divide d.

b is not smaller than a.
Proof by Contradiction.
  Assume b < a.
  We have p^a = (p^(a-b))*(p^b).

  (1) (p^a)*c = (p^b)*d.
  (2) ((p^(a-b))*(p^b))*c = (p^b)*d.
  (3) ((p^b)*(p^(a-b)))*c = (p^b)*d (by 1, MulComm).
  (4) (p^b)*((p^(a-b))*c) = (p^b)*d (by 3, MulAsso).
  (5) ((p^(a-b))*c)*(p^b) = d*(p^b) (by 4, MulComm).
  
  (6)((p^(a-b))*c) = d (by 5, IntCanc, PotNotZero).
  
  a-b != 0.

  p is a divisor of p^(a-b).
  p is a divisor of ((p^(a-b))*c).

  p does divide d.
  p does not divide  d.

  Contradiction.
end.

a is not smaller than b.
Proof by Contradiction.
  Assume a < b.
  We have p^b = (p^(b-a))*(p^a).

  (1) (p^b)*d = (p^a)*c.
  (2) ((p^(b-a))*(p^a))*d = (p^a)*c.
  (3) ((p^a)*(p^(b-a)))*d = (p^a)*c (by 1, MulComm).
  (4) (p^a)*((p^(b-a))*d) = (p^a)*c (by 3, MulAsso).
  (5) ((p^(b-a))*d)*(p^a) = c*(p^a) (by 4, MulComm).
  
  (6)((p^(b-a))*d) = c (by 5, IntCanc, PotNotZero).
  
  b-a != 0.

  p is a divisor of p^(b-a).
  p is a divisor of ((p^(b-a))*d).

  p does divide c.
  p does not divide  c.

  Contradiction.
end.

Therefore the thesis.
qed.