[synonym integer/-s]
[synonym number/-s]

Signature Integers. An integer is a notion.

Signature Naturals. A natural number is an integer.

Let a,b,c,n, m stand for integers.

Signature IntZero.  0 is a natural number.
Signature IntOne.   1 is a natural number.

Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.

Signature. Let b be a natural number.  a ^ b is an integer.

Axiom. If a and b are natural numbers then a + b is a natural number.
Axiom. If a and b are natural numbers then a * b is a natural number.

##Natural Numbers


Signature. a < b is an atom.

Let a - b stand for a + (-b).

Axiom AddAsso.      a + (b + c) = (a + b) + c.
Axiom AddComm.      a + b = b + a.
Axiom AddZero.      a + 0 = a = 0 + a.
Axiom AddNeg.       a - a = 0 = -a + a.

Axiom MulAsso.      a * (b * c) = (a * b) * c.
Axiom MulComm.      a * b = b * a.
Axiom MulOne.       a * 1 = a = 1 * a.


Axiom Distrib.      a * (b + c) = (a*b) + (a*c) and
                    (a + b) * c = (a*c) + (b*c).

Lemma MulZero.      a * 0 = 0 = 0 * a.
Proof. a*(1+(-1)) = (a*1)+(a*(-1))=0. Qed.

Lemma MulMinOne.    (-1) * a = -a = a * -1.
Proof. a+(-1 * a)= (1*a)+(-1 * a) = 0.  Qed.

Lemma ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.

Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b.

Lemma.
If  q | a and q | b then q | (a + b).

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