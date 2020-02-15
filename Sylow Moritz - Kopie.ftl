
Let M, N denote sets.
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
Let f be a function. f is bijection from M to N iff (f is injective and f is from M to N) and (f is surjective onto M).

Definition.
Let f be a function. Ran(f) = {f[x] | x << Dom(f)}.

Axiom FunExt.
Let f,g be functions. If Dom(f) = Dom(g) and for every element x of Dom(f) f[x] = g[x] then f = g.

Axiom.
Let f be a function.
Assume f is bijection from M to N.
There is a function g such that (g is bijection from N to M and for every x << M g[f[x]] = x).

[synonym group/-s]

##Definition von Gruppen

Signature.
A group is a notion.

Signature.
A finite group is a group.

Let G denote a group.

Signature.
El(G) is a set.

#Lemma.
#Let x, y be elements of El(G).
#(x, y) is an element of Prod(El(G), El(G)).

Signature.
One(G) is a set.

Axiom.
One(G) << El(G).

Signature.
Let a, b be elements of El(G).
a *^{G} b is an element of El(G).

Signature.
Inv(G) is a function from El(G) to El(G).

Axiom Assoc.
Let x, y, z be elements of El(G). x *^{G} ( y *^{G} z) = (x *^{G} y) *^{G} z. 

Axiom InvOne.
Let x be an element of El(G). Then x *^{G} Inv(G)[x] = One(G) =  Inv(G)[x] *^{G} x.

Axiom MulOne.
Let x be an element of El(G). Then x *^{G} One(G) = x =  One(G) *^{G} x.

Lemma.
Let x, y be elements of El(G).
If x *^{G} y = One(G) then y = Inv(G)[x].

Lemma.
Let x, y be elements of El(G).
If x *^{G} y = x then y = One(G).

Definition. #Warum nicht El(H)?
A subgroup of G is set H such that
(H is a subset of El(G))
and (One(G) << H)
and (for every x << H Inv(G)[x] << H)
and (for all elements x, y of H x *^{G} y << H).

Definition.
Let U be a subgroup of G.
Gr(U, G) is a group H such that
(El(H) = U)
and (One(H) = One(G))
and (for every x << U Inv(H)[x] = Inv(G)[x])
and (for all elements x, y of U x *^{Gr(U, G)} y = x *^{G} y).

Lemma.
Let G be a group.
Let H be a subset of El(G).
Assume ((There is a x << H such that x = x) and (for all elements  y, z of H  z *^{G} Inv(G)[y] << H)).
Then H is a subgroup of G.
Proof.
  One(G) << H.
    Proof.
      Take x << H.
      Then One(G) = x *^{G} Inv(G)[x].
      Thus One(G) << H.
    end.

  For every x << H Inv(G)[x] << H.
    Proof.
      Let x be an element of H.
      Then Inv(G)[x] = One(G) *^{G} Inv(G)[x].
      Thus Inv(G)[x] << H.
    end.

  For all elements x, y of H x *^{G} y << H.
  Proof.
    Let x, y be elements of H.
    Then Inv(G)[x] << H.
    x *^{G} y = x *^{G}  Inv(G)[Inv(G)[y]].
    Hence x *^{G} y << H.
    end.
Qed.

Definition.
Let g be an element of El(G).
Let H be a subgroup of G.
LeftCoset(g, H, G) = {g *^{G} h | h << H}.

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then Inv(G)[g2] *^{G} g1 << H.
Proof.
  Take y << El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
  Take b << H such that y = g1 *^{G} b.
  Take c << H such that y = g2 *^{G} c.

  g1 = y *^{G} Inv(G)[b].
  Inv(G)[g2] = c *^{G} Inv(G)[y].
  Inv(G)[g2] *^{G} g1 = c *^{G} (((Inv(G)[y]) *^{G} y) *^{G} Inv(G)[b])
                      = c *^{G} Inv(G)[b].

qed.


Let Mul(G)[(a, b)] stand for a *^{G} b.

Axiom Ext.
Let D, E be sets.
If E is a subset of D and D is a subset of E then D = E.

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume Inv(G)[g2] *^{G} g1 << H.
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).
Proof.
LeftCoset(g1, H, G) is a subset of LeftCoset(g2, H, G).
Proof.
  Let y be an element of LeftCoset(g1, H, G).
  Take a << H such that y = g1 *^{G} a.

  (Inv(G)[g2] *^{G}  g1) *^{G}  a << H.

  Then y = g1 *^{G}  a = g2 *^{G} ((Inv(G)[g2] *^{G}  g1) *^{G}  a).
end.

LeftCoset(g2, H, G) is a subset of LeftCoset(g1, H, G).
Proof.
  Let y be an element of LeftCoset(g2, H, G).
  Take a << H such that y = g2 *^{G} a.

  Then y = g2 *^{G} a = g1 *^{G} ((Inv(G)[g1]*^{G} g2)*^{G} a).
end.

Qed.

Lemma CosEq.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Assume there is an element y of El(G) such that (y << LeftCoset(g1, H, G) and y << LeftCoset(g2, H, G)).
Then LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Lemma.
Let H be a subgroup of G.
Let g1, g2 be elements of El(G).
Inv(G)[g2]*^{G}  g1 << H Iff LeftCoset(g1, H, G) = LeftCoset(g2, H, G).

Lemma.
Let H be a subgroup of G.
Let g,h be elements of El(G).
Assume g is an element of LeftCoset(h, H, G).
Then LeftCoset(g, H, G) = LeftCoset(h, H, G).

Definition.
Let H be a subgroup of G.
LeftCosets(H, G) = {LeftCoset(g, H, G) | g << El(G)}.

[synonym integer/-s]

Signature Integers. An integer is a notion.

Let a,b,c,n,m stand for integers.

Signature IntZero.  0 is an integer.
Signature IntOne.   1 is an integer.
Signature IntNeg.   -a is an integer.
Signature IntPlus.  a + b is an integer.
Signature IntMult.  a * b is an integer.
Signature.          a ^ b is an integer.

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

Axiom MulMinOne.    (-1) * a = -a = a * -1.
##Proof. a+(-1 * a)= (1*a)+(-1 * a) = 0.  Qed.

Axiom ZeroDiv.      a != 0 /\ b != 0 => a * b != 0.





Let a is nonzero stand for a != 0.
Let p,q stand for nonzero integers.

[synonym divisor/-s] [synonym divide/-s]

Definition Divisor. A divisor of b is a nonzero integer a
                    such that for some n (a * n = b).

Let a divides b stand for a is a divisor of b.
Let a | b stand for a is a divisor of b. #Definiert Let eine Relation?

Lemma.
Assume q | a and q | b.
q | (a + b).
Proof.
  q is a divisor of a and q is a divisor of b.
  Let r,s be integers such that (q*r=a and q*s=b).
  q*(r+s)=a+b.
Qed.

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
[/ontored]
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

Signature Prime. a is prime is an atom.

Let a prime stand for a prime nonzero integer.

Axiom PrimeDivisor. n has a prime divisor iff n != 1 /\ n != -1.


[synonym number/-s]

Signature.
Let y be a integer.
y is nonnegative is an atom.

Signature.
A natural number is a nonnegative integer.

Signature.
A finite set is a set.

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

Definition. #
Let N1, N2 be sets.
#Let N2 be a subset of N1.
N1 \\ N2 = {x | x is an element of N1 and (x is not an element of N2)}.

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
card(Union(M)) = card(N)*card(M).

Axiom.
Let N1, N2 be sets.
card(N1) = card(N2) iff there is a function f such that (f is from N1 to N2 and f is injective and f is surjective onto N2).

Axiom.
Let M be a set.
If card(M) != 0 then there is an element x of M such that x = x.

Axiom.
Let M be a set.
card(M) = 1 iff there is an element y of M such that for all elements x of M x = y.

Axiom.
Let M be a set.
Assume 1 < card(M).
Let x be an element of M.
Then there is an element y of M such that x != y.

Axiom.
Let M be a set.
Let N be a subset of M.
If card(M) = card(N) then M = N.


Definition.
Let U be a subgroup of G.
Index(G, U) = card(LeftCosets(U, G)).


Lemma.
Let U be a subgroup of G.
El(G) = Union(LeftCosets(U, G)).
Proof.
Let us show that El(G) is a subset of Union(LeftCosets(U, G)).
  Let g be an element of El(G).
  Then g is an element of LeftCoset(g, U, G).
end.

Let us show that Union(LeftCosets(U, G)) is a subset of El(G).
  Let h be an element of Union(LeftCosets(U, G)).
  Take an element k of El(G) such that h is an element of LeftCoset(k, U, G).
  Take an element j of U such that h = k *^{G} j.
  j is an element of El(G). Hence h is an element of El(G).
end.
Qed.

Lemma.
Let G be a group.
Let U be a subgroup of G.
LeftCosets(U, G) is disjunct collection.
Proof.
Let N1, N2 be elements of LeftCosets(U, G).
Assume that not (N1 and  N2 are disjunct).
Take elements g1, g2  of El(G) such that N1 = LeftCoset(g1, U, G) and N2 = LeftCoset(g2, U, G).
Then g1 << N1 and g1 << N2.
Hence N1 = N2 (by CosEq).
Qed.

Definition.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is a function f
such that Dom(f) = U
and  for all elements u of U f[u] = (g *^{G} u).

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is from U to LeftCoset(g, U, G).

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is injective.

Lemma.
Let G be a group.
Let U be a subgroup of G.
Let g be an element of El(G).
fCoset(g, U, G) is surjective onto LeftCoset(g, U, G).


Lemma Lagrange.
Let G be a group.
Let U be a subgroup of G.
card(Union(LeftCosets(U, G))) = card(U)*card(LeftCosets(U, G)).
Proof.
  card(El(G)) = card(Union(LeftCosets(U, G))).
  Let N1, N2 be elements of LeftCosets(U, G).
  Take elements g1, g2 of El(G) such that N1 = LeftCoset(g1, U, G) and N2 = LeftCoset(g2, U, G).
  card(N1) = card(U) = card(N2).
  Thus for all elements N11, N12 of LeftCosets(U, G) card(N11) = card(N12).
  U = { One(G) *^{G} j | j << U } and LeftCoset(One(G),U,G) = { One(G) *^{G} j | j << U }.
  Hence U is an element of LeftCosets(U, G).
  LeftCosets(U, G) is disjunct collection.
  card(Union(LeftCosets(U, G))) = card(N1)*card(LeftCosets(U, G)) (by cardUnion).
Qed.

Definition.
Let M be a set.
Let G be a group.
A groupaction from G on M is a function f
such that f is from Prod(El(G), M) to M
and (for every element x of M f[(One(G), x)] = x)
and for every element x of M for all elements a, b of El(G)
f[((a *^{G}  b), x)] = f[(a, f[(b, x)])].

Definition.
Let p be a prime number.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(p, U, P, G) is a function f 
such that f is from Prod(El(Gr(U, G)), LeftCosets(P, G)) to LeftCosets(P, G) and
for all elements u of U for all elements x of El(G) 
f[(u, LeftCoset(x, P, G))] = LeftCoset(u *^{G}  x,P, G).

Lemma.
Let p be a prime number.
Let P be a subgroup of G.
Let U be a subgroup of G.
Op(p, U, P, G) is a groupaction from Gr(U, G) on LeftCosets(P, G).
Proof.
  Take a function f such that f = Op(p, U, P, G).
  
  Let us show that for every element N of LeftCosets(P, G) f[(One(Gr(U, G)), N)] = N.
    Let N be an element of LeftCosets(P, G).
    Take an element k of El(G) such that (N = LeftCoset(k,P,G)).
    f[(One(Gr(U, G)), LeftCoset(k,P,G))] = LeftCoset(One(Gr(U, G)) *^{G} k,P,G).     
    end.
  
  Let us show that for every element N of LeftCosets(P, G) for all elements a, b of El(Gr(U, G))
  f[(Mul(Gr(U, G))[(a, b)], N)] =  f[(a,  f[(b, N)])].
    Take an element k of El(G) such that (N = LeftCoset(k,P,G)).
    Take elements a, b of El(Gr(U, G)).
    f[(a, LeftCoset(k, P, G))] = LeftCoset(Mul(G)[(a, k)],P, G).
    f[(b,  LeftCoset(a *^{G}  k,P, G))] = LeftCoset(Mul(G)[(b, Mul(G)[(a, k)])],P, G).
    f[(Mul(G)[(b, a)], LeftCoset(k,P, G))] = LeftCoset(Mul(G)[(Mul(G)[(b, a)], k)],P, G).
    Therefore f[(b, f[(a, N)])] = f[(Mul(Gr(U, G))[(b, a)], N)].
  end.
  
  #f is from Prod(El(Gr(U, G)), LeftCosets(P, G)) to LeftCosets(P, G).
  #f is a function.
  #f is from Prod(El(Gr(U, G)), LeftCosets(P, G)) to LeftCosets(P, G).
  #for every element x of LeftCosets(P, G) for all elements a, b of El(Gr(U, G))
  #((a *^{Gr(U, G)} b, x) is an element of Prod(El(Gr(U, G)), LeftCosets(P, G)) and  f[(a *^{Gr(U, G)} b, x)] =  f[(a,  f[(b, x)])]).
  #for every element x of LeftCosets(P, G) 
  #f[(One(Gr(U, G)), x)] = x.
  
  #f is a groupaction from Gr(U, G) on LeftCosets(P, G). ##??
Qed.

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
Let x be an element of M.
Orbit(x, f, G, M) = { f[(a, x)] | a << El(G)}.

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
A fixedpoint on M on G of f is an element y of M such that
for every element a of El(G) f[(a, y)] = y.

Definition.
Let M be a set.
Let G be a group.
Let f be a function from Prod(El(G), M) to M.
fixedPoints(M, G, f) = {y | y is a fixedpoint on M on G of f}.

###
Lemma. 
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x be an element of M.
x << Orbit(x, f, G, M).
Proof.
f[(One(G),x)] << Orbit(x,f,G,M).
f[(One(G),x)] = x.
Qed.

###
Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x be an element of M.
x is a fixedpoint on M on G of f iff card(Orbit(x, f, G, M)) = 1.
Proof.

  Let us show that if x is a fixedpoint on M on G of f then card(Orbit(x, f, G, M)) = 1.
    Assume x is a fixedpoint on M on G of f.
    (1) Thus for all a << El(G) f[(a, x)] = x.
    Take y << Orbit(x,f,G,M).
    y = f[(b, x)] for some b << El(G).
    y = x (by 1).
  end.

  Let us show that if card(Orbit(x, f, G, M)) = 1 then x is a fixedpoint on M on G of f.
    Assume card(Orbit(x, f, G, M)) = 1.
    Let b << El(G).
    (1) f[(One(G),x)] = x.
    f[(One(G),x)] << Orbit(x, f, G, M).
    f[(b,x)] << Orbit(x, f, G, M).
    Hence f[(b,x)] = x.
  end.

Qed.

Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) = {y | y << El(G) and f[(y, x)] = x}.

###
Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Stab(x,f, G, M) is a subgroup of G.
Proof.
  Stab(x,f, G, M) is a subset of El(G).
Qed.

Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
fStabOrb(x, f, G, M) is a function h such that
h is from LeftCosets(Stab(x, f, G, M), G) to Orbit(x, f, G, M)
and (for all elements i of El(G) h[LeftCoset(i,Stab(x, f, G, M),G)] = f[(i, x)]).

###
Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
fStabOrb(x, f, G, M) is injective and surjective onto Orbit(x, f, G, M).
Proof.

fStabOrb(x, f, G, M) is from LeftCosets(Stab(x, f, G, M), G) to Orbit(x, f, G, M).

fStabOrb(x, f, G, M) is surjective onto Orbit(x, f, G, M). #Dauert lange.

Let us show that fStabOrb(x, f, G, M) is injective.
  
  Let us show that for all elements h1,h2 of LeftCosets(Stab(x, f, G, M), G)
  we have (h1 != h2 => fStabOrb(x, f, G, M)[h1] != fStabOrb(x, f, G, M)[h2]).
   
    Assume h1, h2 be elements of LeftCosets(Stab(x, f, G, M), G).
    Take elements g1, g2 of El(G) such that
    h1 = LeftCoset(g1,Stab(x, f, G, M),G) and h2 = LeftCoset(g2, Stab(x, f, G, M),G).
  
    Let us show that if fStabOrb(x, f, G, M)[h1] = fStabOrb(x, f, G, M)[h2] then h1 = h2.
      Assume fStabOrb(x, f, G, M)[h1] = fStabOrb(x, f, G, M)[h2].
      Then f[(g1, x)] = f[(g2, x)].
    
      ((Inv(G)[g2] *^{G} g1), x) is an element of Prod(El(G), M).
    
       f[((Inv(G)[g2] *^{G} g1), x)] = f[((Inv(G)[g2]*^{G} g2), x)] = x.
      
      Thus Inv(G)[g2] *^{G} g1 is an element of Stab(x, f, G, M).
      
      Therefore h1 = h2.
    end.
  end.
end.
qed.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x << M.
Index(G, Stab(x, f, G, M)) = card(Orbit(x, f, G, M)).

Axiom.
Let n be a natural number.
Let p be a prime number.
Let k be a natural number.
If k | p^n then k = 1 or p | k.

Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let x1, x2 be elements of M.
Assume that Orbit(x1, f, G, M) and Orbit(x2, f, G, M) are not disjunct.
Then Orbit(x1, f, G, M) = Orbit(x2, f, G, M).
Proof.
Take elements y1, y2 of El(G) such that f[(y1, x1)] = f[(y2, x2)].

x2 = f[(Inv(G)[y2] * ^{G} y1, x1)]. #Dauert lang.
x2 is an element of Orbit(x1, f, G, M).

Let us show that Orbit(x1, f, G, M) is a subset of Orbit(x2, f, G, M).
  Let x3 be an element of Orbit(x1, f, G, M).
  Take an element y3 of El(G) such that f[(y3, x1)] = x3.
  x3 = f[(y3 *^{G} (Inv(G)[y1] *^{G} y2), x2)]. #Dauert lang.
  Thus x3 is an element of Orbit(x2, f, G, M).
end.
Qed.

Definition.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) = {Orbit(x, f, G, M) | x is an element of M and x is not an element of fixedPoints(M, G, f)}.

###
Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) is a set such that for all elements N of OrbitsNotTriv(f, G, M) N is a set.
Proof.
Let us show that for all elements N of OrbitsNotTriv(f, G, M) N is a set.
  Let N be an element of OrbitsNotTriv(f, G, M).
  Take an element x of M such that N = Orbit(x, f, G, M).
end.
Qed.

###
Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
OrbitsNotTriv(f, G, M) is disjunct collection.
Proof.
Let N1, N2 be elements of OrbitsNotTriv(f,G,M).
Take elements x1, x2 of M such that N1 = Orbit(x1, f, G, M) and N2 = Orbit(x2, f, G, M).
Qed.

###
Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
For all y << M Orbit(y, f, G, M) is a subset of M.  

###
Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
fixedPoints(M , G, f) is a subset of M.

###
Axiom Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Let y << M.
Assume y is not an element of fixedPoints(M, G, f).
card(Orbit(y, f, G, M)) != 1.

###
Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) = M \\ fixedPoints(M, G, f).
Proof.

Let us show that Union(OrbitsNotTriv(f, G, M)) is a subset of M \\ fixedPoints(M, G, f).
  
  Let x be an element of Union(OrbitsNotTriv(f, G, M)).
  Take an element y of M such that x is an element of Orbit(y, f, G, M) 
  and y is not an element of fixedPoints(M, G, f).

  card(Orbit(x, f, G, M)) = card(Orbit(y, f, G, M)) != 1.
  
  Let us show that x is not an element of fixedPoints(M, G, f).
    Assume x is an element of fixedPoints(M, G, f).
    x is a fixedpoint on M on G of f.
    card(Orbit(x, f, G, M)) = 1.
  end.

  Hence x is an element of M \\ fixedPoints(M, G, f).
end.

Let us show that M \\ fixedPoints(M, G, f) is a subset of Union(OrbitsNotTriv(f, G, M)).
  Let x be an element of M \\ fixedPoints(M , G, f).
  x is an element of M.
  x is not an element of fixedPoints(M , G, f).
  Orbit(x, f, G, M) is an element of OrbitsNotTriv(f, G, M).
  x is an element of Orbit(x, f, G, M).
  Thus x is an element of Union(OrbitsNotTriv(f, G, M)).
end.
qed.


Lemma.
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) and fixedPoints(M, G, f) are disjunct.

Lemma. #Warum braucht dieses Lemma viel Zeit?
Let M be a set.
Let G be a group.
Let f be a groupaction from G on M.
Union(OrbitsNotTriv(f, G, M)) \-/ fixedPoints(M, G, f) = M.

Signature.
Let p be a prime number.
A group of order p is a group H  such that
(there is a natural number n such that card(El(H)) = p ^ n).



Axiom cardUnion2.
Let M be a set such that for all elements N of M N is a set.
Let k be an integer.
If M is disjunct collection and  for all elements N of M  k | card(N) then
k | card(Union(M)).

Lemma.
Let M be a set.
Let p be a prime number.
Let G be a group of order p.
Let f be a groupaction from G on M.
card(fixedPoints(M, G, f)) = card(M) (mod p).
Proof.

Let us show that p | card(Union(OrbitsNotTriv(f, G, M))).
  Let us show that for all elements N1 of OrbitsNotTriv(f, G, M) p | card(N1).
    Let N be an element of OrbitsNotTriv(f, G, M).
    Take an element x of M such that N = Orbit(x, f, G, M).
    If card(N) = 1 then x is an element of fixedPoints(M, G, f).
    Hence card(N) != 1.
    card(N) = Index(G, Stab(x, f, G, M)).
    Hence card(El(G)) = card(Stab(x, f, G, M))*card(N).
    Hence card(N) | card(El(G)).
    Hence p | card(N).
  end.
end.
 
card(M) = card(fixedPoints(M, G, f)) + card(Union(OrbitsNotTriv(f, G, M))).
Hence card(M) = card(fixedPoints(M, G, f)) (mod p).

qed.


Definition.
Let g be an element of El(G).
Let U be a subgroup of G.
ConjugateSet(g, U, G) = {(g *^{G} (u *^{G} Inv(G)[g]))| u is an element of U}.

##lemma conjugatesets same size


Definition.
Let p be a prime number.
Syl(p, G) = {P | P is a subgroup of G and not (p | Index(G, P)) and Gr(P, G) is a group of order p}.

Axiom.
Let p be a prime number.
Let U, P be elements of Syl(p, G).
card(U) = card(P).



Theorem Sylow2.
Let p be a prime number.
Let G be a finite group.
Let P, U be an element of Syl(p, G).
Then there is an element g of El(G) such that ConjugateSet(g, U, G) is a subset of P.
Proof.
  Index(G, P) != 0  (mod p).

  card(fixedPoints(LeftCosets(P, G), Gr(U, G), Op(p, U, P, G))) = Index(G, P) (mod p).
  
  Hence card(fixedPoints(LeftCosets(P, G), Gr(U, G),  Op(p, U, P, G))) != 0.
  
  Take an element x of fixedPoints(LeftCosets(P, G), Gr(U, G),  Op(p, U, P, G)).
  Take an element y of El(G) such that x = LeftCoset(y, P, G).
  
  Let us show that ConjugateSet(Inv(G)[y], U, G) is a subset of P.
    Let h be an element of U.
    x = Op(p, U, P, G)[(h, x)].
    LeftCoset(y, P, G) = Op(p, U, P, G)[(h, LeftCoset(y, P, G))]  =  LeftCoset((h *^{G} y) ,P, G).
    
    Hence h *^{G} y is an element of LeftCoset(y, P, G).
  
    Take an element w of P such that h *^{G} y = y *^{G} w.

    Then we have w = Inv(G)[y] *^{G} (y *^{G} w) =  Inv(G)[y] *^{G} (h *^{G} y).
    Therefore  Inv(G)[y] *^{G} (h *^{G}  y) is an element of P.
  end.
Qed.