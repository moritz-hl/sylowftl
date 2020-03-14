# Second Sylow Theorem in Naproche / ForTheL

This repository contains files that can be interpreted as a proof of the [Second Sylow Theorem](https://en.wikipedia.org/wiki/Sylow_theorems) by [Naproche-SAD](https://github.com/Naproche/Naproche-SAD).  
The proof is based on a lecture held by Prof. Dr. Jan Schröer at the university of Bonn in 2019/20.


## Structure

The proof is divided into eight files:

- **01basicgrptheory.ftl**  
&ensp;Introduction of groups, subgroups and cosets
- **02numbers.ftl**  
Axiomatic introduction of natural numbers and integers.
- **03cards.ftl**  
Axiomatic introduction of finite sets and finite cardinalities.
- **04lagrange.ftl**  
Proof of [Lagrange's Theorem](https://en.wikipedia.org/wiki/Lagrange%27s_theorem_(group_theory))
- **05staborb.ftl**  
Bijection between Stabilizer and Orbit
- **06fixedpointsmodp.ftl**  
Properties of fixed points of group actions
- **07grpaction.ftl**  
Definition of the group action used in the following proof
- **08sylow2.ftl**  
Proof of Sylow's Second Theorem

The files have been verified in Isabelle - Naproche on a MacBook Pro with an 2,7 GHz Quad-Core Intel Core i7 and 16 GB of RAM in approximately 5 minutes.

## Formalization in Lean

A formalization in LEAN can be found under [https://github.com/moritz-hl/sylow2] (based on [https://github.com/ChrisHughes24/Sylow])
