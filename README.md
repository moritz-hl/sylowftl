# Second Sylow Theorem in Naproche / ForTheL

This repository contains files that can be interpreted as a proof of [Sylow's Second Theorem](https://en.wikipedia.org/wiki/Sylow_theorems) by [Naproche-SAD](https://github.com/Naproche/Naproche-SAD).  
The proof is based on a lecture held by Prof. Dr. Jan Schröer at the university of Bonn in 2019/20.

<hr>

The goal of this project was to create a to serve as a comparison to an exisiting formaliziation in [LEAN](https://github.com/moritz-hl/sylowftl#formalization-in-lean)

## The Proof

The proof is divided into eight files located in <tt>/PROOF/</tt>:

- **01basicgrptheory.ftl**  
&ensp;&ensp;Introduction of groups, subgroups and cosets
- **02numbers.ftl**  
&ensp;&ensp;Axiomatic introduction of natural numbers and integers
- **03cards.ftl**  
&ensp;&ensp;Axiomatic introduction of finite sets and finite cardinalities
- **04lagrange.ftl**  
&ensp;&ensp;Proof of [Lagrange's Theorem](https://en.wikipedia.org/wiki/Lagrange%27s_theorem_(group_theory))
- **05staborb.ftl**  
&ensp;&ensp;Bijection between Stabilizer and Orbit
- **06fixedpointsmodp.ftl**  
&ensp;&ensp;Properties of fixed points of group actions
- **07grpaction.ftl**  
&ensp;&ensp;Definition of the group action used in the following proof
- **08sylow2.ftl**  
&ensp;&ensp;Proof of Sylow's Second Theorem

The files have been verified in [Isabelle - Naproche](https://sketis.net/2019/isabelle-naproche-for-automatic-proof-checking-of-ordinary-mathematical-texts) on a MacBook Pro with an 2,7 GHz Quad-Core Intel Core i7 and 16 GB of RAM in approximately 5 minutes.

## Formalization in Lean

A formalization in [LEAN](https://leanprover.github.io) can be found under https://github.com/moritz-hl/sylow2 (based on https://github.com/ChrisHughes24/Sylow)
