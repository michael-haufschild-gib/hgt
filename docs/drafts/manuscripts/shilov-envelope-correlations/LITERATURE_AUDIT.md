# Literature audit: Shilov envelope correlations

Audit date: 2026-08-04

Scope: complete-order quotients, Shilov ideals, \(C^*\)-envelopes, subdirect products,
noncommutative relations, partial-map categories, ideal-lattice cohomology, Mayer--Vietoris
methods, local operator systems, and derived inverse limits.

## Primary-source matrix

| Source | Verified content | Exact gap relative to manuscript |
|---|---|---|
| Hamana, *Publ. RIMS* 15 (1979), 773--785 | Injective envelopes of operator systems and existence/minimality of the \(C^*\)-envelope. | No quotient-diagram correlation, transported Shilov join, oplax law, or migration cohomology. |
| Arveson, *Acta Math.* 123 (1969); *JAMS* 21 (2008) | Boundary ideals/representations and noncommutative Choquet boundary. | Detects each vertex Shilov ideal, not minimal joins across quotient arrows. |
| Kavruk--Paulsen--Todorov--Tomforde, *Adv. Math.* 235 (2013), 321--360; [arXiv:1008.2811](https://arxiv.org/abs/1008.2811) | Operator-system quotients, exactness, and universal quotient constructions. | No \(C^*\)-envelope common quotient \(Q_q\), subdirect pullback \(\Gamma_q\), or diagram cohomology. |
| Han, *JMAA* 384 (2011), 375--386; [arXiv:1010.0380](https://arxiv.org/abs/1010.0380) | Complete quotient maps and positive matricial lifting. | Lifting is at operator-system level; it does not encode migration of Shilov ideals or repair envelope nonfunctoriality. |
| Joiţa, *Adv. Oper. Theory* 10 (2025), no. 3; [arXiv:2409.10474](https://arxiv.org/abs/2409.10474) | Shilov boundary ideal and envelope for local operator systems. | No quotient-path correlation, minimal transported join, long exact sequence, or finite transmutation theorem. |
| Maszczyk, [arXiv:0811.3997](https://arxiv.org/abs/0811.3997) | A resolution of intersections by sums for finite families in a distributive subgroup/ideal lattice; generalized Chinese remainder theorem. | This kills any novelty claim for ordinary finite ideal Čech acyclicity. It does not treat ideals in changing universal covers or face maps mixing inclusion with quotient transport. |
| Naarmann, [arXiv:1812.11442](https://arxiv.org/abs/1812.11442) | Mayer--Vietoris spectral sequence from intersections of \(C^*\)-ideals whose sum is dense. | Fixed ambient algebra and \(K\)-theory input; no operator-system boundary transport or envelope correlations. |
| Weaver, *Mem. AMS* 215 (2012), no. 1010; [arXiv:1005.0354](https://arxiv.org/abs/1005.0354) | Quantum relations as weak-star closed bimodules over commutants. | Different object: no closed subdirect \(C^*\)-product, common quotient, or Shilov ideal data. |
| Daws, [arXiv:2602.18361](https://arxiv.org/abs/2602.18361) | Relations between two von Neumann algebras as commutant bimodules; composition; functor from CP maps. | Current closest relation-valued functor, but its relations are operator bimodules rather than Goursat pullbacks of \(C^*\)-envelopes. |
| Cockett--Lack, *Theoret. Comput. Sci.* 270 (2002), 223--259, DOI 10.1016/S0304-3975(00)00382-0 | Restriction categories and universal realization of partial maps/subobjects. | Partial-map grammar records domains of definition, not the multivalued join \(J_T+\alpha(J_S)\), two vertical faces, or Shilov cohomology. |
| Phillips, *J. Operator Theory* 19 (1988), 159--195; *K-Theory* 3 (1989), 441--478 | Inverse limits of \(C^*\)-algebras, \(\sigma\)-\(C^*\)-algebras, and representable \(K\)-theory Milnor sequences. | Supplies inverse-limit infrastructure, not the boundary coefficient system or arbitrary-quotient relational exact sequence. |

## Collision searches

Searches included exact and paired phrases:

- "Shilov" "subdirect product" operator system quotient
- "C*-envelope" correlation quotient Shilov
- "Shilov boundary" cosheaf cohomology diagram
- "operator system" quotient oplax relation
- "C*-envelope" "long exact sequence" quotient diagram
- "Shilov ideal" simplicial coefficient system
- "envelope correlation" operator system

No primary source located the conjunction

\[
M_q=J_T+\alpha_q(J_S),\qquad
\Gamma_q=C_e^*(S)\times_{C_u^*(T)/M_q}C_e^*(T),
\]

nor its minimal semisimplicial join completion, long exact sequence, or universal two-edge
transmutation.

Absence from search is not proof of novelty. Before submission, MathSciNet and zbMATH expert
searches and direct author/title searches remain mandatory.

## Claims deliberately demoted

1. Finite Čech acyclicity of ideals in one \(C^*\)-algebra is not new; Maszczyk contains the
   relevant distributive-lattice resolution.
2. Partial-map/restriction-category language is not the main theorem. It omits multivalued
   boundary ambiguity.
3. \(H^1(\mathcal M)\) is generally an involutive vector-space quotient, not a \(C^*\)-algebra.
   Nuclearity, ideal lattice, and \(K\)-theory belong to the escape/deficit/vertical-ambiguity
   faces, not intrinsically to cohomology.
4. For infinite diagrams, algebraic exactness does not imply Hausdorff topological cohomology.

## Novelty residue

Candidate new conjunction:

1. canonical common quotient and pullback correlation for every complete-order quotient;
2. identification of escape and deficit as the two quotient faces of the minimal edge join;
3. normal oplax correlation-valued completion of the \(C^*\)-envelope;
4. minimal semisimplicial join completion of transported Shilov ideals;
5. long exact correlation/descent cohomology sequence;
6. every unital \(C^*\)-algebra realized in a split two-edge path as deficit, escape, and
   target-vertical composition ambiguity, with its underlying involutive Banach space equal to
   \(H^1\), while the composite returns to the graph locus.

Items 1--6 together, not the formal long exact sequence alone, are the publication claim.

For higher-dimensional diagrams the manuscript uses
\(\operatorname{Mig}^{k+1}=\operatorname{im}\partial\), not all of
\(H^{k+1}(\mathcal M)\), so ordinary topology of the indexing complex is not mislabeled as
boundary migration.
