# SQB congruence unipotent block averages

Status: finite-ring factorization, actual congruence quotient identification
and uniform full-subgroup source comparison are formalized and fully audited.
RH remains open.
Frontier map is read-only.

Full chain: original modular source → independent current comparison or
full-Xi spectral occurrence → critical-line classification → RH.

Broad OR corpus searches found a four-factor elementary decomposition over
fields and exact finite Reynolds energy identities. The new objective extends
the decomposition to finite commutative rings, including composite congruence
levels, then applies it to full upper/lower unipotent subgroup averages.

Paper mechanism: finite maximal-ideal Chinese remaindering makes one entry of
a unimodular row a unit after one elementary adjustment. The explicit
three-factor decomposition at a unit lower-left entry then gives four factors
for every determinant-one matrix. A displacement within a finite subgroup is
at most twice the distance to that subgroup's Reynolds average. Four factors
therefore give full-group variance at most 16 times the sum of the two block
variances. This controls full subgroup averages; comparing their geometric
cost to original Maass currents remains a separate required step.

- [x] Broad OR discovery across mixing, incidence, unipotence and ring structure.
- [x] Prove finite-ring unit adjustment and four-factor matrix decomposition.
- [x] Descend literal integer elementary factors to every actual Deck quotient.
- [x] Prove the uniform block variance comparison on the actual source.
- [x] Audit scratch proofs, source checks, sole-target builds, axioms and imports.
- [x] Relate full-block displacement to original full currents, retaining mean and nodes.
- [ ] Prove a quotient-area comparison strong enough for the quarter inequality.

No spectral gap, quarter inequality, or Xi occurrence is assumed or established
by the proposed block comparison alone.

[Complete proof, scope and audit](../../../3-formalized/sqb-congruence-unipotent-blocks.md).

All 42 public declarations are indexed exactly once; 43 axiom reports contain
only propext, Classical.choice and Quot.sound. All three sole-target builds
and repository formal lint passed. No owned Lean/Lake process remains.

The [actual current-path reduction](../../../3-formalized/sqb-unipotent-current-paths.md)
is now closed: complete blocks reduce exactly to two one-period
resistance/current products with parameter moment N(2N+1)/12. This identifies
the differential cost; the required quotient-area comparison remains open.
