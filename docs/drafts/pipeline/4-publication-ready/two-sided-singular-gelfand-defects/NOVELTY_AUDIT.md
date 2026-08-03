# Novelty audit — countable observer weaving

Status: `[PROVED HERE; NOVELTY UNVERIFIED]`

## Exact new theorem surface

Let `T_i : G → H_i`, `i ∈ ℕ`, be bounded injective dense-range Hilbert operators.

- If some `T_i` is coercive, every closed `M ≤ G` whose image under every `T_j` is dense equals `G`.
- If every `T_i` is noncoercive, there exists one closed `D ≤ G` such that:
  - `D ∩ ran(T_i*) = {0}` for every `i`;
  - `D` contains a countably indexed linearly independent family;
  - every closed `L ≤ D` yields the simultaneous dense-image defect `L⊥`.

No condition is placed on sums, spans, commutation, self-adjointness, compactness, or joint stability of the family.

Lean declaration: `countable_observer_coercivity_wildness_law`.

## What was already known

1. Fillmore–Williams (1971) develops structure theory for one Hilbert operator range and classifies several nonclosed-range geometries.
2. Classical von Neumann/Dixmier theory, in modern form through ter Elst–Sauter (2016), gives a unitary copy of one suitable nonclosed operator range disjoint from the original range.
3. Kitson–Timoney (2011) proves spaceability of complements of operator ranges and extensions to unions of countable chains under their stated hypotheses.
4. Araújo–Barbosa–Baganha Raposo–Ribeiro (2025) gives general criteria for spaceability of complements of unions.
5. Ribeiro, arXiv:2510.11332v2, proves a Fréchet theorem when the span of the union of the ranges is nonclosed. That hypothesis does not follow from individual nonclosedness. Its remark asserting an arbitrary-family consequence from individual nonclosedness uses the inclusion in the wrong direction; an algebraically dense discontinuous hyperplane is a direct counterexample to that inference.

## Separation from prior results

The new theorem does not ask the span of `⋃ ran(T_i*)` to be nonclosed. It can apply when finite or countable algebraic combinations of observer ranges are large, including complementary two-channel situations. It constructs a common closed subspace disjoint from every adjoint range separately, then proves a hereditary closed-subspace law. This is different from finding a closed subspace in the complement of one combined operator range.

The proof is also different: finite-codimensional persistence of nonclosed range produces an orthonormal small-vector array; square-summable observer weights weave all observer blocks into one closed normal space.

## Priority searches performed

Queries covered:

- exact phrases around finite/countable families of operator ranges;
- common or simultaneous closed subspaces disjoint from operator ranges;
- spaceability of complements of unions of operator ranges;
- nonclosed adjoint ranges and dense images of closed subspaces;
- classical operator-range structure and quasi-complement literature;
- the 2025–2026 arXiv/operator-range spaceability literature.

No exact collision was found. Search-engine absence is not proof of priority. Independent MathSciNet/zbMATH and expert operator-theory review remain required.

## Significance assessment

### Positive

- Removes all spectral and stability assumptions from prior draft.
- Upgrades two-observer hyperplane existence to countable-family hereditary lattice existence.
- Gives exact rigidity boundary through coercivity.
- Applies directly to graph-coordinate problems for closed relations and rigged Hilbert embeddings.
- Entire theorem, construction, and applications have unconditional Lean certificates.

### Limitation

- The theorem is countable, not uncountable.
- It is Hilbertian, not Banach-general.
- It does not settle a major long-standing flagship problem.
- Current realistic venue band is strong general analysis/operator-theory journal or a general journal such as *Advances in Mathematics* only if independent referees agree that the countable law is previously unknown and broadly useful. It is not presently justified as Annals/JAMS/Inventiones scale.

## Door-2 verdict

`KEEP, PRIORITY OPEN.` Mathematical content is materially stronger than the original pre-quasi counterexample and survives hostile internal proof audit. Publication-strength claim must remain conditional on external priority confirmation.

## Sources

- P. A. Fillmore and J. P. Williams, “On operator ranges,” *Adv. Math.* 7 (1971), 254–281. DOI: 10.1016/S0001-8708(71)80006-3.
- D. Kitson and R. M. Timoney, “Operator ranges and spaceability,” *J. Math. Anal. Appl.* 378 (2011), 680–686. DOI: 10.1016/j.jmaa.2010.12.061.
- A. F. M. ter Elst and M. Sauter, “Nonseparability and von Neumann's theorem for domains of unbounded operators,” *J. Operator Theory* 75 (2016), 367–386. DOI: 10.7900/jot.2014nov18.2075.
- G. Araújo et al., “Complements of unions: insights on spaceability and applications,” *Mathematika* 71 (2025), e70006. DOI: 10.1112/mtk.70006.
- G. Ribeiro, “Operator ranges and spaceability: an extension of the Kitson–Timoney theorem,” arXiv:2510.11332v2.
