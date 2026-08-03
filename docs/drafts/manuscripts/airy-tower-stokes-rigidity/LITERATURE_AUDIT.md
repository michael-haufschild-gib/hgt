# Literature audit: irregular nonabelian Hodge theory and Stokes geometry

Audit date: 2026-08-03

## Search question

Does prior literature already contain any of the following exact results?

1. Lexicographic sign law for the diagonal nonabelian Hodge multiplicity of a ramified Stokes circle.
2. Zero-loop classification `beta_i=e_{i-1}+e_i`.
3. Bijection of zero-loop ramified characteristics with ordered multiplicative factorizations.
4. Exact two-circle edge spectra for simple ramified zero-loop circles.
5. Local-spectrum plus rescaled-ultrametric sufficiency for arbitrary finite elementary decorated graphs.
6. Decorated finite-fibre theorem for fission trees over a fixed nonabelian Hodge diagram.

## Primary sources checked

### Biquard--Boalch (2004)

- URL: https://arxiv.org/abs/math/0111098
- DOI: 10.1112/S0010437X03000010
- Scope: wild nonabelian Hodge correspondence on curves and hyperkähler metrics.
- Collision: none. Supplies context, not diagram arithmetic.

### Hiroe (2017)

- URL: https://arxiv.org/abs/1406.5788
- Published: *Josai Mathematical Monographs* 10 (2017), 161--192.
- Scope: dual Puiseux characteristics, irregularity/Milnor formulas, local Fourier resolution criterion, Stokes structure and iterated torus knots.
- Exact check: Theorem 3.10 gives resolution by local Fourier transforms and additions iff
  `e_{i-1} congruent to +/- e_i (mod beta_i)` at every characteristic step. The paper uses the
  negative congruence forced by `beta_i=e_{i-1}+e_i`.
- Closest overlap: formula for the endomorphism irregularity and this Fourier congruence.
- Boundary: no zero-loop nonabelian Hodge equality classification, no first-deviation sign law, no graph recognition theorem located.

### Boalch--Yamakawa (2020)

- URL: https://numdam.org/articles/10.5802/crmath.11/
- DOI: 10.5802/crmath.11
- Scope: diagrams for nonabelian Hodge spaces on the affine line.
- Collision: none; foundational diagram construction.

### Boalch--Douçot--Rembado (2025)

- URL: https://ems.press/doi/10.4171/prims/61-3-4
- DOI: 10.4171/PRIMS/61-3-4
- Scope: arbitrary twisted type-A configuration spaces, exact fission-tree axioms and sharp parameterization of admissible deformation classes.
- Exact check: Lemma 3.21 gives uniqueness from labelled fission data; Theorem 3.27 gives the
  coefficient realization criterion; Corollary 3.28 says every fission tree admits a realization.
- Closest overlap: realizes the trees constructed in the paper.
- Boundary: does not classify zero-loop leaves or elementary Cartan shadows by local spectra.

### Boalch (2025)

- URL: https://doi.org/10.1016/j.geomphys.2025.105512
- arXiv: https://arxiv.org/abs/2410.23358
- Scope: enumeration of untwisted fission trees at fixed slope/leaf number.
- Boundary: explicitly untwisted; no ramified zero-loop divisor-chain count.

### Douçot (2025/2026), new graphs

- URL: https://arxiv.org/abs/2509.24861
- Exact sections checked: loop formula Lemma 2.1; edge formula Lemma 2.2; rescaled formulas Lemma 4.3; ultrametric Theorem 4.2; fission-graph characterization Theorem 3.2; simple-graph result Proposition 4.5.
- Closest overlap: all source formulas and necessary ultrametric constraints used here.
- Explicit boundary: twisted ultrametric constraints are necessary, not a general characterization. Two-vertex ultrametricity is vacuous. No exact pair spectrum or elementary sufficiency theorem located.

### Douçot (2026), enriched trees

- URL: https://sigma-journal.com/2026/027/
- DOI: 10.3842/SIGMA.2026.027
- Scope: enriched-tree data strictly refine diagrams and reconstruct multiple admissible representations.
- Boundary: supports the information-loss motivation; no Airy-tower classification or spectrum theorem.

### Douçot (2026), Fourier/Argyres--Douglas classification

- URL: https://arxiv.org/abs/2603.15942
- Scope: Fourier/Möbius operations and type-A Argyres--Douglas classification.
- Boundary: no collision with zero-loop equality/sign law or elementary graph recognition.

## Novelty verdict

No collision located through 2026-08-03. The exact source formulas are known; the equality case,
strict sign classification, arithmetic factorization, pair spectra, and elementary sufficiency theorem
appear new. This remains a documented search result, not a guarantee against unpublished work or
different terminology in singularity theory.

## Significance assessment

Local sign law alone is too small for a renowned general journal. Combined package is materially
stronger:

- exact local classification of every ramified zero-loop vertex;
- explicit Fourier and knot-theoretic structure;
- exact hidden fibres of a Cartan shadow;
- infinitely many two-vertex obstructions absent from current ultrametric criteria;
- complete arbitrary-size recognition on a natural twisted locus;
- unconditional formal verification of arithmetic/combinatorial core.

Hostile review of recognition sufficiency and source-normalization details passed after the
finite-fibre affine formula and exact realization citations were made explicit. See
`HOSTILE_REVIEW.md`.
