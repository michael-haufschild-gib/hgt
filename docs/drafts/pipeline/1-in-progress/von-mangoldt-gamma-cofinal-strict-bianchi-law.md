# Von Mangoldt--Gamma cofinal strict Bianchi law

- **ID:** von-mangoldt-gamma-cofinal-strict-bianchi-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), hostile literature audit passed
- **Source:** Bottom-up closure of cofinal pointed-Ward Gram, Euler prime-power rays, and discrete
  moment strictness
- **Statement:** At positive displacement, every injectively depth-labelled cofinal analytic
  Euler/Gamma--Bianchi Gram is positive definite and has positive determinant.

## Goal

Upgrade the existing cofinal positive-semidefinite result using structure already present in the
Lean body.  Raw Euler atoms are positive discrete moments at logarithmic nodes; dyadic prime powers
give infinite positive support; arbitrary distinct depth labels form a principal submatrix of one
strict consecutive Hankel block.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes scratch `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `infiniteVonMangoldtGammaRawAtom_eq_eulerCoefficient` identifies each raw atom with the Euler
   Dirichlet carrier.
2. `summable_infiniteVonMangoldtGammaRawAtom` supplies all absolute moments.
3. `eulerGeneralizedCoefficient_ray_complete` supplies every positive dyadic logarithmic ray with
   nonzero von Mangoldt coefficient.
4. `HTGeometry.discreteMomentHankel_posDef` upgrades infinite positive support to strict Hankel
   positivity.
5. `infiniteVonMangoldtGammaRawGram_eq_cofinalBianchiGram` transfers strictness to the analytic
   cofinal Bianchi current.

## Paper proof

Set `w_n` equal to the degree-zero raw atom and `λ_n=log(n+2)`.  Then the order-`a` raw atom is
`w_n λ_n^a`; all weights are nonnegative and all absolute moments converge for `x>0`.  For every
finite set of nodes, choose a dyadic ray `(k+1)log 2` outside it.  Euler ray completeness realizes
that node at a power of `2` with nonzero von Mangoldt coefficient, hence strictly positive weight.
The resulting measure has infinite support, so every consecutive moment Hankel block is positive
definite.  If depth labels `a_i` are distinct, the Gram `(m_{a_i+a_j})` is an injective principal
submatrix of a sufficiently large consecutive block, hence is positive definite.  The exact
raw/Bianchi identification gives the analytic statement and positive determinant. `[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaCofinalStrictBianchiLaw.lean`
- Capstone: `vonMangoldtGammaCofinalBianchiGram_posDef_of_injective`
- Determinant: `det_vonMangoldtGammaCofinalBianchiGram_pos_of_injective`

## Hostile literature audit

Classical moment theory says an infinite-support positive measure gives strict finite Hankel
blocks, and standard analytic number theory gives `-ζ'/ζ` as the positive von Mangoldt Dirichlet
series on the real convergence ray.  Searches for the exact conjunction found no paper identifying
the arbitrary-depth pointed Gamma--Bianchi Gram with that logarithmic prime-power moment measure
and proving positive definiteness for every injective depth schedule.

- NIST DLMF, moment and Hankel framework for orthogonal polynomials,
  https://dlmf.nist.gov/18.2
- Berg--Szwarc, *A determinant characterization of moment sequences with finitely many
  mass-points*, https://arxiv.org/abs/1405.7267
- Mainar et al., *Total positivity and high relative accuracy for several classes of Hankel
  matrices*, https://doi.org/10.1002/nla.2550

Verdict: strict infinite-support moment theorem is classical; exact von Mangoldt/Gamma--Bianchi
identification and arbitrary-depth principal-minor law not found. `[NOVELTY SURVIVES HOSTILE SEARCH]`

## Log

- 2026-07-21 — Found in exhaustive semidefinite/Hankel consumer audit.
- 2026-07-21 — Scratch proof passed exactly.
- 2026-07-21 — Direct tree-file Lean check passed.
- 2026-07-21 — Hostile literature audit found no exact joined law.
