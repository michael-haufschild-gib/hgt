# Completed prime--Gamma central-jet descent law

- **ID:** completed-prime-gamma-central-jet-descent-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), hostile literature audit passed
- **Source:** Bottom-up closure of completed determinant reflection and Schwarz-equivariance theorems
- **Statement:** Every central jet of the completed odd-log-derivative Hankel determinant is real,
  and every odd central jet vanishes.

## Goal

Join the two independent involutions already proved for the explicit completed prime--Gamma Hankel
determinant.  Their common fixed point forces the full central Taylor jet into the real even
subspace; this is strictly stronger than the existing even-order-at-a-zero conclusion.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact fixed-point law
- [x] Complete paper proof with no open dependency
- [x] Lean source passes scratch `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `completedOddLogDerivHankelDet_one_sub` gives functional-equation invariance under
   `σ ↦ 1 - σ`.
2. `completedOddLogDerivHankelDet_conj` gives Schwarz equivariance.
3. `iteratedDeriv_comp_const_sub` and `iteratedDeriv_conj_conj` propagate both involutions through
   every derivative.

## Paper proof

Write `D_n(σ)` for the determinant.  Schwarz equivariance implies
`D_n^(m)(conj σ) = conj(D_n^(m)(σ))`; at `σ=1/2`, every jet is real.  Functional-equation
invariance implies
`D_n^(m)(1-σ)=(-1)^m D_n^(m)(σ)`; at the same fixed point, odd `m` gives
`D_n^(m)(1/2)=-D_n^(m)(1/2)`, hence zero.  Thus the full central jet is real and even.
`[PROVED HERE]`

## Formalization

- Module: `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaCentralJetDescentLaw.lean`
- Capstone: `completedOddLogDerivHankelDet_centralJet_real_even_law`

## Hostile literature audit

Closest literature treats three separate objects: central derivatives of `ξ`, Li/Keiper
logarithmic derivatives, and parameter-dependent Hankel determinants from orthogonal-polynomial
weights.  Searches also found moment-Hankel conditions assembled from central logarithmic
derivatives.  None defines the moving Hankel determinant whose entries are odd derivatives of
`ξ'/ξ`, then proves the joined all-size, all-jet real-even fixed-point law.

- McPhedran et al., *Relations and positivity results for the derivatives of the Riemann ξ
  function*, https://doi.org/10.1016/j.cam.2003.09.003
- Coffey, *New results concerning power series expansions of the Riemann xi function and the
  Li/Keiper constants*, https://doi.org/10.1098/rspa.2007.0212
- Chen--Chen--Fan, *Perturbed Hankel determinant, correlation functions and Painlevé equations*,
  https://arxiv.org/abs/1507.05261

Verdict: reflection/reality of scalar `ξ` jets is classical; exact completed-log-derivative Hankel
determinant jet law not found. `[NOVELTY SURVIVES HOSTILE SEARCH]`

## Log

- 2026-07-21 — Found while auditing every semidefinite/Hankel closure and its analytic consumers.
- 2026-07-21 — Scratch proof passed exactly.
- 2026-07-21 — Direct tree-file Lean check passed.
- 2026-07-21 — Hostile literature audit found no exact joined law.
