# BRST–Hodge master constraint

- **ID:** brst-hodge-master-constraint
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** [BRIDGE] BRST cohomology, supersymmetric quantum mechanics, and Hodge theory
- **Statement:** For a bounded operator `Q`, the positive operator `H_Q = Q†Q + QQ†` has kernel `ker Q ∩ ker Q†`; when `Q² = 0`, it commutes with both `Q` and `Q†`.

## Goal

Package simultaneous closed/coclosed constraints into one automatically self-adjoint positive
constraint.  The package must directly consume the existing Ward-value and two-sided
constraint-ideal theorems, and the nilpotent case must expose the supersymmetric commutation law.
This is a general hypertranscendental-constraint surface; it is not specific to zeta and is not
claimed to prove an RH-equivalent premise.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, consumer sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem names checked, targeted Lean check green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Physics relation

BRST/Hodge and supersymmetric quantum mechanics use the Laplacian/Hamiltonian

`H_Q = {Q, Q†} = Q†Q + QQ†`.

The exact bounded-Hilbert-space identities needed here are

`Re ⟪ψ, H_Q ψ⟫ = ‖Q ψ‖² + ‖Q† ψ‖²`,

`H_Q ψ = 0 ↔ Q ψ = 0 ∧ Q† ψ = 0`,

and, under `Q² = 0`, `H_Q Q = Q H_Q` and `H_Q Q† = Q† H_Q`.

Primary physics sources include Yang–Lee, *BRST Cohomology and Its Application to QED*
(arXiv:hep-th/9502082), Malik, *BRST cohomology and Hodge decomposition theorem in Abelian
gauge theory* (arXiv:hep-th/9808040), and the explicit Witten/Hodge-Laplacian supersymmetry
relations recorded in arXiv:1607.08714.

## Corpus application

- Reuse `quantumMasterConstraint Q = Q†Q` and the finite positive-sum kernel argument in
  `HTGeometry/FiniteConstraintGroupAverage.lean`.
- Give Ward values a single physicality premise for `H_Q`, or the equivalent pair of `Q`/`Q†`
  physicality premises.
- Give the existing two-sided constraint-ideal theorem the same consolidated premise.
- Add the nilpotent commutation law as genuinely new algebra on top of the generic finite-family
  master constraint.

## Direct-application audit

No existing RH-equivalent declaration currently asks for both `Q ψ = 0` and `Q† ψ = 0`.
Accordingly, this strengthens the reusable HTGeometry constraint API and its Ward/ideal consumers,
but does not discharge the compressed-Euler essential-commutation premise in RHTower.

The nearest live downstream route is
`prime-arch-koszul-spectral-quotient-cancellation-rh.md`.  If that card constructs its proposed
source differential `Q`, the present theorem identifies the residual harmonic sector with the
single positive constraint kernel `ker(Q†Q + QQ†)` and makes the Ward/ideal APIs immediately
available.  It does not discharge that card's open cores: the corpus still lacks the source-built
prime--theta differential, its closed-range/cohomology theorem, and the positive determinant
comparison.  No wrapper theorem is added across this gap.

## Verification boundary

The user prohibited computations and requested efficient builds.  During this phase the proposed
Lean declarations are source-reviewed only: no Lean process, build, lint, numerical experiment, or
axiom audit is run.  The card remains in progress until targeted validation is authorized.

## Log

- 2026-07-14 — physics relation and direct consumer surface identified; card opened before Lean edits.
- 2026-07-14 — source-level Lean surface added in `HTGeometry/BRSTHodgeConstraint.lean` and imported by the HTGeometry umbrella; direct corpus scan found no pre-existing joint `Q`/`Q†` consumer; no computation or build run.
