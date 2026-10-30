# Fourth-power mesh signed saving

- **ID:** fourth-power-mesh-signed-saving
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-3010/opus.md, Question 2
- **Statement:** For every ε > 0 there is C ≥ 0 such that, for every integer J ≥ 2,
  `mobiusDivisorDilationPowerMeshCovariance 4 J ≤ C * (J : ℝ) ^ (3 + ε)`.

## Goal

Prove or refute this exact statement unconditionally and formalize the answer.
Criteria, weaker estimates, and obstructions do not resolve the question.

## Gates

- [x] Exact quantifiers checked in `QuasiRHPowerMeshMeanSquareAbscissa.lean`.
- [ ] Dependency-closed proof or refutation.
- [ ] Lean theorem; foreground `lake --old env lean` audit; standard axioms only;
  owning umbrella import.

## Mathematical state

`RHTower.xi_zero_three_quarters_strip_iff_powerMeshCovariance_subpower` identifies
the target with `∀ ρ : ℂ, xi ρ = 0 → 1/4 ≤ ρ.re ∧ ρ.re ≤ 3/4`.
The covariance differs from the literal tail square energy by a diagonal in
`[0, (9/25)J]`. The head costs at most `(9/25)J³` on this mesh.
Consequently the unpaid term is signed high-dilation cancellation, not either
of these already bounded contributions.

## Approach

Inspect the exact small-quotient kernel, prime-deletion cancellation, and signed
damping identities for a bound uniform in the growing cutoff. Any use of a
strip bound or an equivalent Möbius estimate must be discharged, not assumed.
