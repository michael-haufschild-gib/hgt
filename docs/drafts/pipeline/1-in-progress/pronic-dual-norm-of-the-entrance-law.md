# The pronic dual norm of the arithmetic entrance law

- **ID:** pronic-entrance-dual
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** BezoutValuationIncidence README §5, research topic 6 ("the chain on the right norm")
- **Statement:** The entrance functional `e_η` of the damping chain is bounded on the pronic
  `ℓ²` (weight `1/(n(n+1))`) if and only if `η > 1/2`; its pronic dual norm is
  `∑ k^(-2η)` up to bounded factors.

## Goal
BVI research topic 6 asks to carry the compactness and semigroup law of the centred damped
transition `P̊_η = P_η − e_η` from `c₀` to the pronic `ℓ²`, where the receiver's critical
energy lives, **or show no such version exists**. This card answers it: no such version exists
at or below half damping, and the obstruction is exactly the centring. The threshold `1/2` —
the receiver's damping threshold, the parity barrier's number, and the entrance-tail barrier's
number — is here derived from size bias and `ℓ²` duality alone, with no zero input: the pronic
dual weight `k(k+1)` cancels exactly one of the two powers of `k` that the size-biased
discrete derivative of the zeta power law carries, leaving `∑ k^(-2η)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (two-sided Bernoulli bounds; `∑ k^(-2η)` dichotomy)
- [x] 2 → 3  formalized: `GaloisForLFunctions/BezoutValuationIncidence/PronicDualNormOfTheEntranceLaw.lean`
- [ ] 3 → 4  publication-ready

## Approach
`e_η(k) = ρ_η k (k^{-1-η} − (k+1)^{-1-η})`. Bernoulli's inequality at exponent `1+η`, applied
at `s = 1/k` and at `s = −1/(k+1)`, gives the two-sided bound
`ρ_η(1+η) k^{-η}/(k+1+η) ≤ e_η(k) ≤ ρ_η(1+η) k^{-η}/(k+1)`.
Hence `e_η(k)² k(k+1) ≍ k^{-2η}`, summable exactly for `η > 1/2`. Cauchy–Schwarz turns the
finite dual norm into a bounded pronic functional above the threshold; the truncated dual
vectors `b = e_η · k(k+1)` realise pairing-to-norm ratio `√S_N → ∞` at or below it; and the
single power `k^{(η+1/2)/2}` is a pronic-square-summable sequence with divergent entrance
pairing for every `η < 1/2`. The surviving object is the reciprocal observable `e_η(k)/k`,
whose pronic dual norm `≍ ∑ k^{-2-2η}` is finite at every damping.

## Lean
- `arithmeticDampingEntrance_le`, `arithmeticDampingEntrance_ge` — two-sided Bernoulli bounds
- `summable_arithmeticDampingEntrance_pronicDual_iff` — the dichotomy at `1/2`
- `exists_pronicPairing_bound` — bounded functional above half damping
- `exists_pronicPairing_gt` — unboundedness at or below half damping
- `exists_pronicWitness_not_summable_pairing` — explicit divergent pronic witness below `1/2`
- `summable_arithmeticDampingEntrance_reciprocal_pronicDual` — the surviving observable

## Log
- 2026-10-22 — created; paper proof and Lean module written
