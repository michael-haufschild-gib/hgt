# CHMD: the single-prime-power window and prime-2 domination

- **ID:** chmd-single-prime-window-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), unconditional (reduction); the domination itself is open
- **Source:** user pivot 2026-10-16 ("chain-variance domination at a fixed prime power with the explicit weight"); corpus inputs: `phiDoob_markovEnergy_levy_groundState_cancellation`, `phiDoob_mixed_prime_pairing_eq_mixedPhiArchRe_add_phiDoobCoshMass`, `atomPairing_mixed_sub_quad_eq_tsum_integral_phiDoobPrimeJump`, `vonMangoldtAtom_mul_crossCorr_quad_eq_integral_phiDoobPrimeCross`, `sourceEnergy_compactLift`, `riemannHypothesis_iff_forall_phiDoobCoshMass_zero_markovEnergy_nonneg`
- **Statement:** (1) `E(compactLift v) = Λ_∞(Θv) − Σ_n ∫ phiDoobPrimeCross v n` with `Λ_∞(f) = γ(0)∫f² + jumpEnergy f`. (2) Cross terms vanish for `log n ≥ L` when `supp v ⊆ (a, a+L)`; finite-window, prime-blind (`L ≤ log 2`) and single-prime (`L ≤ log 3`) forms. (3) `∫ phiDoobPrimeCross v n ≤ Λ(n)n^{-1/2}(∫_{(a,a+L−log n)}(Θv)² + ∫_{(a+log n,a+L)}(Θv)²)`. (4) On `L ≤ log 3`: `E ≥ 0 ⟺ PrimeTwoDomination v`; RH ⟹ domination on primitive tests; end-strip coercivity ⟹ domination. (5) `vonMangoldtAtom 2 = log 2/√2`.
- **Status:** STATUS MUST-1561. One leaf (`CHMDSinglePrimeWindow`; 17 declarations), standard axioms; `lake env lean` clean; `lake build --old` green; wired.

## Gates
- [x] 0 → 1, [x] 1 → 2, [x] 2 → 3 (`sourceEnergy_compactLift_eq_levy_sub_cross_two`, `integral_phiDoobPrimeCross_le_strips`, `primeTwoDomination_of_riemannHypothesis`)
- [ ] 3 → 4

## What the pivot reduces to
Per prime power `n`, chain variance minus its cosh-mass share is exactly `−∫ phiDoobPrimeCross v n`
(the diagonal of every jump is absorbed by the Φ-smoothed PNT identity), so "domination at `n`"
means anticorrelation of `Θv` at lag `log n`; it fails termwise for positive tests. The honest
fixed-prime-power statement is the window one: on support length `≤ log 3` the whole arithmetic
content is one explicit-weight cross term. The prime-free sufficient condition (end-strip
coercivity of the Lévy form) is quantitative: the corpus archimedean lane (`WeilLevy*`) has
`weilArchRe ≥ 0` for nonnegative tests of support `≤ 12/25` and a deficit of `−0.0033` at `log 2`,
so no present estimate reaches the single-prime window.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDSinglePrimeWindow.lean` — see STATUS MUST-1561 for the declaration list.

## Next
Sign law of the cross terms on the one-signed odd cone (window `≤ 2 log n` pairs opposite signs),
diamagnetic bound `Λ_∞(|f|) ≤ Λ_∞(f)`, prime-free lower bound `E(v) ≥ Λ_∞(Θ|v|)` on windows up
to `log 4`.
