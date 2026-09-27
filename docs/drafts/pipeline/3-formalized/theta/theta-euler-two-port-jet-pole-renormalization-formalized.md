# Finite theta Euler stages have a zero port and a growing-order pole port — Lean certificate

- **Paper card:** `theta-euler-two-port-jet-pole-renormalization.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaEulerTwoPortJetPole`
  (uses `ThetaPrimeDeletionMellin`, `ThetaPrimeDeletionSpectralEscape`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 11 listed theorems; no `sorry`.

`S_P = thetaEulerStageSource P` (sum over `Nat.factoredNumbers P`), `L_P = thetaEulerStageLaplace P`,
`Z_P = thetaEulerStageZeta P`, `G = thetaAtomMellinFactor`, and the meromorphic continuation
`G(w) Z_P(w+1/2) = thetaEulerStageLaplaceExt P w`. `P` is any finite set of primes.

| Card item | Lean theorem |
|-|-|
| (1) `L_P(w) = G(w) Z_P(w+1/2)`, `Re w > -1/2`, with integrability | `integral_cexp_mul_thetaEulerStageSource` (Euler product: `hasSum_factoredNumbers_cpow`) |
| (2) `L_P(1/2) = 0` | `thetaEulerStageLaplace_half` |
| (2) `L_P'(1/2) = Z_P(1)/2` | `hasDerivAt_thetaEulerStageLaplace_half` (with `thetaAtomGammaFactorC_half`) |
| (2) `∏(1 - 1/p) L_P'(1/2) = 1/2` | `prod_one_sub_inv_mul_thetaEulerStage_jet` |
| (3) `s^{|P|} L_P(-1/2+s) → -1/∏ log p` | `tendsto_pow_mul_thetaEulerStageLaplace_left` |
| (3) `L_∅(-1/2) = -1` | `thetaEulerStageLaplace_empty_neg_half` |
| (4) `L_k(1/2) = L_k(-1/2) = 1/2` | `integral_exp_half_mul_thetaCuspFullSource_eq_half` (corpus), `integral_exp_neg_half_mul_thetaCuspFullSource_eq_half` |
| continuation agrees with `L_P`; orders `1` at `+1/2`, `-|P|` at `-1/2` | `thetaEulerStageLaplace_eq_ext`, `meromorphicOrderAt_thetaEulerStageLaplaceExt_half`, `meromorphicOrderAt_thetaEulerStageLaplaceExt_neg_half` |
| divisor-price corollary | `thetaEulerStage_divisor_price` |
| the required left order is unbounded along every exhaustion | `PrimeExhaustion.tendsto_card` |
