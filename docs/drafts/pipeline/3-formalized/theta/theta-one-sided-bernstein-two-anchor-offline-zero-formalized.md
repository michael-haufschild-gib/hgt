# One-sided Bernstein-positive theta gauge with both anchors and an off-line zero — Lean certificate

- **Paper card:** `theta-one-sided-bernstein-two-anchor-offline-zero.md`
- **Lean module:** `GaloisForLFunctions.RHTower.ThetaOneSidedBernsteinGauge` (on top of
  `ThetaCriticalFluxBernstein`, `ThetaPrimeDeletionBernsteinPureRay`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** targeted `lake build`; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound` for all 13 listed theorems; no `sorry`.

`g_c = thetaIntegerShiftGauge c = ∑_m c_m k(·+log m)` (with `c_0 = 0`, `∑|c_m|√m < ∞`);
`g_α = thetaIntegerShiftGauge (oneSidedCoeff α)`; `R_{S,n} = thetaGaugeWeight c (thetaCoprimeLabels S) n`.

| Card item | Lean theorem |
|-|-|
| gauge = weighted atom sum `∑ R_n a_n` (divisor regrouping) | `thetaBaseGauge_eq_weightedAtomSum`, `hasSum_divisorsAntidiagonal_regroup` |
| (7) `D_S g_c` has weights `R_{S,n} = ∑_{m∣n,(n/m,S)=1} c_m√m`; flux formula | `thetaPrimeDeletion_thetaIntegerShiftGauge`, `thetaNormalizedFlux_thetaBaseGauge` |
| all-sieve classification: every `b_{D_S g}` CM ⇔ `c ≥ 0` | `thetaIntegerShiftGauge_allSieve_iff` |
| both anchors ⇒ `c = δ₁`, `g = k` | `thetaIntegerShiftGauge_rigid` (anchors: `integral_exp_mul_thetaIntegerShiftGauge`) |
| 1. rate weights `1-dα`, `1+α`, `1-d²α`; flux completely monotone | `thetaGaugeWeight_oneSided`, `thetaGaugeWeight_oneSided_pos`, `completelyMonotoneOn_flux_oneSided` |
| 2. both anchors | `thetaIntegerShiftGauge_oneSided_anchors` |
| 3. `g_α(x) > 0` for `x ≥ 0` | `thetaIntegerShiftGauge_oneSided_pos` |
| 4. / (4)–(6) `L_w g_α = M_α(w) XiC(iw)`; zero at `σ + iπ/log 2`, `0<σ<1/2` | `integral_cexp_mul_oneSidedGauge`, `exists_offLine_zero_oneSidedGauge` |
| the source is not even | `oneSidedGauge_not_even` |
| `R_{{2},4} = -2κα < 0`: first deleted flux not CM | `oneSidedGauge_deleted_two_not_completelyMonotone` |
