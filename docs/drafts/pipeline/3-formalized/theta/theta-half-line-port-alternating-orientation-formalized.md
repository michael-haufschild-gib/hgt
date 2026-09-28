# Alternating orientation of the literal theta half-line port — Lean certificate

- **Paper card:** `theta-half-line-port-alternating-orientation.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaHalfLinePortOrientation` ((1)–(4), (7a)),
  `GaloisForLFunctions.RHTower.ThetaHalfLinePortCrossings` ((5)–(7), witnesses),
  `GaloisForLFunctions.RHTower.ThetaHalfLinePortGauge` ((7b)–(7e), `E₁`, (8));
  corpus `CausalThetaHalfLaplace` (half-line transform; its integration-by-parts law was extended
  to the closed half-plane), `HedenmalmThetaEigenODE` (9), `SourceZeroHedenmalmMidpointTwoJet` (10);
  general layer `GaloisForLFunctions.HTGeometry.RealZeroCrossingCount`
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** targeted `lake build`; `lake env lean` audit clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound` for all audited theorems; no `sorry`.

Dictionary: `H(w) = thetaHalfLaplace w = ∫₀^∞ e^{wu} k(u) du`, `k = thetaCuspFullSource`,
`ν = -deriv thetaCuspFullSource`, `X(γ) = Xi γ` (`XiC_ofReal`), `b(γ) = thetaHalfSineResponse γ`,
`D(α, γ) = thetaHalfPortImbalance γ α`, `N(T) = xiPosZeroCount T`,
`S(T) = xiSimpleCriticalZeroCount T`, `U(T) = xiSimpleUpCrossingCount T`,
`V(T) = xiSimpleDownCrossingCount T`, `A(T) = xiOddHigherCriticalCount T`,
`F# = halfPortReflect F`, `X(w) = thetaSymmetrizedPort w`, `E₀ = thetaCircularPort`,
`E₁ = thetaMomentPort λ`, `u_z = hedenmalmCausalVolterra z`.

| Card item | Lean theorem |
|-|-|
| `X = H(i·) + H(-i·)` | `thetaHalfLaplace_add_neg`, `ofReal_Xi_eq_thetaHalfLaplace` |
| (1) `wH(-w) = ∫(1 - e^{-wu})ν`, `Re > 0` on `Re w ≥ 0`, `w ≠ 0`; `H(0) > 0` | `mul_thetaHalfLaplace_neg_of_nonneg`, `re_mul_thetaHalfLaplace_neg_pos_of_nonneg`, `thetaHalfLaplace_zero`, `integral_Ioi_thetaCuspFullSource_pos` |
| `H(-w)` zero-free on the closed right half-plane; both halves nonzero at every Xi zero | `thetaHalfLaplace_neg_ne_zero_of_nonneg`, `thetaHalfLaplace_ne_zero_of_add_neg_eq_zero` |
| (2) `D(0, γ) = 0` | `thetaHalfPortImbalance_zero`, `thetaHalfLaplace_conj` |
| (3) `H(iγ) = i b(γ)`, `γ b(γ) = ∫(1 - cos γu)ν > 0` | `thetaHalfLaplace_I_mul_of_Xi_eq_zero`, `mul_thetaHalfSineResponse_eq`, `thetaHalfSineResponse_pos`, `Xi_eq_two_mul_thetaHalfCosineResponse` |
| (4) `∂_α D(0, γ) = -2 b(γ) X'(γ)`; `X' = -2 Im H'(iγ)` | `hasDerivAt_thetaHalfPortImbalance`, `hasDerivAt_Xi_thetaHalfLaplace`, `deriv_thetaHalfLaplace_conj` |
| local factorization of `X`; simple ⇔ `X' ≠ 0` | `exists_Xi_localZeroFactor`, `xiRealOrder_eq_one_iff` (general: `HasLocalZeroFactor`, `exists_down_crossing_between`) |
| (5) `U + V = S`, `|U - V| ≤ A + 1`, `S + 3A ≤ N` | `xiSimpleUp_add_down`, `xiSimpleUp_le`, `xiSimpleDown_le`, `xiSimpleCritical_add_three_mul_oddHigher_le` (general: `card_le_card_add_one_of_separated`) |
| (6) `min(U, V) ≥ (4S - N)/6 - 1/2` | `xiSimpleUp_ge`, `xiSimpleDown_ge` |
| (7) `liminf U/N, liminf V/N ≥ 5/18` | `eventually_xiSimpleUp_ge`, `eventually_xiSimpleDown_ge` (from `two_thirds_simpleCritical_epsilon`), `tendsto_xiPosZeroCount_atTop` |
| `D > 0` and `D < 0` arbitrarily high and close to `α = 0` | `exists_thetaHalfPortImbalance_pos`, `exists_thetaHalfPortImbalance_neg`, `exists_simpleCrossing_above` |
| (7a) `X'(γ) = -2∫ u k(u) sin(γu) du` | `hasDerivAt_Xi_eq_moment`, `deriv_Xi_eq_moment` |
| zero-free finite-type ⇒ `exp(aw + b)` | `exists_eq_exp_affine_of_ne_zero`, `natDegree_le_one_of_re_eval_le` |
| (7b)–(7d) gauge rigidity `g ≡ 1` | `thetaHalfLaplace_gauge_eq_one`, `card_le_of_sin_eq_zero`, `halfPortReflect_thetaHalfLaplace`, `halfPortReflect_thetaSymmetrizedPort` |
| exact symmetrization ⇔ anti-reflected correction | `halfPortReflect_add_eq_iff` |
| (7e) `|E₀|² - |E₀#|² = 2 Re(w)|X|²`; `E₀` vanishes at critical zeros | `thetaCircularPort_imbalance`, `thetaCircularPort_add_reflect`, `thetaCircularPort_eq_zero` |
| `E₁(iγ) = -iλX'(γ)`, normal derivative `2λX'(γ)²`, `E₁# = -E₁` at zeros of `X` | `thetaMomentPort_mul_I`, `hasDerivAt_thetaMomentPort_imbalance`, `halfPortReflect_thetaMomentPort_of_eq_zero`, `thetaMomentPort_add_reflect` |
| (8) `u_z(0) = -iH(-iz)`, nonzero at every Xi zero | `hedenmalmCausalVolterra_zero`, `hedenmalmCausalVolterra_zero_ne_zero` |
| (9) `u_z' = -izu_z - ik` | `hedenmalmCausalVolterra_thetaEigen_ode` (corpus) |
| (10) midpoint two-jet classifier | `sourceZeroHedenmalmMidpointTwoJet_iff_re_eq_half` (corpus) |
