# Literal reciprocal sine response: growth and vanishing boundary

- **ID:** LI-CLOCK-SINE-GROWTH-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [actual-current route](../1-in-progress/li-actual-current-small-mass-sinc-scaling.md)
- **Prior work:** [complete-source Volterra positive mass](../3-formalized/li-actual-clock-volterra-positive-mass.md)

## Source identity and strongest survivors

With `S(w)=liEvenCrossActualCurrentClockSeries w`, `F(t)=tS(t²/16)`, `α_q=xiSpectralPoint q`, `r_q=α_q⁻¹`,

`F(t)=Σ_(q:XiZeroCopy) r_q sin(t r_q)`.

Every analytic multiplicity copy contributes once. No square-root branch is used. Source symmetries make the complex sum real; `t=4√w` for `w≥0`.

Unconditionally, `∀B,T₀ ∃t>T₀, F(t)>B`, and `liminf_(w→∞)|S(w)|=0`. These strengthen divergent positive-part mass and rule out a nonzero uniform absolute tail margin. They give no pointwise source sign or RH producer.

## Complete-source interchange

Literal source moment APIs identify `(M_j:ℂ)=Σ_q r_q^(2j+2)`. Compact absolute double-sum domination is

`Σ_qΣ_j |r_q|^(2j+2)T^(2j+1)/(2j+1)! ≤ A T Σ_j(T²/150)^j/(2j+1)!`,

where `A=Σ_q|r_q|²<∞`. Thus the entire sine Taylor series interchanges with every multiplicity copy, matching the already formalized F series. Required APIs: `XiEndpointCentralMomentBoundaryValue.ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment`, `XiRelativeResolventTrace.tsum_xiZeroCopyReciprocalSquare_pow`, `XiCanonicalProduct.xiSpectralPoint_inv_sq_summable`, and the exact second-moment radius.

## RH branch

Real reciprocal frequencies give `S(w)=Σ_q r_q² sinc(4√w r_q)→0` by summable domination. Positive ordinates have exact multiplicity response `F(t)=2Σ_(γ>0)m_γ sin(t/γ)/γ`.

In fact `(1/T)∫₀ᵀF(t)dt=(1/2)log T+O(1)`. For `N(y)=xiZeroCount y`, exact ordinate gap excludes zeros below 10, and integration yields `(2/T)∫_[10,∞)(1−cos(T/y))dN(y)`. Put `Q(y)=y/(2π)log(y/(2πe))+7/8` and `E=N−Q`; existing RVM theorem gives `|E(y)|≤C log(y+2)` after enlarging C on the initial compact interval. Integration by parts leaves error bounded uniformly by `4|E(10)|/T+2∫₁₀∞|E(y)|/y²dy`. Upper boundary vanishes. In the smooth Q term substitute `x=T/y`; integrable `(1−cos x)log x/x²` and tail bound `∫_U∞(1−cos x)/x²≤2/U` give coefficient `(1/π)∫₀∞(1−cos x)/x²dx=1/2`. Hence F is cofinally unbounded above under RH.

Multiplicity identification is `RiemannVonMangoldt.xiZeroCount_eq_pos_sum`; smooth normalization is in `XiPrimeMarkedPhysicalEndpointRVMRelocation`; remainder is in `XiZeroCountRVMRemainder`. The Stieltjes/mean transfer is paper-only.

## Non-RH branch

Square summability implies reciprocal frequencies tend to zero cofinally. Therefore the positive maximum `b=max_q|Im r_q|` is attained by a finite packet, with a strict remainder gap `b₂<b`. Reflection/conjugation preserve analytic multiplicity; the real-coordinate source gap excludes zero real frequencies.

Top quartets with frequencies `a_ℓ+ib`, `a_ℓ>0`, and weights `m_ℓ>0` give

`F(t)=e^(bt)P(t)+o(e^(bt))`, `P(t)=2Σ_ℓm_ℓ[a_ℓ sin(a_ℓt)−b cos(a_ℓt)]`.

Remainder is bounded by `L e^(−bt)+A t e^(b₂t)`. Distinct positive frequencies give zero mean and positive mean square for P, forcing fixed cofinal positive and negative amplitudes. Thus S has limsup `+∞`, liminf `−∞`, and cofinal zeros, **conditional on failure of RH**. Continuity of S is already formalized. Combining branches gives the unconditional survivors above.

## Novelty and limits

Reciprocal sine growth uses classical mechanisms; RH-equivalent decay/boundedness is a terminal divisor classification, not an independently proved source constraint. Prior actual Euler-jet oscillation concerns a different germ and supplies no negative literal S witness. No RH proof/falsification or world-novelty claim.

## Plan

1. Formalize branch-free literal sine identity and complete-source absolute interchange — complete in [sine-source card](../3-formalized/li-actual-clock-reciprocal-sine-source.md); all 12 public axioms foundational, final exact check passed.
2. Formalize real-frequency decay under RH — complete in `LiEvenCrossActualClockSineDecay.lean`; all four public axioms foundational, named build and final exact check passed. RH remains an explicit premise.
3. Finite attained top-frequency packet and strict tail gap are formalized in `LiEvenCrossActualClockTopFrequency.lean`, from `¬RiemannHypothesis`, with all multiplicity-copy ties included. Named build, final exact check and all nine public axiom audits passed. Oscillatory amplitudes and exact RVM mean transfer remain paper-only.
4. Promote only exact unconditional capstones after named builds, direct checks and axiom audits.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineSource`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineDecay`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockTopFrequency`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockUnboundedResponse`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineOscillation`, `GaloisForLFunctions.HTGeometry.OneSubCosKernelIntegral`, `GaloisForLFunctions.RHTower.XiOrdinateCosineMass`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineMeanLaw`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into `GaloisForLFunctions.RHTower` / `GaloisForLFunctions.HTGeometry`):
`GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineSource`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineDecay`,
`GaloisForLFunctions.RHTower.LiEvenCrossActualClockTopFrequency`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockUnboundedResponse`,
`GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineOscillation` (new), `GaloisForLFunctions.HTGeometry.OneSubCosKernelIntegral` (new),
`GaloisForLFunctions.RHTower.XiOrdinateCosineMass` (new), `GaloisForLFunctions.RHTower.LiEvenCrossActualClockSineMeanLaw` (new).

| Claim | Declaration |
|-|-|
| `F(t)=Σ_q r_q sin(t r_q)`, every copy once, real | `liEvenCrossActualClockResponse_ofReal_eq_tsum_sine`, `im_tsum_liEvenCrossActualClockSineAtom_eq_zero` |
| Complete-source absolute interchange | `summable_liEvenCrossActualClockSineTaylorTerm`, `tsum_liEvenCrossActualClockSineTaylorTerm`, `norm_liEvenCrossActualClockSineTaylorTerm_le` |
| Unconditional `∀B,T₀ ∃t>T₀, F(t)>B` | `liEvenCrossActualClockResponse_unboundedAbove_cofinally` |
| Unconditional `liminf_{w→∞}|S(w)|=0` | `liminf_abs_liEvenCrossActualCurrentClockSeries`, `liEvenCrossActualCurrentClockSeries_frequently_abs_lt` |
| RH: `S(w)→0` | `tendsto_liEvenCrossActualCurrentClockSeries_atTop_zero_of_rh` |
| RH: `F(t)=2Σ_{γ>0} m_γ sin(t/γ)/γ` | `liEvenCrossActualClockResponse_eq_two_mul_tsum_pos_of_rh`, `liEvenCrossActualClockResponse_eq_tsum_ordinate_of_rh` |
| RH: `(1/T)∫₀ᵀF=(1/2)log T+O(1)` | `exists_abs_mean_liEvenCrossActualClockResponse_sub_half_log_le_of_rh` via `integral_liEvenCrossActualClockResponse_of_rh` |
| Stieltjes/RVM mean transfer (unconditional ordinate form) | `exists_abs_xiOrdinateCosineMass_sub_le`, `xiOrdinateCosine_window_eq` (Abel window), `exists_abs_xiZeroCount_sub_smooth_le_sqrt`, `xiOrdinateSmoothTerm_eq` (substitution `x=T/y`), `abs_xiOrdinateSmoothTerm_sub_le` |
| `∫₀^∞(1-cos x)/x²=π/2`, tail `≤2/U`, log-moment integrable | `integral_Ioi_oneSubCosKernel`, `integral_Ioi_oneSubCosKernel_le`, `integrableOn_oneSubCosKernel_mul_log` |
| ¬RH: finite attained top packet, strict gap `b₂<b` | `exists_liEvenCrossActualClockTopPacket_of_not_rh` |
| ¬RH: `F=e^{bt}P+O(Le^{-bt}+Ate^{b₂t})`, `e^{-bt}F-P→0` | `liEvenCrossActualClockResponse_topPacket_of_not_rh` |
| ¬RH: fixed cofinal positive and negative amplitudes | `liEvenCrossActualClockResponse_oscillation_of_not_rh` (positive value of `P`: `exists_liClockTopSineProfile_pos`, bounded primitive + recurrence, replacing the mean-square step) |
| ¬RH: `limsup S=+∞`, `liminf S=-∞`, cofinal zeros | `liEvenCrossActualCurrentClockSeries_frequently_gt_of_not_rh`, `..._frequently_lt_of_not_rh`, `..._frequently_eq_zero_of_not_rh` |
| Real frequencies nonzero | `re_inv_xiSpectralPoint_ne_zero` |

## Log

- 2026-09-30 — Independent literal-source audit closed multiplicity normalization, both branches and exact mean-law remainder. Root checked existing source series and original packet scope. New consequences remain paper-only; card recorded before hard Lean work.
- 2026-09-30 — Branch-free full complex sine identity and absolute double-series interchange formalized, named build and final direct checks passed. RH decay and finite top-frequency isolation assigned to disjoint leaves; growth/mean transfer remain paper-only.
- 2026-09-30 — Literal RH-conditional decay is Lean-closed by complete squared-weight DCT. Structural [unbounded-support alternative](../3-formalized/li-clock-unbounded-support-response-growth.md) is independently paper-audited twice for the unconditional cofinal-unbounded survivor, avoiding the RH/RVM case split; stronger all-R kernel growth and unconditional cofinal response height are now Lean-closed in three leaves, with all 12 public axiom audits foundational. Signed non-RH packet asymptotics and RH RVM mean remain paper-only.
- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
