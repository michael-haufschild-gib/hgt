import GaloisForLFunctions.BiScaleUncertainty.MultiShellOriginBudgetAndGlobalPrimeCollarSynthesis
import GaloisForLFunctions.BiScaleUncertainty.HyperbolicMultiplierIncrementAndOddSignCoercivity

/-!
# Pillar XIX: Unconditional Signed Weil Functional Coercivity & the RH Explicit-Formula Bridge

This module develops **Pillar XIX** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), synthesizing Pillars III, VI, XIV, XV, XVI, XVII, and
XVIII into **completely unconditional theorems** on the explicit-formula test spaces
`RealEvenPolarTestFn`, `RealSmoothEvenPolarTestFn`, and their hyperbolic multiplier images
`coshMultiplier α g.source` / `sinhMultiplier α g.source`.

Every theorem in this module is **100% unconditional**—taking only a test function
`g : RealEvenPolarTestFn` (or `RealSmoothEvenPolarTestFn`) and a natural number scale `M : ℕ`, with
**zero** blindness assumptions, **zero** derivative / spectral-second-moment ($S(f)$) hypotheses,
and **zero** abstract weight or disjointness hypotheses.

## Main Unconditional Results

1. **`dyadicNyquistCoerciveConstant` & `dyadicNyquistCoerciveConstant_pos`**:
   For every `M : ℕ` (`N = M + 2 ≥ 2`), the concrete Nyquist coercive constant
   $$\mathcal{C}_{\mathrm{Nyq}}(N)
     := \sum_{k=0}^{N-1} \bigl(\log(N+k+1) - \log(N+k)\bigr)\left(\frac{2}{\sqrt{N+k+1}} - \frac{2}{N+k+1}\right)$$
   is strictly positive (`0 < dyadicNyquistCoerciveConstant (M + 2)`).
2. **`RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy`**:
   Unconditional identity on `RealEvenPolarTestFn`:
   $$\operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
     = \Omega(0)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re} + \operatorname{biScaleLevyEnergy}(g.\mathrm{source}).$$
3. **`RealEvenPolarTestFn.unconditional_dyadic_signed_weil_lower_bound` &
   `RealSmoothEvenPolarTestFn.unconditional_dyadic_signed_weil_lower_bound`**:
   For EVERY `g : RealEvenPolarTestFn` (or `RealSmoothEvenPolarTestFn`) and EVERY `M : ℕ`
   (`N = M + 2`), with **zero hypotheses**:
   $$\bigl(\Omega(0) + \mathcal{C}_{\mathrm{Nyq}}(M+2)\bigr)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
   $$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
     + \sum_{k=0}^{M+1} \bigl(\log(M+2+k+1) - \log(M+2+k)\bigr)\,\frac{2}{\sqrt{M+2+k+1}}\,
       (\operatorname{weilTest}\,g\,g\,(\log(M+2+k))).\mathrm{re}.$$
4. **`RealEvenPolarTestFn.unconditional_coshMultiplier_dyadic_signed_coercivity`**:
   For EVERY `g : RealEvenPolarTestFn`, `α : ℝ`, and `M : ℕ`, the hyperbolic multiplier lift
   simultaneously controls both the base energy `autocorr g.source 0` and the odd-multiplier energy
   `autocorr (sinhMultiplier α g.source) 0`:
   $$\mathcal{C}_{\mathrm{Nyq}}(M+2)\,\bigl(h_g(0) + h_{S_\alpha g}(0)\bigr)
     \;\le\; \operatorname{biScaleLevyEnergy}(C_\alpha g)
       + \sum_{k=0}^{M+1} \bigl(\log(M+2+k+1) - \log(M+2+k)\bigr)\,\frac{2}{\sqrt{M+2+k+1}}\,
         h_{C_\alpha g}(\log(M+2+k)).$$
-/

open MeasureTheory Set Filter
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open RHTower.EvenSector
open scoped RealInnerProductSpace BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ## §1. The Concrete Dyadic Nyquist Coercive Constant & Its Strict Positivity -/

/-- The concrete critical-line Nyquist coercive constant on the dyadic window `[N, 2N)`:
$$\mathcal{C}_{\mathrm{Nyq}}(N)
  = \sum_{k=0}^{N-1} \bigl(\log(N+k+1) - \log(N+k)\bigr)\left(\frac{2}{\sqrt{N+k+1}} - \frac{2}{N+k+1}\right).$$ -/
def dyadicNyquistCoerciveConstant (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)) *
      (2 / Real.sqrt ((N + k + 1 : ℕ) : ℝ) - 2 / ((N + k + 1 : ℕ) : ℝ))

/-- For every integer `m ≥ 2`, `0 < 2 / √m - 2 / m`. -/
theorem two_div_sqrt_sub_two_div_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < 2 / Real.sqrt (m : ℝ) - 2 / (m : ℝ) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  have hm_gt1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 1 < m)
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_pos
  have hsqrt_lt : Real.sqrt (m : ℝ) < (m : ℝ) := by
    have hsq : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_pos.le
    have hgt1 : 1 < Real.sqrt (m : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt zero_le_one hm_gt1
    nlinarith
  exact sub_pos.mpr (div_lt_div_of_pos_left two_pos hsqrt_pos hsqrt_lt)

/-- **Unconditional Strict Positivity of `dyadicNyquistCoerciveConstant (M + 2)`:**
For every `M : ℕ`, `0 < dyadicNyquistCoerciveConstant (M + 2)`. -/
theorem dyadicNyquistCoerciveConstant_pos (M : ℕ) :
    0 < dyadicNyquistCoerciveConstant (M + 2) := by
  unfold dyadicNyquistCoerciveConstant
  refine Finset.sum_pos (fun k _ => ?_) ⟨0, Finset.mem_range.mpr (by omega)⟩
  have h1 : 1 ≤ M + 2 + k := by omega
  have h2 : 2 ≤ M + 2 + k + 1 := by omega
  exact mul_pos (log_succ_sub_log_pos h1) (two_div_sqrt_sub_two_div_pos h2)

/-! ## §2. Unconditional Signed Weil Functional Coercivity on `RealEvenPolarTestFn` -/

/-- **Unconditional Pole-Eliminated Weil–Lévy Identity on `RealEvenPolarTestFn`:**
For every `g : RealEvenPolarTestFn`,
`weilArchRe (weilTest g g) = Ω(0) * (weilTest g g 0).re + biScaleLevyEnergy g.source`. -/
theorem RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy
    (g : RealEvenPolarTestFn) :
    WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) =
      EF.gammaBracket 0 * (EF.weilTest g.1.1.1 g.1.1.1 0).re +
        biScaleLevyEnergy g.source := by
  rw [g.weilArchRe_eq_levy]
  congr 1
  unfold biScaleLevyEnergy archLevySinhWeight
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [g.autocorr_eq 0, g.autocorr_eq x]

/-- **Unconditional Dyadic-Window Signed Weil Lower Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `M : ℕ` (with zero hypotheses on `g` or `M`),
$$\bigl(\Omega(0) + \mathcal{C}_{\mathrm{Nyq}}(M+2)\bigr)\,(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
$$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + \sum_{k=0}^{M+1} \bigl(\log(M+2+k+1) - \log(M+2+k)\bigr)\,\frac{2}{\sqrt{M+2+k+1}}\,
    (\operatorname{weilTest}\,g\,g\,(\log(M+2+k))).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_dyadic_signed_weil_lower_bound
    (g : RealEvenPolarTestFn) (M : ℕ) :
    (EF.gammaBracket 0 + dyadicNyquistCoerciveConstant (M + 2)) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((M + 2 + k : ℕ) : ℝ))).re := by
  have hN : 2 ≤ M + 2 := by omega
  have hcoerc := global_dyadic_nyquist_signed_coercivity
    g.contDiff_source g.hasCompactSupport_source hN
  change dyadicNyquistCoerciveConstant (M + 2) * autocorr g.source 0 ≤ _ at hcoerc
  rw [RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g, ← g.autocorr_eq 0]
  have hsum_eq :
      (∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((M + 2 + k : ℕ) : ℝ))).re) =
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            autocorr g.source (Real.log ((M + 2 + k : ℕ) : ℝ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [g.autocorr_eq]
  rw [hsum_eq]
  linarith

/-- **Unconditional Single-Node Signed Weil Lower Bound on `RealEvenPolarTestFn`:**
For EVERY `g : RealEvenPolarTestFn` and EVERY `n : ℕ` (testing at integer node `n + 2 ≥ 2` with
zero hypotheses on `g` or `n`),
$$\left(\Omega(0) + \bigl(\log(n+3) - \log(n+2)\bigr)\left(\frac{2}{\sqrt{n+3}} - \frac{2}{n+3}\right)\right)(\operatorname{weilTest}\,g\,g\,0).\mathrm{re}$$
$$\le\; \operatorname{weilArchRe}(\operatorname{weilTest}\,g\,g)
  + \bigl(\log(n+3) - \log(n+2)\bigr)\,\frac{2}{\sqrt{n+3}}\,
    (\operatorname{weilTest}\,g\,g\,(\log(n+2))).\mathrm{re}.$$ -/
theorem RealEvenPolarTestFn.unconditional_single_node_signed_weil_lower_bound
    (g : RealEvenPolarTestFn) (n : ℕ) :
    (EF.gammaBracket 0 +
        (Real.log ((n + 3 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ)) *
          (2 / Real.sqrt ((n + 3 : ℕ) : ℝ) - 2 / ((n + 3 : ℕ) : ℝ))) *
        (EF.weilTest g.1.1.1 g.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1 g.1.1.1) +
        (Real.log ((n + 3 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ)) *
          (2 / Real.sqrt ((n + 3 : ℕ) : ℝ)) *
          (EF.weilTest g.1.1.1 g.1.1.1 (Real.log ((n + 2 : ℕ) : ℝ))).re := by
  have hn2 : 2 ≤ n + 2 := by omega
  have hcell := nyquist_cell_adaptive_signed_coercivity
    g.contDiff_source g.hasCompactSupport_source (k := 0) hn2
  have hN_ge1 : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 2)
  have hinv_le1 : 1 / ((n + 2 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have horig_nn :
      0 ≤ ∫ y in Ioc 0 (Real.log ((n + 2 + 1 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ)),
          (autocorr g.source 0 - autocorr g.source y) * archLevySinhWeight y := by
    refine setIntegral_nonneg measurableSet_Ioc fun y hy => ?_
    exact mul_nonneg
      (autocorr_sub_nonneg g.hasCompactSupport_source g.contDiff_source.continuous y)
      (archLevySinhWeight_pos hy.1).le
  have horig_drop :
      (1 / ((n + 2 : ℕ) : ℝ)) *
          (∫ y in Ioc 0 (Real.log ((n + 2 + 1 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ)),
            (autocorr g.source 0 - autocorr g.source y) * archLevySinhWeight y) ≤
        ∫ y in Ioc 0 (Real.log ((n + 2 + 1 : ℕ) : ℝ) - Real.log ((n + 2 : ℕ) : ℝ)),
          (autocorr g.source 0 - autocorr g.source y) * archLevySinhWeight y := by
    nlinarith
  have h2N_ge :
      Real.log ((n + 2 + 0 + 1 : ℕ) : ℝ) ≤ Real.log ((2 * (n + 2) : ℕ) : ℝ) := by
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast (by omega : n + 2 + 0 + 1 ≤ 2 * (n + 2))
  have hshift_le_dyadic :
      (∫ x in Real.log ((n + 2 + 0 : ℕ) : ℝ)..Real.log ((n + 2 + 0 + 1 : ℕ) : ℝ),
          (autocorr g.source 0 - autocorr g.source x) * archLevySinhWeight x) ≤
        ∫ x in Real.log ((n + 2 : ℕ) : ℝ)..Real.log ((2 * (n + 2) : ℕ) : ℝ),
          (autocorr g.source 0 - autocorr g.source x) * archLevySinhWeight x := by
    have hle1 : Real.log ((n + 2 + 0 : ℕ) : ℝ) ≤ Real.log ((n + 2 + 0 + 1 : ℕ) : ℝ) := by
      refine Real.log_le_log (by positivity) ?_
      exact_mod_cast (by omega : n + 2 + 0 ≤ n + 2 + 0 + 1)
    have hle2 : Real.log ((n + 2 : ℕ) : ℝ) ≤ Real.log ((2 * (n + 2) : ℕ) : ℝ) := by
      refine Real.log_le_log (by positivity) ?_
      exact_mod_cast (by omega : n + 2 ≤ 2 * (n + 2))
    rw [intervalIntegral.integral_of_le hle1, intervalIntegral.integral_of_le hle2]
    have hint := integrableOn_biScaleLevyIntegrand g.contDiff_source g.hasCompactSupport_source
    have hpos_start : 0 < Real.log ((n + 2 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < n + 2))
    refine setIntegral_mono_set
      (hint.mono_set (fun x hx => lt_trans hpos_start hx.1)) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact mul_nonneg
        (autocorr_sub_nonneg g.hasCompactSupport_source g.contDiff_source.continuous x)
        (archLevySinhWeight_pos (lt_trans hpos_start hx.1)).le
    · refine Eventually.of_forall fun x hx => ?_
      have h0 : n + 2 + 0 = n + 2 := by omega
      rw [h0] at hx
      exact ⟨hx.1, le_trans hx.2 h2N_ge⟩
  have hglobal := origin_add_dyadic_window_levy_le_biScaleLevyEnergy
    g.contDiff_source g.hasCompactSupport_source hn2
  rw [RealEvenPolarTestFn.weilArchRe_eq_gamma_add_biScaleLevyEnergy g, ← g.autocorr_eq 0,
    ← g.autocorr_eq (Real.log ((n + 2 : ℕ) : ℝ))]
  have hnat0 : n + 2 + 0 = n + 2 := by omega
  have hnat1 : n + 2 + 0 + 1 = n + 3 := by omega
  rw [hnat0, hnat1] at hcell hshift_le_dyadic
  linarith

/-- **Unconditional Dyadic-Window Signed Weil Lower Bound on `RealSmoothEvenPolarTestFn`:**
Immediate unconditional specialization of `unconditional_dyadic_signed_weil_lower_bound` to smooth
EWU test functions `g : RealSmoothEvenPolarTestFn`. -/
theorem RealSmoothEvenPolarTestFn.unconditional_dyadic_signed_weil_lower_bound
    (g : RealSmoothEvenPolarTestFn) (M : ℕ) :
    (EF.gammaBracket 0 + dyadicNyquistCoerciveConstant (M + 2)) *
        (EF.weilTest g.1.1.1.1 g.1.1.1.1 0).re ≤
      WeilOneSided.weilArchRe (EF.weilTest g.1.1.1.1 g.1.1.1.1) +
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            (EF.weilTest g.1.1.1.1 g.1.1.1.1 (Real.log ((M + 2 + k : ℕ) : ℝ))).re :=
  RealEvenPolarTestFn.unconditional_dyadic_signed_weil_lower_bound g.toRealEvenPolar M

/-! ## §3. Unconditional Hyperbolic Multiplier Dyadic Synthesis (`OWU` / `HF` / `CHMD` Bridge) -/

/-- `coshMultiplier α f` is `C²` whenever `f ∈ C²(ℝ)`. -/
theorem contDiff_coshMultiplier (α : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (coshMultiplier α f) := by
  unfold coshMultiplier
  exact (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).mul hf

/-- `sinhMultiplier α f` is `C²` whenever `f ∈ C²(ℝ)`. -/
theorem contDiff_sinhMultiplier (α : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (sinhMultiplier α f) := by
  unfold sinhMultiplier
  exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).mul hf

/-- **Unconditional Hyperbolic Multiplier Dyadic Nyquist Signed Coercivity:**
For EVERY `g : RealEvenPolarTestFn`, EVERY `α : ℝ`, and EVERY `M : ℕ` (with zero hypotheses!),
the `coshMultiplier α g.source` Lévy energy and signed Nyquist sum simultaneously control **both**
the base energy `autocorr g.source 0` and the odd hyperbolic multiplier energy
`autocorr (sinhMultiplier α g.source) 0`:
$$\mathcal{C}_{\mathrm{Nyq}}(M+2)\,\bigl(h_g(0) + h_{S_\alpha g}(0)\bigr)$$
$$\le\; \operatorname{biScaleLevyEnergy}(C_\alpha g)
  + \sum_{k=0}^{M+1} \bigl(\log(M+2+k+1) - \log(M+2+k)\bigr)\,\frac{2}{\sqrt{M+2+k+1}}\,
    h_{C_\alpha g}(\log(M+2+k)).$$ -/
theorem RealEvenPolarTestFn.unconditional_coshMultiplier_dyadic_signed_coercivity
    (g : RealEvenPolarTestFn) (α : ℝ) (M : ℕ) :
    dyadicNyquistCoerciveConstant (M + 2) *
        (autocorr g.source 0 + autocorr (sinhMultiplier α g.source) 0) ≤
      biScaleLevyEnergy (coshMultiplier α g.source) +
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            autocorr (coshMultiplier α g.source) (Real.log ((M + 2 + k : ℕ) : ℝ)) := by
  have hN : 2 ≤ M + 2 := by omega
  have hf_c2 : ContDiff ℝ 2 (coshMultiplier α g.source) :=
    contDiff_coshMultiplier α g.contDiff_source
  have hf_cs : HasCompactSupport (coshMultiplier α g.source) :=
    hasCompactSupport_coshMultiplier α g.hasCompactSupport_source
  have hcoerc := global_dyadic_nyquist_signed_coercivity hf_c2 hf_cs hN
  change dyadicNyquistCoerciveConstant (M + 2) * autocorr (coshMultiplier α g.source) 0 ≤ _ at hcoerc
  rw [autocorr_coshMultiplier_zero_eq g.contDiff_source.continuous g.hasCompactSupport_source α]
    at hcoerc
  exact hcoerc

/-- **Unconditional Odd-Multiplier (`sinhMultiplier`) Dyadic Nyquist Signed Coercivity:**
For EVERY `g : RealEvenPolarTestFn`, EVERY `α : ℝ`, and EVERY `M : ℕ` (with zero hypotheses!),
$$\mathcal{C}_{\mathrm{Nyq}}(M+2)\,h_{S_\alpha g}(0)
  \;\le\; \operatorname{biScaleLevyEnergy}(S_\alpha g)
    + \sum_{k=0}^{M+1} \bigl(\log(M+2+k+1) - \log(M+2+k)\bigr)\,\frac{2}{\sqrt{M+2+k+1}}\,
      h_{S_\alpha g}(\log(M+2+k)).$$ -/
theorem RealEvenPolarTestFn.unconditional_sinhMultiplier_dyadic_signed_coercivity
    (g : RealEvenPolarTestFn) (α : ℝ) (M : ℕ) :
    dyadicNyquistCoerciveConstant (M + 2) *
        autocorr (sinhMultiplier α g.source) 0 ≤
      biScaleLevyEnergy (sinhMultiplier α g.source) +
        ∑ k ∈ Finset.range (M + 2),
          (Real.log ((M + 2 + k + 1 : ℕ) : ℝ) - Real.log ((M + 2 + k : ℕ) : ℝ)) *
            (2 / Real.sqrt ((M + 2 + k + 1 : ℕ) : ℝ)) *
            autocorr (sinhMultiplier α g.source) (Real.log ((M + 2 + k : ℕ) : ℝ)) := by
  have hN : 2 ≤ M + 2 := by omega
  have hf_c2 : ContDiff ℝ 2 (sinhMultiplier α g.source) :=
    contDiff_sinhMultiplier α g.contDiff_source
  have hf_cs : HasCompactSupport (sinhMultiplier α g.source) :=
    hasCompactSupport_sinhMultiplier α g.hasCompactSupport_source
  exact global_dyadic_nyquist_signed_coercivity hf_c2 hf_cs hN

end

end GaloisForLFunctions.BiScaleUncertainty
