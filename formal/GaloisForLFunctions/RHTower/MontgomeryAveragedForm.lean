import GaloisForLFunctions.RHTower.MontgomeryPairCorrelationUniform
import GaloisForLFunctions.HTGeometry.FejerNearLattice

/-!
# Montgomery's pair form averaged over a window of exponents

For `R > 0` put `P_R(T) = ∫_{−1}^{1} Λ_1(β) F(T^{α₀ + β/R}, T) dβ`, where `Λ_1(β) = (1 − |β|)⁺` and
`F` is Montgomery's pair form over the zeros with `0 < γ ≤ T`.

* `averagedMontgomeryForm_eq`: `P_R(T) = Σ_{j,k} (T^{α₀})^{z} w(z) K̃(z)`, `z = ρ_j + ρ̄_k − 1`, with the
  complex Fejér kernel `K̃(z) = ∫ Λ_1(β) e^{β (log T/R) z} dβ`. On the line, `K̃(iΔ) = sinc(Δ log T/(2R))²`
  (`fejerKernelC_mul_I`), which has width `≍ R/log T`.
* `eventually_re_averagedMontgomeryForm_ge`: for `0 < α₀ − 1/R` and `α₀ + 1/R < 1`,
  `Re P_R(T) ≥ (1 − ε)(T/2π) α₀ log T` eventually. This follows from the corpus asymptotic
  uniformly on `[α₀ − 1/R, α₀ + 1/R]`, with `∫ Λ_1 = 1` and `∫ β Λ_1 = 0`.
-/

noncomputable section

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry (triangleFn triangleFn_nonneg continuous_triangleFn
  fejerKernel integral_triangleFn)

namespace RHTower

/-- The complex Fejér kernel `K̃_c(z) = ∫_{−1}^{1} Λ_1(β) e^{βcz} dβ`. -/
def fejerKernelC (c : ℝ) (z : ℂ) : ℂ :=
  ∫ β in (-1 : ℝ)..1, ((triangleFn 1 β : ℝ) : ℂ) * Complex.exp ((β * c : ℝ) * z)

theorem fejerKernelC_mul_I (c Δ : ℝ) : fejerKernelC c ((Δ : ℂ) * I) = fejerKernel c Δ := by
  unfold fejerKernelC fejerKernel
  refine intervalIntegral.integral_congr fun β _ => ?_
  congr 2
  push_cast; ring

/-- The averaged pair form `P_R(T) = ∫_{−1}^{1} Λ_1(β) F(T^{α₀ + β/R}, T) dβ`. -/
def averagedMontgomeryForm (α₀ R T : ℝ) : ℂ :=
  ∫ β in (-1 : ℝ)..1, ((triangleFn 1 β : ℝ) : ℂ) *
    montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ (α₀ + β / R))

/-- `(T^{α₀ + β/R})^z = (T^{α₀})^z e^{(β log T/R) z}`. -/
theorem ofReal_rpow_add_cpow {T : ℝ} (hT : 0 < T) (α₀ β R : ℝ) (z : ℂ) :
    ((T ^ (α₀ + β / R) : ℝ) : ℂ) ^ z =
      ((T ^ α₀ : ℝ) : ℂ) ^ z * Complex.exp ((β * (Real.log T / R) : ℝ) * z) := by
  have h1 : ((T ^ (α₀ + β / R) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hT _).ne'
  have h2 : ((T ^ α₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hT _).ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2, ← Complex.exp_add,
    ← Complex.ofReal_log (Real.rpow_pos_of_pos hT _).le,
    ← Complex.ofReal_log (Real.rpow_pos_of_pos hT _).le,
    Real.log_rpow hT, Real.log_rpow hT]
  congr 1
  push_cast
  ring

/-- **The averaged form as a pair sum.** -/
theorem averagedMontgomeryForm_eq {α₀ R T : ℝ} (hT : 0 < T) :
    averagedMontgomeryForm α₀ R T =
      ∑ j ∈ zeroWindow T, ∑ k ∈ zeroWindow T,
        ((T ^ α₀ : ℝ) : ℂ) ^ ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) *
          montgomeryWeight ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) *
          fejerKernelC (Real.log T / R) ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) := by
  unfold averagedMontgomeryForm montgomeryForm fejerKernelC
  have hcont : ∀ z : ℂ, Continuous (fun β : ℝ => ((triangleFn 1 β : ℝ) : ℂ) *
      (((T ^ α₀ : ℝ) : ℂ) ^ z * Complex.exp ((β * (Real.log T / R) : ℝ) * z) * montgomeryWeight z)) := by
    intro z
    have := continuous_triangleFn 1
    fun_prop
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum fun k _ => ?_]
    · refine Finset.sum_congr rfl fun k _ => ?_
      set z := (j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1
      have e : ∀ β : ℝ, ((triangleFn 1 β : ℝ) : ℂ) * (((T ^ (α₀ + β / R) : ℝ) : ℂ) ^ z *
          montgomeryWeight z) = ((T ^ α₀ : ℝ) : ℂ) ^ z * montgomeryWeight z *
            (((triangleFn 1 β : ℝ) : ℂ) * Complex.exp ((β * (Real.log T / R) : ℝ) * z)) := by
        intro β
        rw [ofReal_rpow_add_cpow hT]; ring
      simp_rw [e]
      rw [intervalIntegral.integral_const_mul]
    · have := hcont ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1)
      refine (Continuous.intervalIntegrable ?_ _ _)
      refine this.congr fun β => ?_
      rw [ofReal_rpow_add_cpow hT]
  · refine (continuous_finsetSum _ fun k _ => ?_).intervalIntegrable _ _
    refine (hcont ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1)).congr fun β => ?_
    rw [ofReal_rpow_add_cpow hT]


theorem integral_triangleFn_one_real : ∫ β in (-1 : ℝ)..1, triangleFn 1 β = 1 := by
  have h := integral_triangleFn (a := 1) one_pos
  rw [intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

theorem triangleFn_neg (a β : ℝ) : triangleFn a (-β) = triangleFn a β := by
  unfold triangleFn; rw [abs_neg]

theorem integral_mul_triangleFn_one : ∫ β in (-1 : ℝ)..1, β * triangleFn 1 β = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -1) (b := 1) (fun β : ℝ => β * triangleFn 1 β)
  simp only [neg_neg, triangleFn_neg] at h
  have h2 : ∫ β in (-1 : ℝ)..1, -β * triangleFn 1 β = -∫ β in (-1 : ℝ)..1, β * triangleFn 1 β := by
    rw [← intervalIntegral.integral_neg]; congr 1; funext β; ring
  rw [h2] at h
  linarith

/-- The pair form at `T^{α₀ + β/R}` is continuous in `β`. -/
private theorem continuous_montgomeryForm_rpow {T : ℝ} (hT : 0 < T) (α₀ R : ℝ) :
    Continuous (fun β : ℝ =>
      montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ (α₀ + β / R))) := by
  unfold montgomeryForm
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
  have e : (fun β : ℝ => ((T ^ (α₀ + β / R) : ℝ) : ℂ) ^ ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) *
      montgomeryWeight ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1)) = fun β : ℝ =>
      ((T ^ α₀ : ℝ) : ℂ) ^ ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) *
        Complex.exp ((β * (Real.log T / R) : ℝ) * ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1)) *
        montgomeryWeight ((j.1 : ℂ) + (starRingEnd ℂ) (k.1 : ℂ) - 1) := by
    funext β; rw [ofReal_rpow_add_cpow hT]
  rw [e]
  fun_prop

/-- **The averaged form at leading order (lower bound).** -/
theorem eventually_re_averagedMontgomeryForm_ge {α₀ R ε : ℝ} (hR : 0 < R)
    (ha : 0 < α₀ - 1 / R) (hb : α₀ + 1 / R < 1) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      (1 - ε) * ((T / (2 * Real.pi)) * (α₀ * Real.log T)) ≤ (averagedMontgomeryForm α₀ R T).re := by
  filter_upwards [eventually_montgomeryForm_div_leadingOrder_uniform ha
    (by have := one_div_pos.mpr hR; linarith) hb hε,
    eventually_gt_atTop (1 : ℝ)] with T hU hT1
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hcF := continuous_montgomeryForm_rpow hT0 α₀ R
  have hΛ := continuous_triangleFn 1
  have hint : IntervalIntegrable (fun β : ℝ => ((triangleFn 1 β : ℝ) : ℂ) *
      montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ (α₀ + β / R)))
      MeasureTheory.volume (-1) 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hre : (averagedMontgomeryForm α₀ R T).re = ∫ β in (-1 : ℝ)..1, triangleFn 1 β *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ (α₀ + β / R))).re := by
    unfold averagedMontgomeryForm
    rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint]
    refine intervalIntegral.integral_congr fun β _ => ?_
    simp only [Complex.reCLM_apply, Complex.re_ofReal_mul]
  rw [hre]
  set C : ℝ := (1 - ε) * (T / (2 * Real.pi)) * Real.log T with hC
  have hpt : ∀ β ∈ Icc (-1 : ℝ) 1, triangleFn 1 β * (C * (α₀ + β / R)) ≤ triangleFn 1 β *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ (α₀ + β / R))).re := by
    intro β hβ
    apply mul_le_mul_of_nonneg_left _ (triangleFn_nonneg 1 β)
    have hα : α₀ + β / R ∈ Icc (α₀ - 1 / R) (α₀ + 1 / R) := by
      constructor
      · have : -1 / R ≤ β / R := div_le_div_of_nonneg_right hβ.1 hR.le
        rw [neg_div] at this; linarith
      · have : β / R ≤ 1 / R := div_le_div_of_nonneg_right hβ.2 hR.le
        linarith
    have h := hU _ hα
    have hpos : 0 < (T / (2 * Real.pi)) * ((α₀ + β / R) * Real.log T) := by
      have : 0 < α₀ + β / R := by linarith [hα.1]
      positivity
    have h1 := (abs_lt.mp h).1
    rw [lt_sub_iff_add_lt, neg_add_eq_sub, lt_div_iff₀ hpos] at h1
    rw [hC]
    nlinarith
  have hcont1 : Continuous (fun β : ℝ => triangleFn 1 β * (C * (α₀ + β / R))) := by fun_prop
  have hcont2 : Continuous (fun β : ℝ => triangleFn 1 β *
      (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ (α₀ + β / R))).re) := by
    have := Complex.continuous_re.comp hcF; fun_prop
  refine le_trans (le_of_eq ?_) (intervalIntegral.integral_mono_on (by norm_num)
    (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _) hpt)
  have e : (fun β : ℝ => triangleFn 1 β * (C * (α₀ + β / R))) =
      fun β => (C * α₀) * triangleFn 1 β + (C / R) * (β * triangleFn 1 β) := by
    funext β; ring
  rw [e, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_triangleFn_one_real, integral_mul_triangleFn_one]
  · rw [hC]; ring
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)
  · exact (Continuous.intervalIntegrable (by fun_prop) _ _)

end RHTower
