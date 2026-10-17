import GaloisForLFunctions.RHTower.CosDilationKernelBlindnessLink

/-!
# The pole of a core null test

Let `f` be smooth, supported in `[α, β] ⊂ (0, ∞)`, with `𝓜f(1) = ∫ f = 0` (a core), and let
`R_f(s) = 4 𝓜f(s) 𝓜f(1−s)/(s²(s−1)² Γℝ(s) Γℝ(1−s))` be its multiplier (`cosDilationCertMultiplier`,
removable singularity at `s = 1` resolved).  Then (`cosDilationCertMultiplier_one`)

`R_f(1) = −2 𝓜f′(1) 𝓜f(0) = −2 (∫ f(y) log y dy)(∫ f(y) dy/y)`,

and since `Ξ(±i/2) = ξ(1) = ½`, the null test `Ξ² R_f` has pole term
`P = 2 ξ(1)² R_f(1) = −(∫ f log y)(∫ f/y)` (`coreNullPole_eq`), which can have either sign:
the core is odd (`P < 0`), primitive (`P = 0`) or even (`P > 0`) according as the product
`(∫ f log y)(∫ f/y)` is positive, zero or negative (`coreNullPole_neg_iff`, …).
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff

namespace RHTower.CoreNullPole

noncomputable section

variable {f : ℝ → ℝ}

theorem eventuallyEq_zero_atTop {β : ℝ} (hsupp : ∀ y, f y ≠ 0 → y ≤ β) :
    (fun _ : ℝ => (0 : ℂ)) =ᶠ[atTop] fun y => (f y : ℂ) := by
  filter_upwards [eventually_gt_atTop β] with y hy
  by_contra h
  have := hsupp y (fun h0 => h (by rw [h0, Complex.ofReal_zero]))
  linarith

theorem eventuallyEq_zero_nhdsGT {α : ℝ} (hα : 0 < α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y) :
    (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] 0] fun y => (f y : ℂ) := by
  filter_upwards [Ioo_mem_nhdsGT hα] with y hy
  by_contra h
  have := hsupp y (fun h0 => h (by rw [h0, Complex.ofReal_zero]))
  linarith [hy.2]

/-- `𝓜f′(1) = ∫ f(y) log y dy`. -/
theorem hasDerivAt_mellin_one (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    HasDerivAt (mellin fun y : ℝ => (f y : ℂ))
      ((∫ y in Ioi 0, f y * Real.log y : ℝ) : ℂ) 1 := by
  have hloc : LocallyIntegrableOn (fun y : ℝ => (f y : ℂ)) (Ioi 0) :=
    (Complex.continuous_ofReal.comp hf).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : (fun y : ℝ => (f y : ℂ)) =O[atTop] (· ^ (-(2 : ℝ))) :=
    (isBigO_zero _ _).congr' (eventuallyEq_zero_atTop fun y hy => (hsupp y hy).2) EventuallyEq.rfl
  have hbot : (fun y : ℝ => (f y : ℂ)) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) :=
    (isBigO_zero _ _).congr' (eventuallyEq_zero_nhdsGT hα fun y hy => (hsupp y hy).1)
      EventuallyEq.rfl
  have h := (mellin_hasDerivAt_of_isBigO_rpow (s := 1) hloc htop (by norm_num) hbot (by norm_num)).2
  refine h.congr_deriv ?_
  unfold mellin
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  simp only [sub_self, Complex.cpow_zero, one_smul, Complex.real_smul]
  push_cast
  ring

/-- `𝓜f(0) = ∫ f(y) dy/y`. -/
theorem mellin_zero_eq (f : ℝ → ℝ) :
    mellin (fun y : ℝ => (f y : ℂ)) 0 = ((∫ y in Ioi 0, f y / y : ℝ) : ℂ) := by
  unfold mellin
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) ≤ y := le_of_lt hy
  simp only [zero_sub, smul_eq_mul]
  rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow hy0,
    Real.rpow_neg_one]
  push_cast
  ring

/-- **The multiplier at `s = 1`**: `R_f(1) = −2 (∫ f log y)(∫ f/y)`. -/
theorem cosDilationCertMultiplier_one (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    cosDilationCertMultiplier f 1 =
      ((-2 * (∫ y in Ioi 0, f y * Real.log y) * ∫ y in Ioi 0, f y / y : ℝ) : ℂ) := by
  unfold cosDilationCertMultiplier
  rw [dslope_same, (hasDerivAt_mellin_one hf hα hsupp).deriv, sub_self, mellin_zero_eq,
    Complex.Gammaℝ_one]
  have h3 : ((3 : ℂ) - 1) / 2 = 1 := by norm_num
  rw [h3, Complex.Gamma_one]
  simp only [zero_div, Complex.cpow_zero, inv_one, one_pow, mul_one, div_one]
  push_cast
  ring

/-- The pole term `2 ξ(1)² R_f(1)` of the null test `Ξ² R_f` (as `Ξ(±i/2) = ξ(1)`). -/
def coreNullPole (f : ℝ → ℝ) : ℝ := (2 * xi 1 ^ 2 * cosDilationCertMultiplier f 1).re

/-- **The pole of a core null test**: `P = −(∫ f log y)(∫ f/y)`. -/
theorem coreNullPole_eq (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    coreNullPole f = -((∫ y in Ioi 0, f y * Real.log y) * ∫ y in Ioi 0, f y / y) := by
  rw [coreNullPole, cosDilationCertMultiplier_one hf hα hsupp, xi_one]
  norm_num
  ring

/-- **Odd cores**: the null test is pole-negative iff `(∫ f log y)(∫ f/y) > 0`. -/
theorem coreNullPole_neg_iff (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    coreNullPole f < 0 ↔ 0 < (∫ y in Ioi 0, f y * Real.log y) * ∫ y in Ioi 0, f y / y := by
  rw [coreNullPole_eq hf hα hsupp]
  constructor <;> intro h <;> linarith

/-- **Primitive cores**: the null test has zero pole iff `(∫ f log y)(∫ f/y) = 0`. -/
theorem coreNullPole_eq_zero_iff (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    coreNullPole f = 0 ↔ (∫ y in Ioi 0, f y * Real.log y) * ∫ y in Ioi 0, f y / y = 0 := by
  rw [coreNullPole_eq hf hα hsupp, neg_eq_zero]

/-- **Even cores**: the null test is pole-positive iff `(∫ f log y)(∫ f/y) < 0`. -/
theorem coreNullPole_pos_iff (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β) :
    0 < coreNullPole f ↔ (∫ y in Ioi 0, f y * Real.log y) * ∫ y in Ioi 0, f y / y < 0 := by
  rw [coreNullPole_eq hf hα hsupp]
  constructor <;> intro h <;> linarith

end

end RHTower.CoreNullPole
