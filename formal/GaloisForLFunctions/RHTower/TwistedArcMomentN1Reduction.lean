import GaloisForLFunctions.RHTower.TwistedArcN1Reduction
import GaloisForLFunctions.HTGeometry.SymmetricCoshMomentPositivity

/-!
# Decay-class (N1) line witnesses from signed, moment-positive twisted arc measures

The twisted arc vectors `g_u` (`TwistedArcGenerator`) have log profile
`e^{v/2} g_u(e^v) = √(y_u/2) 𝒦^{tw}_u(v)` with cosine transform
`√(y_u/2) (¼ + τ²)² Ŝ_u(τ)`, where `Ŝ_u(τ) = ∫ cos(τv) 𝒦_u(v) dv` and

  `Ŝ_u(τ) = ∑_j 2 C(−½, 2j) u^{2j} C_j(τ)`,   `C_j(τ) = ∫ cos(τv) (cosh v)^{−1/2−2j} dv > 0`.

For a finite measure `ν` on the arc and a bounded measurable (signed) density `g`, the superposition
`h = ∫ g(u) g_u dν(u)` therefore has cosine transform

  `(¼ + τ²)² ∑_j 2 C(−½, 2j) C_j(τ) m_j`,   `m_j = ∫ g(u) √(y_u/2) u^{2j} dν(u)`.

**Theorem** (`exists_decayClass_fullLineWitness_of_momentPositive`).  If `∫ g M_n dν = 0` for every
twisted integer moment `M_n` (`twArcMoment`), every weighted even moment `m_j` is nonnegative and
`m_0 > 0`, then `h` is a decay-class line witness blind at every integer `m ≥ 2`: it is even, satisfies
`h(1/x) = |x| h(x)` and `∫ h = 0`, has log profile `O(e^{−3|v|/2})`, and its log profile is strictly
positive definite.

This contains the positive case (`g ≥ 0`, where all `m_j ≥ 0` automatically).  It replaces the
requirement that the annihilating arc measure be positive by the weaker requirement that its weighted
even moments be nonnegative.
-/

open MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ### The moment expansion of the arc spectrum -/

/-- `C_j(τ) = ∫ cos(τv) (cosh v)^{−1/2−2j} dv`. -/
def coshPowerTransform (j : ℕ) (τ : ℝ) : ℝ :=
  ∫ v, Real.cos (τ * v) * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))

theorem coshPowerTransform_pos (j : ℕ) (τ : ℝ) : 0 < coshPowerTransform j τ :=
  integral_cos_mul_cosh_rpow_neg_pos (by positivity) τ

theorem abs_coshPowerTransform_le (j : ℕ) (τ : ℝ) :
    |coshPowerTransform j τ| ≤ ∫ v, Real.cosh v ^ (-(1 / 2) : ℝ) := by
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)
  unfold coshPowerTransform
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun v => abs_nonneg _) hI (Eventually.of_forall fun v => ?_))
  show |Real.cos (τ * v) * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))| ≤ Real.cosh v ^ (-(1 / 2) : ℝ)
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos v).le _)]
  calc |Real.cos (τ * v)| * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ))
      ≤ 1 * Real.cosh v ^ (-(1 / 2) : ℝ) :=
        mul_le_mul (Real.abs_cos_le_one _) (cosh_rpow_neg_half_two_mul_le j v)
          (Real.rpow_nonneg (Real.cosh_pos v).le _) zero_le_one
    _ = _ := one_mul _

/-- `Ŝ_c(τ) = ∑_j 2 C(−½, 2j) c^{2j} C_j(τ)` for `|c| < 1`. -/
theorem hasSum_integral_cos_mul_symCoshKernel {c : ℝ} (hc : |c| < 1) (τ : ℝ) :
    HasSum (fun j => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * c ^ (2 * j) * coshPowerTransform j τ)
      (∫ v, Real.cos (τ * v) * symCoshKernel c v) := by
  have hI := _root_.HTGeometry.integrable_cosh_rpow_neg (s := 1 / 2) (by norm_num)
  set A : ℕ → ℝ := fun j => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * c ^ (2 * j) with hA
  have hA0 : ∀ j, 0 ≤ A j := fun j => by
    have := choose_neg_half_even_pos j
    have hc2 : 0 ≤ c ^ (2 * j) := by rw [pow_mul]; positivity
    simp only [hA]; positivity
  have hAsum : Summable A := (hasSum_one_add_rpow_add_one_sub (x := c) hc).summable
  set F : ℕ → ℝ → ℝ := fun j v => Real.cos (τ * v) * symCoshTerm c j v with hF
  have hterm : ∀ j v, symCoshTerm c j v = A j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)) := by
    intro j v; simp [symCoshTerm, hA]
  have hbound : ∀ j v, ‖F j v‖ ≤ A j * Real.cosh v ^ (-(1 / 2) : ℝ) := by
    intro j v
    simp only [hF]
    rw [hterm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 j),
      abs_of_nonneg (Real.rpow_nonneg (Real.cosh_pos v).le _)]
    calc |Real.cos (τ * v)| * (A j * Real.cosh v ^ (-(1 / 2 + 2 * j : ℝ)))
        ≤ 1 * (A j * Real.cosh v ^ (-(1 / 2) : ℝ)) :=
          mul_le_mul (Real.abs_cos_le_one _)
            (mul_le_mul_of_nonneg_left (cosh_rpow_neg_half_two_mul_le j v) (hA0 j))
            (mul_nonneg (hA0 j) (Real.rpow_nonneg (Real.cosh_pos v).le _)) zero_le_one
      _ = _ := one_mul _
  have hFint : ∀ j, Integrable (F j) := fun j =>
    (hI.const_mul (A j)).mono' (by simp only [hF, symCoshTerm]; fun_prop)
      (Eventually.of_forall (hbound j))
  have hnormsum : Summable fun j => ∫ v, ‖F j v‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun v => norm_nonneg _)
      (fun j => ?_) (hAsum.mul_right (∫ v, Real.cosh v ^ (-(1 / 2) : ℝ)))
    rw [← integral_const_mul]
    exact integral_mono (hFint j).norm (hI.const_mul (A j)) (hbound j)
  have hswap := integral_tsum_of_summable_integral_norm hFint hnormsum
  have hpt : ∀ v, Real.cos (τ * v) * symCoshKernel c v = ∑' j, F j v := by
    intro v
    rw [(hasSum_symCoshKernel hc v).tsum_eq.symm, ← tsum_mul_left]
  have hterm_int : ∀ j, ∫ v, F j v = A j * coshPowerTransform j τ := by
    intro j
    rw [coshPowerTransform, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hF, hterm]; ring
  have hsumm : Summable fun j => ∫ v, F j v :=
    Summable.of_norm_bounded hnormsum fun j => norm_integral_le_integral_norm _
  have h := hsumm.hasSum
  rw [hswap, ← integral_congr_ae (Eventually.of_forall hpt)] at h
  refine h.congr_fun fun j => ?_
  rw [hterm_int]

/-! ### The weighted superposition -/

/-- The top point `u = 0` of the arc. -/
def arcZeroPt : ArcParam := ⟨0, by constructor <;> norm_num⟩

theorem continuous_modularArcHeight_param : Continuous fun u : ArcParam => modularArcHeight u := by
  unfold modularArcHeight; fun_prop

section Weighted

variable {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} {B : ℝ}

/-- The weighted superposition `h = ∫ g(u) g_u dν(u)`. -/
def twWitnessW (ν : Measure ArcParam) (g : ArcParam → ℝ) (x : ℝ) : ℝ :=
  ∫ u, g u * twArcVector u x ∂ν

/-- Its derivative `∫ g(u) g_u′ dν(u)`. -/
def twWitnessWDeriv (ν : Measure ArcParam) (g : ArcParam → ℝ) (x : ℝ) : ℝ :=
  ∫ u, g u * twArcDeriv u x ∂ν

theorem integrable_g_mul_of_bound (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    {f : ArcParam → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ u, |f u| ≤ C) :
    Integrable (fun u => g u * f u) ν :=
  Integrable.of_bound (hg.mul hf.measurable).aestronglyMeasurable (B * C)
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgB u) (hC u) (abs_nonneg _) ((abs_nonneg _).trans (hgB u)))

theorem hasDerivAt_twWitnessW (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    HasDerivAt (twWitnessW ν g) (twWitnessWDeriv ν g x) x := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun (x : ℝ) (u : ArcParam) => g u * twArcVector u x)
    (F' := fun x u => g u * twArcDeriv u x) (x₀ := x) (bound := fun _ => B * 260000)
    (s := univ) Filter.univ_mem
    (Eventually.of_forall fun x' =>
      (hg.mul (continuous_twArcVector_at x').measurable).aestronglyMeasurable)
    (integrable_g_mul_of_bound hg hgB (continuous_twArcVector_at x)
      (C := 9000) fun u => (abs_twArcVector_le u x).trans (by
        have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
        nlinarith))
    (hg.mul (continuous_twArcDeriv_at x).measurable).aestronglyMeasurable
    (Eventually.of_forall fun u x' _ => by
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hgB u) ((abs_twArcDeriv_le u x').trans ?_) (abs_nonneg _) hB0
      have : (1 + x' ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x'])
      nlinarith)
    (integrable_const _)
    (Eventually.of_forall fun u x' _ => (hasDerivAt_twArcVector u x').const_mul (g u))
  exact key.2

theorem abs_twWitnessW_le (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    |twWitnessW ν g x| ≤ B * ν.real univ * 9000 * (1 + x ^ 2)⁻¹ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun u => g u * twArcVector u x) (C := B * (9000 * (1 + x ^ 2)⁻¹))
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgB u) (abs_twArcVector_le u x) (abs_nonneg _) hB0)
  rw [Real.norm_eq_abs] at h
  unfold twWitnessW
  calc _ ≤ B * (9000 * (1 + x ^ 2)⁻¹) * ν.real univ := h
    _ = _ := by ring

theorem abs_twWitnessWDeriv_le (hgB : ∀ u, |g u| ≤ B) (x : ℝ) :
    |twWitnessWDeriv ν g x| ≤ B * ν.real univ * 260000 * (1 + x ^ 2)⁻¹ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have h := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun u => g u * twArcDeriv u x) (C := B * (260000 * (1 + x ^ 2)⁻¹))
    (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgB u) (abs_twArcDeriv_le u x) (abs_nonneg _) hB0)
  rw [Real.norm_eq_abs] at h
  unfold twWitnessWDeriv
  calc _ ≤ B * (260000 * (1 + x ^ 2)⁻¹) * ν.real univ := h
    _ = _ := by ring

theorem continuous_twWitnessW (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous (twWitnessW ν g) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_twWitnessW hg hgB x).continuousAt

theorem continuous_twWitnessWDeriv (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    Continuous (twWitnessWDeriv ν g) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  unfold twWitnessWDeriv
  refine continuous_of_dominated (bound := fun _ => B * 260000) (fun x => ?_)
    (fun x => Eventually.of_forall fun u => ?_) (integrable_const _)
    (Eventually.of_forall fun u => ?_)
  · exact (hg.mul (continuous_twArcDeriv_at x).measurable).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hgB u) ((abs_twArcDeriv_le u x).trans ?_) (abs_nonneg _) hB0
    have : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    nlinarith
  · exact continuous_const.mul (continuous_twArcDeriv u)

omit [IsFiniteMeasure ν] in
theorem twWitnessW_neg (x : ℝ) : twWitnessW ν g (-x) = twWitnessW ν g x := by
  unfold twWitnessW; simp_rw [twArcVector_neg]

omit [IsFiniteMeasure ν] in
theorem twWitnessW_inv {x : ℝ} (hx : x ≠ 0) :
    twWitnessW ν g (1 / x) = |x| * twWitnessW ν g x := by
  unfold twWitnessW
  simp_rw [twArcVector_inv _ hx]
  rw [← integral_const_mul]
  congr 1; funext u; ring

/-- Product integrability for `(x, u) ↦ g(u) F(x, u)` with `|F| ≤ C (1 + x²)⁻¹`. -/
theorem integrable_prod_g_mul (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    {F : ℝ → ArcParam → ℝ} (hF : Continuous fun p : ℝ × ArcParam => F p.1 p.2) {C : ℝ}
    (hC : ∀ x u, |F x u| ≤ C * (1 + x ^ 2)⁻¹) :
    Integrable (Function.uncurry fun x u => g u * F x u) ((volume : Measure ℝ).prod ν) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have hI : Integrable (fun z : ℝ × ArcParam => (B * C * (1 + z.1 ^ 2)⁻¹) * (1 : ℝ))
      ((volume : Measure ℝ).prod ν) :=
    (integrable_inv_one_add_sq.const_mul (B * C)).mul_prod (integrable_const (1 : ℝ))
  refine hI.mono' ((hg.comp measurable_snd).mul hF.measurable).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, mul_one]
  simp only [Function.uncurry]
  rw [abs_mul]
  calc |g z.2| * |F z.1 z.2| ≤ B * (C * (1 + z.1 ^ 2)⁻¹) :=
        mul_le_mul (hgB z.2) (hC z.1 z.2) (abs_nonneg _) hB0
    _ = _ := by ring

theorem integral_twWitnessW_eq_zero (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) :
    ∫ x, twWitnessW ν g x = 0 := by
  unfold twWitnessW
  rw [integral_integral_swap (integrable_prod_g_mul (ν := ν) hg hgB (F := fun x u => twArcVector u x)
    continuous_twArcVector_param (fun x u => abs_twArcVector_le u x))]
  simp_rw [integral_const_mul, integral_twArcVector_eq_zero, mul_zero, integral_zero]

theorem integral_twWitnessWDeriv_mul_sin (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B) (ω : ℝ) :
    ∫ x, twWitnessWDeriv ν g x * Real.sin (ω * x) =
      -(ω * ∫ u, g u * (∫ x, twArcVector u x * Real.cos (ω * x)) ∂ν) := by
  unfold twWitnessWDeriv
  simp_rw [← integral_mul_const]
  have hsw := integral_integral_swap (integrable_prod_g_mul (ν := ν) hg hgB
    (F := fun x u => twArcDeriv u x * Real.sin (ω * x)) (C := 260000)
    (continuous_twArcDeriv_param.mul (by fun_prop))
    (fun x u => by
      rw [abs_mul]
      exact (mul_le_mul (abs_twArcDeriv_le u x) (Real.abs_sin_le_one _) (abs_nonneg _)
        (by positivity)).trans (by rw [mul_one])))
  simp only [mul_assoc] at hsw ⊢
  rw [hsw]
  simp_rw [integral_const_mul, integral_twArcDeriv_mul_sin]
  rw [← integral_const_mul, ← integral_neg]
  congr 1; funext u; ring

/-- The cosine transform of the weighted witness profile:
`∫ cos(τv) e^{v/2} h(e^v) dv = (¼+τ²)² ∑_j 2 C(−½, 2j) C_j(τ) m_j`. -/
theorem integral_cos_mul_twWitnessWProfile_eq (hg : Measurable g) (hgB : ∀ u, |g u| ≤ B)
    (τ : ℝ) :
    ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * twWitnessW ν g (Real.exp v)) =
      (1 / 4 + τ ^ 2) ^ 2 * ∑' j, 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * coshPowerTransform j τ *
        ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
  have hb : Integrable fun v : ℝ => 9000 * Real.exp (-(3 / 2 * |v|)) :=
    (integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 2)).const_mul 9000
  have hbound : ∀ u : ArcParam, ∀ v : ℝ,
      |Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v))| ≤
        9000 * Real.exp (-(3 / 2 * |v|)) := fun u v => by
    rw [abs_mul]
    refine (mul_le_mul (Real.abs_cos_le_one _) (abs_exp_half_mul_twArcVector_le u v)
      (abs_nonneg _) zero_le_one).trans ?_
    rw [one_mul]; apply le_of_eq; congr 2; ring
  have hcont : Continuous fun p : ℝ × ArcParam =>
      Real.cos (τ * p.1) * (Real.exp (p.1 / 2) * twArcVector p.2 (Real.exp p.1)) := by
    have := continuous_twArcVector_param.comp
      ((Real.continuous_exp.comp continuous_fst).prodMk continuous_snd)
    exact (by fun_prop : Continuous fun p : ℝ × ArcParam => Real.cos (τ * p.1)).mul
      ((by fun_prop : Continuous fun p : ℝ × ArcParam => Real.exp (p.1 / 2)).mul this)
  have hprod : Integrable (Function.uncurry fun v (u : ArcParam) =>
      g u * (Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v))))
      ((volume : Measure ℝ).prod ν) := by
    have hI : Integrable (fun z : ℝ × ArcParam =>
        (B * 9000 * Real.exp (-(3 / 2 * |z.1|))) * (1 : ℝ)) ((volume : Measure ℝ).prod ν) :=
      ((integrable_rexp_neg_mul_abs (by norm_num : (0 : ℝ) < 3 / 2)).const_mul (B * 9000)).mul_prod
        (integrable_const _)
    refine hI.mono' ((hg.comp measurable_snd).mul hcont.measurable).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, mul_one]
    simp only [Function.uncurry]
    rw [abs_mul]
    calc |g z.2| * |Real.cos (τ * z.1) * (Real.exp (z.1 / 2) * twArcVector z.2 (Real.exp z.1))|
        ≤ B * (9000 * Real.exp (-(3 / 2 * |z.1|))) :=
          mul_le_mul (hgB z.2) (hbound z.2 z.1) (abs_nonneg _) hB0
      _ = _ := by ring
  have e : ∀ v, Real.cos (τ * v) * (Real.exp (v / 2) * twWitnessW ν g (Real.exp v)) =
      ∫ u, g u * (Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v))) ∂ν :=
    fun v => by
      unfold twWitnessW
      rw [← integral_const_mul, ← integral_const_mul]
      congr 1; funext u; ring
  simp_rw [e]
  rw [integral_integral_swap hprod]
  simp_rw [integral_const_mul]
  -- the per-point spectrum
  have hspec : ∀ u : ArcParam, ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * twArcVector u (Real.exp v)) =
      (1 / 4 + τ ^ 2) ^ 2 * (Real.sqrt (modularArcHeight u / 2) *
        ∑' j, 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) * coshPowerTransform j τ) := by
    intro u
    simp_rw [exp_half_mul_twArcVector]
    have e2 : (fun v => Real.cos (τ * v) * (Real.sqrt (modularArcHeight u / 2) *
        twSymCoshKernel u v)) = fun v => Real.sqrt (modularArcHeight u / 2) *
          (Real.cos (τ * v) * twSymCoshKernel u v) := by funext v; ring
    rw [e2, integral_const_mul, integral_cos_mul_twSymCoshKernel (abs_arcParam_lt u),
      (hasSum_integral_cos_mul_symCoshKernel (abs_arcParam_lt u) τ).tsum_eq]
    ring
  simp_rw [hspec]
  -- interchange the arc integral with the moment series
  set I₀ := ∫ v, Real.cosh v ^ (-(1 / 2) : ℝ) with hI₀
  set G : ℕ → ArcParam → ℝ := fun j u => g u * (Real.sqrt (modularArcHeight u / 2) *
    (2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) * coshPowerTransform j τ)) with hG
  have hsqrt : ∀ u : ArcParam, Real.sqrt (modularArcHeight u / 2) ≤ 1 := fun u => by
    rw [Real.sqrt_le_one]
    have : modularArcHeight u ≤ 1 := by
      unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
    linarith
  have hu2 : ∀ (j : ℕ) (u : ArcParam), |(u : ℝ) ^ (2 * j)| ≤ (1 / 4 : ℝ) ^ j := fun j u => by
    rw [abs_pow, pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ j
    have := abs_arcParam_le u
    rw [sq_abs]; nlinarith [abs_nonneg (u : ℝ), sq_abs (u : ℝ)]
  have hGbound : ∀ j u, |G j u| ≤ B * (2 * (1 / 4 : ℝ) ^ j * I₀) := by
    intro j u
    simp only [hG]
    rw [abs_mul, abs_mul]
    refine mul_le_mul (hgB u) ?_ (by positivity) hB0
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (modularArcHeight u / 2) *
          |2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) * coshPowerTransform j τ|
        ≤ 1 * (2 * (1 / 4 : ℝ) ^ j * I₀) := by
          refine mul_le_mul (hsqrt u) ?_ (abs_nonneg _) zero_le_one
          rw [abs_mul, abs_mul, abs_mul, abs_two]
          calc 2 * |Ring.choose (-1 / 2 : ℝ) (2 * j)| * |(u : ℝ) ^ (2 * j)| *
                |coshPowerTransform j τ| ≤ 2 * 1 * (1 / 4 : ℝ) ^ j * I₀ := by
                gcongr
                · exact abs_choose_neg_half_le_one _
                · exact hu2 j u
                · exact abs_coshPowerTransform_le j τ
            _ = 2 * (1 / 4 : ℝ) ^ j * I₀ := by ring
      _ = _ := one_mul _
  have hGint : ∀ j, Integrable (G j) ν := fun j =>
    Integrable.of_bound (by
      simp only [hG]
      exact (hg.mul ((Real.continuous_sqrt.comp (continuous_modularArcHeight_param.div_const 2)).mul
        (continuous_const.mul (by fun_prop : Continuous fun u : ArcParam => (u : ℝ) ^ (2 * j))
          |>.mul continuous_const)).measurable).aestronglyMeasurable)
      _ (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hGbound j u)
  have hgeom : Summable fun j : ℕ => (1 / 4 : ℝ) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hnormsum : Summable fun j => ∫ u, ‖G j u‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun u => norm_nonneg _)
      (fun j => ?_) ((hgeom.mul_left (B * 2 * I₀ * ν.real univ)))
    calc ∫ u, ‖G j u‖ ∂ν ≤ ∫ _u, B * (2 * (1 / 4 : ℝ) ^ j * I₀) ∂ν :=
          integral_mono (hGint j).norm (integrable_const _) fun u => by
            rw [Real.norm_eq_abs]; exact hGbound j u
      _ = B * 2 * I₀ * ν.real univ * (1 / 4 : ℝ) ^ j := by
          rw [integral_const, smul_eq_mul]; ring
  have hswap := integral_tsum_of_summable_integral_norm hGint hnormsum
  have hpt : ∀ u : ArcParam, g u * ((1 / 4 + τ ^ 2) ^ 2 * (Real.sqrt (modularArcHeight u / 2) *
      ∑' j, 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * (u : ℝ) ^ (2 * j) * coshPowerTransform j τ)) =
      (1 / 4 + τ ^ 2) ^ 2 * ∑' j, G j u := by
    intro u
    simp only [hG]
    conv_rhs => rw [tsum_mul_left, tsum_mul_left]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, ← hswap]
  congr 1
  congr 1
  funext j
  simp only [hG]
  rw [← integral_const_mul]
  congr 1; funext u; ring

end Weighted

/-- **Decay-class (N1) line witnesses from a moment-positive twisted arc measure.** Let `ν` be a
finite measure on the arc and `g` a bounded measurable density.  If `g ν` annihilates every twisted
integer moment, all weighted even moments `∫ g(u) √(y_u/2) u^{2j} dν` are nonnegative and the
weighted mass is positive, then `h = ∫ g(u) g_u dν(u)` is a decay-class line witness, blind at every
integer `m ≥ 2`, with strictly positive definite log profile. -/
theorem exists_decayClass_fullLineWitness_of_momentPositive
    {ν : Measure ArcParam} [IsFiniteMeasure ν] {g : ArcParam → ℝ} (hg : Measurable g) {B : ℝ}
    (hgB : ∀ u, |g u| ≤ B) (hblind : ∀ n : ℕ, ∫ u, g u * twArcMoment n u ∂ν = 0)
    (hmom : ∀ j : ℕ, 0 ≤ ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν)
    (hmass : 0 < ∫ u, g u * Real.sqrt (modularArcHeight u / 2) ∂ν) :
    ∃ h h' : ℝ → ℝ, (∀ x, HasDerivAt h (h' x) x) ∧ Integrable h ∧ Integrable h' ∧
      (∀ x, h (-x) = h x) ∧ (∀ x, x ≠ 0 → h (1 / x) = |x| * h x) ∧ ∫ x, h x = 0 ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n : ℕ, ∫ x, h' x * Real.sin (arcFreq (n + 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) := by
  refine ⟨twWitnessW ν g, twWitnessWDeriv ν g, hasDerivAt_twWitnessW hg hgB,
    integrable_of_le_inv_one_add_sq (continuous_twWitnessW hg hgB) (abs_twWitnessW_le hgB),
    integrable_of_le_inv_one_add_sq (continuous_twWitnessWDeriv hg hgB) (abs_twWitnessWDeriv_le hgB),
    twWitnessW_neg, fun x hx => twWitnessW_inv hx, integral_twWitnessW_eq_zero hg hgB,
    ⟨B * ν.real univ * 9000, abs_exp_half_mul_le_of_inv (abs_twWitnessW_le hgB)
      (fun _ hx => twWitnessW_inv hx)⟩, fun n => ?_, fun τ => ?_⟩
  · rw [integral_twWitnessWDeriv_mul_sin hg hgB]
    have := hblind n
    unfold twArcMoment at this
    rw [this, mul_zero, neg_zero]
  · rw [integral_cos_mul_twWitnessWProfile_eq hg hgB τ]
    refine mul_pos (by positivity) ?_
    set t : ℕ → ℝ := fun j => 2 * Ring.choose (-1 / 2 : ℝ) (2 * j) * coshPowerTransform j τ *
      ∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν with ht
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB arcZeroPt)
    have ht0 : ∀ j, 0 ≤ t j := fun j =>
      mul_nonneg (mul_nonneg (mul_nonneg two_pos.le (choose_neg_half_even_pos j).le)
        (coshPowerTransform_pos j τ).le) (hmom j)
    have hmj : ∀ j, |∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν| ≤
        B * ν.real univ * (1 / 4 : ℝ) ^ j := fun j => by
      have h := norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun u => g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)))
        (C := B * (1 / 4 : ℝ) ^ j)
        (Eventually.of_forall fun u => by
          rw [Real.norm_eq_abs, abs_mul]
          have h1 : |Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)| ≤ (1 / 4 : ℝ) ^ j := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
            have hs : Real.sqrt (modularArcHeight u / 2) ≤ 1 := by
              rw [Real.sqrt_le_one]
              have : modularArcHeight u ≤ 1 := by
                unfold modularArcHeight; rw [Real.sqrt_le_one]; nlinarith [sq_nonneg (u : ℝ)]
              linarith
            have hp : |(u : ℝ) ^ (2 * j)| ≤ (1 / 4 : ℝ) ^ j := by
              rw [abs_pow, pow_mul]
              refine pow_le_pow_left₀ (by positivity) ?_ j
              have := abs_arcParam_le u
              nlinarith [abs_nonneg (u : ℝ), sq_abs (u : ℝ)]
            calc Real.sqrt (modularArcHeight u / 2) * |(u : ℝ) ^ (2 * j)| ≤ 1 * (1 / 4 : ℝ) ^ j :=
                  mul_le_mul hs hp (abs_nonneg _) zero_le_one
              _ = (1 / 4 : ℝ) ^ j := one_mul _
          calc |g u| * |Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)|
              ≤ B * (1 / 4 : ℝ) ^ j := mul_le_mul (hgB u) h1 (abs_nonneg _) hB0
            _ = B * (1 / 4 : ℝ) ^ j := rfl)
      rw [Real.norm_eq_abs] at h
      calc _ ≤ B * (1 / 4 : ℝ) ^ j * ν.real univ := h
        _ = _ := by ring
    have hsum : Summable t := by
      refine Summable.of_nonneg_of_le ht0 (fun j => ?_)
        ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left
          (2 * (∫ v, Real.cosh v ^ (-(1 / 2) : ℝ)) * (B * ν.real univ)))
      calc t j ≤ |t j| := le_abs_self _
        _ = 2 * |Ring.choose (-1 / 2 : ℝ) (2 * j)| * |coshPowerTransform j τ| *
            |∫ u, g u * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) ∂ν| := by
          simp only [ht]; rw [abs_mul, abs_mul, abs_mul, abs_two]
        _ ≤ 2 * 1 * (∫ v, Real.cosh v ^ (-(1 / 2) : ℝ)) * (B * ν.real univ * (1 / 4 : ℝ) ^ j) := by
          gcongr
          · exact abs_choose_neg_half_le_one _
          · exact abs_coshPowerTransform_le j τ
          · exact hmj j
        _ = _ := by ring
    exact hsum.tsum_pos ht0 0 (by
      simp only [ht]
      refine mul_pos (mul_pos (by simp) (coshPowerTransform_pos 0 τ)) ?_
      simpa using hmass)

end

end RHTower
