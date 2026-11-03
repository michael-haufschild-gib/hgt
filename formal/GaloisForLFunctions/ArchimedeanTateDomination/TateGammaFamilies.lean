import GaloisForLFunctions.ArchimedeanTateDomination.TheDimensionZeroInheritanceLaw
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity

/-!
# Esscher-tilted and symmetrized archimedean Tate-Gamma families

For `|k| < 1/2`, tilting the archimedean Lévy density `ω(x) = e^{−x/2}/(1 − e^{−2x})` by the
integrated Tate factor `(e^{kx} − 1)/x` (`Γ_ℝ(s − k)/Γ_ℝ(s)`) or its symmetrization `sinh(kx)/x`
defines two pure Gamma quadratic forms `backwardTateGammaForm` and `symTateGammaForm`:

* **Vanishing and dimension-zero 1-jet** (`backwardTateGammaForm_zero`, `symTateGammaForm_zero`,
  `hasDerivAt_backwardTateGammaForm_zero`, `hasDerivAt_symTateGammaForm_zero`): both vanish at
  `k = 0` and have two-sided `k = 0` derivative `archGammaForm H`.
* **Monotonicity on nonnegative profiles** (`backwardTateGammaForm_le_mul_archGammaForm_of_nonneg`,
  `symTateGammaForm_le_mul_archGammaForm_of_nonneg`): for `H ≥ 0` and `k ≥ 0`, both lie at or
  below `k · archGammaForm H`.
* **Explicit quadratic remainder** (`abs_backwardTateGammaForm_sub_linear_le`,
  `abs_symTateGammaForm_sub_linear_le`): for `|k| ≤ 1/4` and any window test `H`,
  `|A_k^Γ(H) − k · archGammaForm H| ≤ 18 k² ‖H‖²`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.ArchimedeanTateDomination

open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
open _root_.RHTower _root_.RHTower.WeilMarkovPole

/-! ### Exponential Taylor bound and tilted Lévy kernels -/

/-- Elementary calculus bound `|e^t − 1 − t| ≤ (t² / 2) e^{|t|}` for all real `t`. -/
theorem abs_exp_sub_one_sub_le (t : ℝ) :
    |Real.exp t - 1 - t| ≤ t ^ 2 / 2 * Real.exp |t| := by
  have hnn : 0 ≤ Real.exp t - 1 - t := by linarith [Real.add_one_le_exp t]
  rw [abs_of_nonneg hnn]
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    set g : ℝ → ℝ := fun s => s ^ 2 / 2 * Real.exp t - (Real.exp s - 1 - s)
    have hg_cont : ContinuousOn g (Icc 0 t) := by unfold g; fun_prop
    have hg_deriv : ∀ s ∈ Ioo 0 t,
        HasDerivAt g (s * Real.exp t - Real.exp s + 1) s := fun s _ => by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2 * Real.exp t) (s * Real.exp t) s := by
        simpa [ show 2 * s / 2 = s by ring ] using
          (((hasDerivAt_pow 2 s).div_const 2).mul_const (Real.exp t))
      have h2 : HasDerivAt (fun x : ℝ => Real.exp x - 1 - x) (Real.exp s - 1) s :=
        ((Real.hasDerivAt_exp s).sub_const 1).sub (hasDerivAt_id s)
      exact (h1.sub h2).congr_deriv (by ring)
    have hmono : MonotoneOn g (Icc 0 t) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 t) hg_cont
        (fun s hs => by
          rw [interior_Icc] at hs
          exact (hg_deriv s hs).differentiableAt.differentiableWithinAt)
        fun s hs => by
          rw [interior_Icc] at hs
          rw [(hg_deriv s hs).deriv]
          have h1 : (1 - s) * Real.exp s ≤ 1 := by
            have := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-s)) (Real.exp_pos s).le
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
            linarith
          have h2 : s * Real.exp s ≤ s * Real.exp t :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs.2.le) hs.1.le
          linarith
    have h0t := hmono (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
    dsimp only [g] at h0t
    norm_num at h0t
    linarith
  · set u := -t
    have hu : 0 ≤ u := by dsimp only [u]; linarith
    set h : ℝ → ℝ := fun s => s ^ 2 / 2 - (Real.exp (-s) - 1) - s
    have hh_cont : ContinuousOn h (Icc 0 u) := by unfold h; fun_prop
    have hh_deriv : ∀ s ∈ Ioo 0 u,
        HasDerivAt h (s + Real.exp (-s) - 1) s := fun s _ => by
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) s s := by
        simpa [show 2 * s / 2 = s by ring] using (hasDerivAt_pow 2 s).div_const 2
      have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-s) * -1) s :=
        (Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id s).neg
      exact ((h1.sub (hexp.sub_const 1)).sub (hasDerivAt_id s)).congr_deriv (by ring)
    have hmono : MonotoneOn h (Icc 0 u) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 u) hh_cont
        (fun s hs => by
          rw [interior_Icc] at hs
          exact (hh_deriv s hs).differentiableAt.differentiableWithinAt)
        fun s hs => by
          rw [interior_Icc] at hs
          rw [(hh_deriv s hs).deriv]
          linarith [Real.add_one_le_exp (-s)]
    have h0u := hmono (left_mem_Icc.mpr hu) (right_mem_Icc.mpr hu) hu
    dsimp only [h, u] at h0u
    norm_num at h0u
    have he1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
    have hmul : t ^ 2 / 2 * 1 ≤ t ^ 2 / 2 * Real.exp |t| :=
      mul_le_mul_of_nonneg_left he1 (by positivity)
    linarith

theorem abs_sinh_sub_le (t : ℝ) :
    |Real.sinh t - t| ≤ t ^ 2 / 2 * Real.exp |t| := by
  have hpt : Real.sinh t - t = ((Real.exp t - 1 - t) - (Real.exp (-t) - 1 - -t)) / 2 := by
    rw [Real.sinh_eq]
    ring
  rw [hpt, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have h1 := abs_exp_sub_one_sub_le t
  have h2 := abs_exp_sub_one_sub_le (-t)
  rw [neg_sq, abs_neg] at h2
  have h3 := (abs_sub_le (Real.exp t - 1 - t) 0 (Real.exp (-t) - 1 - -t))
  rw [sub_zero, zero_sub, abs_neg] at h3
  linarith

/-- The Esscher-tilted Gamma jump remainder kernel `ω(x) ((e^{kx} − 1)/x − k)`. -/
def backwardTateGammaKernel (k x : ℝ) : ℝ :=
  archLevyDensity x * ((Real.exp (k * x) - 1) / x - k)

/-- The symmetrized Tate-Gamma jump remainder kernel `ω(x) (sinh(kx)/x − k)`. -/
def symTateGammaKernel (k x : ℝ) : ℝ :=
  archLevyDensity x * (Real.sinh (k * x) / x - k)

private theorem archLevyDensity_mul_id_mul_exp_quarter_le {x : ℝ} (hx : 0 < x) :
    archLevyDensity x * (x * Real.exp (x / 4)) ≤
      Real.exp (-(1 / 4 * x)) / 2 + x * Real.exp (-(1 / 4 * x)) := by
  unfold archLevyDensity
  have hden : 2 * x / (1 + 2 * x) ≤ 1 - Real.exp (-2 * x) := by
    have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
    have h2 : Real.exp (-2 * x) ≤ 1 / (1 + 2 * x) := by
      rw [show -2 * x = -(2 * x) by ring, Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by positivity) h1
    have h3 : 2 * x / (1 + 2 * x) = 1 - 1 / (1 + 2 * x) := by field_simp; ring
    linarith
  have hden_pos : 0 < 2 * x / (1 + 2 * x) := by positivity
  have hdiv : Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) ≤
      Real.exp (-x / 2) / (2 * x / (1 + 2 * x)) :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le hden_pos hden
  have hexp : Real.exp (-x / 2) * Real.exp (x / 4) = Real.exp (-(1 / 4 * x)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (-x / 2) / (1 - Real.exp (-2 * x)) * (x * Real.exp (x / 4))
      ≤ (Real.exp (-x / 2) / (2 * x / (1 + 2 * x))) * (x * Real.exp (x / 4)) :=
        mul_le_mul_of_nonneg_right hdiv (by positivity)
    _ = (Real.exp (-x / 2) * Real.exp (x / 4)) * ((1 + 2 * x) / 2) := by
        field_simp
    _ = Real.exp (-(1 / 4 * x)) / 2 + x * Real.exp (-(1 / 4 * x)) := by
        rw [hexp]; ring

private theorem integrableOn_exp_neg_quarter :
    IntegrableOn (fun x : ℝ => Real.exp (-(1 / 4 * x))) (Ioi 0) := by
  have hG : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ ((1 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent zero_lt_one
  have hG1 : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Ioi 0) :=
    IntegrableOn.congr_fun hG (fun y _ => by
      show Real.exp (-y) * y ^ ((1 : ℝ) - 1) = Real.exp (-y)
      rw [sub_self, Real.rpow_zero, mul_one]) measurableSet_Ioi
  exact (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => Real.exp (-y)) 0
    (by norm_num : (0 : ℝ) < 1 / 4)).mpr (by simpa using hG1)

private theorem integrableOn_mul_exp_neg_quarter :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(1 / 4 * x))) (Ioi 0) := by
  have hG : IntegrableOn (fun y : ℝ => Real.exp (-y) * y ^ ((2 : ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent (by norm_num)
  have hG2 : IntegrableOn (fun y : ℝ => Real.exp (-y) * y) (Ioi 0) :=
    IntegrableOn.congr_fun hG (fun y _ => by
      show Real.exp (-y) * y ^ ((2 : ℝ) - 1) = Real.exp (-y) * y
      rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]) measurableSet_Ioi
  have hs : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 4 * x)) * (1 / 4 * x)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => Real.exp (-y) * y) 0
      (by norm_num : (0 : ℝ) < 1 / 4)).mpr (by simpa using hG2)
  refine IntegrableOn.congr_fun (hs.const_mul 4) (fun x _ => ?_) measurableSet_Ioi
  show 4 * (Real.exp (-(1 / 4 * x)) * (1 / 4 * x)) = x * Real.exp (-(1 / 4 * x))
  ring

private theorem integrableOn_tateMajorant :
    IntegrableOn (fun x : ℝ => archLevyDensity x * (x * Real.exp (x / 4))) (Ioi 0) := by
  have hdom : IntegrableOn
      (fun x : ℝ => Real.exp (-(1 / 4 * x)) / 2 + x * Real.exp (-(1 / 4 * x))) (Ioi 0) :=
    (integrableOn_exp_neg_quarter.div_const 2).add integrableOn_mul_exp_neg_quarter
  refine hdom.mono' ?_ ?_
  · exact (measurable_archLevyDensity.mul
      (measurable_id.mul (Real.continuous_exp.measurable.comp
        (measurable_id.div_const 4)))).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
    have hpos : 0 ≤ archLevyDensity x * (x * Real.exp (x / 4)) :=
      mul_nonneg (archLevyDensity_pos hx).le (mul_nonneg hx.le (Real.exp_pos _).le)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    exact archLevyDensity_mul_id_mul_exp_quarter_le hx

private theorem integral_archLevyDensity_mul_id_mul_exp_quarter_le :
    (∫ x in Ioi (0 : ℝ), archLevyDensity x * (x * Real.exp (x / 4))) ≤ 18 := by
  have hdom : IntegrableOn
      (fun x : ℝ => Real.exp (-(1 / 4 * x)) / 2 + x * Real.exp (-(1 / 4 * x))) (Ioi 0) :=
    (integrableOn_exp_neg_quarter.div_const 2).add integrableOn_mul_exp_neg_quarter
  have hmono := setIntegral_mono_on integrableOn_tateMajorant hdom measurableSet_Ioi
    fun x hx => archLevyDensity_mul_id_mul_exp_quarter_le hx
  have hi1 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := 1 / 4) zero_lt_one (by norm_num)
  have hi2 := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := 1 / 4) (by norm_num) (by norm_num)
  have he1 : (∫ x in Ioi (0 : ℝ), Real.exp (-(1 / 4 * x))) = 4 := by
    have hf : (fun t : ℝ => t ^ ((1 : ℝ) - 1) * Real.exp (-(1 / 4 * t))) =
        fun t => Real.exp (-(1 / 4 * t)) := by
      funext t; rw [sub_self, Real.rpow_zero, one_mul]
    rw [hf, Real.Gamma_one, show (1 : ℝ) / (1 / 4) = 4 by norm_num, Real.rpow_one] at hi1
    linarith
  have he2 : (∫ x in Ioi (0 : ℝ), x * Real.exp (-(1 / 4 * x))) = 16 := by
    have hf : (fun t : ℝ => t ^ ((2 : ℝ) - 1) * Real.exp (-(1 / 4 * t))) =
        fun t => t * Real.exp (-(1 / 4 * t)) := by
      funext t; rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    have hg2 : Real.Gamma 2 = 1 := by
      rw [show (2 : ℝ) = ((1 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
      norm_num [Nat.factorial]
    rw [hf, hg2, show (1 : ℝ) / (1 / 4) = 4 by norm_num, Real.rpow_two] at hi2
    norm_num at hi2
    exact hi2
  rw [integral_add (integrableOn_exp_neg_quarter.div_const 2) integrableOn_mul_exp_neg_quarter,
    integral_div, he1, he2] at hmono
  linarith

theorem abs_backwardTateGammaKernel_le {k x : ℝ} (hk : |k| ≤ 1 / 4) (hx : 0 < x) :
    |backwardTateGammaKernel k x| ≤
      k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) := by
  unfold backwardTateGammaKernel
  have hω := archLevyDensity_pos hx
  have heq : (Real.exp (k * x) - 1) / x - k = (Real.exp (k * x) - 1 - k * x) / x := by
    field_simp
  rw [heq, abs_mul, abs_div, abs_of_pos hω, abs_of_pos hx]
  have ht := abs_exp_sub_one_sub_le (k * x)
  have hexp : Real.exp |k * x| ≤ Real.exp (x / 4) := by
    rw [abs_mul, abs_of_pos hx]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hnum : |Real.exp (k * x) - 1 - k * x| ≤ (k * x) ^ 2 / 2 * Real.exp (x / 4) :=
    ht.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  calc archLevyDensity x * (|Real.exp (k * x) - 1 - k * x| / x)
      ≤ archLevyDensity x * (((k * x) ^ 2 / 2 * Real.exp (x / 4)) / x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hx.le) hω.le
    _ = k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) := by
        field_simp

theorem abs_symTateGammaKernel_le {k x : ℝ} (hk : |k| ≤ 1 / 4) (hx : 0 < x) :
    |symTateGammaKernel k x| ≤
      k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) := by
  unfold symTateGammaKernel
  have hω := archLevyDensity_pos hx
  have heq : Real.sinh (k * x) / x - k = (Real.sinh (k * x) - k * x) / x := by
    field_simp
  rw [heq, abs_mul, abs_div, abs_of_pos hω, abs_of_pos hx]
  have ht := abs_sinh_sub_le (k * x)
  have hexp : Real.exp |k * x| ≤ Real.exp (x / 4) := by
    rw [abs_mul, abs_of_pos hx]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hnum : |Real.sinh (k * x) - k * x| ≤ (k * x) ^ 2 / 2 * Real.exp (x / 4) :=
    ht.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  calc archLevyDensity x * (|Real.sinh (k * x) - k * x| / x)
      ≤ archLevyDensity x * (((k * x) ^ 2 / 2 * Real.exp (x / 4)) / x) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnum hx.le) hω.le
    _ = k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) := by
        field_simp

theorem backwardTateGammaKernel_nonneg (k : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ backwardTateGammaKernel k x := by
  unfold backwardTateGammaKernel
  refine mul_nonneg (archLevyDensity_pos hx).le ?_
  rw [sub_nonneg, le_div_iff₀ hx]
  linarith [Real.add_one_le_exp (k * x)]

theorem symTateGammaKernel_nonneg {k x : ℝ} (hk : 0 ≤ k) (hx : 0 < x) :
    0 ≤ symTateGammaKernel k x := by
  unfold symTateGammaKernel
  refine mul_nonneg (archLevyDensity_pos hx).le ?_
  rw [sub_nonneg, le_div_iff₀ hx]
  exact Real.self_le_sinh_iff.mpr (mul_nonneg hk hx.le)

/-! ### The Esscher-tilted and symmetrized Tate-Gamma quadratic forms -/

/-- The **Esscher-tilted (backward) archimedean Tate-Gamma form** in dimension `k`:
`k · archGammaForm H − 2 ∫_{x > 0} ω(x)((e^{kx} − 1)/x − k) c_H(x) dx`, the position-space
quadratic form of `∫_0^k 2 θ′_{1/2 − u}(τ) du` (`Γ_ℝ(s − k)/Γ_ℝ(s)`). -/
def backwardTateGammaForm (k : ℝ) (H : ℝ → ℝ) : ℝ :=
  k * archGammaForm H -
    2 * ∫ x in Ioi (0 : ℝ), backwardTateGammaKernel k x * ∫ u, H u * H (u + x)

/-- The **symmetrized archimedean Tate-Gamma form** in dimension `k`:
`k · archGammaForm H − 2 ∫_{x > 0} ω(x)(sinh(kx)/x − k) c_H(x) dx`. -/
def symTateGammaForm (k : ℝ) (H : ℝ → ℝ) : ℝ :=
  k * archGammaForm H -
    2 * ∫ x in Ioi (0 : ℝ), symTateGammaKernel k x * ∫ u, H u * H (u + x)

theorem backwardTateGammaForm_zero (H : ℝ → ℝ) : backwardTateGammaForm 0 H = 0 := by
  simp [backwardTateGammaForm, backwardTateGammaKernel]

theorem symTateGammaForm_zero (H : ℝ → ℝ) : symTateGammaForm 0 H = 0 := by
  simp [symTateGammaForm, symTateGammaKernel]

/-- On every nonnegative profile `H ≥ 0` and every `k ∈ ℝ`, `backwardTateGammaForm k H` lies
at or below `k · archGammaForm H`. -/
theorem backwardTateGammaForm_le_mul_archGammaForm_of_nonneg {H : ℝ → ℝ} (hpos : ∀ u, 0 ≤ H u)
    (k : ℝ) :
    backwardTateGammaForm k H ≤ k * archGammaForm H := by
  unfold backwardTateGammaForm
  have hnn : 0 ≤ ∫ x in Ioi (0 : ℝ), backwardTateGammaKernel k x * ∫ u, H u * H (u + x) :=
    setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (backwardTateGammaKernel_nonneg k hx)
        (integral_nonneg fun u => mul_nonneg (hpos u) (hpos _))
  linarith

/-- On every nonnegative profile `H ≥ 0` and every `k ≥ 0`, `symTateGammaForm k H` lies
at or below `k · archGammaForm H`. -/
theorem symTateGammaForm_le_mul_archGammaForm_of_nonneg {H : ℝ → ℝ} (hpos : ∀ u, 0 ≤ H u)
    {k : ℝ} (hk : 0 ≤ k) :
    symTateGammaForm k H ≤ k * archGammaForm H := by
  unfold symTateGammaForm
  have hnn : 0 ≤ ∫ x in Ioi (0 : ℝ), symTateGammaKernel k x * ∫ u, H u * H (u + x) :=
    setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (symTateGammaKernel_nonneg hk hx)
        (integral_nonneg fun u => mul_nonneg (hpos u) (hpos _))
  linarith

/-- Explicit quadratic remainder bound `|backwardTateGammaForm k H − k · archGammaForm H| ≤ 18 k² ‖H‖²`
for `|k| ≤ 1/4`. -/
theorem abs_backwardTateGammaForm_sub_linear_le {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {k : ℝ} (hk : |k| ≤ 1 / 4) :
    |backwardTateGammaForm k H - k * archGammaForm H| ≤ 18 * k ^ 2 * ∫ u, H u ^ 2 := by
  have hE : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hc_auto : Continuous fun x => ∫ u, H u * H (u + x) :=
    _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hH.contDiff hH.hasCompactSupport
  have hdom : IntegrableOn
      (fun x : ℝ => k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) * ∫ u, H u ^ 2)
      (Ioi 0) := (integrableOn_tateMajorant.const_mul (k ^ 2 / 2)).mul_const _
  have hint_abs : IntegrableOn
      (fun x : ℝ => |backwardTateGammaKernel k x * ∫ u, H u * H (u + x)|) (Ioi 0) := by
    refine hdom.mono' ?_ ?_
    · have hm : Measurable (backwardTateGammaKernel k) :=
        measurable_archLevyDensity.mul (by fun_prop)
      exact (hm.mul hc_auto.measurable).abs.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      rw [Real.norm_eq_abs, abs_abs, abs_mul]
      exact mul_le_mul (abs_backwardTateGammaKernel_le hk hx) (abs_autocorr_le_norm_sq hH x)
        (abs_nonneg _) (mul_nonneg (by positivity)
          (mul_nonneg (archLevyDensity_pos hx).le (mul_nonneg hx.le (Real.exp_pos _).le)))
  have hdiff : backwardTateGammaForm k H - k * archGammaForm H =
      -2 * ∫ x in Ioi (0 : ℝ), backwardTateGammaKernel k x * ∫ u, H u * H (u + x) := by
    unfold backwardTateGammaForm; ring
  rw [hdiff, abs_mul, abs_neg, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have h1 : |∫ x in Ioi (0 : ℝ), backwardTateGammaKernel k x * ∫ u, H u * H (u + x)| ≤
      ∫ x in Ioi (0 : ℝ), |backwardTateGammaKernel k x * ∫ u, H u * H (u + x)| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (fun x => backwardTateGammaKernel k x * ∫ u, H u * H (u + x))
  have h2 : ∫ x in Ioi (0 : ℝ), |backwardTateGammaKernel k x * ∫ u, H u * H (u + x)| ≤
      ∫ x in Ioi (0 : ℝ),
        k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) * ∫ u, H u ^ 2 := by
    refine setIntegral_mono_on hint_abs hdom measurableSet_Ioi fun x hx => ?_
    rw [abs_mul]
    exact mul_le_mul (abs_backwardTateGammaKernel_le hk hx) (abs_autocorr_le_norm_sq hH x)
      (abs_nonneg _) (mul_nonneg (by positivity)
        (mul_nonneg (archLevyDensity_pos hx).le (mul_nonneg hx.le (Real.exp_pos _).le)))
  have h3 : (∫ x in Ioi (0 : ℝ),
      k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) * ∫ u, H u ^ 2) =
      k ^ 2 / 2 * (∫ x in Ioi (0 : ℝ), archLevyDensity x * (x * Real.exp (x / 4))) *
        ∫ u, H u ^ 2 := by
    rw [integral_mul_const, integral_const_mul]
  have h4 := integral_archLevyDensity_mul_id_mul_exp_quarter_le
  have h5 : k ^ 2 / 2 * (∫ x in Ioi (0 : ℝ), archLevyDensity x * (x * Real.exp (x / 4))) *
      (∫ u, H u ^ 2) ≤ k ^ 2 / 2 * 18 * ∫ u, H u ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by positivity)) hE
  linarith [h1.trans (h2.trans (h3.le.trans h5))]

/-- Explicit quadratic remainder bound `|symTateGammaForm k H − k · archGammaForm H| ≤ 18 k² ‖H‖²`
for `|k| ≤ 1/4`. -/
theorem abs_symTateGammaForm_sub_linear_le {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H)
    {k : ℝ} (hk : |k| ≤ 1 / 4) :
    |symTateGammaForm k H - k * archGammaForm H| ≤ 18 * k ^ 2 * ∫ u, H u ^ 2 := by
  have hE : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hc_auto : Continuous fun x => ∫ u, H u * H (u + x) :=
    _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hH.contDiff hH.hasCompactSupport
  have hdom : IntegrableOn
      (fun x : ℝ => k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) * ∫ u, H u ^ 2)
      (Ioi 0) := (integrableOn_tateMajorant.const_mul (k ^ 2 / 2)).mul_const _
  have hint_abs : IntegrableOn
      (fun x : ℝ => |symTateGammaKernel k x * ∫ u, H u * H (u + x)|) (Ioi 0) := by
    refine hdom.mono' ?_ ?_
    · have hm : Measurable (symTateGammaKernel k) :=
        measurable_archLevyDensity.mul (by fun_prop)
      exact (hm.mul hc_auto.measurable).abs.aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      rw [Real.norm_eq_abs, abs_abs, abs_mul]
      exact mul_le_mul (abs_symTateGammaKernel_le hk hx) (abs_autocorr_le_norm_sq hH x)
        (abs_nonneg _) (mul_nonneg (by positivity)
          (mul_nonneg (archLevyDensity_pos hx).le (mul_nonneg hx.le (Real.exp_pos _).le)))
  have hdiff : symTateGammaForm k H - k * archGammaForm H =
      -2 * ∫ x in Ioi (0 : ℝ), symTateGammaKernel k x * ∫ u, H u * H (u + x) := by
    unfold symTateGammaForm; ring
  rw [hdiff, abs_mul, abs_neg, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  have h1 : |∫ x in Ioi (0 : ℝ), symTateGammaKernel k x * ∫ u, H u * H (u + x)| ≤
      ∫ x in Ioi (0 : ℝ), |symTateGammaKernel k x * ∫ u, H u * H (u + x)| := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (fun x => symTateGammaKernel k x * ∫ u, H u * H (u + x))
  have h2 : ∫ x in Ioi (0 : ℝ), |symTateGammaKernel k x * ∫ u, H u * H (u + x)| ≤
      ∫ x in Ioi (0 : ℝ),
        k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) * ∫ u, H u ^ 2 := by
    refine setIntegral_mono_on hint_abs hdom measurableSet_Ioi fun x hx => ?_
    rw [abs_mul]
    exact mul_le_mul (abs_symTateGammaKernel_le hk hx) (abs_autocorr_le_norm_sq hH x)
      (abs_nonneg _) (mul_nonneg (by positivity)
        (mul_nonneg (archLevyDensity_pos hx).le (mul_nonneg hx.le (Real.exp_pos _).le)))
  have h3 : (∫ x in Ioi (0 : ℝ),
      k ^ 2 / 2 * (archLevyDensity x * (x * Real.exp (x / 4))) * ∫ u, H u ^ 2) =
      k ^ 2 / 2 * (∫ x in Ioi (0 : ℝ), archLevyDensity x * (x * Real.exp (x / 4))) *
        ∫ u, H u ^ 2 := by
    rw [integral_mul_const, integral_const_mul]
  have h4 := integral_archLevyDensity_mul_id_mul_exp_quarter_le
  have h5 : k ^ 2 / 2 * (∫ x in Ioi (0 : ℝ), archLevyDensity x * (x * Real.exp (x / 4))) *
      (∫ u, H u ^ 2) ≤ k ^ 2 / 2 * 18 * ∫ u, H u ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 (by positivity)) hE
  linarith [h1.trans (h2.trans (h3.le.trans h5))]

/-- Two-sided derivative at `k = 0`: `∂_k backwardTateGammaForm k H |_{k=0} = archGammaForm H`. -/
theorem hasDerivAt_backwardTateGammaForm_zero {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    HasDerivAt (fun k => backwardTateGammaForm k H) (archGammaForm H) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h0 : Tendsto (fun t : ℝ => (18 * ∫ u, H u ^ 2) * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => (18 * ∫ u, H u ^ 2) * |t| := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr <|
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [nhdsWithin_le_nhds
      (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)),
    self_mem_nhdsWithin] with t ht hne
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
  rw [Set.mem_compl_singleton_iff] at hne
  simp only [zero_add, backwardTateGammaForm_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs]
  have hrew : t⁻¹ * backwardTateGammaForm t H - archGammaForm H =
      (backwardTateGammaForm t H - t * archGammaForm H) / t := by
    field_simp [hne]
  rw [hrew, abs_div]
  have hb := abs_backwardTateGammaForm_sub_linear_le hH ht
  have habs_pos : 0 < |t| := abs_pos.mpr hne
  rw [div_le_iff₀ habs_pos]
  calc |backwardTateGammaForm t H - t * archGammaForm H|
      ≤ 18 * t ^ 2 * ∫ u, H u ^ 2 := hb
    _ = (18 * ∫ u, H u ^ 2) * |t| * |t| := by rw [← sq_abs t]; ring

/-- Two-sided derivative at `k = 0`: `∂_k symTateGammaForm k H |_{k=0} = archGammaForm H`. -/
theorem hasDerivAt_symTateGammaForm_zero {A : ℝ} {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    HasDerivAt (fun k => symTateGammaForm k H) (archGammaForm H) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h0 : Tendsto (fun t : ℝ => (18 * ∫ u, H u ^ 2) * |t|) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => (18 * ∫ u, H u ^ 2) * |t| := by fun_prop
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr <|
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
  filter_upwards [nhdsWithin_le_nhds
      (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)),
    self_mem_nhdsWithin] with t ht hne
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
  rw [Set.mem_compl_singleton_iff] at hne
  simp only [zero_add, symTateGammaForm_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs]
  have hrew : t⁻¹ * symTateGammaForm t H - archGammaForm H =
      (symTateGammaForm t H - t * archGammaForm H) / t := by
    field_simp [hne]
  rw [hrew, abs_div]
  have hb := abs_symTateGammaForm_sub_linear_le hH ht
  have habs_pos : 0 < |t| := abs_pos.mpr hne
  rw [div_le_iff₀ habs_pos]
  calc |symTateGammaForm t H - t * archGammaForm H|
      ≤ 18 * t ^ 2 * ∫ u, H u ^ 2 := hb
    _ = (18 * ∫ u, H u ^ 2) * |t| * |t| := by rw [← sq_abs t]; ring

end GaloisForLFunctions.ArchimedeanTateDomination

#print axioms GaloisForLFunctions.ArchimedeanTateDomination.hasDerivAt_backwardTateGammaForm_zero
#print axioms GaloisForLFunctions.ArchimedeanTateDomination.hasDerivAt_symTateGammaForm_zero
