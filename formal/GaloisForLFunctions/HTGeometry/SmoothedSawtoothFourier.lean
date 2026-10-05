import Mathlib

/-!
# The sawtooth split into a smooth trigonometric part and a positive majorant

Let `ψ(y) = {y} − 1/2` (`saw`).  For every `Δ > 0` there are coefficients `a, k : ℤ → ℂ` with

* `a 0 = 0`, `|a_h| ≤ A min(1, (hΔ)^{−2})/|h|`,
* `|k_h| ≤ A Δ min(1, (hΔ)^{−2})`,

such that for every finite family of points `y_i`, coefficients `c_i` and weights `β_i ≥ |c_i|`,

`|Σ c_i ψ(y_i)| ≤ Σ_h |a_h| |Σ c_i e(h y_i)| + Σ_h |k_h| |Σ β_i e(h y_i)|`
(`exists_saw_decomposition`), with `A` absolute.

**Construction.**  `ψ_Δ = φ_Δ ∗ ψ` with `φ_Δ(t) = Δ^{−1}φ(t/Δ)` a normalized even bump supported in
`(−Δ, Δ)`.  It is the periodization of the Schwartz function `G = φ_Δ ∗ g₀`, `g₀ = (u − 1/2) 1_{[0,1)}`,
so by Poisson summation `ψ_Δ(y) = Σ_h 𝓕G(h) e(hy)` with `𝓕G(h) = 𝓕φ(hΔ) 𝓕g₀(h)`,
`𝓕g₀(h) = 1/(−2πih)` for `h ≠ 0` and `𝓕g₀(0) = 0`.  If `[y − Δ, y + Δ]` contains no integer then
`ψ(y − t) = ψ(y) − t` on the support of `φ_Δ`, and evenness gives `ψ_Δ(y) = ψ(y)`; otherwise
`|ψ − ψ_Δ| ≤ 1`.  The majorant is the periodization `K(y) = Σ_n κ((y + n)/Δ)` of a bump equal to `1`
on `[−1, 1]`, whose Fourier coefficients are `Δ 𝓕κ(hΔ)`.
-/

open Set Function Filter MeasureTheory Real Complex
open scoped FourierTransform ContDiff

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SmoothedSawtooth

/-- The centred sawtooth `ψ(y) = {y} − 1/2`. -/
def saw (y : ℝ) : ℝ := Int.fract y - 1 / 2

theorem abs_saw_le (y : ℝ) : |saw y| ≤ 1 / 2 := by
  unfold saw
  rw [abs_le]
  constructor <;> linarith [Int.fract_nonneg y, Int.fract_lt_one y]

/-- One period of the sawtooth, `(u − 1/2) 1_{[0,1)}(u)`. -/
def sawCell (u : ℝ) : ℂ := (Ico (0 : ℝ) 1).indicator (fun u => ((u - 1 / 2 : ℝ) : ℂ)) u

theorem sawCell_add_int_eq_zero {y : ℝ} {n : ℤ} (hn : n ≠ -⌊y⌋) : sawCell (y + n) = 0 := by
  unfold sawCell
  rw [Set.indicator_of_notMem]
  intro h
  apply hn
  have h1 : ⌊y + n⌋ = 0 := Int.floor_eq_iff.mpr ⟨by simpa using h.1, by simpa using h.2⟩
  rw [Int.floor_add_intCast] at h1
  omega

/-- The periodization of one cell is the sawtooth. -/
theorem tsum_sawCell (y : ℝ) : ∑' n : ℤ, sawCell (y + n) = (saw y : ℂ) := by
  rw [tsum_eq_single (-⌊y⌋) fun n hn => sawCell_add_int_eq_zero hn]
  unfold sawCell saw
  have h : y + ((-⌊y⌋ : ℤ) : ℝ) = Int.fract y := by
    rw [Int.fract]; push_cast; ring
  rw [h, Set.indicator_of_mem (show Int.fract y ∈ Ico (0 : ℝ) 1 from
    ⟨Int.fract_nonneg y, Int.fract_lt_one y⟩)]

theorem norm_sawCell_le (u : ℝ) : ‖sawCell u‖ ≤ 1 / 2 := by
  unfold sawCell
  by_cases hu : u ∈ Ico (0 : ℝ) 1
  · rw [Set.indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hu.1, hu.2]
  · rw [Set.indicator_of_notMem hu]; norm_num

theorem sawCell_eq_zero_of_notMem {u : ℝ} (hu : u ∉ Ico (0 : ℝ) 1) : sawCell u = 0 := by
  unfold sawCell; rw [Set.indicator_of_notMem hu]

theorem integrable_sawCell : Integrable sawCell := by
  unfold sawCell
  exact ((Continuous.integrableOn_Icc (μ := volume) (a := 0) (b := 1)
    (by fun_prop : Continuous fun u : ℝ => ((u - 1 / 2 : ℝ) : ℂ))).mono_set
      Ico_subset_Icc_self).integrable_indicator measurableSet_Ico

theorem hasCompactSupport_sawCell : HasCompactSupport sawCell :=
  HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun _ hu =>
    sawCell_eq_zero_of_notMem fun h => hu (Ico_subset_Icc_self h)

/-! ## The Fourier transform of one cell -/

/-- `𝓕g₀(h) = 1/(−2πih)` for `h ≠ 0`. -/
theorem fourier_sawCell_int {h : ℤ} (hh : h ≠ 0) :
    𝓕 sawCell (h : ℝ) = 1 / (-(2 * π * I * (h : ℂ))) := by
  set c : ℂ := -(2 * π * I * (h : ℂ)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, neg_ne_zero]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) I_ne_zero) ?_
    · exact_mod_cast Real.pi_ne_zero
    · exact_mod_cast hh
  rw [Real.fourier_real_eq]
  have hind : ∀ v : ℝ, 𝐞 (-(v * (h : ℝ))) • sawCell v =
      (Ico (0 : ℝ) 1).indicator (fun v => Complex.exp (c * v) * ((v - 1 / 2 : ℝ) : ℂ)) v := by
    intro v
    unfold sawCell
    by_cases hv : v ∈ Ico (0 : ℝ) 1
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv, Circle.smul_def, Real.fourierChar_apply,
        smul_eq_mul, hc]
      congr 1
      congr 1
      push_cast; ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv, smul_zero]
  simp_rw [hind]
  rw [integral_indicator measurableSet_Ico, ← integral_Icc_eq_integral_Ico,
    ← intervalIntegral.integral_of_le zero_le_one |>.trans integral_Icc_eq_integral_Ioc.symm]
  -- antiderivative `e^{cv}((v − 1/2)/c − 1/c²)`
  set F : ℝ → ℂ := fun v => Complex.exp (c * v) * ((((v - 1 / 2 : ℝ) : ℂ)) / c - 1 / c ^ 2) with hF
  have hFd : ∀ v ∈ uIcc (0 : ℝ) 1, HasDerivAt F (Complex.exp (c * v) * ((v - 1 / 2 : ℝ) : ℂ)) v := by
    intro v _
    have h1 : HasDerivAt (fun v : ℝ => Complex.exp (c * v)) (Complex.exp (c * v) * c) v := by
      have := ((hasDerivAt_id (v : ℂ)).const_mul c).cexp.comp_ofReal (z := v)
      simpa using this
    have h2 : HasDerivAt (fun v : ℝ => (((v - 1 / 2 : ℝ) : ℂ)) / c - 1 / c ^ 2) (1 / c) v := by
      have := ((hasDerivAt_id v).sub_const (1 / 2 : ℝ)).ofReal_comp.div_const c
      simpa using this.sub_const (1 / c ^ 2)
    exact (h1.mul h2).congr_deriv (by field_simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFd
    ((by fun_prop : Continuous fun v : ℝ => Complex.exp (c * v) * ((v - 1 / 2 : ℝ) : ℂ)).intervalIntegrable _ _)]
  have he : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
    rw [hc, Complex.ofReal_one, mul_one, show -(2 * π * I * (h : ℂ)) = (-h : ℤ) * (2 * π * I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-h)
  simp only [hF, he, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  field_simp
  push_cast
  ring

theorem fourier_sawCell_zero : 𝓕 sawCell 0 = 0 := by
  rw [Real.fourier_real_eq]
  have hind : ∀ v : ℝ, 𝐞 (-(v * 0)) • sawCell v = sawCell v := by
    intro v; simp
  simp_rw [hind]
  unfold sawCell
  rw [integral_indicator measurableSet_Ico, ← integral_Icc_eq_integral_Ico,
    ← intervalIntegral.integral_of_le zero_le_one |>.trans integral_Icc_eq_integral_Ioc.symm]
  have : ∫ v in (0 : ℝ)..1, (((v - 1 / 2 : ℝ)) : ℂ) = (((∫ v in (0 : ℝ)..1, (v - 1 / 2)) : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  rw [this]
  simp [integral_id]

theorem norm_fourier_sawCell_int_le (h : ℤ) : ‖𝓕 sawCell (h : ℝ)‖ ≤ 1 / (2 * π * |(h : ℝ)|) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp [fourier_sawCell_zero]
  rw [fourier_sawCell_int hh, norm_div, norm_one, norm_neg, norm_mul, norm_mul, norm_mul,
    Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_two, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have : ‖(h : ℂ)‖ = |(h : ℝ)| := by
    rw [show (h : ℂ) = ((h : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real, Real.norm_eq_abs]
  rw [this]

/-! ## Scaling and decay of Fourier transforms -/

/-- `𝓕[g(·/Δ)](ξ) = Δ 𝓕g(Δξ)` for `Δ > 0`. -/
theorem fourier_comp_div {g : ℝ → ℂ} {Δ : ℝ} (hΔ : 0 < Δ) (ξ : ℝ) :
    𝓕 (fun t => g (t / Δ)) ξ = (Δ : ℂ) * 𝓕 g (Δ * ξ) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have h := Measure.integral_comp_div (fun u : ℝ => 𝐞 (-(u * (Δ * ξ))) • g u) Δ
  rw [abs_of_pos hΔ, Complex.real_smul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  congr 2
  field_simp

/-- A Schwartz function has `|𝓕g(ξ)| ≤ C/(1 + ξ²)`. -/
theorem exists_norm_fourier_le (g : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, ‖𝓕 (g : ℝ → ℂ) ξ‖ ≤ C * (1 + ξ ^ 2)⁻¹ := by
  obtain ⟨C₀, hC₀, h₀⟩ := (𝓕 g : SchwartzMap ℝ ℂ).decay 0 0
  obtain ⟨C₂, hC₂, h₂⟩ := (𝓕 g : SchwartzMap ℝ ℂ).decay 2 0
  refine ⟨C₀ + C₂, by positivity, fun ξ => ?_⟩
  have e : ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (g : ℝ → ℂ) := SchwartzMap.fourier_coe g
  have a0 := h₀ ξ
  have a2 := h₂ ξ
  rw [norm_iteratedFDeriv_zero, e, pow_zero, one_mul] at a0
  rw [norm_iteratedFDeriv_zero, e, Real.norm_eq_abs, sq_abs] at a2
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith

/-! ## The mollifier -/

/-- A smooth bump supported in `(−1, 1)`. -/
def molBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The normalized even mollifier `φ` with `∫ φ = 1`, supported in `(−1, 1)`. -/
def mol (t : ℝ) : ℝ := molBump.normed volume t

theorem mol_nonneg (t : ℝ) : 0 ≤ mol t := molBump.nonneg_normed t

theorem mol_neg (t : ℝ) : mol (-t) = mol t := molBump.normed_neg t

theorem integral_mol : ∫ t, mol t = 1 := molBump.integral_normed

theorem mol_eq_zero {t : ℝ} (ht : 1 ≤ |t|) : mol t = 0 := by
  by_contra h
  have hm : t ∈ Function.support mol := h
  have : Function.support mol = Metric.ball 0 1 := molBump.support_normed_eq
  rw [this, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hm
  linarith

theorem contDiff_mol : ContDiff ℝ ∞ mol := molBump.contDiff_normed

theorem hasCompactSupport_mol : HasCompactSupport mol := molBump.hasCompactSupport_normed

/-- `φ_Δ(t) = Δ^{−1} φ(t/Δ)`. -/
def molScaled (Δ : ℝ) (t : ℝ) : ℂ := ((Δ⁻¹ * mol (t / Δ) : ℝ) : ℂ)

theorem molScaled_eq_zero {Δ : ℝ} (hΔ : 0 < Δ) {t : ℝ} (ht : Δ ≤ |t|) : molScaled Δ t = 0 := by
  unfold molScaled
  rw [mol_eq_zero (by rw [abs_div, abs_of_pos hΔ, le_div_iff₀ hΔ]; linarith)]
  simp

theorem molScaled_nonneg (Δ : ℝ) (hΔ : 0 < Δ) (t : ℝ) : 0 ≤ Δ⁻¹ * mol (t / Δ) :=
  mul_nonneg (inv_nonneg.mpr hΔ.le) (mol_nonneg _)

theorem continuous_molScaled (Δ : ℝ) : Continuous (molScaled Δ) := by
  unfold molScaled
  exact continuous_ofReal.comp (continuous_const.mul
    (molBump.continuous_normed.comp (continuous_id.div_const Δ)))

theorem contDiff_molScaled (Δ : ℝ) : ContDiff ℝ ∞ (molScaled Δ) := by
  unfold molScaled
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
    (contDiff_mol.comp (contDiff_id.div_const Δ)))

theorem hasCompactSupport_molScaled {Δ : ℝ} (hΔ : 0 < Δ) : HasCompactSupport (molScaled Δ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -Δ) (b := Δ)) fun t ht => by
    refine molScaled_eq_zero hΔ ?_
    by_contra h
    push Not at h
    exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

theorem integrable_molScaled {Δ : ℝ} (hΔ : 0 < Δ) : Integrable (molScaled Δ) :=
  (continuous_molScaled Δ).integrable_of_hasCompactSupport (hasCompactSupport_molScaled hΔ)

theorem integral_molScaled {Δ : ℝ} (hΔ : 0 < Δ) : ∫ t, molScaled Δ t = 1 := by
  unfold molScaled
  rw [integral_complex_ofReal, integral_const_mul]
  have h := Measure.integral_comp_div mol Δ
  rw [abs_of_pos hΔ, smul_eq_mul, integral_mol, mul_one] at h
  rw [h, inv_mul_cancel₀ hΔ.ne']
  simp

/-- `∫ t φ_Δ(t) dt = 0`. -/
theorem integral_mul_molScaled (Δ : ℝ) : ∫ t : ℝ, (t : ℂ) * molScaled Δ t = 0 := by
  have h := integral_neg_eq_self (fun t : ℝ => (t : ℂ) * molScaled Δ t) volume
  have hodd : ∀ t : ℝ, ((-t : ℝ) : ℂ) * molScaled Δ (-t) = -((t : ℂ) * molScaled Δ t) := by
    intro t
    unfold molScaled
    rw [neg_div, mol_neg]
    push_cast; ring
  simp_rw [hodd, integral_neg] at h
  have : (2 : ℂ) * ∫ t : ℝ, (t : ℂ) * molScaled Δ t = 0 := by
    rw [two_mul]; nth_rewrite 1 [← h]; ring
  simpa using this

/-- The mollifier with complex values. -/
def molC (t : ℝ) : ℂ := (mol t : ℂ)

theorem fourier_molScaled {Δ : ℝ} (hΔ : 0 < Δ) (ξ : ℝ) :
    𝓕 (molScaled Δ) ξ = 𝓕 molC (Δ * ξ) := by
  have e : molScaled Δ = fun t => ((Δ⁻¹ : ℝ) : ℂ) * molC (t / Δ) := by
    funext t; unfold molScaled molC; push_cast; ring
  have hlin : 𝓕 (fun t => ((Δ⁻¹ : ℝ) : ℂ) * molC (t / Δ)) ξ =
      ((Δ⁻¹ : ℝ) : ℂ) * 𝓕 (fun t => molC (t / Δ)) ξ := by
    rw [Real.fourier_real_eq, Real.fourier_real_eq, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul, Circle.smul_def]
    ring
  rw [e, hlin, fourier_comp_div hΔ, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hΔ.ne']
  simp

/-- The mollifier as a Schwartz function. -/
def molSchwartz : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_mol.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp contDiff_mol)

theorem molSchwartz_coe : (molSchwartz : ℝ → ℂ) = molC := rfl

/-! ## The smoothed sawtooth -/

/-- `ψ_Δ(y) = ∫ φ_Δ(t) ψ(y − t) dt`. -/
def sawSmooth (Δ y : ℝ) : ℂ := ∫ t, molScaled Δ t * (saw (y - t) : ℂ)

theorem integrable_molScaled_mul {Δ : ℝ} (hΔ : 0 < Δ) {g : ℝ → ℂ} (hg : AEStronglyMeasurable g)
    {B : ℝ} (hB : ∀ t, ‖g t‖ ≤ B) : Integrable fun t => molScaled Δ t * g t :=
  (integrable_molScaled hΔ).mul_bdd hg (Eventually.of_forall hB)

theorem measurable_saw : Measurable saw := by
  unfold saw; fun_prop

theorem norm_sawSmooth_le {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) : ‖sawSmooth Δ y‖ ≤ 1 / 2 := by
  unfold sawSmooth
  calc ‖∫ t, molScaled Δ t * (saw (y - t) : ℂ)‖ ≤ ∫ t, ‖molScaled Δ t‖ * (1 / 2) := by
        refine norm_integral_le_of_norm_le ((integrable_molScaled hΔ).norm.mul_const _)
          (Eventually.of_forall fun t => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (abs_saw_le _) (norm_nonneg _)
    _ = 1 / 2 := by
        rw [integral_mul_const]
        have : ∫ t, ‖molScaled Δ t‖ = 1 := by
          have h1 : ∀ t, ‖molScaled Δ t‖ = Δ⁻¹ * mol (t / Δ) := fun t => by
            unfold molScaled
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (molScaled_nonneg Δ hΔ t)]
          simp_rw [h1]
          have h2 := integral_molScaled hΔ
          unfold molScaled at h2
          rw [integral_complex_ofReal] at h2
          exact_mod_cast h2
        rw [this, one_mul]

/-- Away from the integers the mollification does not move the sawtooth. -/
theorem sawSmooth_eq {Δ : ℝ} (hΔ : 0 < Δ) {y : ℝ} (hy : ∀ n : ℤ, Δ < |y - n|) :
    sawSmooth Δ y = saw y := by
  set k := ⌊y⌋ with hk
  have h1 : Δ < y - k := by
    have := hy k
    rwa [abs_of_nonneg (by linarith [Int.floor_le y])] at this
  have h2 : Δ < k + 1 - y := by
    have := hy (k + 1)
    rw [abs_of_neg (by push_cast; linarith [Int.lt_floor_add_one y])] at this
    push_cast at this; linarith
  have hpt : ∀ t : ℝ, molScaled Δ t * (saw (y - t) : ℂ) =
      molScaled Δ t * ((saw y : ℂ) - (t : ℂ)) := by
    intro t
    by_cases ht : Δ ≤ |t|
    · rw [molScaled_eq_zero hΔ ht]; simp
    · push Not at ht
      have hfl : ⌊y - t⌋ = k := by
        rw [Int.floor_eq_iff]
        constructor <;> linarith [neg_abs_le t, le_abs_self t]
      congr 1
      unfold saw
      rw [Int.fract, Int.fract, hfl, ← hk]
      push_cast; ring
  unfold sawSmooth
  simp_rw [hpt, mul_sub]
  have hI1 : Integrable fun t => molScaled Δ t * (saw y : ℂ) :=
    (integrable_molScaled hΔ).mul_const _
  have hI2 : Integrable fun t : ℝ => molScaled Δ t * (t : ℂ) :=
    ((continuous_molScaled Δ).mul continuous_ofReal).integrable_of_hasCompactSupport
      (hasCompactSupport_molScaled hΔ).mul_right
  rw [integral_sub hI1 hI2, integral_mul_const, integral_molScaled hΔ, one_mul]
  have h0 : ∫ t : ℝ, molScaled Δ t * (t : ℂ) = 0 := by
    have := integral_mul_molScaled Δ
    simpa [mul_comm] using this
  rw [h0, sub_zero]

/-! ## The periodized convolution and Poisson summation -/

/-- `G = φ_Δ ∗ g₀`. -/
def cellSmooth (Δ : ℝ) : ℝ → ℂ :=
  convolution (molScaled Δ) sawCell (ContinuousLinearMap.mul ℝ ℂ) volume

theorem cellSmooth_apply (Δ x : ℝ) :
    cellSmooth Δ x = ∫ t, molScaled Δ t * sawCell (x - t) := by
  simp [cellSmooth, convolution_def]

theorem contDiff_cellSmooth {Δ : ℝ} (hΔ : 0 < Δ) : ContDiff ℝ ∞ (cellSmooth Δ) :=
  (hasCompactSupport_molScaled hΔ).contDiff_convolution_left _ (contDiff_molScaled Δ)
    integrable_sawCell.locallyIntegrable

theorem hasCompactSupport_cellSmooth {Δ : ℝ} (hΔ : 0 < Δ) : HasCompactSupport (cellSmooth Δ) :=
  (hasCompactSupport_molScaled hΔ).convolution _ hasCompactSupport_sawCell

/-- `G` as a Schwartz function. -/
def cellSchwartz {Δ : ℝ} (hΔ : 0 < Δ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_cellSmooth hΔ).toSchwartzMap (contDiff_cellSmooth hΔ)

theorem measurable_sawCell : Measurable sawCell :=
  (by fun_prop : Measurable fun u : ℝ => ((u - 1 / 2 : ℝ) : ℂ)).indicator measurableSet_Ico

theorem integrable_molScaled_mul_sawCell {Δ : ℝ} (hΔ : 0 < Δ) (x : ℝ) :
    Integrable fun t => molScaled Δ t * sawCell (x - t) :=
  integrable_molScaled_mul hΔ
    (measurable_sawCell.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (B := 1 / 2) fun _ => norm_sawCell_le _

/-- **Periodization.**  `Σ_n G(y + n) = ψ_Δ(y)`. -/
theorem tsum_cellSmooth {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) :
    ∑' n : ℤ, cellSmooth Δ (y + n) = sawSmooth Δ y := by
  set N : ℕ := ⌈|y| + Δ⌉₊ + 2 with hN
  have hNle : |y| + Δ + 2 ≤ (N : ℝ) := by
    have := Nat.le_ceil (|y| + Δ); rw [hN]; push_cast; linarith
  have hvan : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) N → ∀ t : ℝ,
      molScaled Δ t * sawCell (y + n - t) = 0 := by
    intro n hn t
    by_cases ht : Δ ≤ |t|
    · rw [molScaled_eq_zero hΔ ht, zero_mul]
    · push Not at ht
      rw [sawCell_eq_zero_of_notMem, mul_zero]
      intro hmem
      apply hn
      rw [Finset.mem_Icc]
      have h1 := hmem.1
      have h2 := hmem.2
      have ht1 := le_abs_self t
      have ht2 := neg_abs_le t
      have hy1 := le_abs_self y
      have hy2 := neg_abs_le y
      constructor
      · have : (-(N : ℤ) : ℝ) ≤ n := by push_cast; linarith
        exact_mod_cast this
      · have : (n : ℝ) ≤ N := by linarith
        exact_mod_cast this
  have hpt : ∀ t : ℝ, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, molScaled Δ t * sawCell (y + n - t) =
      molScaled Δ t * (saw (y - t) : ℂ) := by
    intro t
    have hfin : ∑' n : ℤ, molScaled Δ t * sawCell (y + n - t) =
        ∑ n ∈ Finset.Icc (-(N : ℤ)) N, molScaled Δ t * sawCell (y + n - t) :=
      tsum_eq_sum fun n hn => hvan n hn t
    rw [← hfin, tsum_mul_left, ← tsum_sawCell]
    congr 1
    refine tsum_congr fun n => ?_
    congr 1; ring
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) fun n hn => by
    rw [cellSmooth_apply]
    have : (fun t : ℝ => molScaled Δ t * sawCell (y + n - t)) = fun _ => 0 := funext (hvan n hn)
    rw [this, integral_zero]]
  simp_rw [cellSmooth_apply]
  rw [← integral_finsetSum _ fun n _ => integrable_molScaled_mul_sawCell hΔ _]
  unfold sawSmooth
  exact integral_congr_ae (Eventually.of_forall hpt)

theorem fourier_cellSmooth {Δ : ℝ} (hΔ : 0 < Δ) (ξ : ℝ) :
    𝓕 (cellSmooth Δ) ξ = 𝓕 molC (Δ * ξ) * 𝓕 sawCell ξ := by
  have e : cellSmooth Δ =
      convolution (molScaled Δ) sawCell (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext x; simp [cellSmooth, convolution_def]
  rw [e, Real.fourier_mul_convolution_eq (integrable_molScaled hΔ) integrable_sawCell,
    fourier_molScaled hΔ]

/-- **Poisson.**  `ψ_Δ(y) = Σ_h 𝓕G(h) e(hy)`. -/
theorem sawSmooth_eq_tsum {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) :
    sawSmooth Δ y = ∑' h : ℤ, 𝓕 (cellSmooth Δ) h * fourier h (y : UnitAddCircle) := by
  rw [← tsum_cellSmooth hΔ]
  exact SchwartzMap.tsum_eq_tsum_fourier (cellSchwartz hΔ) y

/-- `Σ_h (1 + (hΔ)²)^{−1}` converges. -/
theorem summable_inv_one_add_sq {Δ : ℝ} (hΔ : 0 < Δ) :
    Summable fun h : ℤ => (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ := by
  have hs : Summable fun h : ℤ => 1 / (h : ℝ) ^ 2 := summable_one_div_int_pow.mpr one_lt_two
  have hs0 : Summable fun h : ℤ => (Pi.single (0 : ℤ) (1 : ℝ) : ℤ → ℝ) h :=
    summable_of_ne_finset_zero (s := {0}) fun b hb => by
      rw [Finset.mem_singleton] at hb; simp [hb]
  refine Summable.of_nonneg_of_le (fun h => by positivity) (fun h => ?_)
    ((hs.mul_left (Δ ^ 2)⁻¹).add hs0)
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · have hh' : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    have : (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ ≤ (Δ ^ 2)⁻¹ * (1 / (h : ℝ) ^ 2) := by
      rw [← one_div, ← one_div, div_mul_div_comm, one_mul]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [sq_nonneg (h : ℝ), sq_nonneg Δ]
    simp only [Pi.single_apply, hh, if_false, add_zero]
    exact this

/-! ## The majorant -/

/-- A smooth bump equal to `1` on `[−1, 1]` and supported in `(−2, 2)`. -/
def majBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `κ` with complex values. -/
def majC (t : ℝ) : ℂ := (majBump t : ℂ)

/-- `κ(t/Δ)`. -/
def majScaled (Δ t : ℝ) : ℂ := majC (t / Δ)

theorem hasCompactSupport_majScaled {Δ : ℝ} (hΔ : 0 < Δ) : HasCompactSupport (majScaled Δ) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(2 * Δ)) (b := 2 * Δ)) fun t ht => by
    unfold majScaled majC
    rw [majBump.zero_of_le_dist]
    · simp
    · rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hΔ, le_div_iff₀ hΔ]
      show 2 * Δ ≤ |t|
      by_contra h
      push Not at h
      exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

theorem contDiff_majScaled (Δ : ℝ) : ContDiff ℝ ∞ (majScaled Δ) :=
  Complex.ofRealCLM.contDiff.comp (majBump.contDiff.comp (contDiff_id.div_const Δ))

/-- `κ(·/Δ)` as a Schwartz function. -/
def majScaledSchwartz {Δ : ℝ} (hΔ : 0 < Δ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_majScaled hΔ).toSchwartzMap (contDiff_majScaled Δ)

/-- `κ` as a Schwartz function. -/
def majSchwartz : SchwartzMap ℝ ℂ :=
  (majBump.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp majBump.contDiff)

theorem majSchwartz_coe : (majSchwartz : ℝ → ℂ) = majC := rfl

theorem fourier_majScaled {Δ : ℝ} (hΔ : 0 < Δ) (ξ : ℝ) :
    𝓕 (majScaled Δ) ξ = (Δ : ℂ) * 𝓕 majC (Δ * ξ) :=
  fourier_comp_div hΔ ξ

theorem majScaled_re_nonneg (Δ t : ℝ) : 0 ≤ (majScaled Δ t).re := by
  simp [majScaled, majC, majBump.nonneg]

theorem majScaled_im (Δ t : ℝ) : (majScaled Δ t).im = 0 := by
  simp [majScaled, majC]

theorem summable_majScaled {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) :
    Summable fun n : ℤ => majScaled Δ (y + n) := by
  set N : ℕ := ⌈|y| + 2 * Δ⌉₊ + 1 with hN
  have hNle : |y| + 2 * Δ ≤ (N : ℝ) := by
    have := Nat.le_ceil (|y| + 2 * Δ); rw [hN]; push_cast; linarith
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N) fun n hn => ?_
  unfold majScaled majC
  rw [majBump.zero_of_le_dist]
  · simp
  · rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hΔ, le_div_iff₀ hΔ]
    show 2 * Δ ≤ |y + n|
    rw [Finset.mem_Icc, not_and_or] at hn
    have hy1 := le_abs_self y
    have hy2 := neg_abs_le y
    rcases hn with hn | hn
    · push Not at hn
      have : (n : ℝ) < -(N : ℝ) := by exact_mod_cast hn
      rw [abs_of_neg (by linarith)]; linarith
    · push Not at hn
      have : (N : ℝ) < n := by exact_mod_cast hn
      rw [abs_of_pos (by linarith)]; linarith

/-- The real majorant `K(y) = Σ_n κ((y + n)/Δ)`. -/
def majPer (Δ y : ℝ) : ℝ := ∑' n : ℤ, (majScaled Δ (y + n)).re

theorem majPer_nonneg (Δ y : ℝ) : 0 ≤ majPer Δ y :=
  tsum_nonneg fun _ => majScaled_re_nonneg Δ _

theorem majPer_eq_tsum (Δ y : ℝ) :
    (majPer Δ y : ℂ) = ∑' n : ℤ, majScaled Δ (y + n) := by
  unfold majPer
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun _ => ?_
  apply Complex.ext <;> simp [majScaled_im]

theorem one_le_majPer {Δ : ℝ} (hΔ : 0 < Δ) {y : ℝ} {n : ℤ} (hn : |y - n| ≤ Δ) :
    1 ≤ majPer Δ y := by
  have hs : Summable fun m : ℤ => (majScaled Δ (y + m)).re :=
    (Complex.reCLM.summable (summable_majScaled hΔ y))
  have h1 : (majScaled Δ (y + (-n : ℤ))).re = 1 := by
    unfold majScaled majC
    rw [majBump.one_of_mem_closedBall]
    · simp
    · rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hΔ]
      show |y + ((-n : ℤ) : ℝ)| / Δ ≤ 1
      rw [div_le_one hΔ]
      push_cast
      rwa [← sub_eq_add_neg]
  calc (1 : ℝ) = (majScaled Δ (y + (-n : ℤ))).re := h1.symm
    _ ≤ majPer Δ y := hs.le_tsum _ fun j _ => majScaled_re_nonneg Δ _

/-- **Poisson for the majorant.**  `K(y) = Σ_h Δ 𝓕κ(hΔ) e(hy)`. -/
theorem majPer_eq_tsum_fourier {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) :
    (majPer Δ y : ℂ) = ∑' h : ℤ, (Δ : ℂ) * 𝓕 majC (Δ * h) * fourier h (y : UnitAddCircle) := by
  rw [majPer_eq_tsum]
  have h := SchwartzMap.tsum_eq_tsum_fourier (majScaledSchwartz hΔ) y
  have e : ((majScaledSchwartz hΔ) : ℝ → ℂ) = majScaled Δ := rfl
  rw [e] at h
  rw [h]
  refine tsum_congr fun k => ?_
  have := congrFun (SchwartzMap.fourier_coe (majScaledSchwartz hΔ)) k
  rw [this, e, fourier_majScaled hΔ]

/-! ## The decomposition -/

theorem norm_saw_sub_sawSmooth_le {Δ : ℝ} (hΔ : 0 < Δ) (y : ℝ) :
    ‖(saw y : ℂ) - sawSmooth Δ y‖ ≤ majPer Δ y := by
  by_cases hy : ∀ n : ℤ, Δ < |y - n|
  · rw [sawSmooth_eq hΔ hy, sub_self, norm_zero]; exact majPer_nonneg Δ y
  · push Not at hy
    obtain ⟨n, hn⟩ := hy
    calc ‖(saw y : ℂ) - sawSmooth Δ y‖ ≤ ‖(saw y : ℂ)‖ + ‖sawSmooth Δ y‖ := norm_sub_le _ _
      _ ≤ 1 / 2 + 1 / 2 := by
          gcongr
          · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_saw_le y
          · exact norm_sawSmooth_le hΔ y
      _ = 1 := by norm_num
      _ ≤ majPer Δ y := one_le_majPer hΔ hn

theorem norm_fourier_apply (h : ℤ) (y : ℝ) : ‖fourier h (y : UnitAddCircle)‖ = 1 :=
  Circle.norm_coe _

/-- Exchanging a finite sum with an absolutely convergent Fourier series. -/
theorem sum_mul_tsum_eq {ι : Type*} (s : Finset ι) (c : ι → ℂ) (y : ι → ℝ) {a : ℤ → ℂ}
    (ha : Summable fun h => ‖a h‖) :
    ∑ i ∈ s, c i * ∑' h : ℤ, a h * fourier h (y i : UnitAddCircle) =
      ∑' h : ℤ, a h * ∑ i ∈ s, c i * fourier h (y i : UnitAddCircle) := by
  have hs : ∀ i ∈ s, Summable fun h : ℤ => a h * (c i * fourier h (y i : UnitAddCircle)) := by
    intro i _
    refine Summable.of_norm_bounded (ha.mul_right ‖c i‖) fun h => ?_
    rw [norm_mul, norm_mul, norm_fourier_apply, mul_one]
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun h => ?_
  ring

theorem summable_mul_norm_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (y : ι → ℝ) {a : ℤ → ℂ}
    (ha : Summable fun h => ‖a h‖) :
    Summable fun h : ℤ => ‖a h‖ * ‖∑ i ∈ s, c i * fourier h (y i : UnitAddCircle)‖ := by
  refine Summable.of_nonneg_of_le (fun h => by positivity) (fun h => ?_)
    (ha.mul_right (∑ i ∈ s, ‖c i‖))
  gcongr
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, norm_fourier_apply, mul_one]

/-- **The sawtooth decomposition.** -/
theorem exists_saw_decomposition :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ Δ : ℝ, 0 < Δ → ∃ a k : ℤ → ℂ,
      Summable (fun h => ‖a h‖) ∧ Summable (fun h => ‖k h‖) ∧
      (∀ h : ℤ, ‖a h‖ ≤ A * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ / |(h : ℝ)|) ∧
      (∀ h : ℤ, ‖k h‖ ≤ A * Δ * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹) ∧
      ∀ {ι : Type} (s : Finset ι) (y : ι → ℝ) (c : ι → ℂ) (β : ι → ℝ), (∀ i, ‖c i‖ ≤ β i) →
        ‖∑ i ∈ s, c i * (saw (y i) : ℂ)‖ ≤
          ∑' h, ‖a h‖ * ‖∑ i ∈ s, c i * fourier h (y i : UnitAddCircle)‖ +
          ∑' h, ‖k h‖ * ‖∑ i ∈ s, (β i : ℂ) * fourier h (y i : UnitAddCircle)‖ := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_norm_fourier_le molSchwartz
  obtain ⟨Ck, hCk0, hCk⟩ := exists_norm_fourier_le majSchwartz
  rw [molSchwartz_coe] at hCm
  rw [majSchwartz_coe] at hCk
  refine ⟨Cm + Ck, by positivity, fun Δ hΔ => ?_⟩
  set a : ℤ → ℂ := fun h => 𝓕 (cellSmooth Δ) h with ha
  set k : ℤ → ℂ := fun h => (Δ : ℂ) * 𝓕 majC (Δ * h) with hk
  have hsq : ∀ h : ℤ, (1 + (Δ * (h : ℝ)) ^ 2)⁻¹ = (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ := fun h => by
    rw [mul_comm]
  have haB : ∀ h : ℤ, ‖a h‖ ≤ (Cm + Ck) * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ / |(h : ℝ)| := by
    intro h
    simp only [ha]
    rw [fourier_cellSmooth hΔ, norm_mul]
    rcases eq_or_ne h 0 with rfl | hh
    · simp [fourier_sawCell_zero]
    have hh' : 0 < |(h : ℝ)| := abs_pos.mpr (by exact_mod_cast hh)
    have h1 := hCm (Δ * h)
    rw [hsq] at h1
    have h2 := norm_fourier_sawCell_int_le h
    have h3 : 1 / (2 * π * |(h : ℝ)|) ≤ 1 / |(h : ℝ)| := by
      apply one_div_le_one_div_of_le hh'
      have : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
      nlinarith
    calc ‖𝓕 molC (Δ * h)‖ * ‖𝓕 sawCell h‖
        ≤ (Cm * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹) * (1 / |(h : ℝ)|) :=
          mul_le_mul h1 (h2.trans h3) (norm_nonneg _) (by positivity)
      _ ≤ (Cm + Ck) * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ * (1 / |(h : ℝ)|) := by gcongr; linarith
      _ = _ := by ring
  have hkB : ∀ h : ℤ, ‖k h‖ ≤ (Cm + Ck) * Δ * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ := by
    intro h
    simp only [hk]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΔ]
    have h1 := hCk (Δ * h)
    rw [hsq] at h1
    calc Δ * ‖𝓕 majC (Δ * h)‖ ≤ Δ * (Ck * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹) := by gcongr
      _ ≤ Δ * ((Cm + Ck) * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹) := by gcongr; linarith
      _ = _ := by ring
  have hsum := summable_inv_one_add_sq hΔ
  have haS : Summable fun h => ‖a h‖ := by
    refine Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => ?_)
      (hsum.mul_left (Cm + Ck))
    refine (haB h).trans ?_
    rcases eq_or_ne h 0 with rfl | hh
    · simp; positivity
    have hh' : 1 ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hh
    rw [div_le_iff₀ (by linarith)]
    have : 0 ≤ (Cm + Ck) * (1 + ((h : ℝ) * Δ) ^ 2)⁻¹ := by positivity
    nlinarith
  have hkS : Summable fun h => ‖k h‖ :=
    Summable.of_nonneg_of_le (fun h => norm_nonneg _) hkB (hsum.mul_left ((Cm + Ck) * Δ))
  refine ⟨a, k, haS, hkS, haB, hkB, ?_⟩
  intro ι s y c β hcβ
  have hβ0 : ∀ i, 0 ≤ β i := fun i => (norm_nonneg _).trans (hcβ i)
  -- the smooth part
  have hsmooth : ∑ i ∈ s, c i * sawSmooth Δ (y i) =
      ∑' h : ℤ, a h * ∑ i ∈ s, c i * fourier h (y i : UnitAddCircle) := by
    simp_rw [sawSmooth_eq_tsum hΔ]
    exact sum_mul_tsum_eq s c y haS
  -- the majorant part
  have hmaj : ∑ i ∈ s, (β i : ℂ) * (majPer Δ (y i) : ℂ) =
      ∑' h : ℤ, k h * ∑ i ∈ s, (β i : ℂ) * fourier h (y i : UnitAddCircle) := by
    simp_rw [majPer_eq_tsum_fourier hΔ]
    exact sum_mul_tsum_eq s (fun i => (β i : ℂ)) y hkS
  have hsplit : ∑ i ∈ s, c i * (saw (y i) : ℂ) = ∑ i ∈ s, c i * sawSmooth Δ (y i) +
      ∑ i ∈ s, c i * ((saw (y i) : ℂ) - sawSmooth Δ (y i)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [hsmooth]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun h => norm_mul _ _))
    exact (summable_mul_norm_sum s c y haS).congr fun h => (norm_mul _ _).symm
  · calc ‖∑ i ∈ s, c i * ((saw (y i) : ℂ) - sawSmooth Δ (y i))‖
        ≤ ∑ i ∈ s, β i * majPer Δ (y i) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          rw [norm_mul]
          exact mul_le_mul (hcβ i) (norm_saw_sub_sawSmooth_le hΔ (y i)) (norm_nonneg _)
            (hβ0 i)
      _ = ‖((∑ i ∈ s, β i * majPer Δ (y i) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
          exact Finset.sum_nonneg fun i _ => mul_nonneg (hβ0 i) (majPer_nonneg Δ _)
      _ = ‖∑' h : ℤ, k h * ∑ i ∈ s, (β i : ℂ) * fourier h (y i : UnitAddCircle)‖ := by
          rw [← hmaj]; push_cast; rfl
      _ ≤ ∑' h, ‖k h‖ * ‖∑ i ∈ s, (β i : ℂ) * fourier h (y i : UnitAddCircle)‖ := by
          refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq (tsum_congr fun h => norm_mul _ _))
          exact (summable_mul_norm_sum s (fun i => (β i : ℂ)) y hkS).congr
            fun h => (norm_mul _ _).symm

end GaloisForLFunctions.HTGeometry.SmoothedSawtooth
