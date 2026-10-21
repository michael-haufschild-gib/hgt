import GaloisForLFunctions.HTGeometry.LerchHurwitzDerivative

/-!
# Lerch's formula for complex shifts

For `b` in the slit plane `ℂ ∖ (-∞, 0]` the shifted powers `(x + b)^c`, `x ≥ 0`, never meet the
branch cut.  The second-order Euler–Maclaurin function

`ζ_H(s,b) = b^{1-s}/(s-1) + b^{-s}/2 - s(s+1) ∫_0^∞ P₂(x)(x+b)^{-s-2} dx`

agrees with `∑_{n ≥ 0} (n+b)^{-s}` for `Re s > 1`, takes the value `1/2 - b` at `s = 0`, and has
`∂_s ζ_H(0,b) = (b - 1/2) log b - b - J(b)` with `J(b) = ∫_0^∞ P₂(x)(x+b)^{-2} dx`.

`J` is holomorphic on the slit plane, so Binet's formula `Γ(b) = √(2π) e^{(b-1/2) log b - b - J(b)}`
extends from `b > 0` by the identity theorem.  Hence `exp(-∂_s ζ_H(0,b)) = √(2π)/Γ(b)`: the
ζ-regularized determinant of `N + b` for every complex shift off the negative axis.
-/

open Filter Real MeasureTheory Set Complex
open scoped Topology ComplexOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Geometry of the shifted ray -/

theorem ofReal_add_mem_slitPlane {b : ℂ} (hb : b ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + b ∈ slitPlane := by
  rcases mem_slitPlane_iff.mp hb with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h))

theorem ofReal_add_ne_zero {b : ℂ} (hb : b ∈ slitPlane) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + b ≠ 0 :=
  slitPlane_ne_zero (ofReal_add_mem_slitPlane hb hx)

/-- The shifted ray `x + b`, `x ≥ 0`, grows linearly away from the origin. -/
theorem exists_mul_add_one_le_norm_add {b : ℂ} (hb : b ∈ slitPlane) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x : ℝ, 0 ≤ x → κ * (x + 1) ≤ ‖(x : ℂ) + b‖ := by
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 ≤ x → δ ≤ ‖(x : ℂ) + b‖ := by
    rcases mem_slitPlane_iff.mp hb with hre | him
    · refine ⟨b.re, hre, fun x hx => ?_⟩
      calc b.re ≤ ((x : ℂ) + b).re := by simp; linarith
        _ ≤ ‖(x : ℂ) + b‖ := Complex.re_le_norm _
    · refine ⟨|b.im|, abs_pos.mpr him, fun x _ => ?_⟩
      calc |b.im| = |((x : ℂ) + b).im| := by simp
        _ ≤ ‖(x : ℂ) + b‖ := Complex.abs_im_le_norm _
  have hb0 := norm_nonneg b
  refine ⟨min (δ / (2 * ‖b‖ + 3)) (1 / 4), by positivity, fun x hx => ?_⟩
  by_cases hx2 : x ≤ 2 * ‖b‖ + 2
  · calc min (δ / (2 * ‖b‖ + 3)) (1 / 4) * (x + 1) ≤ δ / (2 * ‖b‖ + 3) * (x + 1) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
      _ ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
      _ ≤ ‖(x : ℂ) + b‖ := hδle x hx
  · rw [not_le] at hx2
    have hxnorm : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx]
    have htri : ‖(x : ℂ)‖ ≤ ‖(x : ℂ) + b‖ + ‖b‖ := by
      calc ‖(x : ℂ)‖ = ‖((x : ℂ) + b) - b‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖(x : ℂ) + b‖ + ‖b‖ := norm_sub_le _ _
    calc min (δ / (2 * ‖b‖ + 3)) (1 / 4) * (x + 1) ≤ 1 / 4 * (x + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
      _ ≤ x - ‖b‖ := by nlinarith
      _ ≤ ‖(x : ℂ) + b‖ := by linarith

/-- `‖z^w‖ ≤ ‖z‖^{Re w} e^{π |Im w|}`. -/
theorem norm_cpow_le_rpow_mul_exp {z : ℂ} (hz : z ≠ 0) (w : ℂ) :
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (π * |w.im|) := by
  rw [norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (norm_nonneg _) _)
  have h1 : -(z.arg * w.im) ≤ |z.arg| * |w.im| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h2 : |z.arg| * |w.im| ≤ π * |w.im| :=
    mul_le_mul_of_nonneg_right (abs_arg_le_pi z) (abs_nonneg _)
  linarith

/-- Power decay along the shifted ray: for `e ≤ 0`, `‖(x+b)^c‖ ≤ (κ(x+1))^{Re c} e^{π|Im c|}`. -/
theorem norm_shiftCpowC_le {b : ℂ} (hb : b ∈ slitPlane) {κ : ℝ} (hκ : 0 < κ)
    (hκb : ∀ x : ℝ, 0 ≤ x → κ * (x + 1) ≤ ‖(x : ℂ) + b‖) {c : ℂ} (hc : c.re ≤ 0) {x : ℝ}
    (hx : 0 ≤ x) :
    ‖((x : ℂ) + b) ^ c‖ ≤ (κ * (x + 1)) ^ c.re * Real.exp (π * |c.im|) := by
  refine (norm_cpow_le_rpow_mul_exp (ofReal_add_ne_zero hb hx) c).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (hκb x hx) hc

/-! ## Calculus of the shifted powers -/

theorem hasDerivAt_shiftCpowC {b : ℂ} (hb : b ∈ slitPlane) (c : ℂ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => ((y : ℂ) + b) ^ c) (c * ((x : ℂ) + b) ^ (c - 1)) x := by
  have hbase : HasDerivAt (fun y : ℝ => (y : ℂ) + b) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const b
  have hout : HasDerivAt (fun z : ℂ => z ^ c) (c * ((x : ℂ) + b) ^ (c - 1) * 1) ((x : ℂ) + b) :=
    (hasDerivAt_id ((x : ℂ) + b)).cpow_const (ofReal_add_mem_slitPlane hb hx)
  have hcomp := hout.comp x hbase
  exact hcomp.congr_deriv (by ring)

theorem continuousOn_shiftCpowC {b : ℂ} (hb : b ∈ slitPlane) (c : ℂ) :
    ContinuousOn (fun y : ℝ => ((y : ℂ) + b) ^ c) (Ici (0 : ℝ)) := by
  refine ContinuousOn.cpow_const (by fun_prop) ?_
  intro y hy
  exact ofReal_add_mem_slitPlane hb hy

theorem integral_shiftCpowC {b : ℂ} (hb : b ∈ slitPlane) {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    (∫ x in (0 : ℝ)..(N : ℝ), ((x : ℂ) + b) ^ (-s))
      = ((((N : ℝ) : ℂ) + b) ^ (1 - s) - b ^ (1 - s)) / (1 - s) := by
  have hle : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) ((N : ℝ)),
      HasDerivAt (fun y : ℝ => ((y : ℂ) + b) ^ (1 - s) / (1 - s)) (((x : ℂ) + b) ^ (-s)) x := by
    intro x hx
    rw [uIcc_of_le hle] at hx
    have hd := (hasDerivAt_shiftCpowC hb (1 - s) hx.1).div_const (1 - s)
    refine hd.congr_deriv ?_
    rw [show (1 : ℂ) - s - 1 = -s by ring]
    field_simp
  have hint : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + b) ^ (-s)) volume 0 ((N : ℝ)) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hle]
    exact (continuousOn_shiftCpowC hb (-s)).mono (fun x hx => hx.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Complex.ofReal_zero, zero_add]
  rw [div_sub_div_same]

/-! ## The Euler–Maclaurin kernel with complex shift -/

/-- The Euler–Maclaurin kernel `∫_0^∞ P₂(x)(x+b)^{-s-2} dx`. -/
def emKernelC (b s : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2)

theorem aestronglyMeasurable_emKernelC_integrand {b : ℂ} (hb : b ∈ slitPlane) (s : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2))
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine AEStronglyMeasurable.mul ?_ ?_
  · exact (Complex.measurable_ofReal.comp measurable_bernoulliHalfPer).aestronglyMeasurable
  · exact ((continuousOn_shiftCpowC hb (-s - 2)).mono Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi

/-- Dominating bound for the kernel integrand when `Re s ≥ -1/2`. -/
theorem norm_emKernelC_integrand_le {b : ℂ} (hb : b ∈ slitPlane) {κ : ℝ} (hκ : 0 < κ)
    (hκb : ∀ x : ℝ, 0 ≤ x → κ * (x + 1) ≤ ‖(x : ℂ) + b‖) {s : ℂ} (h1 : -(1 / 2 : ℝ) ≤ s.re)
    {x : ℝ} (hx : 0 ≤ x) :
    ‖((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2)‖ ≤
      (1 / 8) * Real.exp (π * |s.im|) * κ ^ (-s.re - 2) * (x + 1) ^ (-(3 / 2 : ℝ)) := by
  have hre : (-s - 2).re = -s.re - 2 := by simp
  have him : |(-s - 2).im| = |s.im| := by simp
  have hcp := norm_shiftCpowC_le hb hκ hκb (c := -s - 2) (by rw [hre]; linarith) hx
  rw [hre, him, Real.mul_rpow hκ.le (by linarith)] at hcp
  have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
  have hmono : (x + 1) ^ (-s.re - 2) ≤ (x + 1) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hker := abs_bernoulliHalfPer_le x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |bernoulliHalfPer x| * ‖((x : ℂ) + b) ^ (-s - 2)‖
      ≤ (1 / 8) * (κ ^ (-s.re - 2) * (x + 1) ^ (-s.re - 2) * Real.exp (π * |s.im|)) :=
        mul_le_mul hker hcp (norm_nonneg _) (by norm_num)
    _ ≤ (1 / 8) * (κ ^ (-s.re - 2) * (x + 1) ^ (-(3 / 2 : ℝ)) * Real.exp (π * |s.im|)) := by
        gcongr
    _ = (1 / 8) * Real.exp (π * |s.im|) * κ ^ (-s.re - 2) * (x + 1) ^ (-(3 / 2 : ℝ)) := by ring

theorem integrableOn_emKernelC_integrand {b : ℂ} (hb : b ∈ slitPlane) {s : ℂ}
    (h1 : -(1 / 2 : ℝ) ≤ s.re) :
    IntegrableOn
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2)) (Ioi (0 : ℝ)) := by
  obtain ⟨κ, hκ, hκb⟩ := exists_mul_add_one_le_norm_add hb
  have hdom : IntegrableOn
      (fun x : ℝ => (1 / 8) * Real.exp (π * |s.im|) * κ ^ (-s.re - 2) *
        (x + 1) ^ (-(3 / 2 : ℝ))) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_shift_rpow_neg one_pos (by norm_num)).const_mul _
  refine Integrable.mono hdom (aestronglyMeasurable_emKernelC_integrand hb s) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) ≤ x := (mem_Ioi.mp hx).le
  have hnn : 0 ≤ (1 / 8) * Real.exp (π * |s.im|) * κ ^ (-s.re - 2) *
      (x + 1) ^ (-(3 / 2 : ℝ)) := by positivity
  rw [Real.norm_of_nonneg hnn]
  exact norm_emKernelC_integrand_le hb hκ hκb h1 hx0

/-- The complex-shift kernel is continuous at `s = 0`. -/
theorem continuousAt_emKernelC_zero {b : ℂ} (hb : b ∈ slitPlane) :
    ContinuousAt (emKernelC b) 0 := by
  obtain ⟨κ, hκ, hκb⟩ := exists_mul_add_one_le_norm_add hb
  have hball : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -(1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ 1 / 2 ∧ |s.im| ≤ 1 := by
    have h1 : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), -(1 / 2 : ℝ) < s.re :=
      Complex.continuous_re.continuousAt.eventually_const_lt (by norm_num)
    have h2 : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), s.re < 1 / 2 :=
      Complex.continuous_re.continuousAt.eventually_lt_const (by norm_num)
    have h3 : ∀ᶠ s : ℂ in 𝓝 (0 : ℂ), |s.im| < 1 :=
      (continuous_abs.comp Complex.continuous_im).continuousAt.eventually_lt_const (by simp)
    filter_upwards [h1, h2, h3] with s hs1 hs2 hs3
    exact ⟨hs1.le, hs2.le, hs3.le⟩
  set C : ℝ := (1 / 8) * Real.exp (π * 1) * max (κ ^ (-(5 / 2 : ℝ))) (κ ^ (-(3 / 2 : ℝ)))
  refine MeasureTheory.continuousAt_of_dominated
    (bound := fun x : ℝ => C * (x + 1) ^ (-(3 / 2 : ℝ))) ?_ ?_ ?_ ?_
  · filter_upwards [hball] with s _
    exact aestronglyMeasurable_emKernelC_integrand hb s
  · filter_upwards [hball] with s hs
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    refine (norm_emKernelC_integrand_le hb hκ hκb hs.1 (mem_Ioi.mp hx).le).trans ?_
    have hx1 : 0 ≤ (x + 1) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_nonneg (by linarith [(mem_Ioi.mp hx).le]) _
    have he : Real.exp (π * |s.im|) ≤ Real.exp (π * 1) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2.2 Real.pi_pos.le)
    have hk : κ ^ (-s.re - 2) ≤ max (κ ^ (-(5 / 2 : ℝ))) (κ ^ (-(3 / 2 : ℝ))) := by
      rcases le_or_gt 1 κ with hκ1 | hκ1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_le hκ1 (by linarith)) (le_max_right _ _)
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hκ hκ1.le (by linarith))
          (le_max_left _ _)
    calc (1 / 8) * Real.exp (π * |s.im|) * κ ^ (-s.re - 2) * (x + 1) ^ (-(3 / 2 : ℝ))
        ≤ (1 / 8) * Real.exp (π * 1) * max (κ ^ (-(5 / 2 : ℝ))) (κ ^ (-(3 / 2 : ℝ))) *
          (x + 1) ^ (-(3 / 2 : ℝ)) := by gcongr
      _ = C * (x + 1) ^ (-(3 / 2 : ℝ)) := rfl
  · exact (integrableOn_Ioi_shift_rpow_neg one_pos (by norm_num)).const_mul _
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    refine ContinuousAt.mul continuousAt_const ?_
    exact ContinuousAt.const_cpow (by fun_prop)
      (Or.inl (ofReal_add_ne_zero hb (mem_Ioi.mp hx).le))

/-! ## The complex-shift Hurwitz function -/

/-- Euler–Maclaurin continuation of `∑_{n ≥ 0} (n+b)^{-s}`. -/
def hurwitzZetaEMC (b s : ℂ) : ℂ :=
  b ^ (1 - s) / (s - 1) + b ^ (-s) / 2 - s * (s + 1) * emKernelC b s

/-- `ζ_H(0,b) = 1/2 - b`. -/
theorem hurwitzZetaEMC_zero (b : ℂ) : hurwitzZetaEMC b 0 = 1 / 2 - b := by
  simp [hurwitzZetaEMC]
  ring

/-- The Binet kernel `J(b) = ∫_0^∞ P₂(x)(x+b)^{-2} dx`. -/
def binetKernelC (b : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-2 : ℤ)

theorem emKernelC_zero (b : ℂ) : emKernelC b 0 = binetKernelC b := by
  rw [emKernelC, binetKernelC]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have h : (-(0 : ℂ) - 2) = ((-2 : ℤ) : ℂ) := by norm_num
  rw [h, Complex.cpow_intCast]

theorem hasDerivAt_hurwitzZetaEMC_zero {b : ℂ} (hb : b ∈ slitPlane) :
    HasDerivAt (hurwitzZetaEMC b) ((b - 1 / 2) * Complex.log b - b - binetKernelC b) 0 := by
  have hbne : b ≠ 0 := slitPlane_ne_zero hb
  have hu : HasDerivAt (fun s : ℂ => b ^ (1 - s)) (-(b * Complex.log b)) 0 := by
    have hc : HasDerivAt (fun s : ℂ => 1 - s) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
    have hd := hc.const_cpow (c := b) (Or.inl hbne)
    refine hd.congr_deriv ?_
    simp
  have hv : HasDerivAt (fun s : ℂ => s - 1) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).sub_const 1
  have hA : HasDerivAt (fun s : ℂ => b ^ (1 - s) / (s - 1)) (b * Complex.log b - b) 0 := by
    have hd := hu.div hv (by norm_num)
    refine hd.congr_deriv ?_
    simp
  have hB : HasDerivAt (fun s : ℂ => b ^ (-s) / 2) (-(Complex.log b) / 2) 0 := by
    have hc : HasDerivAt (fun s : ℂ => -s) (-1) 0 := hasDerivAt_neg 0
    have hd := (hc.const_cpow (c := b) (Or.inl hbne)).div_const 2
    refine hd.congr_deriv ?_
    simp
  have hC : HasDerivAt (fun s : ℂ => s * (s + 1) * emKernelC b s) (emKernelC b 0) 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hbase : Tendsto (fun s : ℂ => (s + 1) * emKernelC b s) (𝓝 (0 : ℂ))
        (𝓝 (((0 : ℂ) + 1) * emKernelC b 0)) :=
      (continuousAt_id.add continuousAt_const).mul (continuousAt_emKernelC_zero hb)
    rw [zero_add, one_mul] at hbase
    refine (hbase.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := hs
    rw [slope_def_field]
    field_simp
    ring
  have hsum := (hA.add hB).sub hC
  have hfun : ((fun s : ℂ => b ^ (1 - s) / (s - 1)) + (fun s : ℂ => b ^ (-s) / 2) -
      fun s : ℂ => s * (s + 1) * emKernelC b s) = hurwitzZetaEMC b := by
    funext s
    simp [hurwitzZetaEMC]
  rw [hfun] at hsum
  refine hsum.congr_deriv ?_
  rw [emKernelC_zero]
  ring

/-! ## Holomorphy in `s` -/

/-- The logarithm along the shifted ray grows at most like `log(x+1)`. -/
theorem norm_log_shift_le {b : ℂ} (hb : b ∈ slitPlane) {κ : ℝ} (hκ : 0 < κ)
    (hκb : ∀ x : ℝ, 0 ≤ x → κ * (x + 1) ≤ ‖(x : ℂ) + b‖) {x : ℝ} (hx : 0 ≤ x) :
    ‖Complex.log ((x : ℂ) + b)‖ ≤
      |Real.log κ| + Real.log (1 + ‖b‖) + Real.log (x + 1) + π := by
  have hnpos : 0 < ‖(x : ℂ) + b‖ := norm_pos_iff.mpr (ofReal_add_ne_zero hb hx)
  have hupper : ‖(x : ℂ) + b‖ ≤ (1 + ‖b‖) * (x + 1) := by
    calc ‖(x : ℂ) + b‖ ≤ ‖(x : ℂ)‖ + ‖b‖ := norm_add_le _ _
      _ = x + ‖b‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hx]
      _ ≤ (1 + ‖b‖) * (x + 1) := by nlinarith [norm_nonneg b]
  have hx1 : 0 < x + 1 := by linarith
  have hlog_up : Real.log ‖(x : ℂ) + b‖ ≤ Real.log (1 + ‖b‖) + Real.log (x + 1) := by
    rw [← Real.log_mul (by positivity) hx1.ne']
    exact Real.log_le_log hnpos hupper
  have hlog_lo : Real.log κ + Real.log (x + 1) ≤ Real.log ‖(x : ℂ) + b‖ := by
    rw [← Real.log_mul hκ.ne' hx1.ne']
    exact Real.log_le_log (by positivity) (hκb x hx)
  have hlog1 : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hlogb : 0 ≤ Real.log (1 + ‖b‖) := Real.log_nonneg (by linarith [norm_nonneg b])
  have habs : |Real.log ‖(x : ℂ) + b‖| ≤
      |Real.log κ| + Real.log (1 + ‖b‖) + Real.log (x + 1) := by
    rw [abs_le]
    constructor
    · have := neg_abs_le (Real.log κ); linarith
    · have := abs_nonneg (Real.log κ); linarith
  calc ‖Complex.log ((x : ℂ) + b)‖
      ≤ |(Complex.log ((x : ℂ) + b)).re| + |(Complex.log ((x : ℂ) + b)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖(x : ℂ) + b‖| + |((x : ℂ) + b).arg| := by
        rw [Complex.log_re, Complex.log_im]
    _ ≤ (|Real.log κ| + Real.log (1 + ‖b‖) + Real.log (x + 1)) + π :=
        add_le_add habs (abs_arg_le_pi _)

/-- The kernel is holomorphic in `s` on `Re s > -1/2`. -/
theorem hasDerivAt_emKernelC {b : ℂ} (hb : b ∈ slitPlane) {s₀ : ℂ}
    (hs₀ : -(1 / 2 : ℝ) < s₀.re) :
    HasDerivAt (emKernelC b)
      (∫ x in Ioi (0 : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) *
        (-Complex.log ((x : ℂ) + b) * ((x : ℂ) + b) ^ (-s₀ - 2))) s₀ := by
  obtain ⟨κ, hκ, hκb⟩ := exists_mul_add_one_le_norm_add hb
  set δ : ℝ := (s₀.re + 1 / 2) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hball : ∀ s ∈ Metric.ball s₀ δ,
      -(1 / 2 : ℝ) + δ ≤ s.re ∧ s.re ≤ s₀.re + δ ∧ |s.im| ≤ |s₀.im| + δ := by
    intro s hs
    have hd : ‖s - s₀‖ < δ := by simpa [dist_eq_norm] using hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_re_le_norm (s - s₀)
    have him : |s.im - s₀.im| ≤ ‖s - s₀‖ := by
      simpa using Complex.abs_im_le_norm (s - s₀)
    rw [abs_le] at hre
    refine ⟨by linarith [hre.1], by linarith [hre.2], ?_⟩
    have := abs_sub_abs_le_abs_sub s.im s₀.im
    linarith
  set A : ℝ := |Real.log κ| + Real.log (1 + ‖b‖) + π with hA
  have hA0 : 0 ≤ A := by
    have : 0 ≤ Real.log (1 + ‖b‖) := Real.log_nonneg (by linarith [norm_nonneg b])
    have := abs_nonneg (Real.log κ)
    have := Real.pi_pos
    rw [hA]; linarith
  set K : ℝ := max (κ ^ (-(s₀.re + δ) - 2)) (κ ^ (-(-(1 / 2 : ℝ) + δ) - 2)) with hK
  set C : ℝ := (1 / 8) * Real.exp (π * (|s₀.im| + δ)) * K * (A + 2 / δ) with hC
  have hkappa : ∀ s ∈ Metric.ball s₀ δ, κ ^ (-s.re - 2) ≤ K := by
    intro s hs
    obtain ⟨h1, h2, _⟩ := hball s hs
    rcases le_or_gt 1 κ with hκ1 | hκ1
    · exact le_trans (Real.rpow_le_rpow_of_exponent_le hκ1 (by linarith)) (le_max_right _ _)
    · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hκ hκ1.le (by linarith))
        (le_max_left _ _)
  have hderivBound : ∀ s ∈ Metric.ball s₀ δ, ∀ x : ℝ, 0 ≤ x →
      ‖((bernoulliHalfPer x : ℝ) : ℂ) *
          (-Complex.log ((x : ℂ) + b) * ((x : ℂ) + b) ^ (-s - 2))‖ ≤
        C * (x + 1) ^ (-(3 / 2 : ℝ) - δ / 2) := by
    intro s hs x hx
    obtain ⟨h1, _, h3⟩ := hball s hs
    have hx1 : (1 : ℝ) ≤ x + 1 := by linarith
    have hre : (-s - 2).re = -s.re - 2 := by simp
    have him : |(-s - 2).im| = |s.im| := by simp
    have hcp := norm_shiftCpowC_le hb hκ hκb (c := -s - 2) (by rw [hre]; linarith) hx
    rw [hre, him, Real.mul_rpow hκ.le (by linarith)] at hcp
    have hpow : (x + 1) ^ (-s.re - 2) ≤ (x + 1) ^ (-(3 / 2 : ℝ) - δ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have hexp : Real.exp (π * |s.im|) ≤ Real.exp (π * (|s₀.im| + δ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h3 Real.pi_pos.le)
    have hlog := norm_log_shift_le hb hκ hκb hx
    have hlog1 : Real.log (x + 1) ≤ (x + 1) ^ (δ / 2) / (δ / 2) :=
      Real.log_le_rpow_div (by linarith) (by positivity)
    have hgeom : (1 : ℝ) ≤ (x + 1) ^ (δ / 2) := Real.one_le_rpow hx1 (by positivity)
    have hL : ‖Complex.log ((x : ℂ) + b)‖ ≤ (A + 2 / δ) * (x + 1) ^ (δ / 2) := by
      have : (x + 1) ^ (δ / 2) / (δ / 2) = 2 / δ * (x + 1) ^ (δ / 2) := by
        field_simp
      rw [this] at hlog1
      nlinarith
    have hsplit : (x + 1) ^ (-(3 / 2 : ℝ) - δ) * (x + 1) ^ (δ / 2) =
        (x + 1) ^ (-(3 / 2 : ℝ) - δ / 2) := by
      rw [← Real.rpow_add (by linarith)]; congr 1; ring
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    calc |bernoulliHalfPer x| * (‖Complex.log ((x : ℂ) + b)‖ * ‖((x : ℂ) + b) ^ (-s - 2)‖)
        ≤ (1 / 8) * (((A + 2 / δ) * (x + 1) ^ (δ / 2)) *
            (κ ^ (-s.re - 2) * (x + 1) ^ (-s.re - 2) * Real.exp (π * |s.im|))) := by
          refine mul_le_mul (abs_bernoulliHalfPer_le x) ?_ (by positivity) (by norm_num)
          exact mul_le_mul hL hcp (norm_nonneg _) (by positivity)
      _ ≤ (1 / 8) * (((A + 2 / δ) * (x + 1) ^ (δ / 2)) *
            (K * (x + 1) ^ (-(3 / 2 : ℝ) - δ) * Real.exp (π * (|s₀.im| + δ)))) := by
          gcongr
          exact hkappa s hs
      _ = C * ((x + 1) ^ (-(3 / 2 : ℝ) - δ) * (x + 1) ^ (δ / 2)) := by rw [hC]; ring
      _ = C * (x + 1) ^ (-(3 / 2 : ℝ) - δ / 2) := by rw [hsplit]
  have hF : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2))
      (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun s => aestronglyMeasurable_emKernelC_integrand hb s
  have hint := integrableOn_emKernelC_integrand hb (s := s₀) hs₀.le
  have hF' : AEStronglyMeasurable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) *
        (-Complex.log ((x : ℂ) + b) * ((x : ℂ) + b) ^ (-s₀ - 2)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEStronglyMeasurable.mul
      (Complex.measurable_ofReal.comp measurable_bernoulliHalfPer).aestronglyMeasurable ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.neg ?_) ?_
    · refine ContinuousOn.clog (by fun_prop) fun x hx =>
        ofReal_add_mem_slitPlane hb (mem_Ioi.mp hx).le
    · exact (continuousOn_shiftCpowC hb (-s₀ - 2)).mono Ioi_subset_Ici_self
  have hdom : Integrable (fun x : ℝ => C * (x + 1) ^ (-(3 / 2 : ℝ) - δ / 2))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h := integrableOn_Ioi_shift_rpow_neg (a := 1) (p := 3 / 2 + δ / 2) one_pos
      (by linarith)
    have hfun : (fun x : ℝ => (x + 1) ^ (-(3 / 2 + δ / 2))) =
        fun x : ℝ => (x + 1) ^ (-(3 / 2 : ℝ) - δ / 2) := by
      funext x; congr 1; ring
    rw [hfun] at h
    exact h.const_mul C
  have hbd : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ s ∈ Metric.ball s₀ δ,
      ‖((bernoulliHalfPer x : ℝ) : ℂ) *
          (-Complex.log ((x : ℂ) + b) * ((x : ℂ) + b) ^ (-s - 2))‖ ≤
        C * (x + 1) ^ (-(3 / 2 : ℝ) - δ / 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx s hs
    exact hderivBound s hs x (mem_Ioi.mp hx).le
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ s ∈ Metric.ball s₀ δ,
      HasDerivAt (fun s => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2))
        (((bernoulliHalfPer x : ℝ) : ℂ) *
          (-Complex.log ((x : ℂ) + b) * ((x : ℂ) + b) ^ (-s - 2))) s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx s _
    have hz := ofReal_add_ne_zero hb (mem_Ioi.mp hx).le
    have hexpo : HasDerivAt (fun s : ℂ => -s - 2) (-1) s := by
      simpa using ((hasDerivAt_id s).neg).sub_const 2
    have hd := (hexpo.const_cpow (c := (x : ℂ) + b) (Or.inl hz)).const_mul
      ((bernoulliHalfPer x : ℝ) : ℂ)
    refine hd.congr_deriv ?_
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds s₀ hδ0) hF hint
    hF' hbd hdom hdiff).2

/-- The complex-shift Hurwitz function is holomorphic on `Re s > -1/2`, `s ≠ 1`; with
`hurwitzZetaEMC_eq_tsum` it is the analytic continuation of the Hurwitz series. -/
theorem differentiableAt_hurwitzZetaEMC {b : ℂ} (hb : b ∈ slitPlane) {s : ℂ}
    (hs : -(1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) : DifferentiableAt ℂ (hurwitzZetaEMC b) s := by
  have hbne : b ≠ 0 := slitPlane_ne_zero hb
  unfold hurwitzZetaEMC
  refine DifferentiableAt.sub (DifferentiableAt.add ?_ ?_) ?_
  · refine DifferentiableAt.div ?_ (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1)
    exact ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow (Or.inl hbne)
  · exact ((differentiableAt_id.neg).const_cpow (Or.inl hbne)).div_const 2
  · exact ((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
      (hasDerivAt_emKernelC hb hs).differentiableAt)

/-! ## Holomorphy of the Binet kernel -/

theorem hasDerivAt_binetKernelC {b₀ : ℂ} (hb₀ : b₀ ∈ slitPlane) :
    HasDerivAt binetKernelC
      (∫ x in Ioi (0 : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) *
        ((-2 : ℤ) * ((x : ℂ) + b₀) ^ (-3 : ℤ))) b₀ := by
  obtain ⟨κ, hκ, hκb⟩ := exists_mul_add_one_le_norm_add hb₀
  set r := κ / 2 with hr
  have hr0 : 0 < r := by positivity
  -- uniform lower bound on the ball
  have hball : ∀ b ∈ Metric.ball b₀ r, ∀ x : ℝ, 0 ≤ x → r * (x + 1) ≤ ‖(x : ℂ) + b‖ := by
    intro b hb x hx
    have hdist : ‖b - b₀‖ < r := by simpa [dist_eq_norm] using hb
    have h1 : ‖(x : ℂ) + b₀‖ ≤ ‖(x : ℂ) + b‖ + ‖b - b₀‖ := by
      calc ‖(x : ℂ) + b₀‖ = ‖((x : ℂ) + b) - (b - b₀)‖ := by ring_nf
        _ ≤ ‖(x : ℂ) + b‖ + ‖b - b₀‖ := norm_sub_le _ _
    have h2 := hκb x hx
    nlinarith
  have hne : ∀ b ∈ Metric.ball b₀ r, ∀ x : ℝ, 0 ≤ x → (x : ℂ) + b ≠ 0 := by
    intro b hb x hx h0
    have := hball b hb x hx
    rw [h0, norm_zero] at this
    nlinarith
  have hmeas : ∀ b : ℂ, b ∈ Metric.ball b₀ r → AEStronglyMeasurable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-2 : ℤ))
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro b hb
    refine AEStronglyMeasurable.mul
      (Complex.measurable_ofReal.comp measurable_bernoulliHalfPer).aestronglyMeasurable ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.zpow₀ (by fun_prop) _ fun x hx => Or.inl (hne b hb x (le_of_lt hx))
  have hbound : ∀ b ∈ Metric.ball b₀ r, ∀ x : ℝ, 0 ≤ x → ∀ m : ℕ,
      ‖((x : ℂ) + b) ^ (-(m : ℤ))‖ ≤ (r * (x + 1)) ^ (-(m : ℝ)) := by
    intro b hb x hx m
    rw [norm_zpow, zpow_neg, zpow_natCast, Real.rpow_neg (by positivity), Real.rpow_natCast]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (hball b hb x hx) m)
  have hF : ∀ᶠ b in 𝓝 b₀, AEStronglyMeasurable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-2 : ℤ))
      (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [Metric.ball_mem_nhds b₀ hr0] with b hb
    exact hmeas b hb
  have hint : Integrable (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b₀) ^ (-2 : ℤ))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hdom : IntegrableOn (fun x : ℝ => (1 / 8) * (r ^ (-(2 : ℝ)) * (x + 1) ^ (-(2 : ℝ))))
        (Ioi (0 : ℝ)) :=
      ((integrableOn_Ioi_shift_rpow_neg one_pos (by norm_num)).const_mul _).const_mul _
    refine Integrable.mono hdom (hmeas b₀ (Metric.mem_ball_self hr0)) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    have hb := hbound b₀ (Metric.mem_ball_self hr0) x hx0 2
    rw [show (-((2 : ℕ) : ℤ)) = (-2 : ℤ) by norm_num,
      Real.mul_rpow hr0.le (by linarith)] at hb
    exact mul_le_mul (abs_bernoulliHalfPer_le x) (by simpa using hb) (norm_nonneg _) (by norm_num)
  have hF' : AEStronglyMeasurable
      (fun x : ℝ => ((bernoulliHalfPer x : ℝ) : ℂ) * ((-2 : ℤ) * ((x : ℂ) + b₀) ^ (-3 : ℤ)))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEStronglyMeasurable.mul
      (Complex.measurable_ofReal.comp measurable_bernoulliHalfPer).aestronglyMeasurable ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.zpow₀ (by fun_prop) _ fun x hx =>
      Or.inl (hne b₀ (Metric.mem_ball_self hr0) x (le_of_lt hx))
  have hdomD : Integrable (fun x : ℝ => (1 / 4) * (r ^ (-(3 : ℝ)) * (x + 1) ^ (-(3 : ℝ))))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((integrableOn_Ioi_shift_rpow_neg one_pos (by norm_num)).const_mul _).const_mul _
  have hbd : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ b ∈ Metric.ball b₀ r,
      ‖((bernoulliHalfPer x : ℝ) : ℂ) * ((-2 : ℤ) * ((x : ℂ) + b) ^ (-3 : ℤ))‖ ≤
        (1 / 4) * (r ^ (-(3 : ℝ)) * (x + 1) ^ (-(3 : ℝ))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx b hb
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    have h3 := hbound b hb x hx0 3
    rw [show (-((3 : ℕ) : ℤ)) = (-3 : ℤ) by norm_num,
      Real.mul_rpow hr0.le (by linarith)] at h3
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hc : ‖((-2 : ℤ) : ℂ)‖ = 2 := by simp
    rw [hc]
    calc |bernoulliHalfPer x| * (2 * ‖((x : ℂ) + b) ^ (-3 : ℤ)‖)
        ≤ (1 / 8) * (2 * (r ^ (-(3 : ℝ)) * (x + 1) ^ (-(3 : ℝ)))) := by
          refine mul_le_mul (abs_bernoulliHalfPer_le x) ?_ (by positivity) (by norm_num)
          gcongr
          simpa using h3
      _ = (1 / 4) * (r ^ (-(3 : ℝ)) * (x + 1) ^ (-(3 : ℝ))) := by ring
  have hdiff : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ∀ b ∈ Metric.ball b₀ r,
      HasDerivAt (fun b => ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-2 : ℤ))
        (((bernoulliHalfPer x : ℝ) : ℂ) * ((-2 : ℤ) * ((x : ℂ) + b) ^ (-3 : ℤ))) b := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx b hb
    have hz := hne b hb x (le_of_lt hx)
    have hinner : HasDerivAt (fun b : ℂ => (x : ℂ) + b) 1 b := (hasDerivAt_id b).const_add _
    have hpow := (hasDerivAt_zpow (-2 : ℤ) ((x : ℂ) + b) (Or.inl hz)).comp b hinner
    refine (hpow.const_mul _).congr_deriv ?_
    simp only [mul_one]
    norm_num
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds b₀ hr0) hF hint
    hF' hbd hdomD hdiff).2

theorem differentiableOn_binetKernelC : DifferentiableOn ℂ binetKernelC slitPlane :=
  fun _ hb => (hasDerivAt_binetKernelC hb).differentiableAt.differentiableWithinAt

/-! ## Binet's formula on the slit plane -/

theorem binetKernelC_ofReal {a : ℝ} (ha : 0 < a) : binetKernelC (a : ℂ) = (binetKernel a : ℂ) := by
  rw [binetKernelC, binetKernel, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hxa : (0 : ℝ) < x + a := by have : (0 : ℝ) < x := hx; linarith
  push_cast
  rw [zpow_neg, zpow_two, div_eq_mul_inv, sq]

/-- The Binet right-hand side `√(2π) e^{(b-1/2) log b - b - J(b)}`. -/
def binetRHS (b : ℂ) : ℂ :=
  (Real.sqrt (2 * π) : ℂ) * Complex.exp ((b - 1 / 2) * Complex.log b - b - binetKernelC b)

theorem binetRHS_ofReal {a : ℝ} (ha : 0 < a) : binetRHS (a : ℂ) = (Real.Gamma a : ℂ) := by
  rw [binetRHS, Gamma_eq_binet_exp ha, binetKernelC_ofReal ha]
  have hlog : Complex.log (a : ℂ) = (Real.log a : ℂ) := (Complex.ofReal_log ha.le).symm
  rw [hlog, Real.rpow_def_of_pos ha]
  push_cast
  rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

theorem slitPlane_isPreconnected : IsPreconnected slitPlane :=
  ((starConvex_slitPlane one_pos).isPathConnected
    (mem_slitPlane_iff.mpr (Or.inl one_pos))).isConnected.isPreconnected

/-- **Binet's formula for complex arguments.**  For `b ∈ ℂ ∖ (-∞, 0]`,
`Γ(b) = √(2π) b^{b-1/2} e^{-b} e^{-J(b)}` with `b^{b-1/2} = e^{(b-1/2) log b}`. -/
theorem Gamma_eq_binetRHS {b : ℂ} (hb : b ∈ slitPlane) : Complex.Gamma b = binetRHS b := by
  have hG : DifferentiableOn ℂ Complex.Gamma slitPlane := by
    intro z hz
    refine (Complex.differentiableAt_Gamma z fun m hm => ?_).differentiableWithinAt
    rw [hm] at hz
    rcases mem_slitPlane_iff.mp hz with h | h
    · simp at h; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    · simp at h
  have hR : DifferentiableOn ℂ binetRHS slitPlane := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold binetRHS
    refine DifferentiableAt.const_mul ?_ _
    refine DifferentiableAt.cexp ?_
    refine DifferentiableAt.sub (DifferentiableAt.sub ?_ differentiableAt_id) ?_
    · exact (differentiableAt_id.sub_const _).mul (differentiableAt_log hz)
    · exact (hasDerivAt_binetKernelC hz).differentiableAt
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), Complex.Gamma z = binetRHS z := by
    have htend : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
        rw [add_zero] at h1
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h1
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have h' : (1 + 1 / ((n : ℝ) + 1)) = 1 := by exact_mod_cast h
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    refine htend.frequently (Frequently.of_forall fun n => ?_)
    have hpos : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by positivity
    rw [binetRHS_ofReal hpos, Complex.Gamma_ofReal]
  exact (hG.analyticOnNhd isOpen_slitPlane).eqOn_of_preconnected_of_frequently_eq
    (hR.analyticOnNhd isOpen_slitPlane) slitPlane_isPreconnected
    (mem_slitPlane_iff.mpr (Or.inl one_pos)) hfreq hb

/-- **Lerch's formula for complex shifts.**  `exp(-∂_s ζ_H(0,b)) = √(2π)/Γ(b)` on the slit plane:
the ζ-regularized determinant of `N + b` is the reciprocal Gamma function up to `√(2π)`. -/
theorem exp_neg_deriv_hurwitzZetaEMC_zero {b : ℂ} (hb : b ∈ slitPlane) :
    Complex.exp (-deriv (hurwitzZetaEMC b) 0) = (Real.sqrt (2 * π) : ℂ) / Complex.Gamma b := by
  rw [(hasDerivAt_hurwitzZetaEMC_zero hb).deriv, Gamma_eq_binetRHS hb, binetRHS]
  have hs : (Real.sqrt (2 * π) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [Complex.exp_neg]
  field_simp

/-! ## Identification with the convergent series -/

theorem sum_shiftCpowC_eq {b : ℂ} (hb : b ∈ slitPlane) {s : ℂ} (hs : s ≠ 1) (N : ℕ) :
    (∑ m ∈ Finset.range (N + 1), (((m : ℝ) : ℂ) + b) ^ (-s))
      = ((((N : ℝ) : ℂ) + b) ^ (1 - s) - b ^ (1 - s)) / (1 - s)
        + (b ^ (-s) + (((N : ℝ) : ℂ) + b) ^ (-s)) / 2
        - s * (s + 1) *
          ∫ x in (0 : ℝ)..(N : ℝ), ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2) := by
  have hem := euler_maclaurin_second_order (f := fun y : ℝ => ((y : ℂ) + b) ^ (-s))
    (f' := fun y : ℝ => -s * ((y : ℂ) + b) ^ (-s - 1))
    (f'' := fun y : ℝ => s * (s + 1) * ((y : ℂ) + b) ^ (-s - 2)) N
    (fun x hx => (hasDerivAt_shiftCpowC hb (-s) hx).congr_deriv (by ring))
    (fun x hx => by
      have hd := (hasDerivAt_shiftCpowC hb (-s - 1) hx).const_mul (-s)
      refine hd.congr_deriv ?_
      rw [show -s - 1 - 1 = -s - 2 by ring]
      ring)
    (ContinuousOn.mul continuousOn_const (continuousOn_shiftCpowC hb (-s - 2)))
  rw [integral_shiftCpowC hb hs N] at hem
  have hker : (∫ x in (0 : ℝ)..(N : ℝ),
      ((bernoulliHalfPer x : ℝ) : ℂ) * (s * (s + 1) * ((x : ℂ) + b) ^ (-s - 2)))
      = s * (s + 1) * ∫ x in (0 : ℝ)..(N : ℝ),
        ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [hker] at hem
  rw [hem]
  simp only [Complex.ofReal_zero, zero_add]

theorem tendsto_shiftCpowC_atTop {b : ℂ} (hb : b ∈ slitPlane) {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun N : ℕ => (((N : ℝ) : ℂ) + b) ^ w) atTop (𝓝 0) := by
  obtain ⟨κ, hκ, hκb⟩ := exists_mul_add_one_le_norm_add hb
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim : Tendsto (fun N : ℕ => (κ * ((N : ℝ) + 1)) ^ w.re * Real.exp (π * |w.im|))
      atTop (𝓝 (0 * Real.exp (π * |w.im|))) := by
    refine Tendsto.mul_const _ ?_
    have hbase : Tendsto (fun N : ℕ => κ * ((N : ℝ) + 1)) atTop atTop :=
      Tendsto.const_mul_atTop hκ (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hrpow : Tendsto (fun t : ℝ => t ^ w.re) atTop (𝓝 0) := by
      simpa using tendsto_rpow_neg_atTop (y := -w.re) (by linarith)
    exact hrpow.comp hbase
  rw [zero_mul] at hlim
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
  exact norm_shiftCpowC_le hb hκ hκb hw.le (Nat.cast_nonneg N)

theorem summable_shiftCpowC {b : ℂ} (hb : b ∈ slitPlane) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (((n : ℝ) : ℂ) + b) ^ (-s)) := by
  obtain ⟨κ, hκ, hκb⟩ := exists_mul_add_one_le_norm_add hb
  have hg : Summable (fun n : ℕ => κ ^ (-s.re) * Real.exp (π * |s.im|) * (n : ℝ) ^ (-s.re)) := by
    refine Summable.mul_left _ ?_
    rw [Real.summable_nat_rpow]
    linarith
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hre : (-s).re = -s.re := by simp
  have him : |(-s).im| = |s.im| := by simp
  have hb' := norm_shiftCpowC_le hb hκ hκb (c := -s) (by rw [hre]; linarith) hn0.le
  rw [hre, him, Real.mul_rpow hκ.le (by linarith)] at hb'
  refine hb'.trans ?_
  have hmono : ((n : ℝ) + 1) ^ (-s.re) ≤ (n : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by linarith)
  calc κ ^ (-s.re) * ((n : ℝ) + 1) ^ (-s.re) * Real.exp (π * |s.im|)
      ≤ κ ^ (-s.re) * (n : ℝ) ^ (-s.re) * Real.exp (π * |s.im|) := by gcongr
    _ = κ ^ (-s.re) * Real.exp (π * |s.im|) * (n : ℝ) ^ (-s.re) := by ring

/-- **The complex-shift Euler–Maclaurin function is the Hurwitz series** for `Re s > 1`. -/
theorem hurwitzZetaEMC_eq_tsum {b : ℂ} (hb : b ∈ slitPlane) {s : ℂ} (hs : 1 < s.re) :
    hurwitzZetaEMC b s = ∑' n : ℕ, (((n : ℝ) : ℂ) + b) ^ (-s) := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hsum := summable_shiftCpowC hb hs
  have hpartial : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), (((m : ℝ) : ℂ) + b) ^ (-s))
      atTop (𝓝 (∑' n : ℕ, (((n : ℝ) : ℂ) + b) ^ (-s))) :=
    hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim1 : Tendsto (fun N : ℕ => (((N : ℝ) : ℂ) + b) ^ (1 - s)) atTop (𝓝 0) :=
    tendsto_shiftCpowC_atTop hb (by simp; linarith)
  have hlim2 : Tendsto (fun N : ℕ => (((N : ℝ) : ℂ) + b) ^ (-s)) atTop (𝓝 0) :=
    tendsto_shiftCpowC_atTop hb (by simp; linarith)
  have hlim3 : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ),
      ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2)) atTop (𝓝 (emKernelC b s)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      (integrableOn_emKernelC_integrand hb (s := s) (by linarith)) tendsto_natCast_atTop_atTop
  have hrhs : Tendsto (fun N : ℕ => ((((N : ℝ) : ℂ) + b) ^ (1 - s) - b ^ (1 - s)) / (1 - s)
      + (b ^ (-s) + (((N : ℝ) : ℂ) + b) ^ (-s)) / 2
      - s * (s + 1) * ∫ x in (0 : ℝ)..(N : ℝ),
        ((bernoulliHalfPer x : ℝ) : ℂ) * ((x : ℂ) + b) ^ (-s - 2)) atTop
      (𝓝 (((0 : ℂ) - b ^ (1 - s)) / (1 - s) + (b ^ (-s) + 0) / 2 - s * (s + 1) * emKernelC b s)) :=
    Tendsto.sub (Tendsto.add ((hlim1.sub tendsto_const_nhds).div_const _)
      ((tendsto_const_nhds.add hlim2).div_const _)) (tendsto_const_nhds.mul hlim3)
  have hfinal := tendsto_nhds_unique (hpartial.congr fun N => sum_shiftCpowC_eq hb hs1 N) hrhs
  rw [hfinal, hurwitzZetaEMC]
  have hs1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1'' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
