import GaloisForLFunctions.RHTower.EvenSectorSpectralConsistency

/-!
# The even functional as an integral against one reference measure

Let `L` be the even Weil functional and `ν_Φ` the cosine-shift measure of an even strip function
`Φ` (`exists_cosineShift_measure`), `ρ(z) = (z² + 2)^{1/2}`.

**Multiplier form** (`evenWeilDensity_specSq_mul_multiplier`).  For every multiplier `T` (even,
holomorphic and exponentially decaying on `|Im z| ≤ 9/4`, with `T(z̄) = conj T(z)`),
`L(Φ Φ^# T) = ∫ Re T̃ dν_Φ`, `T̃(ρ) = T((ρ² − 2)^{1/2})`.  This is the kernel identity
`evenWeilDensity_specSq_mul_kernel` with `κ = stripTest T̃`, because `T = T̃ ∘ ρ` at the points
where `L` reads its argument.

**Reference** `S(z) = sech(z/2)` (`sechHalf`).  On `|Im z| ≤ 9/4`,
`|cosh(z/2)| ≥ cos(Im z/2) cosh(Re z/2) > 0`, so `S` is an even strip function and
`S S^# · cosh²(z/2) = 1`.  Hence for every `Ψ` such that `T_Ψ = Ψ Ψ^# cosh²(z/2)` is a multiplier,
`L(Ψ Ψ^#) = ∫ Re T̃_Ψ dν_S` (`evenWeilDensity_specSq_eq_integral_sechHalf`): a single positive
measure `ν_S` represents `L` on all such spectral squares.  Where `ρ² ≥ 2`,
`T̃_Ψ(ρ) = |Ψ(r)|² cosh²(r/2) ≥ 0` with `r = (ρ² − 2)^{1/2}` (`re_rhoLift_sechWeight_nonneg`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral GaloisForLFunctions.HTGeometry

/-! ## The multiplier form of the kernel identity -/

/-- At a point where `ρ(z)` is real, a multiplier is the cosine transform of `stripTest T̃`. -/
theorem multiplier_eq_kernel_integral {T : ℂ → ℂ} (hT : Multiplier T) {κ : ℝ → ℝ}
    (hκs : ∀ s : ℝ, ∫ t : ℝ, κ t * Real.cos (t * s) = (rhoLift T s).re) {z : ℂ} {s : ℝ}
    (hzs : rhoC z = s) : T z = ∫ t : ℝ, (κ t : ℂ) * Complex.cos (t * rhoC z) := by
  have hl : rhoLift T s = T z := by rw [← hzs, rhoLift_rhoC hT]
  have him : (T z).im = 0 := by rw [← hl]; exact rhoLift_im_ofReal hT s
  rw [hzs, integral_kappa_cos_ofReal, hκs, hl]
  exact Complex.ext (by simp) (by simp [him])

/-- **Multiplier form of the kernel identity.**  `L(Φ Φ^# T) = ∫ Re T̃ dν_Φ`. -/
theorem evenWeilDensity_specSq_mul_multiplier {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {Φ : ℂ → ℂ}
    (hΦ : EvenStrip Φ) {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν : ∀ y, charFun ν y = (cosineShiftFn lam Φ y : ℂ)) {T : ℂ → ℂ} (hT : Multiplier T) :
    evenWeilDensity lam (fun z => specSq Φ z * T z) = ∫ ρ, (rhoLift T ρ).re ∂ν := by
  obtain ⟨ε, C, hε, hs⟩ := stripDecay_rhoLift hT
  set κ := stripTest (rhoLift T) with hκdef
  have hκc : Continuous κ := continuous_stripTest (by norm_num) hε hs
  have hκb : ∀ t, |κ t| ≤ C * (∫ r : ℝ, Real.exp (-(ε * |r|))) / (2 * Real.pi) *
      Real.exp (-(3 / 2 * |t|)) := abs_stripTest_le (by norm_num) hε hs
  have hκs : ∀ s : ℝ, ∫ t : ℝ, κ t * Real.cos (t * s) = (rhoLift T s).re := fun s =>
    integral_stripTest_mul_cos (by norm_num) hε hs (rhoLift_neg T) (rhoLift_im_ofReal hT) s
  rw [evenWeilDensity_congr (K₂ := fun z => specSq Φ z * ∫ t : ℝ, (κ t : ℂ) *
      Complex.cos (t * rhoC z))
    (by rw [multiplier_eq_kernel_integral hT hκs rhoC_I_div_two])
    (by rw [multiplier_eq_kernel_integral hT hκs rhoC_neg_I_div_two])
    (fun r => by rw [multiplier_eq_kernel_integral hT hκs (rhoC_ofReal r)]),
    evenWeilDensity_specSq_mul_kernel hg hΦ hν hκc (by norm_num : (5 / 4 : ℝ) < 3 / 2) hκb]
  congr 1; funext ρ
  exact hκs ρ


/-! ## The reference `sech(z/2)` -/

theorem cosh_ofReal_add_mul_I (a b : ℝ) :
    Complex.cosh ((a : ℂ) + b * I) =
      ((Real.cosh a * Real.cos b : ℝ) : ℂ) + ((Real.sinh a * Real.sin b : ℝ) : ℂ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- `|cosh(a + ib)| ≥ cosh a · |cos b|`. -/
theorem cosh_mul_abs_cos_le_norm_cosh (w : ℂ) :
    Real.cosh w.re * |Real.cos w.im| ≤ ‖Complex.cosh w‖ := by
  have e : w = (w.re : ℂ) + w.im * I := (Complex.re_add_im w).symm
  have h := Complex.abs_re_le_norm (Complex.cosh w)
  rw [e, cosh_ofReal_add_mul_I] at h ⊢
  simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re,
    mul_zero, add_zero, Complex.mul_re, Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero] at h
  rw [abs_mul, abs_of_pos (Real.cosh_pos _)] at h
  simpa using h

/-- `|cosh w| ≤ cosh(Re w)`. -/
theorem norm_cosh_le_real_cosh_re (w : ℂ) : ‖Complex.cosh w‖ ≤ Real.cosh w.re := by
  rw [Complex.cosh, norm_div, Complex.norm_two, Real.cosh_eq]
  gcongr
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re]

theorem cos_half_pos {y : ℝ} (hy : |y| ≤ 9 / 4) : 0 < Real.cos (y / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  have h1 := abs_le.mp hy
  have hpi : (9 / 8 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  constructor <;> linarith [h1.1, h1.2]

theorem cosh_half_ne_zero {z : ℂ} (hz : |z.im| ≤ 9 / 4) : Complex.cosh (z / 2) ≠ 0 := by
  intro h0
  have h := cosh_mul_abs_cos_le_norm_cosh (z / 2)
  rw [h0, norm_zero] at h
  have hre : (z / 2).re = z.re / 2 := by simp
  have him : (z / 2).im = z.im / 2 := by simp
  rw [hre, him, abs_of_pos (cos_half_pos hz)] at h
  have := mul_pos (Real.cosh_pos (z.re / 2)) (cos_half_pos hz)
  linarith

/-- The reference `S(z) = sech(z/2)`. -/
def sechHalf (z : ℂ) : ℂ := (Complex.cosh (z / 2))⁻¹

theorem exp_abs_half_le_two_cosh (x : ℝ) : Real.exp (|x| / 2) ≤ 2 * Real.cosh (x / 2) := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-(x / 2))]
  · rw [abs_of_nonpos hx, show -x / 2 = -(x / 2) by ring]; linarith [Real.exp_pos (x / 2)]

theorem norm_sechHalf_le {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    ‖sechHalf z‖ ≤ 2 / Real.cos (5 / 8) * Real.exp (-(1 / 2 * |z.re|)) := by
  have hz' : |z.im| ≤ 9 / 4 := by linarith
  have hc58 : 0 < Real.cos (5 / 8) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_gt_three]
  have hcy : Real.cos (5 / 8) ≤ Real.cos (z.im / 2) := by
    rw [← Real.cos_abs (z.im / 2)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_gt_three])
    rw [abs_div, abs_two]; linarith
  have h := cosh_mul_abs_cos_le_norm_cosh (z / 2)
  have hre : (z / 2).re = z.re / 2 := by simp
  have him : (z / 2).im = z.im / 2 := by simp
  rw [hre, him, abs_of_pos (cos_half_pos hz')] at h
  have hch := exp_abs_half_le_two_cosh z.re
  have hlow : Real.cos (5 / 8) * Real.exp (|z.re| / 2) / 2 ≤ ‖Complex.cosh (z / 2)‖ := by
    have := mul_le_mul hch hcy hc58.le (by positivity)
    nlinarith [Real.cosh_pos (z.re / 2)]
  have hpos : 0 < Real.cos (5 / 8) * Real.exp (|z.re| / 2) / 2 := by positivity
  unfold sechHalf
  rw [norm_inv, inv_le_iff_one_le_mul₀ (hpos.trans_le hlow)]
  calc (1 : ℝ) = 2 / Real.cos (5 / 8) * Real.exp (-(1 / 2 * |z.re|)) *
        (Real.cos (5 / 8) * Real.exp (|z.re| / 2) / 2) := by
        rw [show -(1 / 2 * |z.re|) = -(|z.re| / 2) by ring, Real.exp_neg]
        field_simp
    _ ≤ _ := by gcongr

theorem evenStrip_sechHalf : EvenStrip sechHalf := by
  refine ⟨⟨1 / 2, 2 / Real.cos (5 / 8), by norm_num, fun z hz => ?_,
    fun z hz => norm_sechHalf_le hz⟩, fun z => ?_, fun r => ?_⟩
  · have hne := cosh_half_ne_zero (z := z) (by linarith)
    exact ((Complex.differentiable_cosh.differentiableAt.comp z
      (differentiableAt_id.div_const 2))).inv hne
  · unfold sechHalf; rw [neg_div, Complex.cosh_neg]
  · unfold sechHalf
    rw [show (r : ℂ) / 2 = ((r / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cosh,
      ← Complex.ofReal_inv, Complex.ofReal_im]

theorem specSq_sechHalf_mul_cosh_sq {z : ℂ} (hz : |z.im| ≤ 9 / 4) :
    specSq sechHalf z * Complex.cosh (z / 2) ^ 2 = 1 := by
  have hne := cosh_half_ne_zero hz
  unfold specSq sechHalf
  rw [show conj z / 2 = conj (z / 2) by rw [map_div₀, map_ofNat], Complex.cosh_conj, ← map_inv₀,
    Complex.conj_conj]
  field_simp

/-- The weight `T_Ψ = Ψ Ψ^# cosh²(z/2)`. -/
def sechWeight (Ψ : ℂ → ℂ) (z : ℂ) : ℂ := specSq Ψ z * Complex.cosh (z / 2) ^ 2

/-- **One reference measure.**  If `Ψ Ψ^# cosh²(z/2)` is a multiplier, then
`L(Ψ Ψ^#) = ∫ Re T̃_Ψ dν_S`, `S = sech(z/2)`. -/
theorem evenWeilDensity_specSq_eq_integral_sechHalf {lam : ℕ → ℝ} {Cg : ℝ}
    (hg : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ Cg * Real.sqrt n * (1 + Real.log n)) {ν : Measure ℝ}
    [IsFiniteMeasure ν] (hν : ∀ y, charFun ν y = (cosineShiftFn lam sechHalf y : ℂ))
    {Ψ : ℂ → ℂ} (hT : Multiplier (sechWeight Ψ)) :
    evenWeilDensity lam (specSq Ψ) = ∫ ρ, (rhoLift (sechWeight Ψ) ρ).re ∂ν := by
  have e : ∀ z : ℂ, |z.im| ≤ 9 / 4 → specSq Ψ z = specSq sechHalf z * sechWeight Ψ z := by
    intro z hz
    unfold sechWeight
    rw [show specSq sechHalf z * (specSq Ψ z * Complex.cosh (z / 2) ^ 2) =
      specSq Ψ z * (specSq sechHalf z * Complex.cosh (z / 2) ^ 2) by ring,
      specSq_sechHalf_mul_cosh_sq hz, mul_one]
  rw [evenWeilDensity_congr (K₂ := fun z => specSq sechHalf z * sechWeight Ψ z)
    (e _ (by norm_num)) (e _ (by norm_num)) (fun r => e _ (by norm_num)),
    evenWeilDensity_specSq_mul_multiplier hg evenStrip_sechHalf hν hT]

theorem sqrtPrincipal_ofReal_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    sqrtPrincipal (a : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
  unfold sqrtPrincipal
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow ha,
    Real.sqrt_eq_rpow]

/-- Off the segment `ρ² < 2` the lifted weight is `|Ψ(r)|² cosh²(r/2) ≥ 0`. -/
theorem re_rhoLift_sechWeight_nonneg (Ψ : ℂ → ℂ) {ρ : ℝ} (hρ : 2 ≤ ρ ^ 2) :
    0 ≤ (rhoLift (sechWeight Ψ) ρ).re := by
  unfold rhoLift sechWeight
  rw [show (ρ : ℂ) ^ 2 - 2 = ((ρ ^ 2 - 2 : ℝ) : ℂ) by push_cast; ring,
    sqrtPrincipal_ofReal_of_nonneg (by linarith), specSq_ofReal_eq,
    show ((Real.sqrt (ρ ^ 2 - 2) : ℝ) : ℂ) / 2 = ((Real.sqrt (ρ ^ 2 - 2) / 2 : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_cosh, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  positivity

end RHTower.EvenSector

end
