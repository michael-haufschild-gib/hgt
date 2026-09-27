import GaloisForLFunctions.RHTower.STCHyperbolicGapFlatCompletionSource
import GaloisForLFunctions.RHTower.STCFlatGapMeasureReaderNoGo

/-!
# The exterior spectral reader forced by the flat Gamma gap

For a nonzero grade `g`, `a = |g|`, the unique flat gap correction is the band kernel
`K_g(x,y) = S(a(x-y)/2) = (1/a)∫_{[-a/2,a/2]} e^{u(x-y)} du`.  On the Hilbert space
`H_a = L²([-a/2,a/2], du/a)` with reflection `Jf(u) = f(-u)` and features `f_x(u) = e^{ux}`:

* `K_g(x,y) = ⟪f_x, J f_y⟫` and `H_g(x,y) = ⟪f_x, f_y⟫ = S(a(x+y)/2)` (positive semidefinite);
* the Krein polarization `K_g = (2/a)∫_0^{a/2} [cosh(ux)cosh(uy) - sinh(ux)sinh(uy)] du`;
* for the canonical seam `u_p(ρ) = -2 p^{-1/2+iτ} x_p sinh(g x_p)` and `v_p = p^{-1/2+iτ} f_{x_p}`,
  `‖v_p‖² = p^{-1} sinh(a x_p)/(a x_p)` and the value-to-norm ratio
  `2 x_p sinh(a x_p)/√(sinh(a x_p)/(a x_p))` exceeds `√(a/2) (log p)^{3/2} p^{a/2}` once
  `a x_p ≥ log 2`; every functional matching the seam on the features is unbounded and
  nonclosable;
* the seam is a derivative evaluation at twice the band edge, `x sinh(gx) = sign(g)[f'_x(a) -
  f'_x(-a)]/2`, and the grade current is the transport tangent of the atoms `(δ_g + δ_{-g})/2`.
-/

open Complex Filter Topology MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal NNReal
open HTGeometry

namespace RHTower

noncomputable section

/-- The band measure `du/a` on `[-a/2, a/2]`. -/
def flatGapBandMeasure (a : ℝ) : Measure ℝ :=
  (Real.toNNReal a⁻¹) • volume.restrict (Set.Icc (-(a / 2)) (a / 2))

instance flatGapBandMeasure_isFinite (a : ℝ) : IsFiniteMeasure (flatGapBandMeasure a) := by
  unfold flatGapBandMeasure; infer_instance

theorem flatGapBand_ae_bound (a : ℝ) : ∀ᵐ u ∂(flatGapBandMeasure a), |u| ≤ a / 2 := by
  unfold flatGapBandMeasure
  have h : ∀ᵐ u ∂(volume.restrict (Set.Icc (-(a / 2)) (a / 2))), |u| ≤ a / 2 :=
    (ae_restrict_mem measurableSet_Icc).mono fun u hu => abs_le.mpr ⟨hu.1, hu.2⟩
  have hac : ((Real.toNNReal a⁻¹ : ℝ≥0∞) • volume.restrict (Set.Icc (-(a / 2)) (a / 2))) ≪
      volume.restrict (Set.Icc (-(a / 2)) (a / 2)) := Measure.smul_absolutelyContinuous
  exact hac.ae_le h

/-- The band Hilbert space `H_a`. -/
abbrev FlatGapBand (a : ℝ) := Lp ℂ 2 (flatGapBandMeasure a)

/-- The exponential band feature `f_x(u) = e^{ux}`. -/
def flatGapFeature (a x : ℝ) : FlatGapBand a :=
  compactSpectralFeature (flatGapBandMeasure a) (flatGapBand_ae_bound a) x

theorem flatGapFeature_ae (a x : ℝ) :
    (flatGapFeature a x : ℝ → ℂ) =ᵐ[flatGapBandMeasure a] fun u => cexp ((u : ℂ) * x) := by
  unfold flatGapFeature compactSpectralFeature
  exact MemLp.coeFn_toLp _

theorem integral_flatGapBandMeasure {a : ℝ} (ha : 0 < a) (f : ℝ → ℂ) :
    ∫ u, f u ∂(flatGapBandMeasure a) = (a⁻¹ : ℝ) • ∫ u in (-(a / 2))..(a / 2), f u := by
  unfold flatGapBandMeasure
  rw [integral_smul_nnreal_measure, intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc, NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.mpr ha.le)]

/-- `(1/a)∫_{-a/2}^{a/2} e^{us} du = S(as/2)`. -/
theorem band_integral_exp {a : ℝ} (ha : 0 < a) (s : ℝ) :
    a⁻¹ * ∫ u in (-(a / 2))..(a / 2), Real.exp (u * s) = hyperbolicGapSinc (a * s / 2) := by
  by_cases hs : s = 0
  · subst hs
    simp only [mul_zero, Real.exp_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one,
      zero_div, hyperbolicGapSinc, if_pos]
    field_simp
    ring
  · rw [intervalIntegral.integral_comp_mul_right (fun t => Real.exp t) hs, integral_exp,
      hyperbolicGapSinc, if_neg (by positivity), smul_eq_mul, Real.sinh_eq]
    field_simp

/-- **(1)** The positive band Gram: `⟪f_x, f_y⟫ = S(a(x+y)/2) = H_g(x,y)`. -/
theorem inner_flatGapFeature {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    ⟪flatGapFeature a x, flatGapFeature a y⟫_ℂ = (hyperbolicGapSinc (a * (x + y) / 2) : ℂ) := by
  rw [L2.inner_def]
  have hae : (fun u => ⟪(flatGapFeature a x : ℝ → ℂ) u, (flatGapFeature a y : ℝ → ℂ) u⟫_ℂ)
      =ᵐ[flatGapBandMeasure a] fun u => ((Real.exp (u * (x + y)) : ℝ) : ℂ) := by
    filter_upwards [flatGapFeature_ae a x, flatGapFeature_ae a y] with u hx hy
    rw [hx, hy, show ∀ a b : ℂ, ⟪a, b⟫_ℂ = conj a * b from fun a b => by simp [mul_comm],
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_exp,
      Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [integral_congr_ae hae, integral_flatGapBandMeasure ha, intervalIntegral.integral_ofReal,
    ← band_integral_exp ha (x + y), Complex.real_smul]
  push_cast
  ring

/-- The band norm: `‖f_x‖² = S(ax) = sinh(ax)/(ax)`. -/
theorem norm_sq_flatGapFeature {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖flatGapFeature a x‖ ^ 2 = hyperbolicGapSinc (a * x) := by
  have h := congrArg (fun z : ℂ => z.re) (inner_flatGapFeature ha x x)
  rw [← RCLike.re_to_complex, inner_self_eq_norm_sq, Complex.ofReal_re] at h
  rw [h]
  congr 1
  ring

/-- **Positive semidefiniteness** of `H_g`: `Re Σ c̄_i c_j S(a(x_i+x_j)/2) ≥ 0`. -/
theorem flatGapGram_posSemidef {a : ℝ} (ha : 0 < a) {n : ℕ} (x : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, conj (c i) * c j * (hyperbolicGapSinc (a * (x i + x j) / 2) : ℂ)).re := by
  have hsum : ∑ i, ∑ j, conj (c i) * c j * (hyperbolicGapSinc (a * (x i + x j) / 2) : ℂ) =
      ⟪∑ i, c i • flatGapFeature a (x i), ∑ j, c j • flatGapFeature a (x j)⟫_ℂ := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, inner_flatGapFeature ha]
    ring
  rw [hsum]
  have := inner_self_nonneg (𝕜 := ℂ) (x := ∑ i, c i • flatGapFeature a (x i))
  rwa [RCLike.re_to_complex] at this

/-- Negation preserves the band measure. -/
theorem measurePreserving_neg_flatGapBand (a : ℝ) :
    MeasurePreserving (fun u : ℝ => -u) (flatGapBandMeasure a) (flatGapBandMeasure a) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Icc (a := -(a / 2)) (b := a / 2))
  have e : (Neg.neg ⁻¹' Set.Icc (-(a / 2)) (a / 2) : Set ℝ) = Set.Icc (-(a / 2)) (a / 2) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro hu <;> constructor <;> linarith [hu.1, hu.2]
  rw [e] at h
  refine ⟨measurable_neg, ?_⟩
  unfold flatGapBandMeasure
  rw [Measure.map_smul, h.map_eq]

/-- The band reflection `J f(u) = f(-u)`. -/
def flatGapReflection (a : ℝ) : FlatGapBand a →ₗᵢ[ℂ] FlatGapBand a :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ => -u) (measurePreserving_neg_flatGapBand a)

theorem flatGapReflection_feature (a y : ℝ) :
    flatGapReflection a (flatGapFeature a y) = flatGapFeature a (-y) := by
  apply Lp.ext
  have h1 : (flatGapReflection a (flatGapFeature a y) : ℝ → ℂ) =ᵐ[flatGapBandMeasure a]
      (flatGapFeature a y : ℝ → ℂ) ∘ (fun u : ℝ => -u) :=
    Lp.coeFn_compMeasurePreserving (flatGapFeature a y) (measurePreserving_neg_flatGapBand a)
  have h2 := (measurePreserving_neg_flatGapBand a).quasiMeasurePreserving.ae_eq_comp
    (flatGapFeature_ae a y)
  filter_upwards [h1, h2, flatGapFeature_ae a (-y)] with u hu1 hu2 hu3
  rw [hu1, hu2, hu3]
  simp only [Function.comp_apply]
  push_cast
  ring_nf

/-- **(1)** The flat gap kernel is the reflected pairing `K_g(x,y) = ⟪f_x, J f_y⟫ = S(a(x-y)/2)`. -/
theorem flatGapKernel_eq_reflected_inner {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    ⟪flatGapFeature a x, flatGapReflection a (flatGapFeature a y)⟫_ℂ =
      (hyperbolicGapSinc (a * (x - y) / 2) : ℂ) := by
  rw [flatGapReflection_feature, inner_flatGapFeature ha, sub_eq_add_neg]

/-- `H_g(x,y) = K_g(x,-y)`. -/
theorem flatGapGram_eq_kernel_neg (a x y : ℝ) :
    ⟪flatGapFeature a x, flatGapFeature a y⟫_ℂ =
      ⟪flatGapFeature a x, flatGapReflection a (flatGapFeature a (-y))⟫_ℂ := by
  rw [flatGapReflection_feature, neg_neg]

/-- **(2) Krein polarization** of the flat gap kernel. -/
theorem flatGapKernel_krein {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    2 / a * ∫ u in (0 : ℝ)..(a / 2),
        (Real.cosh (u * x) * Real.cosh (u * y) - Real.sinh (u * x) * Real.sinh (u * y)) =
      hyperbolicGapSinc (a * (x - y) / 2) := by
  have hint : ∀ u : ℝ, Real.cosh (u * x) * Real.cosh (u * y) - Real.sinh (u * x) * Real.sinh (u * y)
      = Real.cosh (u * (x - y)) := by
    intro u; rw [mul_sub, Real.cosh_sub]
  simp only [hint]
  by_cases hd : x - y = 0
  · rw [hd]
    simp only [mul_zero, Real.cosh_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one,
      sub_zero, zero_div, hyperbolicGapSinc, if_pos]
    field_simp
  · have hcosh : ∫ t in (0 : ℝ)..(a / 2 * (x - y)), Real.cosh t = Real.sinh (a / 2 * (x - y)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => Real.hasDerivAt_sinh t)
        (Real.continuous_cosh.intervalIntegrable _ _), Real.sinh_zero, sub_zero]
    rw [intervalIntegral.integral_comp_mul_right (fun t => Real.cosh t) hd, zero_mul, hcosh,
      hyperbolicGapSinc, if_neg (by positivity), smul_eq_mul]
    field_simp

/-! ### The canonical seam on the band -/

/-- The seam vector `v_p = p^{-1/2+iτ} f_{log p}`. -/
def flatGapSeamVector (a τ : ℝ) (p : ℕ) : FlatGapBand a :=
  ((p : ℂ) ^ ((-1 / 2 : ℂ) + (τ : ℂ) * I)) • flatGapFeature a (Real.log p)

/-- **(3)** The canonical seam at `ρ = 1/2 + g + iτ`: `u_p = -2 p^{-1/2+iτ} x_p sinh(g x_p)`. -/
theorem orbitwiseNatPrimeSeamCharge_band {p : ℕ} (hp : 0 < p) (g τ : ℝ) :
    orbitwiseNatPrimeSeamCharge p (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I) =
      -2 * (p : ℂ) ^ ((-1 / 2 : ℂ) + (τ : ℂ) * I) *
        ((Real.log p * Real.sinh (g * Real.log p) : ℝ) : ℂ) := by
  rw [orbitwiseNatPrimeSeamCharge_eq_grade_derivative hp,
    (HTGeometry.hasDerivAt_cosh_grade (Real.log p) g).deriv]

private theorem norm_phase {p : ℕ} (hp : 0 < p) (τ : ℝ) :
    ‖(p : ℂ) ^ ((-1 / 2 : ℂ) + (τ : ℂ) * I)‖ = (p : ℝ) ^ (-1 / 2 : ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp

/-- **(4)** `‖v_p‖² = p^{-1} sinh(a x_p)/(a x_p)`. -/
theorem norm_sq_flatGapSeamVector {a : ℝ} (ha : 0 < a) (τ : ℝ) {p : ℕ} (hp : 0 < p) :
    ‖flatGapSeamVector a τ p‖ ^ 2 = (p : ℝ)⁻¹ * hyperbolicGapSinc (a * Real.log p) := by
  rw [flatGapSeamVector, norm_smul, mul_pow, norm_phase hp, norm_sq_flatGapFeature ha]
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hsq : ((p : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = (p : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp'.le]
    norm_num
    exact Real.rpow_neg_one _
  rw [hsq]

/-- The value-to-norm ratio of the seam on the band feature. -/
def flatGapSeamRatio (a : ℝ) (p : ℕ) : ℝ :=
  2 * Real.log p * Real.sinh (a * Real.log p) / Real.sqrt (hyperbolicGapSinc (a * Real.log p))

/-- **(4)** `|u_p(ρ)|/‖v_p‖ = 2 x_p sinh(a x_p)/√(sinh(a x_p)/(a x_p))`. -/
theorem norm_seam_div_norm_vector {g : ℝ} (hg : g ≠ 0) (τ : ℝ) {p : ℕ} (hp : p.Prime) :
    ‖orbitwiseNatPrimeSeamCharge p (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I)‖ /
        ‖flatGapSeamVector |g| τ p‖ = flatGapSeamRatio |g| p := by
  have ha : 0 < |g| := abs_pos.mpr hg
  have hp0 : 0 < p := hp.pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hS : 0 < hyperbolicGapSinc (|g| * Real.log p) := by
    have := hyperbolicGapSinc_gt_one_of_pos (mul_pos ha hlog); linarith
  have hv : ‖flatGapSeamVector |g| τ p‖ =
      (p : ℝ) ^ (-1 / 2 : ℝ) * Real.sqrt (hyperbolicGapSinc (|g| * Real.log p)) := by
    rw [flatGapSeamVector, norm_smul, norm_phase hp0]
    congr 1
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_flatGapFeature ha]
  have habs : |Real.sinh (g * Real.log p)| = Real.sinh (|g| * Real.log p) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos hlog]
  rw [orbitwiseNatPrimeSeamCharge_band hp0, hv, norm_mul, norm_mul, norm_phase hp0,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, habs, abs_of_pos hlog, flatGapSeamRatio]
  have hpp : 0 < (p : ℝ) ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hp' _
  have hsq : 0 < Real.sqrt (hyperbolicGapSinc (|g| * Real.log p)) := Real.sqrt_pos.mpr hS
  simp only [norm_neg, RCLike.norm_ofNat]
  field_simp

/-- **(5)** Once `a x_p ≥ log 2`, the ratio exceeds `√(a/2) (log p)^{3/2} p^{a/2}`. -/
theorem flatGapSeamRatio_ge {a : ℝ} (ha : 0 < a) {p : ℕ} (hp : p.Prime)
    (hbig : Real.log 2 ≤ a * Real.log p) :
    Real.sqrt (a / 2) * Real.log p ^ (3 / 2 : ℝ) * (p : ℝ) ^ (a / 2) ≤ flatGapSeamRatio a p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  set x := Real.log (p : ℝ) with hxdef
  have hax : 0 < a * x := mul_pos ha hlog
  have hE : 2 ≤ Real.exp (a * x) := by
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ Real.exp (a * x) := Real.exp_le_exp.mpr hbig
  have hsinh : Real.exp (a * x) / 4 ≤ Real.sinh (a * x) := by
    rw [Real.sinh_eq]
    have : Real.exp (-(a * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hsp : 0 < Real.sinh (a * x) := Real.sinh_pos_iff.mpr hax
  have hS : hyperbolicGapSinc (a * x) = Real.sinh (a * x) / (a * x) := by
    rw [hyperbolicGapSinc, if_neg hax.ne']
  -- ratio = 2 x √(ax) √(sinh(ax))
  have hratio : flatGapSeamRatio a p = 2 * x * Real.sqrt (a * x) * Real.sqrt (Real.sinh (a * x)) := by
    rw [flatGapSeamRatio, ← hxdef, hS, Real.sqrt_div hsp.le]
    have h1 : 0 < Real.sqrt (Real.sinh (a * x)) := Real.sqrt_pos.mpr hsp
    have h2 : 0 < Real.sqrt (a * x) := Real.sqrt_pos.mpr hax
    have h3 : Real.sinh (a * x) = Real.sqrt (Real.sinh (a * x)) * Real.sqrt (Real.sinh (a * x)) :=
      (Real.mul_self_sqrt hsp.le).symm
    rw [div_div_eq_mul_div]
    conv_lhs => rw [h3]
    field_simp
    rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
  rw [hratio]
  have hpa : (p : ℝ) ^ (a / 2) = Real.sqrt (Real.exp (a * x)) := by
    rw [Real.rpow_def_of_pos hp', ← hxdef,
      show Real.exp (a * x) = Real.exp (x * (a / 2)) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
      Real.sqrt_sq (Real.exp_nonneg _)]
  have hx32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hlog.le (by norm_num)]
    norm_num
  rw [hx32, hpa]
  have hsq_e : Real.sqrt (Real.exp (a * x)) ≤ 2 * Real.sqrt (Real.sinh (a * x)) := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)], ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hax' : Real.sqrt (a * x) = Real.sqrt a * Real.sqrt x := Real.sqrt_mul ha.le x
  have ha2 : Real.sqrt (a / 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by linarith)
  rw [hax']
  have hsx := Real.sqrt_nonneg x
  have hse := Real.sqrt_nonneg (Real.exp (a * x))
  have hsa := Real.sqrt_nonneg (a / 2)
  calc Real.sqrt (a / 2) * (x * Real.sqrt x) * Real.sqrt (Real.exp (a * x))
      ≤ Real.sqrt a * (x * Real.sqrt x) * (2 * Real.sqrt (Real.sinh (a * x))) := by
        gcongr
    _ = 2 * x * (Real.sqrt a * Real.sqrt x) * Real.sqrt (Real.sinh (a * x)) := by ring

/-- The ratio diverges along the primes. -/
theorem eventually_flatGapSeamRatio_ge {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p → M ≤ flatGapSeamRatio a p := by
  have hlim : Tendsto (fun n : ℕ => Real.sqrt (a / 2) * Real.log n ^ (3 / 2 : ℝ) *
      (n : ℝ) ^ (a / 2)) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => Real.log n ^ (3 / 2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp (Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (a / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
    exact (h1.const_mul_atTop (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < a / 2))).atTop_mul_atTop₀
      h2 |>.congr fun n => by ring
  have hlog : Tendsto (fun n : ℕ => a * Real.log n) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim.eventually_ge_atTop M).and
    (hlog.eventually_ge_atTop (Real.log 2)))
  exact ⟨N, fun p hp hNp => (hN p hNp).1.trans (flatGapSeamRatio_ge ha hp (hN p hNp).2)⟩

private theorem seam_ne_zero {g : ℝ} (hg : g ≠ 0) (τ : ℝ) {p : ℕ} (hp : p.Prime) :
    orbitwiseNatPrimeSeamCharge p (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I) ≠ 0 := by
  rw [orbitwiseNatPrimeSeamCharge_band hp.pos]
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hs : Real.sinh (g * Real.log p) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero hg hlog.ne')
  have hc : (p : ℂ) ^ ((-1 / 2 : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h (by exact_mod_cast hp.ne_zero)
  exact mul_ne_zero (mul_ne_zero (by norm_num) hc) (by exact_mod_cast mul_ne_zero hlog.ne' hs)

/-- **Norm cost.** Any bounded functional matching the seam at a prime has norm at least the
ratio there. -/
theorem flatGapSeamRatio_le_opNorm {g : ℝ} (hg : g ≠ 0) (τ : ℝ) (φ : FlatGapBand |g| →L[ℂ] ℂ)
    {p : ℕ} (hp : p.Prime)
    (hφ : φ (flatGapSeamVector |g| τ p) =
      orbitwiseNatPrimeSeamCharge p (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I)) :
    flatGapSeamRatio |g| p ≤ ‖φ‖ := by
  rw [← norm_seam_div_norm_vector hg τ hp, ← hφ]
  have hv : 0 < ‖flatGapSeamVector |g| τ p‖ := by
    have := seam_ne_zero hg τ hp
    rw [← hφ] at this
    rcases (norm_nonneg (flatGapSeamVector |g| τ p)).lt_or_eq with h | h
    · exact h
    · exfalso; apply this
      rw [norm_eq_zero.mp h.symm, map_zero]
  rw [div_le_iff₀ hv]
  exact φ.le_opNorm _

/-- **No bounded reader.** No bounded functional on the band sends every `v_p` to `u_p(ρ)`. -/
theorem no_bounded_flatGap_seam_reader {g : ℝ} (hg : g ≠ 0) (τ : ℝ) :
    ¬ ∃ φ : FlatGapBand |g| →L[ℂ] ℂ, ∀ p : ℕ, p.Prime →
      φ (flatGapSeamVector |g| τ p) =
        orbitwiseNatPrimeSeamCharge p (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I) := by
  rintro ⟨φ, hφ⟩
  obtain ⟨N, hN⟩ := eventually_flatGapSeamRatio_ge (abs_pos.mpr hg) (‖φ‖ + 1)
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  have := flatGapSeamRatio_le_opNorm hg τ φ hp (hφ p hp)
  linarith [hN p hp hNp]

/-- **Nonclosability.** Any linear functional on a subspace containing every `v_p`, with
`v_p ↦ u_p(ρ)`, has vectors of its domain tending to `0` on which it takes the value `1`. -/
theorem flatGap_seam_reader_not_closable {g : ℝ} (hg : g ≠ 0) (τ : ℝ)
    (D : Submodule ℂ (FlatGapBand |g|)) (ℓ : D →ₗ[ℂ] ℂ)
    (hD : ∀ p : ℕ, p.Prime → flatGapSeamVector |g| τ p ∈ D)
    (hℓ : ∀ (p : ℕ) (hp : p.Prime), ℓ ⟨_, hD p hp⟩ =
      orbitwiseNatPrimeSeamCharge p (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I)) :
    ∃ z : ℕ → D, Tendsto (fun n => (z n : FlatGapBand |g|)) atTop (𝓝 0) ∧ ∀ n, ℓ (z n) = 1 := by
  have ha : 0 < |g| := abs_pos.mpr hg
  have hex : ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ ((n : ℝ) + 1 ≤ flatGapSeamRatio |g| p) := by
    intro n
    obtain ⟨N, hN⟩ := eventually_flatGapSeamRatio_ge ha ((n : ℝ) + 1)
    obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
    exact ⟨p, hp, hN p hp hNp⟩
  choose P hP hPr using hex
  let uP : ℕ → ℂ := fun n => orbitwiseNatPrimeSeamCharge (P n)
    (((1 / 2 + g : ℝ) : ℂ) + (τ : ℂ) * I)
  have hu : ∀ n, uP n ≠ 0 := fun n => seam_ne_zero hg τ (hP n)
  refine ⟨fun n => (uP n)⁻¹ • ⟨_, hD (P n) (hP n)⟩, ?_, fun n => ?_⟩
  · refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [Submodule.coe_smul, norm_smul, norm_inv]
    have hratio := norm_seam_div_norm_vector hg τ (hP n)
    have hpos : 0 < ‖uP n‖ := norm_pos_iff.mpr (hu n)
    rw [inv_mul_eq_div, div_le_div_iff₀ hpos (by positivity), one_mul]
    have h1 := hPr n
    rw [← hratio, le_div_iff₀ ?_] at h1
    · simpa [uP, mul_comm] using h1
    · rcases (norm_nonneg (flatGapSeamVector |g| τ (P n))).lt_or_eq with h | h
      · exact h
      · exfalso
        have := hℓ (P n) (hP n)
        have hz : (⟨_, hD (P n) (hP n)⟩ : D) = 0 := Subtype.ext (norm_eq_zero.mp h.symm)
        rw [hz, map_zero] at this
        exact hu n this.symm
  · rw [map_smul, hℓ (P n) (hP n), smul_eq_mul, inv_mul_cancel₀ (hu n)]

/-! ### The seam is a derivative evaluation at twice the band edge -/

/-- **(6)** `x sinh(gx) = sign(g) [f'_x(a) - f'_x(-a)]/2` with `f'_x(u) = x e^{ux}`, `a = |g|`. -/
theorem seam_derivative_band_edge {g : ℝ} (hg : g ≠ 0) (x : ℝ) :
    x * Real.sinh (g * x) =
      Real.sign g * (x * Real.exp (|g| * x) - x * Real.exp (-|g| * x)) / 2 := by
  rcases lt_or_gt_of_ne hg with h | h
  · rw [abs_of_neg h, Real.sign_of_neg h, Real.sinh_eq, show -(-g) * x = g * x by ring,
      show -g * x = -(g * x) by ring]
    ring
  · rw [abs_of_pos h, Real.sign_of_pos h, Real.sinh_eq, show -g * x = -(g * x) by ring]
    ring

/-- **Transport current.** The flat potential is the Laplace transform of the moving atoms
`(δ_g + δ_{-g})/2`; its grade derivative is the first-order current
`φ ↦ (φ'(g) - φ'(-g))/2`, which on `φ(u) = e^{ux}` is `x sinh(gx)`. -/
theorem transport_current (φ φ' : ℝ → ℝ) (hφ : ∀ t, HasDerivAt φ (φ' t) t) (g : ℝ) :
    HasDerivAt (fun t => (φ t + φ (-t)) / 2) ((φ' g - φ' (-g)) / 2) g := by
  have h1 := hφ g
  have h2 : HasDerivAt (fun t => φ (-t)) (φ' (-g) * (-1)) g :=
    (hφ (-g)).comp g (hasDerivAt_neg g)
  refine ((h1.add h2).div_const 2).congr_deriv ?_
  ring

theorem cosh_eq_atom_average (g x : ℝ) :
    Real.cosh (g * x) = (Real.exp (g * x) + Real.exp ((-g) * x)) / 2 := by
  rw [Real.cosh_eq, neg_mul]

theorem transport_current_exponential (g x : ℝ) :
    HasDerivAt (fun t => (Real.exp (t * x) + Real.exp ((-t) * x)) / 2) (x * Real.sinh (g * x)) g := by
  have h := transport_current (fun t => Real.exp (t * x)) (fun t => x * Real.exp (t * x))
    (fun t => by simpa [mul_comm] using ((hasDerivAt_id t).mul_const x).exp) g
  convert h using 1
  rw [Real.sinh_eq, neg_mul]
  ring

end

end RHTower
