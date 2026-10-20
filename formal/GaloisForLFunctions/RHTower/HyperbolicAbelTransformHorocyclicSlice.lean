import GaloisForLFunctions.RHTower.DeckPointPairSelbergTransform
import GaloisForLFunctions.RHTower.HyperbolicOrbitalIntegral

/-!
# The Abel transform of a point-pair profile and the horocyclic slice

For a continuous profile `k` vanishing on `(R, ∞)` the **Abel transform**

`𝒜k(v) = ∫_ℝ k(η²/4 + sinh²(v/2)) dη`

is even, continuous and compactly supported (`abelTransform`).  It is the integral of the
point-pair kernel `k(u(z, w))` along a horocycle:

* **Slice** (`integral_pairU_slice`).  For `y, y' > 0`,
  `∫_ℝ k(u(x + iy, x' + iy')) dx = √(yy') 𝒜k(log y − log y')`,
  since `u = ((x − x')² + (y − y')²)/(4yy')` and `(y − y')²/(4yy') = sinh²((log y − log y')/2)`.
* **Mehler–Fock = Fourier ∘ Abel** (`selbergTransform_eq_integral_abelTransform`).  The Selberg
  transform `h_k(s) = ∫_ℍ k(u(i, w)) (Im w)^s dμ(w)` is
  `h_k(s) = ∫_ℝ 𝒜k(v) e^{(s − ½)v} dv`; on the critical line `h_k(½ + iτ)` is the Fourier
  transform of `𝒜k` (`selbergTransform_critical`).

The integrals over `ℍ` are computed in the chart `(y, x) ↦ x + iy` with the density `y⁻²`
(`integral_upperHalfPlane_eq_iterated`).
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.RHTower.MehlerFock

open DeckPointPair HyperbolicPowerEigen

/-! ### The chart `(y, x) ↦ x + iy` -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The chart integrand `y⁻² F(x + iy)` at `p = (y, x)`. -/
def hyperbolicChartIntegrand (F : ℍ → E) (p : ℝ × ℝ) : E := (p.1 ^ 2)⁻¹ • F (ofComplex ⟨p.2, p.1⟩)

theorem chartIntegrand_eq_on (F : ℍ → E) {p : ℝ × ℝ} (hp : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) :
    (hyperbolicDensity (ofComplex (stripEquiv.symm p))).toReal • F (ofComplex (stripEquiv.symm p))
      = hyperbolicChartIntegrand F p := by
  have hy : (0 : ℝ) < p.1 := hp.1
  have him : (ofComplex (⟨p.2, p.1⟩ : ℂ)).im = p.1 := by
    rw [ofComplex_apply_of_im_pos (by simpa using hy)]
    rfl
  rw [stripEquiv_symm_apply, hyperbolicDensity_toReal, him, hyperbolicChartIntegrand]

/-- **The invariant integral in the chart.**  `∫_ℍ F dμ = ∫_{(0,∞)×ℝ} y⁻² F(x + iy) d(y, x)`. -/
theorem integral_upperHalfPlane_eq_chart (F : ℍ → E) :
    ∫ z, F z = ∫ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), hyperbolicChartIntegrand F p := by
  rw [volume_eq_comap_withDensity, integral_withDensity_eq_integral_toReal_smul
    measurable_hyperbolicDensity (ae_of_all _ fun z => hyperbolicDensity_lt_top z)]
  have h2 := measurePreserving_coe.integral_comp measurableEmbedding_coe
    (fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w))
  simp only [ofComplex_apply] at h2
  rw [h2]
  have h3 := (measurePreserving_stripEquiv.symm).setIntegral_preimage_emb
    stripEquiv.symm.measurableEmbedding
    (fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w)) (range UpperHalfPlane.coe)
  rw [_root_.RHTower.stripEquiv_symm_preimage_range_coe] at h3
  rw [← h3]
  exact setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
    fun p hp => chartIntegrand_eq_on F hp

/-- Integrability on `ℍ` is integrability of the chart integrand. -/
theorem integrable_upperHalfPlane_iff_chart (F : ℍ → E) :
    Integrable F ↔ IntegrableOn (hyperbolicChartIntegrand F) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  rw [volume_eq_comap_withDensity, integrable_withDensity_iff_integrable_smul'
    measurable_hyperbolicDensity (ae_of_all _ fun z => hyperbolicDensity_lt_top z)]
  have h2 := measurePreserving_coe.integrable_comp_emb measurableEmbedding_coe
    (g := fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w))
  simp only [Function.comp_def, ofComplex_apply] at h2
  rw [h2]
  have h3 := (measurePreserving_stripEquiv.symm).integrableOn_comp_preimage
    stripEquiv.symm.measurableEmbedding
    (f := fun w => (hyperbolicDensity (ofComplex w)).toReal • F (ofComplex w))
    (s := range UpperHalfPlane.coe)
  rw [_root_.RHTower.stripEquiv_symm_preimage_range_coe] at h3
  change IntegrableOn _ (range UpperHalfPlane.coe) volume ↔ _
  rw [← h3]
  constructor
  · intro h
    exact h.congr_fun (fun p hp => chartIntegrand_eq_on F hp)
      (measurableSet_Ioi.prod MeasurableSet.univ)
  · intro h
    exact h.congr_fun (fun p hp => (chartIntegrand_eq_on F hp).symm)
      (measurableSet_Ioi.prod MeasurableSet.univ)

/-- **Fubini in the chart.**  `∫_ℍ F dμ = ∫_0^∞ y⁻² ∫_ℝ F(x + iy) dx dy`. -/
theorem integral_upperHalfPlane_eq_iterated (F : ℍ → E) (hF : Integrable F) :
    ∫ z, F z = ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • ∫ x : ℝ, F (ofComplex ⟨x, y⟩) := by
  have h := (integrable_upperHalfPlane_iff_chart F).mp hF
  rw [Measure.volume_eq_prod] at h
  rw [integral_upperHalfPlane_eq_chart, Measure.volume_eq_prod, setIntegral_prod _ h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  simp only [hyperbolicChartIntegrand, Measure.restrict_univ]
  rw [integral_smul]

end Chart

/-! ### The Abel transform -/

/-- The Abel transform `𝒜k(v) = ∫_ℝ k(η²/4 + sinh²(v/2)) dη`. -/
def abelTransform (k : ℝ → ℝ) (v : ℝ) : ℝ := ∫ η : ℝ, k (η ^ 2 / 4 + Real.sinh (v / 2) ^ 2)

theorem abelTransform_neg (k : ℝ → ℝ) (v : ℝ) : abelTransform k (-v) = abelTransform k v := by
  simp only [abelTransform, neg_div, Real.sinh_neg, neg_sq]

theorem exists_abs_le_of_kernelSupport {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k)
    (hkR : KernelSupport k R) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u, 0 ≤ u → |k u| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hkc.continuousOn (s := Icc 0 R))
  refine ⟨max M 0, le_max_right _ _, fun u hu => ?_⟩
  rcases le_or_gt u R with h | h
  · exact (hM u ⟨hu, h⟩).trans (le_max_left _ _)
  · rw [hkR u h, abs_zero]; exact le_max_right _ _

/-- The dominating function `M · 1_{|η| ≤ 2√R}` of the Abel integrand. -/
def abelBound (R M : ℝ) : ℝ → ℝ :=
  (Icc (-(2 * Real.sqrt (max R 0))) (2 * Real.sqrt (max R 0))).indicator fun _ => M

theorem integrable_abelBound (R M : ℝ) : Integrable (abelBound R M) :=
  (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp) (by simp))

section Abel

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
include hkc hkR

omit hkc in
theorem abelTransform_integrand_eq_zero {v η : ℝ} (hη : 4 * R < η ^ 2) :
    k (η ^ 2 / 4 + Real.sinh (v / 2) ^ 2) = 0 :=
  hkR _ (by nlinarith [sq_nonneg (Real.sinh (v / 2))])

omit hkc in
theorem abs_abelTransform_integrand_le {M : ℝ} (hM : ∀ u, 0 ≤ u → |k u| ≤ M) (v η : ℝ) :
    |k (η ^ 2 / 4 + Real.sinh (v / 2) ^ 2)| ≤ abelBound R M η := by
  unfold abelBound
  by_cases hη : η ∈ Icc (-(2 * Real.sqrt (max R 0))) (2 * Real.sqrt (max R 0))
  · rw [indicator_of_mem hη]; exact hM _ (by positivity)
  · rw [indicator_of_notMem hη, abelTransform_integrand_eq_zero hkR, abs_zero]
    rw [mem_Icc, not_and_or, not_le, not_le] at hη
    have hs : (2 * Real.sqrt (max R 0)) ^ 2 = 4 * max R 0 := by
      rw [mul_pow, Real.sq_sqrt (le_max_right _ _)]; ring
    have hs0 : 0 ≤ 2 * Real.sqrt (max R 0) := by positivity
    rcases hη with h | h
    · nlinarith [le_max_left R 0]
    · nlinarith [le_max_left R 0]

theorem integrable_abelTransform_integrand (v : ℝ) :
    Integrable fun η : ℝ => k (η ^ 2 / 4 + Real.sinh (v / 2) ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  refine (integrable_abelBound R M).mono'
    (by fun_prop : Continuous fun η : ℝ => k (η ^ 2 / 4 + Real.sinh (v / 2) ^ 2)).aestronglyMeasurable
    (Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs]
  exact abs_abelTransform_integrand_le hkR hM v η

theorem continuous_abelTransform : Continuous (abelTransform k) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_kernelSupport hkc hkR
  refine continuous_of_dominated (fun v => (by fun_prop : Continuous fun η : ℝ =>
      k (η ^ 2 / 4 + Real.sinh (v / 2) ^ 2)).aestronglyMeasurable)
    (fun v => Eventually.of_forall fun η => ?_)
    (integrable_abelBound R M) (Eventually.of_forall fun η => by fun_prop)
  rw [Real.norm_eq_abs]
  exact abs_abelTransform_integrand_le hkR hM v η

omit hkc in
/-- `𝒜k(v) = 0` once `sinh²(v/2) > R`. -/
theorem abelTransform_eq_zero {v : ℝ} (hv : R < Real.sinh (v / 2) ^ 2) : abelTransform k v = 0 := by
  rw [abelTransform]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun η => ?_)
  exact hkR _ (by nlinarith [sq_nonneg η])


omit hkc hkR in
/-- Beyond `V = 2 arsinh √R` the argument `sinh²(v/2)` exceeds `R`. -/
theorem lt_sinh_sq_of_lt_abs {v : ℝ} (hv : 2 * Real.arsinh (Real.sqrt (max R 0)) < |v|) :
    R < Real.sinh (v / 2) ^ 2 := by
  have h0 : 0 ≤ Real.sqrt (max R 0) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (max R 0) < Real.sinh (|v| / 2) := by
    rw [← Real.sinh_arsinh (Real.sqrt (max R 0)), Real.sinh_lt_sinh]; linarith
  have hsq : Real.sinh (|v| / 2) ^ 2 = Real.sinh (v / 2) ^ 2 := by
    rcases abs_cases v with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    rw [neg_div, Real.sinh_neg, neg_sq]
  have h2 : (Real.sqrt (max R 0)) ^ 2 = max R 0 := Real.sq_sqrt (le_max_right _ _)
  rw [← hsq]
  nlinarith [le_max_left R 0]

omit hkc in
theorem hasCompactSupport_abelTransform : HasCompactSupport (abelTransform k) := by
  set V := 2 * Real.arsinh (Real.sqrt (max R 0))
  refine HasCompactSupport.intro (isCompact_Icc (a := -V) (b := V)) fun v hv => ?_
  refine abelTransform_eq_zero hkR (lt_sinh_sq_of_lt_abs ?_)
  rw [mem_Icc, not_and_or, not_le, not_le] at hv
  rcases hv with h | h
  · rw [abs_of_neg (by nlinarith [Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg (max R 0))])]
    linarith
  · rw [abs_of_pos (by nlinarith [Real.arsinh_nonneg_iff.mpr (Real.sqrt_nonneg (max R 0))])]
    exact h

end Abel

/-! ### The horocyclic slice -/

theorem pairU_ofComplex_eq {x y x' y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    pairU (ofComplex ⟨x, y⟩) (ofComplex ⟨x', y'⟩) = ((x - x') ^ 2 + (y - y') ^ 2) / (4 * y * y') := by
  rw [ofComplex_apply_of_im_pos (by simpa using hy), ofComplex_apply_of_im_pos (by simpa using hy'),
    pairU]
  simp only [UpperHalfPlane.im, Complex.dist_eq, Complex.sq_norm,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- `(y − y')²/(4yy') = sinh²((log y − log y')/2)`. -/
theorem sq_sub_div_eq_sinh_sq {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') :
    (y - y') ^ 2 / (4 * y * y') = Real.sinh ((Real.log y - Real.log y') / 2) ^ 2 := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hs' : 0 < Real.sqrt y' := Real.sqrt_pos.mpr hy'
  have hlog : (Real.log y - Real.log y') / 2 = Real.log (Real.sqrt y) - Real.log (Real.sqrt y') := by
    rw [Real.log_sqrt hy.le, Real.log_sqrt hy'.le]; ring
  rw [hlog, Real.sinh_eq, Real.exp_sub, neg_sub, Real.exp_sub, Real.exp_log hs, Real.exp_log hs']
  have hy2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have hy2' : Real.sqrt y' ^ 2 = y' := Real.sq_sqrt hy'.le
  conv_lhs => rw [← hy2, ← hy2']
  field_simp
  ring

/-- **The horocyclic slice.**  `∫_ℝ k(u(x + iy, x' + iy')) dx = √(yy') 𝒜k(log y − log y')`. -/
theorem integral_pairU_slice (k : ℝ → ℝ) {y y' : ℝ} (hy : 0 < y) (hy' : 0 < y') (x' : ℝ) :
    ∫ x : ℝ, k (pairU (ofComplex ⟨x, y⟩) (ofComplex ⟨x', y'⟩)) =
      Real.sqrt (y * y') * abelTransform k (Real.log y - Real.log y') := by
  set c := Real.sqrt (y * y') with hc
  have hc0 : 0 < c := Real.sqrt_pos.mpr (mul_pos hy hy')
  have hc2 : c ^ 2 = y * y' := Real.sq_sqrt (mul_pos hy hy').le
  have hfun : (fun x : ℝ => k (pairU (ofComplex ⟨x, y⟩) (ofComplex ⟨x', y'⟩))) =
      fun x => k (((x - x') ^ 2 + (y - y') ^ 2) / (4 * y * y')) := by
    funext x; rw [pairU_ofComplex_eq hy hy']
  rw [hfun, ← integral_add_left_eq_self (μ := volume)
    (fun x => k (((x - x') ^ 2 + (y - y') ^ 2) / (4 * y * y'))) x']
  have h := Measure.integral_comp_mul_left
    (fun t : ℝ => k (((x' + t - x') ^ 2 + (y - y') ^ 2) / (4 * y * y'))) c
  rw [abs_inv, abs_of_pos hc0, smul_eq_mul] at h
  have h' : ∫ t : ℝ, k (((x' + t - x') ^ 2 + (y - y') ^ 2) / (4 * y * y')) =
      c * ∫ η : ℝ, k (((x' + c * η - x') ^ 2 + (y - y') ^ 2) / (4 * y * y')) := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  rw [h', abelTransform]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only
  congr 1
  rw [← sq_sub_div_eq_sinh_sq hy hy']
  have h4 : (4 * y * y') ≠ 0 := by positivity
  field_simp
  rw [show (x' + c * η - x') ^ 2 = c ^ 2 * η ^ 2 by ring, hc2]
  ring

/-! ### Mehler–Fock = Fourier ∘ Abel -/

/-- The exponential substitution `y = e^v` on `(0, ∞)`. -/
theorem integral_Ioi_eq_integral_realExp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) : ∫ y in Ioi (0 : ℝ), g y = ∫ v : ℝ, Real.exp v • g (Real.exp v) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun v _ => (Real.hasDerivAt_exp v).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [image_univ, Real.range_exp, setIntegral_univ] at h
  rw [h]
  exact integral_congr_ae (Eventually.of_forall fun v => by
    simp only [abs_of_pos (Real.exp_pos v)])

theorem ofReal_realExp_cpow (v : ℝ) (s : ℂ) : ((Real.exp v : ℝ) : ℂ) ^ s = cexp (s * v) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos v).ne'), ← Complex.ofReal_log
    (Real.exp_pos v).le, Real.log_exp, mul_comm]

theorem sqrt_realExp_eq_exp_half (v : ℝ) : Real.sqrt (Real.exp v) = Real.exp (v / 2) := by
  rw [show v = v / 2 + v / 2 by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  ring_nf

theorem continuous_powerEigen (s : ℂ) : Continuous (powerEigen s) :=
  HyperbolicPointPair.continuous_of_smooth (powerEigen_smooth s)

section MehlerFock

variable {k : ℝ → ℝ} {R : ℝ} (hkc : Continuous k) (hkR : KernelSupport k R)
include hkc hkR

/-- **Mehler–Fock = Fourier ∘ Abel.**  `h_k(s) = ∫_ℝ 𝒜k(v) e^{(s − ½)v} dv`. -/
theorem selbergTransform_eq_integral_abelTransform (s : ℂ) :
    selbergTransform k s = ∫ v : ℝ, (abelTransform k v : ℂ) * cexp ((s - 1 / 2) * v) := by
  have hint : Integrable fun w : ℍ => ((k (pairU UpperHalfPlane.I w) : ℝ) : ℂ) * powerEigen s w :=
    (integrable_pairKernel_smul' hkc hkR (continuous_powerEigen s) UpperHalfPlane.I).congr
      (Eventually.of_forall fun w => by simp [Complex.real_smul])
  rw [selbergTransform, integral_upperHalfPlane_eq_iterated _ hint]
  have hslice : ∀ y ∈ Ioi (0 : ℝ),
      (y ^ 2)⁻¹ • ∫ x : ℝ, ((k (pairU UpperHalfPlane.I (ofComplex ⟨x, y⟩)) : ℝ) : ℂ) *
        powerEigen s (ofComplex ⟨x, y⟩) =
      (y ^ 2)⁻¹ • (((Real.sqrt y * abelTransform k (Real.log y) : ℝ) : ℂ) * (y : ℂ) ^ s) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hpow : ∀ x : ℝ, powerEigen s (ofComplex ⟨x, y⟩) = (y : ℂ) ^ s := fun x => by
      rw [powerEigen, ofComplex_apply_of_im_pos (by simpa using hy0)]
      rfl
    have hI : UpperHalfPlane.I = ofComplex ⟨0, 1⟩ := by
      apply UpperHalfPlane.ext
      rw [ofComplex_apply_of_im_pos (by norm_num)]
      rfl
    simp only [hpow]
    rw [integral_mul_const, integral_complex_ofReal]
    congr 3
    have h := integral_pairU_slice k hy0 one_pos 0
    rw [Real.log_one, sub_zero, mul_one] at h
    rw [← h]
    congr 1 with x
    rw [hI, pairU_comm]
  rw [setIntegral_congr_fun measurableSet_Ioi hslice, integral_Ioi_eq_integral_realExp_smul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [Real.log_exp, sqrt_realExp_eq_exp_half, ofReal_realExp_cpow, Complex.real_smul, Complex.real_smul]
  push_cast
  have h1 : (cexp (v : ℂ) ^ 2)⁻¹ = cexp (-(2 * (v : ℂ))) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; push_cast; ring_nf
  rw [h1]
  calc cexp (v : ℂ) * (cexp (-(2 * (v : ℂ))) * (cexp ((v : ℂ) / 2) * (abelTransform k v : ℂ) *
        cexp (s * v)))
      = (abelTransform k v : ℂ) * (cexp (v : ℂ) * cexp (-(2 * (v : ℂ))) * cexp ((v : ℂ) / 2) *
          cexp (s * v)) := by ring
    _ = (abelTransform k v : ℂ) * cexp ((s - 1 / 2) * v) := by
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 2
        ring


/-- On the critical line the Selberg transform is the Fourier transform of the Abel transform. -/
theorem selbergTransform_critical (τ : ℝ) :
    selbergTransform k (1 / 2 + τ * Complex.I) = ∫ v : ℝ, (abelTransform k v : ℂ) * cexp (τ * v * Complex.I) := by
  rw [selbergTransform_eq_integral_abelTransform hkc hkR]
  congr 1 with v
  congr 2
  ring

theorem integrable_abelTransform_mul {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable fun v => abelTransform k v * f v :=
  ((continuous_abelTransform hkc hkR).mul hf).integrable_of_hasCompactSupport
    (hasCompactSupport_abelTransform hkR).mul_right

/-- **The critical line.**  `h_k(½ + iτ) = ∫ 𝒜k(v) cos(τv) dv` is real: `𝒜k` is even. -/
theorem selbergTransform_critical_eq_ofReal (τ : ℝ) :
    selbergTransform k (1 / 2 + τ * Complex.I) =
      ((∫ v : ℝ, abelTransform k v * Real.cos (τ * v) : ℝ) : ℂ) := by
  rw [selbergTransform_critical hkc hkR]
  have hodd : ∫ v : ℝ, abelTransform k v * Real.sin (τ * v) = 0 := by
    have h := integral_neg_eq_self (fun v => abelTransform k v * Real.sin (τ * v)) volume
    simp only [abelTransform_neg, mul_neg, Real.sin_neg, integral_neg] at h
    linarith
  have hfun : (fun v : ℝ => (abelTransform k v : ℂ) * cexp (τ * v * Complex.I)) =
      fun v => ((abelTransform k v * Real.cos (τ * v) : ℝ) : ℂ) +
        ((abelTransform k v * Real.sin (τ * v) : ℝ) : ℂ) * Complex.I := by
    funext v
    rw [show (τ : ℂ) * v * Complex.I = ((τ * v : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    push_cast
    ring
  have hc := integrable_abelTransform_mul hkc hkR (f := fun v => Real.cos (τ * v)) (by fun_prop)
  have hs := integrable_abelTransform_mul hkc hkR (f := fun v => Real.sin (τ * v)) (by fun_prop)
  have hc' : Integrable fun v : ℝ => ((abelTransform k v * Real.cos (τ * v) : ℝ) : ℂ) := hc.ofReal
  have hs' : Integrable fun v : ℝ =>
      ((abelTransform k v * Real.sin (τ * v) : ℝ) : ℂ) * Complex.I := hs.ofReal.mul_const _
  rw [hfun, integral_add hc' hs', integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal, hodd]
  simp

end MehlerFock

end GaloisForLFunctions.RHTower.MehlerFock
