import GaloisForLFunctions.RHTower.CCMMetaplecticGammaMomentDeterminacy
import GaloisForLFunctions.RHTower.SemilocalJacobiMeixnerPollaczekGeneratingFunction

/-!
# The archimedean characteristic function at complex rapidity

The corpus knows `∫ e^{its} dμ = (cosh t)^{-1/2}` for the normalized Gamma measure
`dμ ∝ |Γ(1/4 + is/2)|² ds` and real `t`.  Since the density is bounded by `C e^{-π|s|/2}`, the
complex moment generating function `z ↦ ∫ e^{zs} dμ` is analytic on the strip `|Re z| < π/2`, and the
identity theorem extends the closed form to

`∫ e^{zs} dμ(s) = (cos z)^{-1/2}`,   `|Re z| < π/2`   (principal branch; `Re cos z > 0` there).

Together with the Meixner–Pollaczek generating function this gives the **two-variable boost
generating function**: for real `w, z` with `|w|, |z| < 1`,

`∫ G_s(w) G_s(z) e^{its} dμ(s) = (cosh t)^{-1/2} (1 − wz − i (w + z) tanh t)^{-1/2}`,

where `G_s(w) = Σ_n c_n p_n(s) w^n`.  This is the brick of MUST-148 after the generating function.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace RHTower

namespace ComplexRapidity

open MeixnerPollaczek

/-! ## The strip and the tilt integrability -/

/-- The open strip `|Re z| < π/2`. -/
def rapidityStrip : Set ℂ := {z : ℂ | -(Real.pi / 2) < z.re ∧ z.re < Real.pi / 2}

theorem isOpen_rapidityStrip : IsOpen rapidityStrip :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)

theorem convex_rapidityStrip : Convex ℝ rapidityStrip := by
  have h : rapidityStrip = Complex.reLm ⁻¹' Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    ext z
    simp [rapidityStrip, Ioo]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage _

theorem isPreconnected_rapidityStrip : IsPreconnected rapidityStrip :=
  convex_rapidityStrip.isPreconnected

theorem zero_mem_rapidityStrip : (0 : ℂ) ∈ rapidityStrip := by
  refine ⟨?_, ?_⟩ <;> simp [Real.pi_pos]

theorem mem_rapidityStrip_iff {z : ℂ} : z ∈ rapidityStrip ↔ |z.re| < Real.pi / 2 := by
  rw [abs_lt]; rfl

/-- Real tilts of rate `|a| < π/2` are integrable against the Gamma measure. -/
theorem integrable_exp_mul_semilocalArchimedeanGammaMeasure {a : ℝ} (ha : |a| < Real.pi / 2) :
    Integrable (fun s : ℝ => Real.exp (a * s)) semilocalArchimedeanGammaMeasure := by
  rw [semilocalArchimedeanGammaMeasure,
    integrable_withDensity_iff_integrable_smul
      continuous_semilocalArchimedeanGammaDensityNNReal.measurable]
  have hd : 0 < Real.pi / 2 - |a| := by linarith
  have hmaj := (integrable_exp_neg_mul_abs_metaplectic hd).const_mul
    ccmMetaplecticGammaExponentialMajorantConstant
  refine hmaj.mono' ?_ ?_
  · exact ((NNReal.continuous_coe.comp continuous_semilocalArchimedeanGammaDensityNNReal).smul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · filter_upwards with s
    have hdens := semilocalArchimedeanGammaDensity_le_exponentialMajorant s
    have hnn := semilocalArchimedeanGammaDensity_nonneg s
    have hexp : Real.exp (a * s) ≤ Real.exp (|a| * |s|) := by
      rw [Real.exp_le_exp, ← abs_mul]; exact le_abs_self _
    have hC := ccmMetaplecticGammaExponentialMajorantConstant_nonneg
    change ‖(semilocalArchimedeanGammaDensity s) • Real.exp (a * s)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
      abs_of_pos (Real.exp_pos _)]
    calc semilocalArchimedeanGammaDensity s * Real.exp (a * s)
        ≤ (ccmMetaplecticGammaExponentialMajorantConstant * Real.exp (-((Real.pi / 2) * |s|))) *
            Real.exp (|a| * |s|) :=
          mul_le_mul hdens hexp (Real.exp_pos _).le (by positivity)
      _ = ccmMetaplecticGammaExponentialMajorantConstant *
            Real.exp (-(Real.pi / 2 - |a|) * |s|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem Ioo_subset_integrableExpSet :
    Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ integrableExpSet id semilocalArchimedeanGammaMeasure := by
  intro a ha
  simp only [integrableExpSet, mem_setOf_eq, id]
  exact integrable_exp_mul_semilocalArchimedeanGammaMeasure (abs_lt.mpr ha)

theorem rapidityStrip_subset_interior :
    rapidityStrip ⊆ {z : ℂ | z.re ∈ interior (integrableExpSet id semilocalArchimedeanGammaMeasure)} := by
  intro z hz
  apply interior_mono Ioo_subset_integrableExpSet
  rw [isOpen_Ioo.interior_eq]
  exact ⟨hz.1, hz.2⟩

theorem analyticOnNhd_complexMGF_rapidityStrip :
    AnalyticOnNhd ℂ (complexMGF id semilocalArchimedeanGammaMeasure) rapidityStrip :=
  analyticOnNhd_complexMGF.mono rapidityStrip_subset_interior

/-! ## The target `(cos z)^{-1/2}` -/

/-- The complex-rapidity characteristic `(cos z)^{-1/2}`. -/
noncomputable def rapidityCharacteristic (z : ℂ) : ℂ := Complex.cos z ^ (-(1 / 2 : ℂ))

theorem cos_eq_re_im (z : ℂ) :
    Complex.cos z = ((Real.cos z.re * Real.cosh z.im : ℝ) : ℂ) -
      ((Real.sin z.re * Real.sinh z.im : ℝ) : ℂ) * I := by
  conv_lhs => rw [← re_add_im z]
  rw [cos_add, cos_mul_I, sin_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cosh, ← ofReal_sinh]
  push_cast
  ring

theorem re_cos_pos {z : ℂ} (hz : z ∈ rapidityStrip) : 0 < (Complex.cos z).re := by
  rw [cos_eq_re_im]
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero]
  exact mul_pos (Real.cos_pos_of_mem_Ioo ⟨hz.1, hz.2⟩) (Real.cosh_pos _)

theorem cos_mem_slitPlane {z : ℂ} (hz : z ∈ rapidityStrip) : Complex.cos z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (re_cos_pos hz))

theorem differentiableOn_rapidityCharacteristic :
    DifferentiableOn ℂ rapidityCharacteristic rapidityStrip := by
  intro z hz
  exact ((Complex.hasDerivAt_cos z).cpow_const (cos_mem_slitPlane hz)).differentiableAt
    |>.differentiableWithinAt

theorem analyticOnNhd_rapidityCharacteristic :
    AnalyticOnNhd ℂ rapidityCharacteristic rapidityStrip :=
  differentiableOn_rapidityCharacteristic.analyticOnNhd isOpen_rapidityStrip

/-! ## Agreement on the imaginary axis -/

theorem complexMGF_ofReal_mul_I (t : ℝ) :
    complexMGF id semilocalArchimedeanGammaMeasure ((t : ℂ) * I) =
      rapidityCharacteristic ((t : ℂ) * I) := by
  have h := integral_cexp_semilocalArchimedeanGammaMeasure t
  unfold complexMGF rapidityCharacteristic
  rw [cos_mul_I, ← ofReal_cosh]
  have hfun : (fun s : ℝ => cexp (((t : ℂ) * I) * ((id s : ℝ) : ℂ))) =
      fun s : ℝ => cexp (((t * s : ℝ) : ℂ) * I) := by
    funext s; simp only [id]; push_cast; ring_nf
  rw [hfun, h]
  unfold semilocalArchimedeanCharacteristic
  rw [ofReal_cpow (Real.cosh_pos t).le]
  push_cast
  norm_num

theorem frequently_eq_at_zero :
    ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      complexMGF id semilocalArchimedeanGammaMeasure z = rapidityCharacteristic z := by
  rw [Filter.frequently_iff]
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hU
  refine ⟨((ε / 2 : ℝ) : ℂ) * I, hsub ⟨?_, ?_⟩, complexMGF_ofReal_mul_I (ε / 2)⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · simp [hε.ne']

/-! ## The complex-rapidity characteristic function -/

/-- **Characteristic function of the Gamma measure at complex rapidity.**  For `|Re z| < π/2`,
`∫ e^{zs} dμ(s) = (cos z)^{-1/2}`. -/
theorem complexMGF_eq_rapidityCharacteristic {z : ℂ} (hz : z ∈ rapidityStrip) :
    complexMGF id semilocalArchimedeanGammaMeasure z = rapidityCharacteristic z :=
  analyticOnNhd_complexMGF_rapidityStrip.eqOn_of_preconnected_of_frequently_eq
    analyticOnNhd_rapidityCharacteristic isPreconnected_rapidityStrip zero_mem_rapidityStrip
    frequently_eq_at_zero hz

theorem integral_cexp_mul_semilocalArchimedeanGammaMeasure_of_mem_strip {z : ℂ}
    (hz : z ∈ rapidityStrip) :
    (∫ s : ℝ, cexp (z * s) ∂semilocalArchimedeanGammaMeasure) =
      Complex.cos z ^ (-(1 / 2 : ℂ)) := by
  have h := complexMGF_eq_rapidityCharacteristic hz
  unfold complexMGF rapidityCharacteristic at h
  simpa only [id] using h

/-- The tilted characteristic function: for real `|α| < π/2` and real `t`,
`∫ e^{αs} e^{its} dμ = (cos (α + it))^{-1/2}`. -/
theorem integral_exp_mul_cexp_semilocalArchimedeanGammaMeasure {α : ℝ} (hα : |α| < Real.pi / 2)
    (t : ℝ) :
    (∫ s : ℝ, ((Real.exp (α * s) : ℝ) : ℂ) * cexp (((t * s : ℝ) : ℂ) * I)
        ∂semilocalArchimedeanGammaMeasure) =
      Complex.cos ((α : ℂ) + (t : ℂ) * I) ^ (-(1 / 2 : ℂ)) := by
  have hz : (α : ℂ) + (t : ℂ) * I ∈ rapidityStrip := by
    rw [mem_rapidityStrip_iff]; simpa using hα
  rw [← integral_cexp_mul_semilocalArchimedeanGammaMeasure_of_mem_strip hz]
  congr 1
  funext s
  rw [ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The two-variable boost generating function -/

theorem abs_arctan_lt_pi_div_four {w : ℝ} (hw : |w| < 1) : |Real.arctan w| < Real.pi / 4 := by
  rw [abs_lt] at hw ⊢
  constructor
  · have := Real.arctan_strictMono hw.1
    rw [Real.arctan_neg, Real.arctan_one] at this
    linarith
  · have := Real.arctan_strictMono hw.2
    rw [Real.arctan_one] at this
    linarith

theorem abs_arctan_add_arctan_lt {w z : ℝ} (hw : |w| < 1) (hz : |z| < 1) :
    |Real.arctan w + Real.arctan z| < Real.pi / 2 := by
  have h1 := abs_arctan_lt_pi_div_four hw
  have h2 := abs_arctan_lt_pi_div_four hz
  calc |Real.arctan w + Real.arctan z| ≤ |Real.arctan w| + |Real.arctan z| := abs_add_le _ _
    _ < Real.pi / 4 + Real.pi / 4 := add_lt_add h1 h2
    _ = Real.pi / 2 := by ring

theorem cexp_boost_split (w z t s : ℝ) :
    cexp ((((Real.arctan w : ℝ) : ℂ) + ((Real.arctan z : ℝ) : ℂ) + (t : ℂ) * I) * (s : ℂ)) =
      cexp ((s : ℂ) * ((Real.arctan w : ℝ) : ℂ)) * cexp ((s : ℂ) * ((Real.arctan z : ℝ) : ℂ)) *
        cexp ((t : ℂ) * (s : ℂ) * I) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrable_mpGeneratingFunction_mul_cexp {w z : ℝ} (hw : |w| < 1) (hz : |z| < 1) (t : ℝ) :
    Integrable (fun s : ℝ => mpGeneratingFunction s w * mpGeneratingFunction s z *
      cexp (((t * s : ℝ) : ℂ) * I)) semilocalArchimedeanGammaMeasure := by
  have hα := abs_arctan_add_arctan_lt hw hz
  have hzs : ((Real.arctan w : ℝ) : ℂ) + ((Real.arctan z : ℝ) : ℂ) + (t : ℂ) * I ∈ rapidityStrip := by
    rw [mem_rapidityStrip_iff]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero]
    exact hα
  have hint := integrable_cexp_mul_of_re_mem_interior_integrableExpSet
    (rapidityStrip_subset_interior hzs)
  have hfun : (fun s : ℝ => mpGeneratingFunction s w * mpGeneratingFunction s z *
      cexp (((t * s : ℝ) : ℂ) * I)) =
      fun s : ℝ => (((1 + w ^ 2) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) * (((1 + z ^ 2) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        cexp ((((Real.arctan w : ℝ) : ℂ) + ((Real.arctan z : ℝ) : ℂ) + (t : ℂ) * I) * ((id s : ℝ) : ℂ)) := by
    funext s
    rw [mpGeneratingFunction_ofReal, mpGeneratingFunction_ofReal]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, id]
    rw [cexp_boost_split]
    ring
  rw [hfun]
  exact hint.const_mul _

/-- **Two-variable boost generating function (cosine form).**  For real `|w|, |z| < 1`,
`∫ G_s(w) G_s(z) e^{its} dμ = (1+w²)^{-1/4}(1+z²)^{-1/4} (cos(arctan w + arctan z + it))^{-1/2}`. -/
theorem integral_mpGeneratingFunction_mul_cexp {w z : ℝ} (hw : |w| < 1) (hz : |z| < 1) (t : ℝ) :
    (∫ s : ℝ, mpGeneratingFunction s w * mpGeneratingFunction s z *
        cexp (((t * s : ℝ) : ℂ) * I) ∂semilocalArchimedeanGammaMeasure) =
      (((1 + w ^ 2) ^ (-(1 / 4 : ℝ)) * (1 + z ^ 2) ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
        Complex.cos (((Real.arctan w + Real.arctan z : ℝ) : ℂ) + (t : ℂ) * I) ^ (-(1 / 2 : ℂ)) := by
  have hα := abs_arctan_add_arctan_lt hw hz
  rw [← integral_exp_mul_cexp_semilocalArchimedeanGammaMeasure hα t, ← integral_const_mul]
  congr 1
  funext s
  rw [mpGeneratingFunction_ofReal, mpGeneratingFunction_ofReal]
  have hsplit : cexp (((Real.arctan w + Real.arctan z : ℝ) : ℂ) * (s : ℂ)) =
      cexp ((s : ℂ) * ((Real.arctan w : ℝ) : ℂ)) * cexp ((s : ℂ) * ((Real.arctan z : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  rw [hsplit]
  ring

end ComplexRapidity

end RHTower
