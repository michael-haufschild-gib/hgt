import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The exponential-character domain of a positive measure

The set of real parameters at which a finite positive measure has a finite exponential moment is a
convex set containing zero, and it is an exact contravariant resource for the positive formation
operations: mixture and independent fusion intersect it, exponential tilt translates it, reflection
negates it, imaginary modulation leaves it untouched, and clock-preserving Markov recovery is
neutral.  One admitted vertical line of the two-sided Laplace transform still determines the
measure.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The moment response and its domain -/

/-- Extended exponential moment response of a positive measure on the line. -/
def momentResponse (μ : Measure ℝ) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂μ

/-- The exponential-character domain: the parameters with a finite moment response. -/
def characterDomain (μ : Measure ℝ) : Set ℝ := {s | momentResponse μ s ≠ ⊤}

theorem measurable_expKernel (s : ℝ) :
    Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (s * x)) :=
  ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_id).exp)

theorem momentResponse_pos {μ : Measure ℝ} (hμ : μ ≠ 0) (s : ℝ) : 0 < momentResponse μ s := by
  rw [pos_iff_ne_zero, Ne, momentResponse, lintegral_eq_zero_iff (measurable_expKernel s)]
  intro h
  have hfalse : ∀ᵐ x ∂μ, False := by
    filter_upwards [h] with x hx
    have hpos := Real.exp_pos (s * x)
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
    linarith
  have hall : μ {_x : ℝ | ¬ False} = 0 := ae_iff.1 hfalse
  simp only [not_false_eq_true, Set.setOf_true] at hall
  exact hμ (Measure.measure_univ_eq_zero.1 hall)

@[simp] theorem momentResponse_zero (μ : Measure ℝ) : momentResponse μ 0 = μ Set.univ := by
  simp [momentResponse]

theorem zero_mem_characterDomain (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (0 : ℝ) ∈ characterDomain μ := by
  simp [characterDomain, measure_ne_top]

/-- **Convexity of the exponential-character domain.**  Generalized Hölder in the exponent. -/
theorem convex_characterDomain (μ : Measure ℝ) : Convex ℝ (characterDomain μ) := by
  intro s hs t ht a b ha hb hab
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · have hb1 : b = 1 := by linarith [ha0.symm ▸ hab]
    simpa [← ha0, hb1] using ht
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · have ha1 : a = 1 := by linarith [hb0.symm ▸ hab]
    simpa [← hb0, ha1] using hs
  have halt : a < 1 := by linarith
  have hblt : b < 1 := by linarith
  have hconj : Real.HolderConjugate (1 / a) (1 / b) := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ ha0]; linarith
    · rw [one_div, inv_inv, one_div, inv_inv]
      linarith
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (a * s * x)) :=
    measurable_expKernel _
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (b * t * x)) :=
    measurable_expKernel _
  have hpow : ∀ (c u : ℝ), 0 < c →
      (fun x : ℝ => ENNReal.ofReal (Real.exp (c * u * x)) ^ (1 / c))
        = fun x : ℝ => ENNReal.ofReal (Real.exp (u * x)) := by
    intro c u hc
    funext x
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    field_simp
  have hbound := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hf.aemeasurable hg.aemeasurable
  rw [hpow a s ha0, hpow b t hb0] at hbound
  have hprod : (fun x : ℝ => ENNReal.ofReal (Real.exp (a * s * x)) *
      ENNReal.ofReal (Real.exp (b * t * x)))
      = fun x : ℝ => ENNReal.ofReal (Real.exp ((a • s + b • t) * x)) := by
    funext x
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    simp only [smul_eq_mul]
    ring
  have hleft : ∫⁻ x, (fun x : ℝ => ENNReal.ofReal (Real.exp (a * s * x))) x *
      (fun x : ℝ => ENNReal.ofReal (Real.exp (b * t * x))) x ∂μ
      = momentResponse μ (a • s + b • t) := by
    rw [momentResponse, ← hprod]
  simp only [Pi.mul_apply] at hbound
  rw [hleft] at hbound
  have hrs : ((∫⁻ x, ENNReal.ofReal (Real.exp (s * x)) ∂μ) ^ (1 / (1 / a))) ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by positivity) hs
  have hrt : ((∫⁻ x, ENNReal.ofReal (Real.exp (t * x)) ∂μ) ^ (1 / (1 / b))) ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ht
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hrs hrt) hbound

/-! ## The exact formation calculus -/

theorem ne_top_mul_iff {c x : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤) : c * x ≠ ⊤ ↔ x ≠ ⊤ := by
  constructor
  · intro h hx
    exact h (by rw [hx, ENNReal.mul_top hc])
  · intro h
    exact ENNReal.mul_ne_top hc' h

theorem mul_ne_top_iff_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  constructor
  · intro h
    refine ⟨fun hxt => h ?_, fun hyt => h ?_⟩
    · rw [hxt, ENNReal.top_mul hy]
    · rw [hyt, ENNReal.mul_top hx]
  · rintro ⟨h1, h2⟩
    exact ENNReal.mul_ne_top h1 h2

theorem momentResponse_mixture (c d : ℝ≥0∞) (μ ν : Measure ℝ) (s : ℝ) :
    momentResponse (c • μ + d • ν) s = c * momentResponse μ s + d * momentResponse ν s := by
  simp [momentResponse, lintegral_add_measure, lintegral_smul_measure]

/-- **Positive mixture intersects the character domain.** -/
theorem characterDomain_mixture {c d : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤) (hd : d ≠ 0)
    (hd' : d ≠ ⊤) (μ ν : Measure ℝ) :
    characterDomain (c • μ + d • ν) = characterDomain μ ∩ characterDomain ν := by
  ext s
  have hM : c * momentResponse μ s ≠ ⊤ ↔ momentResponse μ s ≠ ⊤ := ne_top_mul_iff hc hc'
  have hN : d * momentResponse ν s ≠ ⊤ ↔ momentResponse ν s ≠ ⊤ := ne_top_mul_iff hd hd'
  simp only [characterDomain, Set.mem_setOf_eq, Set.mem_inter_iff, momentResponse_mixture,
    ne_eq, ENNReal.add_eq_top, not_or]
  exact and_congr hM hN

theorem momentResponse_conv (μ ν : Measure ℝ) [SFinite ν] (s : ℝ) :
    momentResponse (μ ∗ ν) s = momentResponse μ s * momentResponse ν s := by
  rw [momentResponse, Measure.lintegral_conv (measurable_expKernel s)]
  have hinner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (s * (x + y))) ∂ν
      = ENNReal.ofReal (Real.exp (s * x)) * momentResponse ν s := by
    intro x
    rw [momentResponse, ← lintegral_const_mul _ (measurable_expKernel s)]
    refine lintegral_congr fun y => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    ring
  rw [lintegral_congr hinner, lintegral_mul_const _ (measurable_expKernel s)]
  simp only [momentResponse]

/-- **Independent fusion intersects the character domain.** -/
theorem characterDomain_conv {μ ν : Measure ℝ} [SFinite ν] (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    characterDomain (μ ∗ ν) = characterDomain μ ∩ characterDomain ν := by
  ext s
  have h := mul_ne_top_iff_of_ne_zero (momentResponse_pos hμ s).ne' (momentResponse_pos hν s).ne'
  simp only [characterDomain, Set.mem_setOf_eq, Set.mem_inter_iff, momentResponse_conv, ne_eq]
  exact h

/-- Normalized exponential intervention. -/
def exponentialTilt (μ : Measure ℝ) (a : ℝ) : Measure ℝ :=
  (momentResponse μ a)⁻¹ • μ.withDensity fun x => ENNReal.ofReal (Real.exp (a * x))

theorem momentResponse_exponentialTilt (μ : Measure ℝ) (a s : ℝ) :
    momentResponse (exponentialTilt μ a) s
      = (momentResponse μ a)⁻¹ * momentResponse μ (s + a) := by
  rw [exponentialTilt, momentResponse, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_expKernel a) (measurable_expKernel s)]
  congr 1
  rw [momentResponse]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

/-- **Exponential intervention translates the character domain.** -/
theorem characterDomain_exponentialTilt {μ : Measure ℝ} {a : ℝ} (hμ : μ ≠ 0)
    (ha : a ∈ characterDomain μ) :
    characterDomain (exponentialTilt μ a) = {s : ℝ | s + a ∈ characterDomain μ} := by
  have hane : momentResponse μ a ≠ 0 := (momentResponse_pos hμ a).ne'
  have hatop : momentResponse μ a ≠ ⊤ := ha
  have hinv0 : (momentResponse μ a)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hatop
  have hinvtop : (momentResponse μ a)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hane
  ext s
  have h : (momentResponse μ a)⁻¹ * momentResponse μ (s + a) ≠ ⊤
      ↔ momentResponse μ (s + a) ≠ ⊤ := ne_top_mul_iff hinv0 hinvtop
  simp only [characterDomain, Set.mem_setOf_eq, momentResponse_exponentialTilt, ne_eq]
  exact h

theorem characterDomain_exponentialTilt_image {μ : Measure ℝ} {a : ℝ} (hμ : μ ≠ 0)
    (ha : a ∈ characterDomain μ) :
    characterDomain (exponentialTilt μ a) = (fun u : ℝ => u - a) '' characterDomain μ := by
  rw [characterDomain_exponentialTilt hμ ha]
  ext s
  constructor
  · intro hs
    exact ⟨s + a, hs, by ring⟩
  · rintro ⟨u, hu, rfl⟩
    simpa using hu

/-- Reflection of a measure on the line. -/
def reflectMeasure (μ : Measure ℝ) : Measure ℝ := μ.map fun x => -x

theorem momentResponse_reflectMeasure (μ : Measure ℝ) (s : ℝ) :
    momentResponse (reflectMeasure μ) s = momentResponse μ (-s) := by
  rw [momentResponse, reflectMeasure,
    lintegral_map (measurable_expKernel s) measurable_neg, momentResponse]
  refine lintegral_congr fun x => ?_
  congr 2
  ring

/-- **Reflection negates the character domain.** -/
theorem characterDomain_reflectMeasure (μ : Measure ℝ) :
    characterDomain (reflectMeasure μ) = -characterDomain μ := by
  ext s
  simp [characterDomain, momentResponse_reflectMeasure]

theorem reflectMeasure_reflectMeasure (μ : Measure ℝ) :
    reflectMeasure (reflectMeasure μ) = μ := by
  rw [reflectMeasure, reflectMeasure, Measure.map_map measurable_neg measurable_neg]
  simp

theorem reflectMeasure_ne_zero {μ : Measure ℝ} (hμ : μ ≠ 0) : reflectMeasure μ ≠ 0 := by
  intro h
  refine hμ ?_
  rw [← reflectMeasure_reflectMeasure μ, h, reflectMeasure, Measure.map_zero]

instance instSFiniteReflectMeasure (μ : Measure ℝ) [SFinite μ] : SFinite (reflectMeasure μ) := by
  rw [reflectMeasure]
  infer_instance

/-- **Imaginary modulation does not change absolute exponential integrability.** -/
theorem lintegral_norm_complexCharacter (μ : Measure ℝ) (s t : ℝ) :
    ∫⁻ x, ENNReal.ofReal ‖Complex.exp ((s + t * Complex.I) * (x : ℂ))‖ ∂μ
      = momentResponse μ s := by
  rw [momentResponse]
  refine lintegral_congr fun x => ?_
  rw [Complex.norm_exp]
  congr 2
  simp [Complex.add_re, Complex.mul_re]

/-- **Functional-equation symmetrization retains the reflection-stable core.** -/
theorem characterDomain_conv_reflect {μ : Measure ℝ} [SFinite μ] (hμ : μ ≠ 0) :
    characterDomain (μ ∗ reflectMeasure μ)
      = characterDomain μ ∩ (-characterDomain μ) := by
  rw [characterDomain_conv hμ (reflectMeasure_ne_zero hμ), characterDomain_reflectMeasure]

/-! ## Clock-preserving recovery -/

/-- Moment response of a measure read through a real clock. -/
def clockedMomentResponse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (r : Ω → ℝ) (s : ℝ) :
    ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (s * r ω)) ∂μ

/-- Character domain of a clocked measure. -/
def clockedCharacterDomain {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (r : Ω → ℝ) : Set ℝ :=
  {s | clockedMomentResponse μ r s ≠ ⊤}

theorem clockedMomentResponse_id (μ : Measure ℝ) (s : ℝ) :
    clockedMomentResponse μ id s = momentResponse μ s := rfl

/-- **Clock-preserving Markov recovery is admission-neutral.** -/
theorem clockedMomentResponse_compProd {Y : Type*} [MeasurableSpace Y]
    (μ : Measure ℝ) [SFinite μ] (K : Kernel ℝ Y) [IsMarkovKernel K] (s : ℝ) :
    clockedMomentResponse (μ ⊗ₘ K) Prod.fst s = momentResponse μ s := by
  have hmeas : Measurable fun ω : ℝ × Y => ENNReal.ofReal (Real.exp (s * ω.1)) :=
    (measurable_expKernel s).comp measurable_fst
  rw [clockedMomentResponse, Measure.lintegral_compProd hmeas, momentResponse]
  refine lintegral_congr fun x => ?_
  simp

/-- **Recovery neutrality of the character domain.** -/
theorem clockedCharacterDomain_compProd {Y : Type*} [MeasurableSpace Y]
    (μ : Measure ℝ) [SFinite μ] (K : Kernel ℝ Y) [IsMarkovKernel K] :
    clockedCharacterDomain (μ ⊗ₘ K) Prod.fst = characterDomain μ := by
  ext s
  simp [clockedCharacterDomain, characterDomain, clockedMomentResponse_compProd]

/-! ## Admitted-line reconstruction -/

/-- Unnormalized exponential tilt. -/
def tiltedMeasure (μ : Measure ℝ) (a : ℝ) : Measure ℝ :=
  μ.withDensity fun x => ENNReal.ofReal (Real.exp (a * x))

theorem tiltedMeasure_univ (μ : Measure ℝ) (a : ℝ) :
    tiltedMeasure μ a Set.univ = momentResponse μ a := by
  rw [tiltedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    momentResponse]

theorem isFiniteMeasure_tiltedMeasure {μ : Measure ℝ} {a : ℝ} (ha : a ∈ characterDomain μ) :
    IsFiniteMeasure (tiltedMeasure μ a) := by
  refine ⟨?_⟩
  rw [tiltedMeasure_univ]
  exact lt_top_iff_ne_top.2 ha

/-- The complete response on the admitted vertical line. -/
def lineResponse (μ : Measure ℝ) (a t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) ∂μ

theorem charFun_tiltedMeasure (μ : Measure ℝ) (a t : ℝ) :
    charFun (tiltedMeasure μ a) t = lineResponse μ a t := by
  rw [charFun, tiltedMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_expKernel a)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top), lineResponse]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (ENNReal.ofReal (Real.exp (a * x))).toReal •
      Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I)
    = Complex.exp (((a : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ))
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), Real.inner_apply, Complex.real_smul,
    Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Untilting recovers the source measure. -/
theorem withDensity_tiltedMeasure (μ : Measure ℝ) (a : ℝ) :
    (tiltedMeasure μ a).withDensity (fun x => ENNReal.ofReal (Real.exp (-(a * x)))) = μ := by
  have hprod : ((fun x : ℝ => ENNReal.ofReal (Real.exp (a * x))) *
      fun x : ℝ => ENNReal.ofReal (Real.exp (-(a * x)))) = 1 := by
    funext x
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-(a * x))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul measurable_id).neg.exp)
  rw [tiltedMeasure, ← withDensity_mul _ (measurable_expKernel a) hg, hprod, withDensity_one]

/-- **Admitted-line reconstruction.**  One admitted vertical line of the two-sided Laplace
transform determines a finite positive measure. -/
theorem measure_eq_of_lineResponse_eq {μ ν : Measure ℝ} {a : ℝ}
    (haμ : a ∈ characterDomain μ) (haν : a ∈ characterDomain ν)
    (h : ∀ t : ℝ, lineResponse μ a t = lineResponse ν a t) : μ = ν := by
  haveI := isFiniteMeasure_tiltedMeasure haμ
  haveI := isFiniteMeasure_tiltedMeasure haν
  have hchar : charFun (tiltedMeasure μ a) = charFun (tiltedMeasure ν a) := by
    funext t
    rw [charFun_tiltedMeasure, charFun_tiltedMeasure, h t]
  have htilt : tiltedMeasure μ a = tiltedMeasure ν a := Measure.ext_of_charFun hchar
  rw [← withDensity_tiltedMeasure μ a, ← withDensity_tiltedMeasure ν a, htilt]

theorem exponentialTilt_eq_smul_tiltedMeasure (μ : Measure ℝ) (a : ℝ) :
    exponentialTilt μ a = (momentResponse μ a)⁻¹ • tiltedMeasure μ a := rfl

theorem exponentialTilt_univ {μ : Measure ℝ} {a : ℝ} (hμ : μ ≠ 0)
    (ha : a ∈ characterDomain μ) : exponentialTilt μ a Set.univ = 1 := by
  rw [exponentialTilt_eq_smul_tiltedMeasure, Measure.smul_apply, tiltedMeasure_univ,
    smul_eq_mul, ENNReal.inv_mul_cancel (momentResponse_pos hμ a).ne' ha]

theorem isProbabilityMeasure_exponentialTilt {μ : Measure ℝ} {a : ℝ} (hμ : μ ≠ 0)
    (ha : a ∈ characterDomain μ) : IsProbabilityMeasure (exponentialTilt μ a) :=
  ⟨exponentialTilt_univ hμ ha⟩

theorem conv_univ (μ ν : Measure ℝ) [SFinite ν] :
    (μ ∗ ν) Set.univ = μ Set.univ * ν Set.univ := by
  have := momentResponse_conv μ ν 0
  simpa using this

/-! ## Cofinal admission properness -/

/-- Symmetric inradius of a character domain. -/
def symmetricInradius (D : Set ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (_ : Set.Icc (-(r : ℝ)) (r : ℝ) ⊆ D), (r : ℝ≥0∞)

theorem le_symmetricInradius {D : Set ℝ} {r : ℝ≥0} (hr : Set.Icc (-(r : ℝ)) (r : ℝ) ⊆ D) :
    (r : ℝ≥0∞) ≤ symmetricInradius D :=
  le_iSup_of_le r (le_iSup_of_le hr le_rfl)

/-- Relative admission work of a transverse parameter against a cofinal family of inradii. -/
def relativeAdmissionWork (r : ℕ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ n, ENNReal.ofReal (|t| / r n)

@[simp] theorem relativeAdmissionWork_zero (r : ℕ → ℝ) : relativeAdmissionWork r 0 = 0 := by
  simp [relativeAdmissionWork]

/-- **Cofinal character properness.**  A collapsing family of symmetric inradii gives infinite
relative admission work at every nonneutral parameter. -/
theorem relativeAdmissionWork_eq_top {r : ℕ → ℝ} (hpos : ∀ n, 0 < r n)
    (hlim : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : t ≠ 0) : relativeAdmissionWork r t = ⊤ := by
  have habs : 0 < |t| := abs_pos.2 ht
  rw [relativeAdmissionWork, iSup_eq_top]
  intro b hb
  have hbtop : b ≠ ⊤ := hb.ne
  set c : ℝ := b.toReal + 1 with hc
  have hcpos : 0 < c := by
    have : 0 ≤ b.toReal := ENNReal.toReal_nonneg
    linarith
  have hthresh : 0 < |t| / c := div_pos habs hcpos
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hthresh)).exists
  have hrn : 0 < r n := hpos n
  have hmul : r n * c < |t| := by
    have := (lt_div_iff₀ hcpos).1 hn
    linarith
  have hlt : c < |t| / r n := (lt_div_iff₀ hrn).2 (by linarith [hmul])
  refine ⟨n, lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2 hlt)⟩
  rw [ENNReal.le_ofReal_iff_toReal_le hbtop hcpos.le]
  linarith

theorem relativeAdmissionWork_ne_top_iff {r : ℕ → ℝ} (hpos : ∀ n, 0 < r n)
    (hlim : Tendsto r atTop (𝓝 0)) (t : ℝ) :
    relativeAdmissionWork r t ≠ ⊤ ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact h (relativeAdmissionWork_eq_top hpos hlim ht)
  · rintro rfl
    simp

/-- **Exact selection interface.**  Every finite-work sublevel is the neutral singleton. -/
theorem relativeAdmissionWork_sublevel {r : ℕ → ℝ} (hpos : ∀ n, 0 < r n)
    (hlim : Tendsto r atTop (𝓝 0)) (C : ℝ≥0) :
    {t : ℝ | relativeAdmissionWork r t ≤ (C : ℝ≥0∞)} = {0} := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    refine (relativeAdmissionWork_ne_top_iff hpos hlim t).1 ?_
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top h
  · rintro rfl
    simp

end

end GaloisForLFunctions.HTGeometry
