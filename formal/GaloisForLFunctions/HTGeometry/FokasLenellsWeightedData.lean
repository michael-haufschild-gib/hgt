import GaloisForLFunctions.HTGeometry.FokasLenellsSecondDecay
import GaloisForLFunctions.HTGeometry.FokasLenellsSquareIntegrableData
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrable and spectrally weighted actual reflection data

The second spectral-power bound supplies L¹ reflection coefficients and
L² coefficients after multiplication by frequency. The actual time and
position phases preserve these weighted norms. This closes the missing
forcing-space requirement for spatial differentiation of the constructed
RH problem and supplies integrable reconstruction data.
-/

open Complex Matrix Set MeasureTheory Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

def regularSecondReflectionDecay (q : SchwartzMap ℝ ℂ) (upper : Bool) : ℝ :=
  (4/3 : ℝ)*uniformizedSecondDecay (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) upper

theorem regularSecondReflectionDecay_nonneg (q : SchwartzMap ℝ ℂ) (upper : Bool) :
    0 ≤ regularSecondReflectionDecay q upper :=
  mul_nonneg (by positivity) (uniformizedSecondDecay_nonneg _ _ _ _)

/-- Uniform nonvanishing of the actual transmissions preserves the second spectral power in both quotients. -/
theorem globalSmall_regularReflection_second_frequency_bound (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    |z|^(2 : ℕ)*‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ regularSecondReflectionDecay q false ∧
    |z|^(2 : ℕ)*‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ regularSecondReflectionDecay q true := by
  have hl := globalSmall_regularTransmission_lower q z
  have hb (upper : Bool) := uniformizedOffDiagonal_second_frequency_bound
    (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) z upper
  have hn (upper : Bool) := uniformizedSecondDecay_nonneg
    (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))
    (reflectedDerivative (globalSmallScatteringPotential q))
    (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (globalSmallScatteringPotential q))) upper
  constructor
  · rw [regularReflectionCoefficient,norm_div,← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [hl.1])).mpr
    have hbf := hb false
    change |z|^(2 : ℕ)*‖regularScatteringMatrix (globalSmallScatteringPotential q) z 1 0‖ ≤ _ at hbf
    unfold regularSecondReflectionDecay
    nlinarith [mul_nonneg (hn false) (by linarith : 0 ≤ ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 0 0‖-3/4)]
  · rw [regularReverseReflectionCoefficient,norm_div,← mul_div_assoc]
    apply (div_le_iff₀ (by linarith [hl.2])).mpr
    have hbt := hb true
    change |z|^(2 : ℕ)*‖regularScatteringMatrix (globalSmallScatteringPotential q) z 0 1‖ ≤ _ at hbt
    unfold regularSecondReflectionDecay
    nlinarith [mul_nonneg (hn true) (by linarith : 0 ≤ ‖regularScatteringMatrix (globalSmallScatteringPotential q) z 1 1‖-3/4)]

/-- The actual reflection coefficients admit nonsingular, integrable quadratic envelopes. -/
theorem globalSmall_regularReflection_quadratic_bound (q : SchwartzMap ℝ ℂ) (z : ℝ) :
    ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ (1/3+regularSecondReflectionDecay q false)/(1+z^(2 : ℕ)) ∧
    ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ (1/3+regularSecondReflectionDecay q true)/(1+z^(2 : ℕ)) := by
  have h0 := globalSmall_regularReflection_bounds q z
  have h2 := globalSmall_regularReflection_second_frequency_bound q z
  rw [sq_abs] at h2
  constructor <;> apply (le_div_iff₀ (by positivity)).mpr <;> nlinarith [h0.1,h0.2,h2.1,h2.2]

theorem quadraticEnvelope_integrable (C : ℝ) : Integrable (fun z : ℝ => C/(1+z^(2 : ℕ))) := by
  simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul C

/-- Genuine regularized reflection coefficients are integrable, in addition to their already proved L² regularity. -/
theorem globalSmall_regularReflection_integrable (q : SchwartzMap ℝ ℂ) :
    Integrable (regularReflectionCoefficient (globalSmallScatteringPotential q)) ∧
    Integrable (regularReverseReflectionCoefficient (globalSmallScatteringPotential q)) := by
  have hc := continuous_globalSmall_regularReflection q
  exact ⟨(quadraticEnvelope_integrable (1/3+regularSecondReflectionDecay q false)).mono' hc.1.aestronglyMeasurable
      (Eventually.of_forall fun z => (globalSmall_regularReflection_quadratic_bound q z).1),
    (quadraticEnvelope_integrable (1/3+regularSecondReflectionDecay q true)).mono' hc.2.aestronglyMeasurable
      (Eventually.of_forall fun z => (globalSmall_regularReflection_quadratic_bound q z).2)⟩

def regularSpectralReflection (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) : ℂ :=
  (z : ℂ)*(if reverse then regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z
    else regularReflectionCoefficient (globalSmallScatteringPotential q) z)

theorem regularSpectralReflection_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    ‖regularSpectralReflection q reverse z‖ ≤ regularReflectionDecay q reverse := by
  cases reverse
  · simpa only [regularSpectralReflection,Bool.false_eq_true,↓reduceIte,norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      (globalSmall_regularReflection_frequency_bound q z).1
  · simpa only [regularSpectralReflection,↓reduceIte,norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      (globalSmall_regularReflection_frequency_bound q z).2

/-- The weighted coefficient retains a reciprocal envelope and therefore lies in L². -/
theorem regularSpectralReflection_reciprocal_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    ‖regularSpectralReflection q reverse z‖ ≤
      (regularReflectionDecay q reverse+regularSecondReflectionDecay q reverse)/(1+|z|) := by
  have h1 := globalSmall_regularReflection_frequency_bound q z
  have h2 := globalSmall_regularReflection_second_frequency_bound q z
  apply (le_div_iff₀ (by positivity)).mpr
  cases reverse <;>
    simp only [regularSpectralReflection,Bool.false_eq_true,↓reduceIte,norm_mul,Complex.norm_real,Real.norm_eq_abs] <;>
    nlinarith [h1.1,h1.2,h2.1,h2.2]

theorem regularSpectralReflection_measurable (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Measurable (regularSpectralReflection q reverse) := by
  cases reverse
  · exact Complex.measurable_ofReal.mul (continuous_globalSmall_regularReflection q).1.measurable
  · exact Complex.measurable_ofReal.mul (continuous_globalSmall_regularReflection q).2.measurable

theorem regularSpectralReflection_memLp (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    MemLp (regularSpectralReflection q reverse) 2 volume :=
  (reciprocalEnvelope_memLp (regularReflectionDecay q reverse+regularSecondReflectionDecay q reverse)).mono'
    (regularSpectralReflection_measurable q reverse).aestronglyMeasurable
    (Eventually.of_forall (regularSpectralReflection_reciprocal_bound q reverse))

def regularSpectralJump (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  (z : ℂ)*(if reverse then regularJumpReverseReflection (globalSmallScatteringPotential q) t x z
    else regularJumpReflection (globalSmallScatteringPotential q) t x z)

/-- The actual space-time phase preserves the weighted scattering norm exactly. -/
theorem regularSpectralJump_norm (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖regularSpectralJump q t x reverse z‖ = ‖regularSpectralReflection q reverse z‖ := by
  cases reverse <;>
    simp only [regularSpectralJump,regularSpectralReflection,Bool.false_eq_true,↓reduceIte,norm_mul,
      (regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).1,
      (regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).2]

theorem regularSpectralJump_measurable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Measurable (regularSpectralJump q t x reverse) := by
  cases reverse
  · exact Complex.measurable_ofReal.mul (measurable_globalSmall_regularJump q t x).1
  · exact Complex.measurable_ofReal.mul (measurable_globalSmall_regularJump q t x).2

/-- Both frequency-weighted actual jump channels are square integrable at every physical parameter. -/
theorem regularSpectralJump_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    MemLp (regularSpectralJump q t x reverse) 2 volume :=
  (regularSpectralReflection_memLp q reverse).congr_norm (regularSpectralJump_measurable q t x reverse).aestronglyMeasurable
    (Eventually.of_forall fun z => (regularSpectralJump_norm q t x reverse z).symm)

theorem regularSpectralJump_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖regularSpectralJump q t x reverse z‖ ≤ regularReflectionDecay q reverse := by
  rw [regularSpectralJump_norm]
  exact regularSpectralReflection_bound q reverse z

/-- Both actual oscillatory jump channels are integrable at every space-time point. -/
theorem globalSmall_regularJump_integrable (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Integrable (regularJumpReflection (globalSmallScatteringPotential q) t x) ∧
    Integrable (regularJumpReverseReflection (globalSmallScatteringPotential q) t x) := by
  have hr := globalSmall_regularReflection_integrable q
  have hm := measurable_globalSmall_regularJump q t x
  exact ⟨hr.1.norm.mono' hm.1.aestronglyMeasurable (Eventually.of_forall fun z => (regularJumpReflection_norms _ t x z).1.le),
    hr.2.norm.mono' hm.2.aestronglyMeasurable (Eventually.of_forall fun z => (regularJumpReflection_norms _ t x z).2.le)⟩

/-- The product channel is integrable by the L² Hölder estimate already available in the corpus. -/
theorem globalSmall_regularJump_product_integrable (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Integrable (fun z => regularJumpReflection (globalSmallScatteringPotential q) t x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t x z) :=
  (globalSmall_regularJump_memLp q t x).1.integrable_mul (globalSmall_regularJump_memLp q t x).2

/-- Every actual jump perturbation entry is integrable. -/
theorem globalSmall_regularJump_sub_one_integrable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    Integrable (fun z => (regularJump (globalSmallScatteringPotential q) t x z-1) i j) := by
  fin_cases i <;> fin_cases j
  · simp [regularJump,jump]
  · simpa [regularJump,jump] using (globalSmall_regularJump_integrable q t x).2
  · have hm := (globalSmall_regularJump_integrable q t x).1.neg
    change Integrable (fun z => -regularJumpReflection (globalSmallScatteringPotential q) t x z) at hm
    simpa [regularJump,jump] using hm
  · have hm := (globalSmall_regularJump_product_integrable q t x).neg
    change Integrable (fun z => -(regularJumpReflection (globalSmallScatteringPotential q) t x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t x z)) at hm
    simpa [regularJump,jump] using hm

/-- The weighted nonlinear product channel remains square integrable. -/
theorem globalSmall_regularJump_weighted_product_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    MemLp (fun z : ℝ => (z : ℂ)*(regularJumpReflection (globalSmallScatteringPotential q) t x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t x z)) 2 volume := by
  have hm := measurable_globalSmall_regularJump q t x
  apply ((regularSpectralJump_memLp q t x false).norm.const_mul (1/3 : ℝ)).mono'
    (Complex.measurable_ofReal.mul (hm.1.mul hm.2)).aestronglyMeasurable
  filter_upwards with z
  change ‖(z : ℂ)*(_*_)‖ ≤ (1/3 : ℝ)*‖regularSpectralJump q t x false z‖
  rw [← mul_assoc,norm_mul]
  change ‖regularSpectralJump q t x false z‖*‖regularJumpReverseReflection (globalSmallScatteringPotential q) t x z‖ ≤ _
  exact (mul_le_mul_of_nonneg_left (globalSmall_regularJump_bounds q t x z).2 (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- Every entry of the genuine jump perturbation also lies in the frequency-weighted L² space. -/
theorem globalSmall_regularJump_sub_one_weighted_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (i j : Fin 2) :
    MemLp (fun z : ℝ => (z : ℂ)*((regularJump (globalSmallScatteringPotential q) t x z-1) i j)) 2 volume := by
  fin_cases i <;> fin_cases j
  · simp [regularJump,jump]
  · have hm := regularSpectralJump_memLp q t x true
    change MemLp (fun z : ℝ => (z : ℂ)*regularJumpReverseReflection (globalSmallScatteringPotential q) t x z) 2 volume at hm
    simpa [regularJump,jump] using hm
  · have hm := (regularSpectralJump_memLp q t x false).neg
    change MemLp (fun z => -regularSpectralJump q t x false z) 2 volume at hm
    simpa [regularJump,jump,regularSpectralJump] using hm
  · have hm := (globalSmall_regularJump_weighted_product_memLp q t x).neg
    change MemLp (fun z : ℝ => -((z : ℂ)*(regularJumpReflection (globalSmallScatteringPotential q) t x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t x z))) 2 volume at hm
    simpa [regularJump,jump] using hm

end
end GaloisForLFunctions.HTGeometry.FokasLenells
