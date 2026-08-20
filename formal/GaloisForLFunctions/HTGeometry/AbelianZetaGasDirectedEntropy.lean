import GaloisForLFunctions.HTGeometry.AbelianZetaGasModeChirality
import GaloisForLFunctions.HTGeometry.EsscherFormationChirality
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.RelativeEntropy

/-!
# Directed relative entropy of the abelian zeta gas

The chemical-potential shift realizes the class law as an Esscher tilt of the base class law by the
socle observable, so the two directed relative entropies of the gas are exactly the Esscher
formulas.  Their difference is the gas commutator, which the geometric-mode analysis has already
shown to be strictly positive on every ordered pair.  Hence no measurable involution exchanges two
distinct admitted formation laws, and every finite-order formation symmetry acts as the identity.
-/

open MeasureTheory InformationTheory
open scoped NNReal ENNReal
namespace GaloisForLFunctions.HTGeometry

/-- The zero-occupation normalizer is strictly positive. -/
theorem coe_nnNormalizer_pos (η : AbelianZetaConvergentParameters) :
    0 < ((η.nnNormalizer : ℝ≥0) : ℝ) := by
  rcases (η.nnNormalizer : ℝ≥0).coe_nonneg.lt_or_eq with h' | h'
  · exact h'
  · exact absurd (by
      simp only [AbelianZetaConvergentParameters.ennNormalizer]
      rw [show η.nnNormalizer = 0 from NNReal.coe_injective h'.symm]
      simp) (AbelianZetaConvergentParameters.ennNormalizer_ne_zero η)

/-- The Esscher normalization constant of the shifted class law. -/
noncomputable def gasEsscherConst (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) : ℝ :=
  (((fugacityShiftConv θ u hu).nnNormalizer : ℝ≥0) : ℝ) / ((θ.nnNormalizer : ℝ≥0) : ℝ)

theorem gasEsscherConst_pos (θ : AbelianZetaConvergentParameters) (u : ℝ) (hu : 0 ≤ u) :
    0 < gasEsscherConst θ u hu :=
  div_pos (coe_nnNormalizer_pos _) (coe_nnNormalizer_pos _)

theorem log_gasEsscherConst_div (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Real.log (gasEsscherConst θ s hs / gasEsscherConst θ t ht)
      = gasLogPartition θ t ht - gasLogPartition θ s hs := by
  have hNs := coe_nnNormalizer_pos (fugacityShiftConv θ s hs)
  have hNt := coe_nnNormalizer_pos (fugacityShiftConv θ t ht)
  have hN0 := coe_nnNormalizer_pos θ
  have hdiv : gasEsscherConst θ s hs / gasEsscherConst θ t ht
      = (((fugacityShiftConv θ s hs).nnNormalizer : ℝ≥0) : ℝ)
        / (((fugacityShiftConv θ t ht).nnNormalizer : ℝ≥0) : ℝ) := by
    simp only [gasEsscherConst]
    field_simp
  rw [hdiv, Real.log_div (ne_of_gt hNs) (ne_of_gt hNt), gasLogPartition, gasLogPartition]
  ring


/-- The shifted class law is the Esscher tilt of the base class law by the socle observable. -/
theorem classLaw_fugacityShift_eq_esscherLaw (θ : AbelianZetaConvergentParameters)
    (u : ℝ) (hu : 0 ≤ u) :
    classLaw (fugacityShiftConv θ u hu).toAbelianZetaParameters
      = esscherLaw (classLaw θ.toAbelianZetaParameters)
          (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
          (gasEsscherConst θ u hu) u := by
  classical
  simp only [gasEsscherConst]
  apply Measure.ext_of_singleton
  intro A
  rw [esscherLaw, withDensity_apply _ (MeasurableSet.singleton A), lintegral_singleton,
    classLaw_singleton, classLaw_singleton,
    θ.classMass_eq_ennNormalizer_mul_twoObservableWeight A,
    (fugacityShiftConv θ u hu).classMass_eq_ennNormalizer_mul_twoObservableWeight A]
  have hsoc : (0 : ℝ) < ((A.socleOrder : ℕ) : ℝ) := by exact_mod_cast A.socleOrder_pos
  have hord : (0 : ℝ) < ((A.order : ℕ) : ℝ) := by exact_mod_cast A.order_pos
  have hN0 : (0 : ℝ) < ((θ.nnNormalizer : ℝ≥0) : ℝ) := by
    have h := AbelianZetaConvergentParameters.ennNormalizer_ne_zero θ
    rcases (θ.nnNormalizer : ℝ≥0).coe_nonneg.lt_or_eq with h' | h'
    · exact h'
    · exact absurd (by
        simp only [AbelianZetaConvergentParameters.ennNormalizer]
        rw [show θ.nnNormalizer = 0 from NNReal.coe_injective h'.symm]
        simp) h
  have hNu : (0 : ℝ) ≤ (((fugacityShiftConv θ u hu).nnNormalizer : ℝ≥0) : ℝ) :=
    NNReal.coe_nonneg _
  have hw0 : (0 : ℝ) ≤ abelianZetaTwoObservableWeight θ.toAbelianZetaParameters A := by
    rw [abelianZetaTwoObservableWeight]; positivity
  have hexp : (0 : ℝ) ≤ Real.exp (-u * Real.log ((A.socleOrder : ℕ) : ℝ)) := (Real.exp_pos _).le
  simp only [AbelianZetaConvergentParameters.ennNormalizer]
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul hNu, ← ENNReal.ofReal_mul hN0.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hkey : Real.exp (-u * Real.log ((A.socleOrder : ℕ) : ℝ))
      = ((A.socleOrder : ℕ) : ℝ) ^ (-u) := by
    rw [Real.rpow_def_of_pos hsoc]
    ring_nf
  rw [abelianZetaTwoObservableWeight, abelianZetaTwoObservableWeight]
  simp only [fugacityShiftConv]
  rw [hkey, show -(θ.tau + u) = -θ.tau + -u from by ring, Real.rpow_add hsoc]
  field_simp


/-- **(FCRM.9) for the abelian zeta gas.**  The directed relative entropy between two admitted
chemical potentials is the log-partition difference plus the first-response term. -/
theorem klDiv_classLaw_fugacityShift (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    klDiv (classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters)
        (classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters)
      = ENNReal.ofReal (gasLogPartition θ t ht - gasLogPartition θ s hs
          + (t - s) * gasFirstMoment θ s hs) := by
  have hEs := classLaw_fugacityShift_eq_esscherLaw θ s hs
  have hEt := classLaw_fugacityShift_eq_esscherLaw θ t ht
  haveI hps : IsProbabilityMeasure (esscherLaw (classLaw θ.toAbelianZetaParameters)
      (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
      (gasEsscherConst θ s hs) s) := hEs ▸ (inferInstance : IsProbabilityMeasure (classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters))
  haveI hpt : IsProbabilityMeasure (esscherLaw (classLaw θ.toAbelianZetaParameters)
      (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
      (gasEsscherConst θ t ht) t) := hEt ▸ (inferInstance : IsProbabilityMeasure (classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters))
  have hQint : Integrable (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
      (esscherLaw (classLaw θ.toAbelianZetaParameters)
        (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
        (gasEsscherConst θ s hs) s) := by
    rw [← hEs]
    exact integrable_classLaw_logSocle _ (socleExpectation_ne_top _)
  rw [hEs, hEt, klDiv_esscherLaw _ measurable_logSocle (gasEsscherConst_pos θ s hs)
    (gasEsscherConst_pos θ t ht) s t hQint, log_gasEsscherConst_div]
  congr 2
  rw [← hEs, gasFirstMoment, integral_classLaw_logSocle]

theorem gasDirected_nonneg (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    0 ≤ gasLogPartition θ t ht - gasLogPartition θ s hs + (t - s) * gasFirstMoment θ s hs := by
  have hEs := classLaw_fugacityShift_eq_esscherLaw θ s hs
  have hEt := classLaw_fugacityShift_eq_esscherLaw θ t ht
  haveI hps : IsProbabilityMeasure (esscherLaw (classLaw θ.toAbelianZetaParameters)
      (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
      (gasEsscherConst θ s hs) s) := hEs ▸
        (inferInstance : IsProbabilityMeasure
          (classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters))
  haveI hpt : IsProbabilityMeasure (esscherLaw (classLaw θ.toAbelianZetaParameters)
      (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
      (gasEsscherConst θ t ht) t) := hEt ▸
        (inferInstance : IsProbabilityMeasure
          (classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters))
  have hQint : Integrable (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
      (esscherLaw (classLaw θ.toAbelianZetaParameters)
        (fun A : AbelianZetaGroupClass => Real.log ((A.socleOrder : ℕ) : ℝ))
        (gasEsscherConst θ s hs) s) := by
    rw [← hEs]
    exact integrable_classLaw_logSocle _ (socleExpectation_ne_top _)
  have h := esscherDirected_nonneg (classLaw θ.toAbelianZetaParameters) measurable_logSocle
    (gasEsscherConst_pos θ s hs) (gasEsscherConst_pos θ t ht) s t hQint
  rw [log_gasEsscherConst_div, ← hEs] at h
  rwa [show gasFirstMoment θ s hs
      = ∫ A, Real.log ((A.socleOrder : ℕ) : ℝ)
          ∂(classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters) from
    (integral_classLaw_logSocle _).symm]

/-- **The gas commutator is the directed relative-entropy asymmetry of the two class laws.** -/
theorem klChirality_classLaw_fugacityShift (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    klChirality (classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters)
        (classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters)
      = gasChirality θ s t hs ht := by
  rw [klChirality, klDiv_classLaw_fugacityShift θ s t hs ht,
    klDiv_classLaw_fugacityShift θ t s ht hs,
    ENNReal.toReal_ofReal (gasDirected_nonneg θ s t hs ht),
    ENNReal.toReal_ofReal (gasDirected_nonneg θ t s ht hs), gasChirality]
  ring

/-- **Theorem 7.1 (FCRM.24).**  A measurable involution of the class space exchanging two admitted
formation laws forces the two chemical potentials to agree. -/
theorem fugacityShift_eq_of_involution (θ : AbelianZetaConvergentParameters)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    {Θ : AbelianZetaGroupClass → AbelianZetaGroupClass} (hΘ : Measurable Θ)
    (hinv : ∀ A, Θ (Θ A) = A)
    (hmap : (classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters).map Θ
      = classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters) :
    s = t := by
  have hback : (classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters).map Θ
      = classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters := by
    rw [← hmap, Measure.map_map hΘ hΘ]
    have : Θ ∘ Θ = id := funext hinv
    rw [this, Measure.map_id]
  have hzero := klChirality_eq_zero_of_reversal
    (classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters)
    (classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters) hΘ hinv hmap hback
  rw [klChirality_classLaw_fugacityShift θ s t hs ht] at hzero
  rcases lt_trichotomy s t with hst | hst | hst
  · exact absurd hzero (ne_of_gt (gasChirality_pos θ s t hs ht hst))
  · exact hst
  · have hneg : gasChirality θ s t hs ht = -gasChirality θ t s ht hs := by
      simp only [gasChirality]; ring
    have := gasChirality_pos θ t s ht hs hst
    rw [hneg] at hzero
    linarith

/-- **(FCRM.25)  Centered reversal selection.**  An involution exchanging the two centered
formation laws forces zero displacement. -/
theorem centered_reversal_selection (θ : AbelianZetaConvergentParameters)
    (c a : ℝ) (ha : 0 ≤ a) (hca : 0 ≤ c - a) (hcb : 0 ≤ c + a)
    {Θ : AbelianZetaGroupClass → AbelianZetaGroupClass} (hΘ : Measurable Θ)
    (hinv : ∀ A, Θ (Θ A) = A)
    (hmap : (classLaw (fugacityShiftConv θ (c - a) hca).toAbelianZetaParameters).map Θ
      = classLaw (fugacityShiftConv θ (c + a) hcb).toAbelianZetaParameters) :
    a = 0 := by
  have h := fugacityShift_eq_of_involution θ (c - a) (c + a) hca hcb hΘ hinv hmap
  linarith

end GaloisForLFunctions.HTGeometry
