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

/-- Injectivity of the formation family: distinct admitted chemical potentials give distinct laws. -/
theorem classLaw_fugacityShift_injective (θ : AbelianZetaConvergentParameters)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : classLaw (fugacityShiftConv θ s hs).toAbelianZetaParameters
      = classLaw (fugacityShiftConv θ t ht).toAbelianZetaParameters) : s = t := by
  have hzero : gasChirality θ s t hs ht = 0 := by
    rw [← klChirality_classLaw_fugacityShift θ s t hs ht, h, klChirality]
    ring
  rcases lt_trichotomy s t with hst | hst | hst
  · exact absurd hzero (ne_of_gt (gasChirality_pos θ s t hs ht hst))
  · exact hst
  · have hneg : gasChirality θ s t hs ht = -gasChirality θ t s ht hs := by
      simp only [gasChirality]; ring
    have := gasChirality_pos θ t s ht hs hst
    rw [hneg] at hzero
    linarith

/-- The formation law depends on the chemical potential only through its value. -/
theorem classLaw_fugacityShift_congr (θ : AbelianZetaConvergentParameters)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a = b) :
    classLaw (fugacityShiftConv θ a ha).toAbelianZetaParameters
      = classLaw (fugacityShiftConv θ b hb).toAbelianZetaParameters := by
  subst h; rfl

/-- A finite-order measurable self-map of a measurable space is a measurable embedding. -/
theorem measurableEmbedding_of_finite_order {α : Type*} [MeasurableSpace α]
    {Θ : α → α} (hΘ : Measurable Θ) {N : ℕ} (hN : 0 < N) (hiter : ∀ A, Θ^[N] A = A) :
    MeasurableEmbedding Θ := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hinvL : ∀ A, Θ^[k] (Θ A) = A := by
    intro A
    have := hiter A
    rwa [Function.iterate_succ_apply] at this
  have hinvR : ∀ A, Θ (Θ^[k] A) = A := by
    intro A
    have := hiter A
    rwa [Function.iterate_succ_apply'] at this
  let e : α ≃ᵐ α :=
    { toFun := Θ
      invFun := Θ^[k]
      left_inv := hinvL
      right_inv := hinvR
      measurable_toFun := hΘ
      measurable_invFun := hΘ.iterate k }
  exact e.measurableEmbedding

/-- Relative entropy is invariant under a finite-order measurable symmetry. -/
theorem klChirality_map_of_finite_order {α : Type*} [MeasurableSpace α]
    {Θ : α → α} (hΘ : Measurable Θ) {N : ℕ} (hN : 0 < N) (hiter : ∀ A, Θ^[N] A = A)
    (P R : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure R] :
    klChirality (P.map Θ) (R.map Θ) = klChirality P R := by
  have hemb := measurableEmbedding_of_finite_order hΘ hN hiter
  rw [klChirality, klChirality, klDiv_map_measurableEmbedding hemb,
    klDiv_map_measurableEmbedding hemb]

/-- **Theorem 7.2 (FCRM.27).**  A finite-order measurable symmetry transporting the formation
family along a parameter map acts as the identity on the parameter. -/
theorem fugacityShift_finite_order_symmetry_id (θ : AbelianZetaConvergentParameters)
    {Θ : AbelianZetaGroupClass → AbelianZetaGroupClass} (hΘ : Measurable Θ)
    {N : ℕ} (hN : 0 < N) (hiter : ∀ A, Θ^[N] A = A)
    {φ : ℝ → ℝ} {I : Set ℝ} (hI : ∀ t ∈ I, 0 ≤ t) (hmapI : ∀ t ∈ I, φ t ∈ I)
    (htrans : ∀ t, ∀ ht : t ∈ I,
      (classLaw (fugacityShiftConv θ t (hI t ht)).toAbelianZetaParameters).map Θ
        = classLaw (fugacityShiftConv θ (φ t) (hI (φ t) (hmapI t ht))).toAbelianZetaParameters) :
    ∀ t ∈ I, φ t = t := by
  have hiterI : ∀ (k : ℕ), ∀ t ∈ I, φ^[k] t ∈ I := by
    intro k
    induction k with
    | zero => intro t ht; simpa using ht
    | succ k ih =>
        intro t ht
        rw [Function.iterate_succ_apply]
        exact ih _ (hmapI t ht)
  have hmono : ∀ s ∈ I, ∀ t ∈ I, s < t → φ s < φ t := by
    intro s hsI t htI hst
    have hchir := gasChirality_pos θ s t (hI s hsI) (hI t htI) hst
    rw [← klChirality_classLaw_fugacityShift θ s t (hI s hsI) (hI t htI)] at hchir
    rw [← klChirality_map_of_finite_order hΘ hN hiter, htrans s hsI, htrans t htI,
      klChirality_classLaw_fugacityShift] at hchir
    exact (gasChirality_lt_iff θ (φ s) (φ t) (hI _ (hmapI s hsI)) (hI _ (hmapI t htI))).mpr hchir
  have hmapIter : ∀ (k : ℕ), ∀ t, ∀ ht : t ∈ I,
      (classLaw (fugacityShiftConv θ t (hI t ht)).toAbelianZetaParameters).map (Θ^[k])
        = classLaw (fugacityShiftConv θ (φ^[k] t)
            (hI (φ^[k] t) (hiterI k t ht))).toAbelianZetaParameters := by
    intro k
    induction k with
    | zero => intro t ht; simp
    | succ k ih =>
        intro t ht
        rw [show (Θ^[k + 1]) = Θ^[k] ∘ Θ from Function.iterate_succ Θ k,
          ← Measure.map_map (hΘ.iterate k) hΘ, htrans t ht, ih (φ t) (hmapI t ht)]
        exact classLaw_fugacityShift_congr θ _ _ (Function.iterate_succ_apply φ k t).symm
  have hfix : ∀ t ∈ I, φ^[N] t = t := by
    intro t ht
    have h := hmapIter N t ht
    have hid : Θ^[N] = id := funext hiter
    rw [hid, Measure.map_id] at h
    exact (classLaw_fugacityShift_injective θ (hI _ (hiterI N t ht)) (hI t ht) h.symm)
  exact eq_id_of_strictMonoOn_of_iterate_id hmapI hmono hN hfix

end GaloisForLFunctions.HTGeometry
