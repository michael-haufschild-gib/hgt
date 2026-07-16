import GaloisForLFunctions.RHTower.MobiusIncidenceKMSEntropyProduction
import GaloisForLFunctions.RHTower.MobiusCriticalClockWeakConvergence
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

noncomputable section

namespace RHTower

def squarefreeMobiusCriticalFiniteIndex (N : ℕ) :=
  {i : Fin (N + 2) // Squarefree (i : ℕ)}

instance (N : ℕ) : Fintype (squarefreeMobiusCriticalFiniteIndex N) := by
  unfold squarefreeMobiusCriticalFiniteIndex
  infer_instance

instance (N : ℕ) : MeasurableSpace (squarefreeMobiusCriticalFiniteIndex N) := ⊤

instance (N : ℕ) : Nonempty (squarefreeMobiusCriticalFiniteIndex N) :=
  ⟨⟨⟨1, by omega⟩, squarefree_one⟩⟩

def squarefreeMobiusCriticalFiniteIndexValue {N : ℕ} :
    squarefreeMobiusCriticalFiniteIndex N → ℕ :=
  fun i => i.1

theorem squarefreeMobiusCriticalFiniteIndexValue_pos
    {N : ℕ} (i : squarefreeMobiusCriticalFiniteIndex N) :
    0 < squarefreeMobiusCriticalFiniteIndexValue i := by
  by_contra h
  have hi0 : squarefreeMobiusCriticalFiniteIndexValue i = 0 := Nat.eq_zero_of_not_pos h
  have hi0' : (i.1 : ℕ) = 0 := by
    simpa [squarefreeMobiusCriticalFiniteIndexValue] using hi0
  exact not_squarefree_zero (hi0' ▸ i.2)

theorem squarefreeMobiusCriticalFiniteIndexValue_injective {N : ℕ} :
    Function.Injective
      (squarefreeMobiusCriticalFiniteIndexValue (N := N)) := by
  intro i j h
  apply Subtype.ext
  apply Fin.ext
  exact h

theorem finiteIncidencePartition_squarefreeMobiusCriticalFiniteIndex
    (sigma : ℝ) (N : ℕ) :
    finiteIncidencePartition sigma
        (squarefreeMobiusCriticalFiniteIndexValue (N := N)) =
      ∑ n ∈ Finset.range (N + 2), squarefreeMobiusMass sigma n := by
  unfold finiteIncidencePartition squarefreeMobiusCriticalFiniteIndexValue
    squarefreeMobiusCriticalFiniteIndex squarefreeMobiusMass
  calc
    (∑ i : {i : Fin (N + 2) // Squarefree (i : ℕ)},
        ((i.1 : ℕ) : ℝ) ^ (-sigma)) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin (N + 2) => Squarefree (i : ℕ)),
          (((i : ℕ) : ℝ) ^ (-sigma)) := by
      exact (Finset.sum_subtype
        (p := fun i : Fin (N + 2) => Squarefree (i : ℕ))
        (M := ℝ)
        (Finset.univ.filter (fun i : Fin (N + 2) => Squarefree (i : ℕ)))
        (by
          intro i
          constructor
          · exact fun hi => (Finset.mem_filter.mp hi).2
          · exact fun hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        (fun i : Fin (N + 2) => (((i : ℕ) : ℝ) ^ (-sigma)))).symm
    _ = ∑ i : Fin (N + 2),
          if Squarefree (i : ℕ) then (((i : ℕ) : ℝ) ^ (-sigma)) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ n ∈ Finset.range (N + 2),
          if Squarefree n then (n : ℝ) ^ (-sigma) else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro n hn
      simp [Finset.mem_range.mp hn]

theorem squarefreeMobiusCriticalIndexTruncation_toReal
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) :
    ((squarefreeMobiusCriticalPMF sigma).toMeasure (Iio (N + 2))).toReal =
      ∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n := by
  rw [show Iio (N + 2) = (Finset.range (N + 2) : Set ℕ) by
    ext n
    simp]
  rw [(squarefreeMobiusCriticalPMF sigma).toMeasure_apply_finset]
  rw [ENNReal.toReal_sum (fun n _ =>
    (squarefreeMobiusCriticalPMF sigma).apply_ne_top n)]
  apply Finset.sum_congr rfl
  intro n hn
  exact squarefreeMobiusCriticalPMF_toReal hsigma n

theorem sum_range_squarefreeMobiusProbability_eq_partition_div_total
    {sigma : ℝ} (N : ℕ) :
    (∑ n ∈ Finset.range (N + 2), squarefreeMobiusProbability sigma n) =
      finiteIncidencePartition sigma
          (squarefreeMobiusCriticalFiniteIndexValue (N := N)) /
        squarefreeMobiusTotal sigma := by
  rw [finiteIncidencePartition_squarefreeMobiusCriticalFiniteIndex]
  simp only [squarefreeMobiusProbability, Finset.sum_div]

theorem finiteIncidenceProbability_squarefreeMobiusCriticalFiniteIndex
    {sigma : ℝ} (N : ℕ) (i : squarefreeMobiusCriticalFiniteIndex N) :
    finiteIncidenceProbability sigma
        (squarefreeMobiusCriticalFiniteIndexValue (N := N)) i =
      squarefreeMobiusMass sigma (squarefreeMobiusCriticalFiniteIndexValue i) /
        finiteIncidencePartition sigma
          (squarefreeMobiusCriticalFiniteIndexValue (N := N)) := by
  unfold finiteIncidenceProbability squarefreeMobiusCriticalFiniteIndexValue
  rw [squarefreeMobiusMass, if_pos i.2]

theorem squarefreeMobiusCriticalTruncatedIndexProbabilityMeasure_singleton_toReal
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ)
    (i : squarefreeMobiusCriticalFiniteIndex N) :
    ((squarefreeMobiusCriticalTruncatedIndexProbabilityMeasure sigma hsigma N :
        Measure ℕ) {squarefreeMobiusCriticalFiniteIndexValue i}).toReal =
      finiteIncidenceProbability sigma
        (squarefreeMobiusCriticalFiniteIndexValue (N := N)) i := by
  unfold squarefreeMobiusCriticalTruncatedIndexProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [ProbabilityTheory.cond_apply (MeasurableSet.of_discrete)
    (squarefreeMobiusCriticalPMF sigma).toMeasure]
  have hi : squarefreeMobiusCriticalFiniteIndexValue i < N + 2 := by
    exact i.1.isLt
  rw [show Iio (N + 2) ∩ {squarefreeMobiusCriticalFiniteIndexValue i} =
      ({squarefreeMobiusCriticalFiniteIndexValue i} : Set ℕ) by
    ext n
    simp [hi]]
  rw [(squarefreeMobiusCriticalPMF sigma).toMeasure_apply_singleton _
    (MeasurableSet.singleton _), ENNReal.toReal_mul, ENNReal.toReal_inv,
    squarefreeMobiusCriticalPMF_toReal hsigma,
    squarefreeMobiusCriticalIndexTruncation_toReal hsigma,
    sum_range_squarefreeMobiusProbability_eq_partition_div_total,
    squarefreeMobiusProbability,
    finiteIncidenceProbability_squarefreeMobiusCriticalFiniteIndex]
  have htotal : squarefreeMobiusTotal sigma ≠ 0 :=
    (squarefreeMobiusTotal_pos hsigma).ne'
  have hpartition : finiteIncidencePartition sigma
      (squarefreeMobiusCriticalFiniteIndexValue (N := N)) ≠ 0 :=
    (finiteIncidencePartition_pos
      (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N))).ne'
  field_simp [htotal, hpartition]

def squarefreeMobiusCriticalFinitePMF (sigma : ℝ) (N : ℕ) :
    PMF (squarefreeMobiusCriticalFiniteIndex N) := by
  refine PMF.ofFintype
    (fun i => ENNReal.ofReal (finiteIncidenceProbability sigma
      (squarefreeMobiusCriticalFiniteIndexValue (N := N)) i)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    (finiteIncidenceProbability_pos
      (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N)) i).le)]
  rw [sum_finiteIncidenceProbability
    (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N))]
  norm_num

def squarefreeMobiusCriticalFiniteIndexProbabilityMeasure
    (sigma : ℝ) (N : ℕ) : ProbabilityMeasure ℕ :=
  ProbabilityMeasure.map
    (⟨(squarefreeMobiusCriticalFinitePMF sigma N).toMeasure,
      inferInstance⟩ : ProbabilityMeasure
        (squarefreeMobiusCriticalFiniteIndex N))
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable (squarefreeMobiusCriticalFiniteIndexValue (N := N))
        (squarefreeMobiusCriticalFinitePMF sigma N).toMeasure)

theorem squarefreeMobiusCriticalFiniteIndexProbabilityMeasure_eq_truncated
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) :
    squarefreeMobiusCriticalFiniteIndexProbabilityMeasure sigma N =
      squarefreeMobiusCriticalTruncatedIndexProbabilityMeasure sigma hsigma N := by
  apply Subtype.ext
  change (squarefreeMobiusCriticalFiniteIndexProbabilityMeasure sigma N : Measure ℕ) =
    (squarefreeMobiusCriticalTruncatedIndexProbabilityMeasure sigma hsigma N : Measure ℕ)
  apply Measure.ext_of_singleton
  intro n
  by_cases hn : n < N + 2 ∧ Squarefree n
  · let i : squarefreeMobiusCriticalFiniteIndex N :=
      ⟨⟨n, hn.1⟩, hn.2⟩
    unfold squarefreeMobiusCriticalFiniteIndexProbabilityMeasure ProbabilityMeasure.map
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply_of_aemeasurable Measurable.of_discrete.aemeasurable
      (MeasurableSet.singleton n)]
    rw [show squarefreeMobiusCriticalFiniteIndexValue ⁻¹' ({n} : Set ℕ) =
        ({i} : Set (squarefreeMobiusCriticalFiniteIndex N)) by
      ext j
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        apply Subtype.ext
        apply Fin.ext
        exact h
      · rintro rfl
        rfl]
    rw [(squarefreeMobiusCriticalFinitePMF sigma N).toMeasure_apply_singleton i
      (MeasurableSet.singleton i)]
    change ENNReal.ofReal (finiteIncidenceProbability sigma
      (squarefreeMobiusCriticalFiniteIndexValue (N := N)) i) = _
    apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top
      (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_ofReal
      (finiteIncidenceProbability_pos
        (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N)) i).le]
    simpa [i, squarefreeMobiusCriticalFiniteIndexValue] using
      (squarefreeMobiusCriticalTruncatedIndexProbabilityMeasure_singleton_toReal
        hsigma N i).symm
  · unfold squarefreeMobiusCriticalFiniteIndexProbabilityMeasure ProbabilityMeasure.map
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply_of_aemeasurable Measurable.of_discrete.aemeasurable
      (MeasurableSet.singleton n)]
    rw [show squarefreeMobiusCriticalFiniteIndexValue ⁻¹' ({n} : Set ℕ) =
        (∅ : Set (squarefreeMobiusCriticalFiniteIndex N)) by
      ext i
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hi
      apply hn
      rw [← hi]
      exact ⟨i.1.isLt, i.2⟩]
    rw [measure_empty]
    symm
    unfold squarefreeMobiusCriticalTruncatedIndexProbabilityMeasure
    simp only [ProbabilityMeasure.coe_mk]
    rw [ProbabilityTheory.cond_apply (MeasurableSet.of_discrete)
      (squarefreeMobiusCriticalPMF sigma).toMeasure]
    by_cases hnRange : n < N + 2
    · have hnSquarefree : ¬Squarefree n := fun h => hn ⟨hnRange, h⟩
      rw [show Iio (N + 2) ∩ {n} = ({n} : Set ℕ) by
        ext m
        simp [hnRange]]
      rw [(squarefreeMobiusCriticalPMF sigma).toMeasure_apply_singleton n
        (MeasurableSet.singleton n)]
      have hpzero : squarefreeMobiusCriticalPMF sigma n = 0 := by
        apply (ENNReal.toReal_eq_toReal_iff'
          ((squarefreeMobiusCriticalPMF sigma).apply_ne_top n)
          ENNReal.zero_ne_top).mp
        rw [squarefreeMobiusCriticalPMF_toReal hsigma]
        simp [squarefreeMobiusProbability, squarefreeMobiusMass, hnSquarefree]
      rw [hpzero]
      simp
    · rw [show Iio (N + 2) ∩ {n} = (∅ : Set ℕ) by
        ext m
        simp [hnRange]]
      simp

def squarefreeMobiusCriticalFiniteStateProbabilityMeasure
    (sigma : ℝ) (N : ℕ) :
    ProbabilityMeasure (squarefreeMobiusCriticalFiniteIndex N) :=
  ⟨(squarefreeMobiusCriticalFinitePMF sigma N).toMeasure, inferInstance⟩

def squarefreeMobiusCriticalFiniteClockProbabilityMeasure
    (sigma : ℝ) (N : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (squarefreeMobiusCriticalFiniteStateProbabilityMeasure sigma N)
    (Measurable.of_discrete.aemeasurable :
      AEMeasurable
        (fun i : squarefreeMobiusCriticalFiniteIndex N =>
          squarefreeMobiusCriticalClock sigma
            (squarefreeMobiusCriticalFiniteIndexValue i))
        (squarefreeMobiusCriticalFinitePMF sigma N).toMeasure)

theorem squarefreeMobiusCriticalFiniteClockProbabilityMeasure_eq_truncated
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) :
    squarefreeMobiusCriticalFiniteClockProbabilityMeasure sigma N =
      squarefreeMobiusCriticalTruncatedClockProbabilityMeasure sigma hsigma N := by
  unfold squarefreeMobiusCriticalFiniteClockProbabilityMeasure
    squarefreeMobiusCriticalTruncatedClockProbabilityMeasure
  simp only [← squarefreeMobiusCriticalFiniteIndexProbabilityMeasure_eq_truncated hsigma N]
  apply Subtype.ext
  unfold squarefreeMobiusCriticalFiniteIndexProbabilityMeasure
    squarefreeMobiusCriticalFiniteStateProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk]
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
  rfl

def squarefreeMobiusCriticalFiniteGapProbabilityMeasure
    (sigma : ℝ) (N : ℕ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    ((squarefreeMobiusCriticalFiniteClockProbabilityMeasure sigma N).prod
      (squarefreeMobiusCriticalFiniteClockProbabilityMeasure sigma N))
    ((continuous_fst.sub continuous_snd).measurable.aemeasurable)

theorem squarefreeMobiusCriticalFiniteGapProbabilityMeasure_eq_truncated
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) :
    squarefreeMobiusCriticalFiniteGapProbabilityMeasure sigma N =
      squarefreeMobiusCriticalTruncatedGapProbabilityMeasure sigma hsigma N := by
  have hclock :=
    squarefreeMobiusCriticalFiniteClockProbabilityMeasure_eq_truncated hsigma N
  have hgap := congrArg
    (fun μ : ProbabilityMeasure ℝ =>
      ProbabilityMeasure.map (μ.prod μ)
        ((continuous_fst.sub continuous_snd).measurable.aemeasurable :
          AEMeasurable (fun p : ℝ × ℝ => p.1 - p.2) (μ.prod μ : Measure (ℝ × ℝ))))
    hclock
  simpa [squarefreeMobiusCriticalFiniteGapProbabilityMeasure,
    squarefreeMobiusCriticalTruncatedGapProbabilityMeasure] using hgap

def squarefreeMobiusCriticalFiniteGapResponse
    (sigma : ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, mobiusIncidenceGapResponseIntegrand z x
    ∂(squarefreeMobiusCriticalFiniteGapProbabilityMeasure sigma N : Measure ℝ)

theorem squarefreeMobiusCriticalFiniteGapResponse_eq_truncated
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) (z : ℂ) :
    squarefreeMobiusCriticalFiniteGapResponse sigma N z =
      squarefreeMobiusCriticalTruncatedGapResponse sigma hsigma N z := by
  unfold squarefreeMobiusCriticalFiniteGapResponse
    squarefreeMobiusCriticalTruncatedGapResponse
  rw [squarefreeMobiusCriticalFiniteGapProbabilityMeasure_eq_truncated hsigma N]

theorem squarefreeMobiusCriticalFiniteGapProbabilityMeasure_toMeasure
    (sigma : ℝ) (N : ℕ) :
    (squarefreeMobiusCriticalFiniteGapProbabilityMeasure sigma N : Measure ℝ) =
      Measure.map
        (fun p : squarefreeMobiusCriticalFiniteIndex N ×
            squarefreeMobiusCriticalFiniteIndex N =>
          squarefreeMobiusCriticalClock sigma
              (squarefreeMobiusCriticalFiniteIndexValue p.1) -
            squarefreeMobiusCriticalClock sigma
              (squarefreeMobiusCriticalFiniteIndexValue p.2))
        ((squarefreeMobiusCriticalFiniteStateProbabilityMeasure sigma N :
            Measure (squarefreeMobiusCriticalFiniteIndex N)).prod
          (squarefreeMobiusCriticalFiniteStateProbabilityMeasure sigma N :
            Measure (squarefreeMobiusCriticalFiniteIndex N))) := by
  unfold squarefreeMobiusCriticalFiniteGapProbabilityMeasure
    squarefreeMobiusCriticalFiniteClockProbabilityMeasure ProbabilityMeasure.map
  simp only [ProbabilityMeasure.coe_mk, ProbabilityMeasure.toMeasure_prod]
  rw [Measure.map_prod_map _ _ Measurable.of_discrete Measurable.of_discrete]
  rw [Measure.map_map (continuous_fst.sub continuous_snd).measurable
    (Measurable.of_discrete.prodMap Measurable.of_discrete)]
  rfl

theorem squarefreeMobiusCriticalFiniteGapResponse_eq_sum
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    squarefreeMobiusCriticalFiniteGapResponse sigma N z =
      ∑ a : squarefreeMobiusCriticalFiniteIndex N,
        ∑ b : squarefreeMobiusCriticalFiniteIndex N,
          ((4 * (sigma - 1) *
              finiteIncidenceProbability sigma
                (squarefreeMobiusCriticalFiniteIndexValue (N := N)) a *
              finiteIncidenceProbability sigma
                (squarefreeMobiusCriticalFiniteIndexValue (N := N)) b *
              |Real.log (squarefreeMobiusCriticalFiniteIndexValue a) -
                Real.log (squarefreeMobiusCriticalFiniteIndexValue b)| : ℝ) : ℂ) /
            (z - (((sigma - 1) *
              (Real.log (squarefreeMobiusCriticalFiniteIndexValue a) -
                Real.log (squarefreeMobiusCriticalFiniteIndexValue b)) : ℝ) : ℂ)) := by
  unfold squarefreeMobiusCriticalFiniteGapResponse
  rw [squarefreeMobiusCriticalFiniteGapProbabilityMeasure_toMeasure]
  rw [integral_map Measurable.of_discrete.aemeasurable
    (continuous_mobiusIncidenceGapResponseIntegrand hz).aestronglyMeasurable]
  unfold squarefreeMobiusCriticalFiniteStateProbabilityMeasure
  simp only [ProbabilityMeasure.coe_mk]
  rw [integral_prod _ Integrable.of_finite]
  rw [PMF.integral_eq_sum]
  simp_rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  change ENNReal.toReal (ENNReal.ofReal (finiteIncidenceProbability sigma
      (squarefreeMobiusCriticalFiniteIndexValue (N := N)) a)) •
      (ENNReal.toReal (ENNReal.ofReal (finiteIncidenceProbability sigma
        (squarefreeMobiusCriticalFiniteIndexValue (N := N)) b)) •
        mobiusIncidenceGapResponseIntegrand z
          (squarefreeMobiusCriticalClock sigma
              (squarefreeMobiusCriticalFiniteIndexValue a) -
            squarefreeMobiusCriticalClock sigma
              (squarefreeMobiusCriticalFiniteIndexValue b))) = _
  rw [ENNReal.toReal_ofReal
      (finiteIncidenceProbability_pos
        (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N)) a).le,
    ENNReal.toReal_ofReal
      (finiteIncidenceProbability_pos
        (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N)) b).le]
  unfold mobiusIncidenceGapResponseIntegrand squarefreeMobiusCriticalClock
  have hepsilon : 0 < sigma - 1 := sub_pos.mpr hsigma
  rw [show (sigma - 1) * Real.log (squarefreeMobiusCriticalFiniteIndexValue a) -
      (sigma - 1) * Real.log (squarefreeMobiusCriticalFiniteIndexValue b) =
      (sigma - 1) *
        (Real.log (squarefreeMobiusCriticalFiniteIndexValue a) -
          Real.log (squarefreeMobiusCriticalFiniteIndexValue b)) by ring,
    abs_mul, abs_of_pos hepsilon]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- The finite squarefree packet response is exactly the Hermitian KMS entropy-production
response constructed in `MobiusIncidenceKMSEntropyProduction`. -/
theorem finiteIncidenceKMSResponse_squarefreeMobiusCriticalFiniteIndex
    {sigma : ℝ} (hsigma : 1 < sigma) (N : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    finiteIncidenceKMSResponse sigma (sigma - 1)
        (squarefreeMobiusCriticalFiniteIndexValue (N := N)) z =
      squarefreeMobiusCriticalFiniteGapResponse sigma N z := by
  rw [finiteIncidenceKMSResponse_eq (zero_lt_one.trans hsigma)
    (sub_pos.mpr hsigma)
    (squarefreeMobiusCriticalFiniteIndexValue_pos (N := N))
    squarefreeMobiusCriticalFiniteIndexValue_injective]
  rw [squarefreeMobiusCriticalFiniteGapResponse_eq_sum hsigma N hz]

/-- At fixed `sigma > 1`, the exact finite KMS squarefree responses converge cofinally to the
complete squarefree incidence response. -/
theorem tendsto_finiteIncidenceKMSResponse_squarefreeMobiusCriticalFiniteIndex
    {sigma : ℝ} (hsigma : 1 < sigma) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto
      (fun N : ℕ => finiteIncidenceKMSResponse sigma (sigma - 1)
        (squarefreeMobiusCriticalFiniteIndexValue (N := N)) z)
      atTop (nhds (squarefreeMobiusCriticalGapResponse sigma z)) := by
  have h := tendsto_squarefreeMobiusCriticalTruncatedGapResponse hsigma hz
  apply h.congr'
  filter_upwards with N
  rw [finiteIncidenceKMSResponse_squarefreeMobiusCriticalFiniteIndex hsigma N hz,
    squarefreeMobiusCriticalFiniteGapResponse_eq_truncated hsigma N z]

private theorem tendsto_posImag_nhdsWithin_zero : Tendsto
    (fun eta : ℝ => Complex.I * (eta : ℂ))
    (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℂ)) := by
  have hcont : ContinuousAt (fun eta : ℝ => Complex.I * (eta : ℂ)) 0 := by
    fun_prop
  simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- The universal incidence response cannot agree even eventually along the positive imaginary
axis with the analytic continued prime--archimedean trace germ. -/
theorem not_eventuallyEq_continuedPrimeArchSourceRelativeTrace_universalGapResponse_posImag :
    ¬ (fun eta : ℝ =>
        continuedPrimeArchSourceRelativeTrace (Complex.I * eta)) =ᶠ[
          nhdsWithin 0 (Ioi 0)]
      (fun eta : ℝ =>
        mobiusIncidenceUniversalGapResponse (Complex.I * eta)) := by
  intro heq
  have hmap_mem : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0),
      Complex.I * (eta : ℂ) ∈ ({0} : Set ℂ)ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with eta heta
    simp only [mem_compl_iff, mem_singleton_iff]
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast heta.ne')
  have hmap : Tendsto
      (fun eta : ℝ => Complex.I * (eta : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 ({0} : Set ℂ)ᶜ) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_posImag_nhdsWithin_zero, hmap_mem⟩
  have htraceFinite :=
    _root_.HTGeometry.tendsto_div_sub_of_hasDerivAt_eq_zero
      analyticAt_continuedPrimeArchSourceRelativeTrace.differentiableAt
      continuedPrimeArchSourceRelativeTrace_zero
  have htraceQuotient : Tendsto
      (fun eta : ℝ =>
        continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
          (Complex.I * eta))
      (nhdsWithin 0 (Ioi 0))
      (nhds (deriv continuedPrimeArchSourceRelativeTrace 0)) := by
    simpa only [Function.comp_apply, sub_zero] using htraceFinite.comp hmap
  have hquotientEq :
      (fun eta : ℝ =>
        continuedPrimeArchSourceRelativeTrace (Complex.I * eta) /
          (Complex.I * eta)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun eta : ℝ =>
        mobiusIncidenceUniversalGapResponse (Complex.I * eta) /
          (Complex.I * eta)) :=
    heq.mono (fun eta h => by
      exact congrArg (fun w : ℂ => w / (Complex.I * eta)) h)
  have huniversal := htraceQuotient.congr' hquotientEq
  exact
    (not_tendsto_mobiusIncidenceUniversalGapResponse_I_mul_div_nhds
      (deriv continuedPrimeArchSourceRelativeTrace 0)) huniversal

/-- There is no punctured upper neighborhood of the centered origin on which the universal
incidence response equals the analytic continued prime--archimedean trace. -/
theorem not_exists_upperNeighborhood_continuedPrimeArchSourceRelativeTrace_eq_universalGapResponse :
    ¬ ∃ U : Set ℂ, U ∈ nhds (0 : ℂ) ∧
      ∀ z ∈ U, 0 < z.im →
        continuedPrimeArchSourceRelativeTrace z =
          mobiusIncidenceUniversalGapResponse z := by
  rintro ⟨U, hU, hagree⟩
  have hmem : ∀ᶠ eta : ℝ in nhdsWithin 0 (Ioi 0),
      Complex.I * (eta : ℂ) ∈ U := tendsto_posImag_nhdsWithin_zero hU
  have heq :
      (fun eta : ℝ =>
        continuedPrimeArchSourceRelativeTrace (Complex.I * eta)) =ᶠ[
          nhdsWithin 0 (Ioi 0)]
      (fun eta : ℝ =>
        mobiusIncidenceUniversalGapResponse (Complex.I * eta)) := by
    filter_upwards [hmem, self_mem_nhdsWithin] with eta hetaU heta
    exact hagree _ hetaU (by simpa using heta)
  exact
    not_eventuallyEq_continuedPrimeArchSourceRelativeTrace_universalGapResponse_posImag heq

end RHTower
