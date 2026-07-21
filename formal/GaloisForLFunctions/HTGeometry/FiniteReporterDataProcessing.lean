import GaloisForLFunctions.HTGeometry.FiniteReporterConditionalInformation

/-!
# Data processing for finite derivative-clock reporters

A downstream linear measurement, coarse graining, or decoder cannot recreate a derivative
direction already erased by a reporter.  The previous-observation space of a postprocessed panel
is exactly the linear image of the original previous-observation space.  Consequently zero
conditional information survives every linear postprocessing, while an injective postprocessor
preserves the zero/positive alternative exactly.

For a bounded postprocessor `D`, the quantitative data-processing value is

`I_N(D ∘ R) ≤ ‖D‖² I_N(R)`.

Thus a contraction cannot increase conditional clock information.  These are static value
relations between observation structures; no temporal channel evolution is assumed.
-/

open scoped InnerProductSpace
open InnerProductSpace

namespace HTGeometry

noncomputable section

open GaloisForLFunctions Module

/-- Postprocessing maps the preceding reported-observable space exactly onto the preceding space
of the composite reporter. -/
theorem finiteDerivativeReporterPreviousSpace_postcomp
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    finiteDerivativeReporterPreviousSpace N f (decode.comp report) =
      (finiteDerivativeReporterPreviousSpace N f report).map decode := by
  unfold finiteDerivativeReporterPreviousSpace
  rw [Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_range, Set.mem_image, LinearMap.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨report (iteratedDeriv (i : ℕ) f), ⟨i, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- **Zero-information data processing.**  Once the new derivative reading is redundant, no
linear downstream operation can make it conditionally informative. -/
theorem finiteDerivativeReporterConditionalInformation_eq_zero_postcomp
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    {N : ℕ} {f : ℂ → ℂ}
    {report : (ℂ → ℂ) →ₗ[ℂ] Y} (decode : Y →ₗ[ℂ] Z)
    (hzero : finiteDerivativeReporterConditionalInformation N f report = 0) :
    finiteDerivativeReporterConditionalInformation N f (decode.comp report) = 0 := by
  rw [finiteDerivativeReporterConditionalInformation_eq_zero_iff] at hzero ⊢
  rw [finiteDerivativeReporterPreviousSpace_postcomp]
  exact ⟨report (iteratedDeriv N f), hzero, rfl⟩

/-- Injective postprocessing preserves the zero conditional-information locus exactly. -/
theorem finiteDerivativeReporterConditionalInformation_postcomp_eq_zero_iff
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hdecode : Function.Injective decode) :
    finiteDerivativeReporterConditionalInformation N f (decode.comp report) = 0 ↔
      finiteDerivativeReporterConditionalInformation N f report = 0 := by
  constructor
  · intro hpost
    rw [finiteDerivativeReporterConditionalInformation_eq_zero_iff] at hpost ⊢
    rw [finiteDerivativeReporterPreviousSpace_postcomp] at hpost
    obtain ⟨y, hy, hyeq⟩ := hpost
    have heq : y = report (iteratedDeriv N f) := by
      apply hdecode
      exact hyeq
    simpa only [heq] using hy
  · exact finiteDerivativeReporterConditionalInformation_eq_zero_postcomp decode

/-- Injective postprocessing preserves strict conditional observability exactly. -/
theorem finiteDerivativeReporterConditionalInformation_postcomp_pos_iff
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hdecode : Function.Injective decode) :
    0 < finiteDerivativeReporterConditionalInformation N f (decode.comp report) ↔
      0 < finiteDerivativeReporterConditionalInformation N f report := by
  have hpost := finiteDerivativeReporterConditionalInformation_nonneg N f (decode.comp report)
  have hpre := finiteDerivativeReporterConditionalInformation_nonneg N f report
  have hzero := finiteDerivativeReporterConditionalInformation_postcomp_eq_zero_iff
    N f report decode hdecode
  constructor
  · intro hpostpos
    have hprene : finiteDerivativeReporterConditionalInformation N f report ≠ 0 := by
      intro hprezero
      exact (ne_of_gt hpostpos) (hzero.mpr hprezero)
    exact lt_of_le_of_ne hpre (Ne.symm hprene)
  · intro hprepos
    have hpostne : finiteDerivativeReporterConditionalInformation N f
        (decode.comp report) ≠ 0 := by
      intro hpostzero
      exact (ne_of_gt hprepos) (hzero.mp hpostzero)
    exact lt_of_le_of_ne hpost (Ne.symm hpostne)

/-- **Quantitative conditional-information data processing.**  A bounded downstream map can
increase the innovation norm by at most its operator norm. -/
theorem finiteDerivativeReporterConditionalInformation_postcomp_le
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →L[ℂ] Z) :
    finiteDerivativeReporterConditionalInformation N f
        (decode.toLinearMap.comp report) ≤
      ‖decode‖ ^ 2 * finiteDerivativeReporterConditionalInformation N f report := by
  let wY : ℕ → Y := fun k => report (iteratedDeriv k f)
  let wZ : ℕ → Z := fun k => decode (wY k)
  let correction : Y := wY N - gramSchmidt ℂ wY N
  have hcorrectionY : correction ∈ Submodule.span ℂ (wY '' Set.Iio N) := by
    rw [← span_gramSchmidt_Iio ℂ wY N]
    change wY N - gramSchmidt ℂ wY N ∈
      Submodule.span ℂ (gramSchmidt ℂ wY '' Set.Iio N)
    exact GaloisForLFunctions.HTGeometry.sub_gramSchmidt_mem_span wY N
  have hcorrectionMap : decode correction ∈
      (Submodule.span ℂ (wY '' Set.Iio N)).map decode.toLinearMap :=
    ⟨correction, hcorrectionY, rfl⟩
  have hsets : (decode.toLinearMap : Y → Z) '' (wY '' Set.Iio N) =
      wZ '' Set.Iio N := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨wY i, ⟨i, hi, rfl⟩, rfl⟩
  have hcorrectionZ : decode correction ∈ Submodule.span ℂ (wZ '' Set.Iio N) := by
    rw [Submodule.map_span, hsets] at hcorrectionMap
    exact hcorrectionMap
  have hcorrectionZ' : decode correction ∈
      Submodule.span ℂ (gramSchmidt ℂ wZ '' Set.Iio N) := by
    rw [span_gramSchmidt_Iio ℂ wZ N]
    exact hcorrectionZ
  have hmin := GaloisForLFunctions.HTGeometry.norm_gramSchmidt_le_of_mem_span
    wZ N hcorrectionZ'
  have hdiff : wZ N - decode correction = decode (gramSchmidt ℂ wY N) := by
    dsimp only [wZ, correction]
    rw [map_sub]
    abel
  rw [hdiff] at hmin
  have hop := decode.le_opNorm (gramSchmidt ℂ wY N)
  unfold finiteDerivativeReporterConditionalInformation
    finiteDerivativeReporterInnovation
  change ‖gramSchmidt ℂ wZ N‖ ^ 2 ≤
    ‖decode‖ ^ 2 * ‖gramSchmidt ℂ wY N‖ ^ 2
  nlinarith [norm_nonneg (gramSchmidt ℂ wZ N),
    norm_nonneg (decode (gramSchmidt ℂ wY N)),
    norm_nonneg decode, norm_nonneg (gramSchmidt ℂ wY N)]

/-- Contractive data processing cannot increase conditional clock information. -/
theorem finiteDerivativeReporterConditionalInformation_postcomp_le_of_norm_le_one
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →L[ℂ] Z)
    (hdecode : ‖decode‖ ≤ 1) :
    finiteDerivativeReporterConditionalInformation N f
        (decode.toLinearMap.comp report) ≤
      finiteDerivativeReporterConditionalInformation N f report := by
  have hbound := finiteDerivativeReporterConditionalInformation_postcomp_le
    N f report decode
  have hinfo := finiteDerivativeReporterConditionalInformation_nonneg N f report
  have hnorm : 0 ≤ ‖decode‖ := norm_nonneg _
  have hnormsq : ‖decode‖ ^ 2 ≤ 1 := by nlinarith
  calc
    finiteDerivativeReporterConditionalInformation N f
        (decode.toLinearMap.comp report) ≤
        ‖decode‖ ^ 2 * finiteDerivativeReporterConditionalInformation N f report := hbound
    _ ≤ 1 * finiteDerivativeReporterConditionalInformation N f report :=
      mul_le_mul_of_nonneg_right hnormsq hinfo
    _ = finiteDerivativeReporterConditionalInformation N f report := one_mul _

/-- A postprocessed block cannot be informationally complete unless the original reporter block
was already complete. -/
theorem finiteDerivativeReporterGram_det_ne_zero_of_postcomp
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hpost : (finiteDerivativeReporterGram N f (decode.comp report)).det ≠ 0) :
    (finiteDerivativeReporterGram N f report).det ≠ 0 := by
  rw [finiteDerivativeReporterGram_det_ne_zero_iff_injective] at hpost ⊢
  intro c d hcd
  apply hpost
  change decode (finiteDerivativeReporterMap N f report c) =
    decode (finiteDerivativeReporterMap N f report d)
  exact congrArg decode hcd

/-- Injective postprocessing preserves finite-block informational completeness exactly. -/
theorem finiteDerivativeReporterGram_postcomp_det_ne_zero_iff
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hdecode : Function.Injective decode) :
    (finiteDerivativeReporterGram N f (decode.comp report)).det ≠ 0 ↔
      (finiteDerivativeReporterGram N f report).det ≠ 0 := by
  constructor
  · exact finiteDerivativeReporterGram_det_ne_zero_of_postcomp N f report decode
  · rw [finiteDerivativeReporterGram_det_ne_zero_iff_injective,
      finiteDerivativeReporterGram_det_ne_zero_iff_injective]
    intro hpre c d hcd
    apply hpre
    apply hdecode
    exact hcd

/-- Postprocessed finite-jet coefficient reporting is literal linear-map composition. -/
theorem finiteDerivativeReporterMap_postcomp
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    finiteDerivativeReporterMap N f (decode.comp report) =
      decode.comp (finiteDerivativeReporterMap N f report) := by
  rfl

/-- Downstream linear processing can only enlarge the blind coefficient subspace. -/
theorem ker_finiteDerivativeReporterMap_le_postcomp
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    LinearMap.ker (finiteDerivativeReporterMap N f report) ≤
      LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  rw [finiteDerivativeReporterMap_postcomp, LinearMap.comp_apply, hc, map_zero]

/-- **Exact finite-reporter capacity data processing.**  A downstream decoder cannot increase
visible coefficient rank or decrease blind nullity, and every lost visible dimension becomes
exactly one additional blind dimension. -/
theorem finiteDerivativeReporterMap_postcomp_capacity_balance
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap N f (decode.comp report))) ≤
        finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f report)) ∧
      finrank ℂ (LinearMap.ker (finiteDerivativeReporterMap N f report)) ≤
        finrank ℂ (LinearMap.ker
          (finiteDerivativeReporterMap N f (decode.comp report))) ∧
      finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f report)) -
          finrank ℂ (LinearMap.range
            (finiteDerivativeReporterMap N f (decode.comp report))) =
        finrank ℂ (LinearMap.ker
            (finiteDerivativeReporterMap N f (decode.comp report))) -
          finrank ℂ (LinearMap.ker (finiteDerivativeReporterMap N f report)) := by
  have hker :
      finrank ℂ (LinearMap.ker (finiteDerivativeReporterMap N f report)) ≤
        finrank ℂ (LinearMap.ker
          (finiteDerivativeReporterMap N f (decode.comp report))) :=
    Submodule.finrank_mono
      (ker_finiteDerivativeReporterMap_le_postcomp N f report decode)
  have hpre := finiteDerivativeReporterMap_rank_nullity N f report
  have hpost := finiteDerivativeReporterMap_rank_nullity N f (decode.comp report)
  omega

/-- Injective postprocessing preserves both visible rank and the complete blind coefficient
subspace. -/
theorem finiteDerivativeReporterMap_postcomp_capacity_eq_of_injective
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hdecode : Function.Injective decode) :
    finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap N f (decode.comp report))) =
        finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f report)) ∧
      LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) =
        LinearMap.ker (finiteDerivativeReporterMap N f report) := by
  have hker :
      LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) =
        LinearMap.ker (finiteDerivativeReporterMap N f report) := by
    apply le_antisymm
    · intro c hc
      rw [LinearMap.mem_ker] at hc ⊢
      apply hdecode
      simpa [finiteDerivativeReporterMap_postcomp] using hc
    · exact ker_finiteDerivativeReporterMap_le_postcomp N f report decode
  have hpre := finiteDerivativeReporterMap_rank_nullity N f report
  have hpost := finiteDerivativeReporterMap_rank_nullity N f (decode.comp report)
  constructor
  · rw [hker] at hpost
    omega
  · exact hker

/-- Every coefficient direction newly erased by a decoder is a genuinely nonzero source packet
which was visible before decoding and vanishes afterwards. -/
theorem finiteDerivativeReporterMap_postcomp_newBlindPacket
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {N : ℕ} {f : ℂ → ℂ}
    (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (finiteDerivativeReporterMap N f (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker (finiteDerivativeReporterMap N f report)) :
    finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) ≠ 0 ∧
      decode (report (finiteDerivativeReporterPacket c f)) = 0 := by
  have hc0 : c ≠ 0 := by
    intro hc
    subst c
    exact hcpre (by simp)
  obtain ⟨hpacket, hdecode⟩ :=
    finiteDerivativeReporterMap_nonzero_packet_of_mem_ker
      hf (decode.comp report) hcpost hc0
  refine ⟨hpacket, ?_, ?_⟩
  · intro hreport
    apply hcpre
    simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hreport
  · simpa using hdecode

/-- **Same-witness finite-reporter data-processing collapse.**  For a genuine infinite derivative
clock, some derivative order no larger than reporter dimension is new at the source but redundant
both before and after every downstream linear decoder. -/
theorem exists_finiteDerivativeReporterConditionalInformation_dataProcessing_collapse
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    {f : ℂ → ℂ} (hf : ConstantCoefficientDifferentiallyTranscendental f)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) :
    ∃ k : ℕ, k ≤ finrank ℂ Y ∧
      finiteDerivativeReporterConditionalInformation k f report = 0 ∧
      finiteDerivativeReporterConditionalInformation k f (decode.comp report) = 0 ∧
      report (iteratedDeriv k f) ∈
        finiteDerivativeReporterPreviousSpace k f report ∧
      decode (report (iteratedDeriv k f)) ∈
        finiteDerivativeReporterPreviousSpace k f (decode.comp report) ∧
      iteratedDeriv k f ∉ Submodule.span ℂ
        (Set.range fun i : Fin k => iteratedDeriv (i : ℕ) f) := by
  obtain ⟨k, hk, hzero, hreported, hsource⟩ :=
    exists_finiteDerivativeReporterConditionalInformation_collapse hf report
  have hpostzero :=
    finiteDerivativeReporterConditionalInformation_eq_zero_postcomp decode hzero
  have hpostreported :=
    (finiteDerivativeReporterConditionalInformation_eq_zero_iff
      k f (decode.comp report)).mp hpostzero
  exact ⟨k, hk, hzero, hpostzero, hreported, hpostreported, hsource⟩

end

end HTGeometry
