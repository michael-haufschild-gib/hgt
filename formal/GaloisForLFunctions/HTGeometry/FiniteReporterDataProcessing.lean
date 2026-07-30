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

open scoped BigOperators InnerProductSpace
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
    simpa only [heq] using! hy
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

/-- **Recoverable postprocessing preserves exact finite-reporter capacity.**  A decoder need not
be injective on its whole domain: a left recovery on the image of the source reporter already
preserves every finite coefficient kernel and visible rank. -/
theorem finiteDerivativeReporterMap_postcomp_capacity_eq_of_recovery
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z) (recover : Z →ₗ[ℂ] Y)
    (hrecover : recover.comp (decode.comp report) = report) :
    finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap N f (decode.comp report))) =
        finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f report)) ∧
      LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) =
        LinearMap.ker (finiteDerivativeReporterMap N f report) := by
  have hrecoverMap :
      recover.comp (finiteDerivativeReporterMap N f (decode.comp report)) =
        finiteDerivativeReporterMap N f report := by
    rw [← finiteDerivativeReporterMap_postcomp, hrecover]
  have hker :
      LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) =
        LinearMap.ker (finiteDerivativeReporterMap N f report) := by
    apply le_antisymm
    · intro c hc
      rw [LinearMap.mem_ker] at hc ⊢
      calc
        finiteDerivativeReporterMap N f report c =
            (recover.comp
              (finiteDerivativeReporterMap N f (decode.comp report))) c := by
              exact congrArg
                (fun T : (Fin N → ℂ) →ₗ[ℂ] Y => T c) hrecoverMap.symm
        _ = recover (finiteDerivativeReporterMap N f (decode.comp report) c) := rfl
        _ = recover 0 := by rw [hc]
        _ = 0 := map_zero recover
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
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    {c : Fin N → ℂ}
    (hcpost : c ∈ LinearMap.ker
      (finiteDerivativeReporterMap N f (decode.comp report)))
    (hcpre : c ∉ LinearMap.ker (finiteDerivativeReporterMap N f report)) :
    finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) ≠ 0 ∧
      decode (report (finiteDerivativeReporterPacket c f)) = 0 := by
  have hreport : report (finiteDerivativeReporterPacket c f) ≠ 0 := by
    intro hreport
    apply hcpre
    simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hreport
  have hpacket : finiteDerivativeReporterPacket c f ≠ 0 := by
    intro hpacket
    apply hreport
    rw [hpacket, map_zero]
  have hdecode : decode (report (finiteDerivativeReporterPacket c f)) = 0 := by
    rw [LinearMap.mem_ker] at hcpost
    simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis] using hcpost
  exact ⟨hpacket, hreport, hdecode⟩

/-- **Strict capacity loss has a genuine packet witness.**  If downstream decoding strictly
reduces visible coefficient rank, some coefficient direction enters the decoded kernel.  Its
synthesized source packet is nonzero, was visible before decoding, and is erased afterwards. -/
theorem exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_finrank_lt
    {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hdrop : finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap N f (decode.comp report))) <
      finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f report))) :
    ∃ c : Fin N → ℂ,
      c ∈ LinearMap.ker
          (finiteDerivativeReporterMap N f (decode.comp report)) ∧
      c ∉ LinearMap.ker (finiteDerivativeReporterMap N f report) ∧
      finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) ≠ 0 ∧
      decode (report (finiteDerivativeReporterPacket c f)) = 0 := by
  have hpre := finiteDerivativeReporterMap_rank_nullity N f report
  have hpost := finiteDerivativeReporterMap_rank_nullity N f (decode.comp report)
  have hkerFinrank :
      finrank ℂ (LinearMap.ker (finiteDerivativeReporterMap N f report)) <
        finrank ℂ (LinearMap.ker
          (finiteDerivativeReporterMap N f (decode.comp report))) := by
    omega
  have hkerLe := ker_finiteDerivativeReporterMap_le_postcomp N f report decode
  have hkerNe :
      LinearMap.ker (finiteDerivativeReporterMap N f report) ≠
        LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) := by
    intro hker
    rw [hker] at hkerFinrank
    exact Nat.lt_irrefl _ hkerFinrank
  have hkerLt :
      LinearMap.ker (finiteDerivativeReporterMap N f report) <
        LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) :=
    lt_of_le_of_ne hkerLe hkerNe
  obtain ⟨_, c, hcpost, hcpre⟩ :=
    (SetLike.lt_iff_le_and_exists).mp hkerLt
  obtain ⟨hpacket, hreport, hdecode⟩ :=
    finiteDerivativeReporterMap_postcomp_newBlindPacket report decode hcpost hcpre
  exact ⟨c, hcpost, hcpre, hpacket, hreport, hdecode⟩

/-- **Gram singularity created by decoding has a genuine lost-packet witness.**  If the original
finite reporter Gram matrix is nonsingular but its decoded Gram matrix is singular, then decoding
strictly loses visible coefficient rank.  A nonzero source packet witnesses that loss: it was
visible before decoding and is erased afterwards. -/
theorem exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_gram_det_transition
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hpre : (finiteDerivativeReporterGram N f report).det ≠ 0)
    (hpost : (finiteDerivativeReporterGram N f (decode.comp report)).det = 0) :
    ∃ c : Fin N → ℂ,
      c ∈ LinearMap.ker
          (finiteDerivativeReporterMap N f (decode.comp report)) ∧
      c ∉ LinearMap.ker (finiteDerivativeReporterMap N f report) ∧
      finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) ≠ 0 ∧
      decode (report (finiteDerivativeReporterPacket c f)) = 0 := by
  have hpreInjective : Function.Injective (finiteDerivativeReporterMap N f report) :=
    (finiteDerivativeReporterGram_det_ne_zero_iff_injective N f report).mp hpre
  have hpostNotInjective :
      ¬ Function.Injective (finiteDerivativeReporterMap N f (decode.comp report)) := by
    intro hpostInjective
    exact (finiteDerivativeReporterGram_det_ne_zero_iff_injective
      N f (decode.comp report)).mpr hpostInjective hpost
  have hpreRank :
      finrank ℂ (LinearMap.range (finiteDerivativeReporterMap N f report)) = N := by
    simpa using LinearMap.finrank_range_of_inj hpreInjective
  have hpostKerNe :
      LinearMap.ker (finiteDerivativeReporterMap N f (decode.comp report)) ≠ ⊥ := by
    intro hker
    apply hpostNotInjective
    exact LinearMap.ker_eq_bot.mp hker
  have hpostKerPos :
      0 < finrank ℂ (LinearMap.ker
        (finiteDerivativeReporterMap N f (decode.comp report))) := by
    exact (Submodule.one_le_finrank_iff.mpr hpostKerNe)
  have hpostRankNullity :=
    finiteDerivativeReporterMap_rank_nullity N f (decode.comp report)
  apply exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_finrank_lt
  rw [hpreRank]
  omega

/-- **A lost sequential innovation has a normalized packet witness.**  Suppose the `N`-th reading
is new before decoding but becomes conditionally redundant afterward.  Then a newly blind
coefficient packet can be chosen with newest coefficient
exactly `-1`; hence the witness records loss of that specific innovation, not merely an earlier
rank defect.  This local positive-innovation premise is strictly weaker than requiring the whole
preceding reporter Gram block to be nonsingular.  No differential-transcendence premise on the
source is needed. -/
theorem exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_conditionalInformation_eq_zero
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hpre : 0 < finiteDerivativeReporterConditionalInformation N f report)
    (hpost : finiteDerivativeReporterConditionalInformation N f
      (decode.comp report) = 0) :
    ∃ c : Fin (N + 1) → ℂ,
      c (Fin.last N) = -1 ∧
      c ∈ LinearMap.ker
          (finiteDerivativeReporterMap (N + 1) f (decode.comp report)) ∧
      c ∉ LinearMap.ker (finiteDerivativeReporterMap (N + 1) f report) ∧
      finiteDerivativeReporterPacket c f ≠ 0 ∧
      report (finiteDerivativeReporterPacket c f) ≠ 0 ∧
      decode (report (finiteDerivativeReporterPacket c f)) = 0 := by
  have hmem :=
    (finiteDerivativeReporterConditionalInformation_eq_zero_iff
      N f (decode.comp report)).mp hpost
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have ha' :
      ∑ i, a i • decode (report (iteratedDeriv (i : ℕ) f)) =
        decode (report (iteratedDeriv N f)) := by
    simpa using ha
  let c : Fin (N + 1) → ℂ := Fin.lastCases (-1) a
  have hclast : c (Fin.last N) = -1 := by
    simp [c]
  have hcpost : c ∈ LinearMap.ker
      (finiteDerivativeReporterMap (N + 1) f (decode.comp report)) := by
    rw [LinearMap.mem_ker]
    simp [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis,
      finiteDerivativeReporterPacket, c, Fin.sum_univ_castSucc, ha']
  have hpreNew : report (iteratedDeriv N f) ∉
      finiteDerivativeReporterPreviousSpace N f report :=
    (finiteDerivativeReporterConditionalInformation_pos_iff N f report).mp hpre
  have hcpre : c ∉ LinearMap.ker
      (finiteDerivativeReporterMap (N + 1) f report) := by
    rw [LinearMap.mem_ker]
    intro hc
    apply hpreNew
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    refine ⟨a, ?_⟩
    have hc' :
        (∑ i, a i • report (iteratedDeriv (i : ℕ) f)) +
          -report (iteratedDeriv N f) = 0 := by
      simpa [finiteDerivativeReporterMap, finiteDerivativeJetSynthesis,
        finiteDerivativeReporterPacket, c, Fin.sum_univ_castSucc] using hc
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg] using hc'
  obtain ⟨hpacket, hreport, hdecode⟩ :=
    finiteDerivativeReporterMap_postcomp_newBlindPacket report decode hcpost hcpre
  exact ⟨c, hclast, hcpost, hcpre, hpacket, hreport, hdecode⟩

/-- **Local innovation loss forces global capacity loss.**  If the newest derivative reading
raises visible rank before decoding but is redundant afterward, then decoding strictly reduces
visible coefficient rank at resolution `N + 1`.  Earlier readings need not be independent. -/
theorem finiteDerivativeReporterMap_postcomp_finrank_lt_of_conditionalInformation
    {Y Z : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
    [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (N : ℕ) (f : ℂ → ℂ)
    (report : (ℂ → ℂ) →ₗ[ℂ] Y) (decode : Y →ₗ[ℂ] Z)
    (hpre : 0 < finiteDerivativeReporterConditionalInformation N f report)
    (hpost : finiteDerivativeReporterConditionalInformation N f
      (decode.comp report) = 0) :
    finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap (N + 1) f (decode.comp report))) <
      finrank ℂ (LinearMap.range
        (finiteDerivativeReporterMap (N + 1) f report)) := by
  obtain ⟨c, _, hcpost, hcpre, _⟩ :=
    exists_finiteDerivativeReporterMap_postcomp_newBlindPacket_of_conditionalInformation_eq_zero
      N f report decode hpre hpost
  have hkerLe :=
    ker_finiteDerivativeReporterMap_le_postcomp (N + 1) f report decode
  have hkerNe :
      LinearMap.ker (finiteDerivativeReporterMap (N + 1) f report) ≠
        LinearMap.ker
          (finiteDerivativeReporterMap (N + 1) f (decode.comp report)) := by
    intro hker
    apply hcpre
    rw [hker]
    exact hcpost
  have hkerLt :
      LinearMap.ker (finiteDerivativeReporterMap (N + 1) f report) <
        LinearMap.ker
          (finiteDerivativeReporterMap (N + 1) f (decode.comp report)) :=
    lt_of_le_of_ne hkerLe hkerNe
  have hkerFinrankLt := Submodule.finrank_lt_finrank_of_lt hkerLt
  have hpreRankNullity := finiteDerivativeReporterMap_rank_nullity (N + 1) f report
  have hpostRankNullity :=
    finiteDerivativeReporterMap_rank_nullity (N + 1) f (decode.comp report)
  omega

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
