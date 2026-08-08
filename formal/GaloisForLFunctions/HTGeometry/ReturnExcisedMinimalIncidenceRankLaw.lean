import GaloisForLFunctions.HTGeometry.QuenchedReplicaReturnExcisionLaw

/-!
# Return-excised minimal incidence-rank law

After removing a measurable return set, compress the occupied replica target
span further to the span of the surviving projected source sheets.  This is
the unique least subspace preserving every off-return target projection.  Its
dimension replaces the full occupied-target Hilbert number in the quenched
coarea bound, while the off-return pair action remains exactly unchanged.

Source measure is never pushed forward or quotiented: fibre-sheet
multiplicity and occupied endpoint image are retained inside the original
double-source integral.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable def returnExcisedReplicaIncidenceSpan
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    Submodule ℂ (EuclideanSpace ℂ (Fin r → α)) :=
  Submodule.span ℂ
    {v | ∃ x, x ∈ returnSetᶜ ∧
      v = (replicaTargetSpan r target).starProjection
        (finitePureTensorPowerEuclidean r (state x))}

theorem returnExcisedReplicaIncidenceSpan_le_targetSpan
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceSpan r target state returnSet ≤
      replicaTargetSpan r target := by
  apply Submodule.span_le.2
  rintro v ⟨x, hx, rfl⟩
  exact Submodule.coe_mem _

theorem targetProjection_mem_returnExcisedReplicaIncidenceSpan
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) {x : X} (hx : x ∈ returnSetᶜ) :
    (replicaTargetSpan r target).starProjection
        (finitePureTensorPowerEuclidean r (state x)) ∈
      returnExcisedReplicaIncidenceSpan r target state returnSet := by
  apply Submodule.subset_span
  exact ⟨x, hx, rfl⟩

theorem returnExcisedReplicaIncidenceSpan_projection_eq_targetProjection
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) {x : X} (hx : x ∈ returnSetᶜ) :
    (returnExcisedReplicaIncidenceSpan r target state returnSet).starProjection
        (finitePureTensorPowerEuclidean r (state x)) =
      (replicaTargetSpan r target).starProjection
        (finitePureTensorPowerEuclidean r (state x)) := by
  let U := returnExcisedReplicaIncidenceSpan r target state returnSet
  let S := replicaTargetSpan r target
  let u := finitePureTensorPowerEuclidean r (state x)
  have hUS : U ≤ S :=
    returnExcisedReplicaIncidenceSpan_le_targetSpan
      r target state returnSet
  have hmem : S.starProjection u ∈ U :=
    targetProjection_mem_returnExcisedReplicaIncidenceSpan
      r target state returnSet hx
  calc
    U.starProjection u = U.starProjection (S.starProjection u) := by
      have hcomp := U.starProjection_comp_starProjection_of_le hUS
      have happ := DFunLike.congr_fun hcomp u
      exact happ.symm
    _ = S.starProjection u := U.starProjection_eq_self_iff.mpr hmem

theorem returnExcisedReplicaIncidenceSpan_le_of_preserves_targetProjection
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X)
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (hW : ∀ x ∈ returnSetᶜ,
      W.starProjection (finitePureTensorPowerEuclidean r (state x)) =
        (replicaTargetSpan r target).starProjection
          (finitePureTensorPowerEuclidean r (state x))) :
    returnExcisedReplicaIncidenceSpan r target state returnSet ≤ W := by
  apply Submodule.span_le.2
  rintro v ⟨x, hx, rfl⟩
  rw [← hW x hx]
  rw [Submodule.starProjection_apply]
  exact Submodule.coe_mem _

theorem returnExcisedReplicaIncidenceSpan_eq_of_targetSpan_eq
    {X C D α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (target' : D → α → ℂ)
    (state : X → α → ℂ) (returnSet : Set X)
    (hspan : replicaTargetSpan r target = replicaTargetSpan r target') :
    returnExcisedReplicaIncidenceSpan r target state returnSet =
      returnExcisedReplicaIncidenceSpan r target' state returnSet := by
  simp only [returnExcisedReplicaIncidenceSpan, hspan]

theorem returnExcisedReplicaIncidenceSpan_duplicated
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceSpan r
        (duplicatedReplicaTarget target) state returnSet =
      returnExcisedReplicaIncidenceSpan r target state returnSet :=
  returnExcisedReplicaIncidenceSpan_eq_of_targetSpan_eq r
    (duplicatedReplicaTarget target) target state returnSet
      (replicaTargetSpan_duplicated r target)

theorem returnExcisedReplicaIncidenceSpan_withZero
    {X C α : Type*} [Fintype α] {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceSpan r
        (replicaTargetWithZero target) state returnSet =
      returnExcisedReplicaIncidenceSpan r target state returnSet :=
  returnExcisedReplicaIncidenceSpan_eq_of_targetSpan_eq r
    (replicaTargetWithZero target) target state returnSet
      (replicaTargetSpan_withZero hr target)

noncomputable def finiteCoordinateEnergy
    {X ι : Type*} [Fintype ι] (a : X → ι → ℂ) (x : X) : ℝ :=
  ∑ i, ‖a x i‖ ^ 2

theorem re_finiteCoordinateCovariance_diag
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (a : X → ι → ℂ) (i : ι) :
    (finiteCoordinateCovariance μ a i i).re =
      ∫ x, ‖a x i‖ ^ 2 ∂μ := by
  unfold finiteCoordinateCovariance
  rw [show
      (fun x => star (a x i) * a x i) =
        (fun x => ((‖a x i‖ ^ 2 : ℝ) : ℂ)) by
    funext x
    rw [show star (a x i) * a x i =
      ((starRingEnd ℂ) (a x i)) * a x i from rfl, RCLike.conj_mul]
    norm_cast]
  exact (congrArg Complex.re
    (@integral_ofReal X _ μ ℂ _ (fun x => ‖a x i‖ ^ 2))).trans
      (Complex.ofReal_re _)

theorem integral_finiteCoordinateEnergy_eq_sum_re_covariance_diag
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (a : X → ι → ℂ)
    (hsq : ∀ i, Integrable (fun x => ‖a x i‖ ^ 2) μ) :
    (∫ x, finiteCoordinateEnergy a x ∂μ) =
      ∑ i, (finiteCoordinateCovariance μ a i i).re := by
  calc
    (∫ x, finiteCoordinateEnergy a x ∂μ) =
        ∫ x, ∑ i, ‖a x i‖ ^ 2 ∂μ := rfl
    _ = ∑ i, ∫ x, ‖a x i‖ ^ 2 ∂μ := by
      rw [integral_finsetSum Finset.univ]
      exact fun i _ => hsq i
    _ = ∑ i, (finiteCoordinateCovariance μ a i i).re := by
      apply Finset.sum_congr rfl
      intro i _
      exact (re_finiteCoordinateCovariance_diag μ a i).symm

theorem sq_integral_finiteCoordinateEnergy_le_card_mul_collision
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (a : X → ι → ℂ)
    (hsq : ∀ i, Integrable (fun x => ‖a x i‖ ^ 2) μ) :
    (∫ x, finiteCoordinateEnergy a x ∂μ) ^ 2 ≤
      (Fintype.card ι : ℝ) *
        ∑ i, ∑ j, ‖finiteCoordinateCovariance μ a i j‖ ^ 2 := by
  rw [integral_finiteCoordinateEnergy_eq_sum_re_covariance_diag μ a hsq]
  exact sq_sum_re_diag_le_card_mul_matrix_hilbertSchmidt
    (finiteCoordinateCovariance μ a)

theorem measureReal_restrict_event_mul_threshold_sq_le_coordinateCollision
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (E returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (a : X → ι → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold)
    (hcapture : E ∩ returnSetᶜ ⊆
      {x | threshold ≤ finiteCoordinateEnergy a x})
    (hsq : ∀ i, Integrable (fun x => ‖a x i‖ ^ 2)
      (μ.restrict returnSetᶜ)) :
    (((μ.restrict returnSetᶜ).real E * threshold) ^ 2) ≤
      (Fintype.card ι : ℝ) *
        ∑ i, ∑ j,
          ‖finiteCoordinateCovariance (μ.restrict returnSetᶜ) a i j‖ ^ 2 := by
  let ν := μ.restrict returnSetᶜ
  let q := finiteCoordinateEnergy a
  let Q : Set X := {x | threshold ≤ q x}
  have hmeas : ν.real E ≤ ν.real Q := by
    calc
      ν.real E = μ.real (E ∩ returnSetᶜ) := by
        exact measureReal_restrict_apply' hreturn.compl
      _ ≤ μ.real (Q ∩ returnSetᶜ) := by
        exact measureReal_mono
          (fun x hx => ⟨hcapture hx, hx.2⟩) (measure_ne_top μ _)
      _ = ν.real Q := by
        exact (measureReal_restrict_apply' hreturn.compl).symm
  have hqint : Integrable q ν := by
    apply integrable_finsetSum Finset.univ
    intro i _
    exact hsq i
  have hqnonneg : 0 ≤ᵐ[ν] q :=
    Filter.Eventually.of_forall fun x =>
      Finset.sum_nonneg fun i _ => sq_nonneg ‖a x i‖
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hqint threshold
  have hscaled : ν.real E * threshold ≤ ∫ x, q x ∂ν := by
    calc
      ν.real E * threshold ≤ ν.real Q * threshold := by gcongr
      _ = threshold * ν.real Q := mul_comm _ _
      _ ≤ ∫ x, q x ∂ν := hmarkov
  have hsquare : (ν.real E * threshold) ^ 2 ≤
      (∫ x, q x ∂ν) ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg measureReal_nonneg hthreshold.le) hscaled 2
  exact hsquare.trans
    (sq_integral_finiteCoordinateEnergy_le_card_mul_collision ν a hsq)

noncomputable def returnExcisedFiniteCoordinateIncidenceAction
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (a : X → ι → ℂ) (returnSet : Set X) : ℝ :=
  ∫ p in (returnSetᶜ ×ˢ returnSetᶜ),
    finiteCoordinatePairKernel a p ∂(μ.prod μ)

theorem returnExcisedFiniteCoordinateIncidenceAction_eq_restrictProduct
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [SFinite μ] (a : X → ι → ℂ)
    (returnSet : Set X) :
    returnExcisedFiniteCoordinateIncidenceAction μ a returnSet =
      ∫ p, finiteCoordinatePairKernel a p
        ∂((μ.restrict returnSetᶜ).prod (μ.restrict returnSetᶜ)) := by
  unfold returnExcisedFiniteCoordinateIncidenceAction
  rw [Measure.prod_restrict]

theorem returnExcisedFiniteCoordinateIncidence_bound
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [IsFiniteMeasure μ]
    (E returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (a : X → ι → ℂ) (threshold : ℝ) (hthreshold : 0 < threshold)
    (hcapture : E ∩ returnSetᶜ ⊆
      {x | threshold ≤ finiteCoordinateEnergy a x})
    (hmeas : ∀ i, AEStronglyMeasurable (fun x => a x i)
      (μ.restrict returnSetᶜ))
    (hsq : ∀ i, Integrable (fun x => ‖a x i‖ ^ 2)
      (μ.restrict returnSetᶜ)) :
    (((μ.restrict returnSetᶜ).real E * threshold) ^ 2) ≤
      (Fintype.card ι : ℝ) *
        returnExcisedFiniteCoordinateIncidenceAction μ a returnSet := by
  calc
    (((μ.restrict returnSetᶜ).real E * threshold) ^ 2) ≤
        (Fintype.card ι : ℝ) *
          ∑ i, ∑ j,
            ‖finiteCoordinateCovariance (μ.restrict returnSetᶜ) a i j‖ ^ 2 :=
      measureReal_restrict_event_mul_threshold_sq_le_coordinateCollision
        μ E returnSet hreturn a threshold hthreshold hcapture hsq
    _ = (Fintype.card ι : ℝ) *
        returnExcisedFiniteCoordinateIncidenceAction μ a returnSet := by
      rw [finiteCoordinate_covarianceCollision_eq_pairKernel
        (μ.restrict returnSetᶜ) a hmeas hsq]
      rw [← returnExcisedFiniteCoordinateIncidenceAction_eq_restrictProduct]

noncomputable def replicaSubspaceProjectionMass
    {α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (ψ : α → ℂ) : ℝ :=
  ‖S.orthogonalProjectionOnto (finitePureTensorPowerEuclidean r ψ)‖ ^ 2

theorem replicaSubspaceProjectionMass_eq_finiteCoordinateEnergy
    {α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (ψ : α → ℂ) :
    replicaSubspaceProjectionMass r S ψ =
      ∑ i, ‖replicaSubspaceCoordinate r S ψ i‖ ^ 2 := by
  let u := finitePureTensorPowerEuclidean r ψ
  let b := replicaSubspaceOrthonormalBasis r S
  change ‖S.orthogonalProjectionOnto u‖ ^ 2 =
    ∑ i, ‖replicaSubspaceCoordinate r S ψ i‖ ^ 2
  rw [← b.sum_sq_norm_inner_right (S.orthogonalProjectionOnto u)]
  apply Finset.sum_congr rfl
  intro i _
  change ‖inner ℂ (b i) (S.orthogonalProjectionOnto u)‖ ^ 2 =
    ‖inner ℂ ((b i : S) : EuclideanSpace ℂ (Fin r → α)) u‖ ^ 2
  rw [S.inner_orthogonalProjectionOnto_eq_of_mem_left]

theorem replicaTargetProjectionMass_eq_incidenceProjectionMass_offReturn
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) {x : X} (hx : x ∈ returnSetᶜ) :
    replicaTargetProjectionMass r target (state x) =
      replicaSubspaceProjectionMass r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) := by
  have hstar :=
    returnExcisedReplicaIncidenceSpan_projection_eq_targetProjection
      r target state returnSet hx
  unfold replicaTargetProjectionMass replicaSubspaceProjectionMass
  simpa only [Submodule.starProjection_apply, Submodule.coe_norm] using
    congrArg (fun v => ‖v‖ ^ 2) hstar.symm

theorem sum_star_replicaSubspaceCoordinate_mul_eq_inner_projection
    {α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (ψ φ : α → ℂ) :
    (∑ i, star (replicaSubspaceCoordinate r S ψ i) *
        replicaSubspaceCoordinate r S φ i) =
      inner ℂ
        (S.orthogonalProjectionOnto
          (finitePureTensorPowerEuclidean r ψ))
        (S.orthogonalProjectionOnto
          (finitePureTensorPowerEuclidean r φ)) := by
  let b := replicaSubspaceOrthonormalBasis r S
  let pψ : S := S.orthogonalProjectionOnto
    (finitePureTensorPowerEuclidean r ψ)
  let pφ : S := S.orthogonalProjectionOnto
    (finitePureTensorPowerEuclidean r φ)
  calc
    (∑ i, star (replicaSubspaceCoordinate r S ψ i) *
        replicaSubspaceCoordinate r S φ i) =
        ∑ i, inner ℂ pψ (b i) * inner ℂ (b i) pφ := by
      apply Finset.sum_congr rfl
      intro i _
      have hψ : replicaSubspaceCoordinate r S ψ i =
          inner ℂ (b i) pψ := by
        unfold replicaSubspaceCoordinate
        exact (S.inner_orthogonalProjectionOnto_eq_of_mem_left
          (b i) (finitePureTensorPowerEuclidean r ψ)).symm
      have hφ : replicaSubspaceCoordinate r S φ i =
          inner ℂ (b i) pφ := by
        unfold replicaSubspaceCoordinate
        exact (S.inner_orthogonalProjectionOnto_eq_of_mem_left
          (b i) (finitePureTensorPowerEuclidean r φ)).symm
      rw [hψ, hφ]
      exact congrArg (fun z => z * inner ℂ (b i) pφ)
        (inner_conj_symm (𝕜 := ℂ) pψ (b i))
    _ = inner ℂ pψ pφ := b.sum_inner_mul_inner pψ pφ

theorem replicaSubspacePairIncidenceKernel_eq_norm_inner_projection
    {X α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) (p : X × X) :
    replicaSubspacePairIncidenceKernel r S state p =
      ‖inner ℂ
        (S.starProjection
          (finitePureTensorPowerEuclidean r (state p.1)))
        (S.starProjection
          (finitePureTensorPowerEuclidean r (state p.2)))‖ ^ 2 := by
  unfold replicaSubspacePairIncidenceKernel finiteCoordinatePairKernel
  rw [sum_star_replicaSubspaceCoordinate_mul_eq_inner_projection]
  rfl

noncomputable def returnExcisedReplicaIncidenceNumber
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) : ℕ :=
  Module.finrank ℂ
    (returnExcisedReplicaIncidenceSpan r target state returnSet)

theorem returnExcisedReplicaIncidenceNumber_le_targetHilbertNumber
    {X C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceNumber r target state returnSet ≤
      replicaTargetHilbertNumber r target := by
  rw [returnExcisedReplicaIncidenceNumber,
    replicaTargetHilbertNumber_eq_finrank_span]
  exact Submodule.finrank_mono
    (returnExcisedReplicaIncidenceSpan_le_targetSpan
      r target state returnSet)

theorem returnExcisedReplicaIncidenceNumber_duplicated
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceNumber r
        (duplicatedReplicaTarget target) state returnSet =
      returnExcisedReplicaIncidenceNumber r target state returnSet := by
  unfold returnExcisedReplicaIncidenceNumber
  rw [returnExcisedReplicaIncidenceSpan_duplicated]

theorem returnExcisedReplicaIncidenceNumber_withZero
    {X C α : Type*} [Fintype α] {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) :
    returnExcisedReplicaIncidenceNumber r
        (replicaTargetWithZero target) state returnSet =
      returnExcisedReplicaIncidenceNumber r target state returnSet := by
  unfold returnExcisedReplicaIncidenceNumber
  rw [returnExcisedReplicaIncidenceSpan_withZero hr]

noncomputable def returnExcisedReplicaMinimalIncidenceAction
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) (returnSet : Set X) : ℝ :=
  let U := returnExcisedReplicaIncidenceSpan r target state returnSet
  returnExcisedFiniteCoordinateIncidenceAction μ
    (fun x i => replicaSubspaceCoordinate r U (state x) i) returnSet

theorem quenchedReplica_returnExcisedMinimalIncidence_bound
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i) (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i‖ ^ 2) (μ.restrict returnSetᶜ)) :
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2) ≤
      (returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
        returnExcisedReplicaMinimalIncidenceAction
          μ r target state returnSet := by
  let U := returnExcisedReplicaIncidenceSpan r target state returnSet
  let a : X → Fin (Module.finrank ℂ U) → ℂ :=
    fun x i => replicaSubspaceCoordinate r U (state x) i
  let E : Set X := {x | ∃ c,
    threshold ≤ finitePureStateFidelity (state x) (target c)}
  have hcapture : E ∩ returnSetᶜ ⊆
      {x | threshold ^ r ≤ finiteCoordinateEnergy a x} := by
    intro x hx
    have htargetNorm : ∀ c,
        ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1 := by
      intro c
      rw [norm_finitePureTensorPowerEuclidean_eq_one r
        (target c) (htarget c)]
    have hproj := completePureStateTargetCapture_subset_replicaProjectionMass
      hr target state htargetNorm threshold hthreshold.le hx.1
    change threshold ^ r ≤ replicaTargetProjectionMass r target (state x) at hproj
    have heq := replicaTargetProjectionMass_eq_incidenceProjectionMass_offReturn
      r target state returnSet hx.2
    rw [heq, replicaSubspaceProjectionMass_eq_finiteCoordinateEnergy] at hproj
    simpa [finiteCoordinateEnergy, a, U] using hproj
  simpa [E, a, U, returnExcisedReplicaIncidenceNumber,
    returnExcisedReplicaMinimalIncidenceAction, Fintype.card_fin] using
    returnExcisedFiniteCoordinateIncidence_bound
      μ E returnSet hreturn a (threshold ^ r) (pow_pos hthreshold r)
        hcapture hmeas hcoord

theorem returnExcisedReplicaMinimalPairKernel_eq_targetPairKernel
    {X C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (state : X → α → ℂ)
    (returnSet : Set X) {x y : X}
    (hx : x ∈ returnSetᶜ) (hy : y ∈ returnSetᶜ) :
    replicaSubspacePairIncidenceKernel r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        state (x, y) =
      replicaTargetPairIncidenceKernel r target state (x, y) := by
  rw [replicaSubspacePairIncidenceKernel_eq_norm_inner_projection]
  unfold replicaTargetPairIncidenceKernel
  rw [replicaSubspacePairIncidenceKernel_eq_norm_inner_projection]
  rw [returnExcisedReplicaIncidenceSpan_projection_eq_targetProjection
      r target state returnSet hx,
    returnExcisedReplicaIncidenceSpan_projection_eq_targetProjection
      r target state returnSet hy]

theorem returnExcisedReplicaMinimalIncidenceAction_eq_targetAction
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) (returnSet : Set X)
    (hreturn : MeasurableSet returnSet) :
    returnExcisedReplicaMinimalIncidenceAction
        μ r target state returnSet =
      returnExcisedReplicaIncidenceAction
        μ r target state returnSet := by
  let U := returnExcisedReplicaIncidenceSpan r target state returnSet
  unfold returnExcisedReplicaMinimalIncidenceAction
  unfold returnExcisedFiniteCoordinateIncidenceAction
  unfold returnExcisedReplicaIncidenceAction
  change (∫ p in (returnSetᶜ ×ˢ returnSetᶜ),
      replicaSubspacePairIncidenceKernel r U state p ∂(μ.prod μ)) = _
  apply setIntegral_congr_fun (hreturn.compl.prod hreturn.compl)
  intro p hp
  exact returnExcisedReplicaMinimalPairKernel_eq_targetPairKernel
    r target state returnSet hp.1 hp.2

/-- Return-excised complete capture pays the dimension of the least
source--target incidence carrier, while retaining the original occupied-target
pair action and every surviving source sheet. -/
theorem quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i) (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i‖ ^ 2) (μ.restrict returnSetᶜ)) :
    (μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)}) ∧
    (((μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2 ≤
      (returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
        returnExcisedReplicaIncidenceAction
          μ r target state returnSet) := by
  constructor
  · exact measureReal_capture_le_return_add_restrict_compl
      μ target state threshold returnSet hreturn
  · rw [← returnExcisedReplicaMinimalIncidenceAction_eq_targetAction
      μ r target state returnSet hreturn]
    exact quenchedReplica_returnExcisedMinimalIncidence_bound
      μ hr target state htarget threshold hthreshold returnSet hreturn
        hmeas hcoord

theorem measureReal_capture_le_return_add_sqrt_minimalRankAction
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i) (μ.restrict returnSetᶜ))
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r
        (returnExcisedReplicaIncidenceSpan r target state returnSet)
        (state x) i‖ ^ 2) (μ.restrict returnSetᶜ)) :
    μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        Real.sqrt
          ((returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
            returnExcisedReplicaIncidenceAction
              μ r target state returnSet) / threshold ^ r := by
  have hcut := quenchedReplica_returnExcisedMinimalRankCoareaIncidence_bound
    μ hr target state htarget threshold hthreshold returnSet hreturn
      hmeas hcoord
  have hscaled :
      (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
          threshold ^ r ≤
        Real.sqrt
          ((returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
            returnExcisedReplicaIncidenceAction
              μ r target state returnSet) :=
    Real.le_sqrt_of_sq_le hcut.2
  have hresidual :
      (μ.restrict returnSetᶜ).real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
        Real.sqrt
          ((returnExcisedReplicaIncidenceNumber r target state returnSet : ℝ) *
            returnExcisedReplicaIncidenceAction
              μ r target state returnSet) / threshold ^ r :=
    (le_div_iff₀' (pow_pos hthreshold r)).2 (by
      simpa [mul_comm] using hscaled)
  exact hcut.1.trans (by
    simpa [add_comm] using add_le_add_left hresidual (μ.real returnSet))

end

end GaloisForLFunctions.HTGeometry
