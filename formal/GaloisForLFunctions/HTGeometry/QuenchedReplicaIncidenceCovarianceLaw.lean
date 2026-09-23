import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw

/-!
# Quenched replica incidence--covariance law

The complete return-removed target union is first compressed to its occupied
replica span.  The square of the resulting quenched projection moment is then
bounded by occupied-span dimension times the Hilbert--Schmidt energy of its
compressed covariance matrix.  This retains every source sheet inside the
quenched integrals while forgetting duplicate target labels and exact-return
zero residuals.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Fixed finite orthonormal coordinates on a replica subspace. -/
noncomputable def replicaSubspaceOrthonormalBasis
    {α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α))) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ S)) ℂ S :=
  stdOrthonormalBasis ℂ S

/-- Fixed finite orthonormal coordinates on the occupied replica target span. -/
noncomputable def replicaTargetOrthonormalBasis
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (replicaTargetSpan r target))) ℂ
      (replicaTargetSpan r target) :=
  replicaSubspaceOrthonormalBasis r (replicaTargetSpan r target)

/-- Coordinate of a replicated source vector along one mode of a replica
subspace. -/
noncomputable def replicaSubspaceCoordinate
    {α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (ψ : α → ℂ) (i : Fin (Module.finrank ℂ S)) : ℂ :=
  inner ℂ
    ((replicaSubspaceOrthonormalBasis r S i : S) :
      EuclideanSpace ℂ (Fin r → α))
    (finitePureTensorPowerEuclidean r ψ)

/-- Coordinate of a replicated source vector along one occupied target-span
mode. -/
noncomputable def replicaTargetCoordinate
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (ψ : α → ℂ)
    (i : Fin (Module.finrank ℂ (replicaTargetSpan r target))) : ℂ :=
  replicaSubspaceCoordinate r (replicaTargetSpan r target) ψ i

/-- Parseval identifies projection mass with the sum of occupied-coordinate
energies. -/
theorem replicaTargetProjectionMass_eq_sum_coordinate_norm_sq
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (ψ : α → ℂ) :
    replicaTargetProjectionMass r target ψ =
      ∑ i, ‖replicaTargetCoordinate r target ψ i‖ ^ (2 : ℕ) := by
  let S := replicaTargetSpan r target
  let u := finitePureTensorPowerEuclidean r ψ
  let b := replicaTargetOrthonormalBasis r target
  change ‖S.orthogonalProjectionOnto u‖ ^ (2 : ℕ) = _
  rw [← b.sum_sq_norm_inner_right (S.orthogonalProjectionOnto u)]
  apply Finset.sum_congr rfl
  intro i _
  change ‖inner ℂ (b i) (S.orthogonalProjectionOnto u)‖ ^ (2 : ℕ) =
    ‖inner ℂ ((b i : S) : EuclideanSpace ℂ (Fin r → α)) u‖ ^ (2 : ℕ)
  rw [S.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- Quenched covariance of coordinates in one replica subspace. -/
noncomputable def replicaSubspaceIncidenceCovariance
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) :
    Matrix
      (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
  fun i j => ∫ x,
    star (replicaSubspaceCoordinate r S (state x) i) *
      replicaSubspaceCoordinate r S (state x) j ∂μ

/-- Quenched covariance of occupied replica coordinates. -/
noncomputable def replicaTargetIncidenceCovariance
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) :
    Matrix
      (Fin (Module.finrank ℂ (replicaTargetSpan r target)))
      (Fin (Module.finrank ℂ (replicaTargetSpan r target))) ℂ :=
  replicaSubspaceIncidenceCovariance μ r
    (replicaTargetSpan r target) state

/-- Squared Hilbert--Schmidt energy of quenched covariance in one replica
subspace. -/
noncomputable def replicaSubspaceIncidenceCollision
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) : ℝ :=
  ∑ i, ∑ j,
    ‖replicaSubspaceIncidenceCovariance μ r S state i j‖ ^ (2 : ℕ)

/-- Squared Hilbert--Schmidt energy of the quenched covariance compressed to
the occupied replica target image. -/
noncomputable def replicaTargetIncidenceCollision
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) : ℝ :=
  replicaSubspaceIncidenceCollision μ r
    (replicaTargetSpan r target) state

/-- Trace versus Hilbert--Schmidt inequality in explicit finite coordinates. -/
theorem sq_sum_re_diag_le_card_mul_matrix_hilbertSchmidt
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    (∑ i, (A i i).re) ^ (2 : ℕ) ≤
      (Fintype.card ι : ℝ) * ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℕ) := by
  have hdiag :
      (∑ i, (A i i).re) ^ (2 : ℕ) ≤
        (Fintype.card ι : ℝ) * ∑ i, (A i i).re ^ (2 : ℕ) := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := fun i => (A i i).re))
  have hsum :
      (∑ i, (A i i).re ^ (2 : ℕ)) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    calc
      (A i i).re ^ (2 : ℕ) ≤ ‖A i i‖ ^ (2 : ℕ) := by
        simpa [pow_two, Complex.normSq_eq_norm_sq] using
          Complex.re_sq_le_normSq (A i i)
      _ ≤ ∑ j, ‖A i j‖ ^ (2 : ℕ) :=
        Finset.single_le_sum (fun j _ => sq_nonneg ‖A i j‖)
          (Finset.mem_univ i)
  exact hdiag.trans
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _))

/-- The diagonal covariance entry is the integral of one occupied-coordinate
energy. -/
theorem re_replicaTargetIncidenceCovariance_diag
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ)
    (i : Fin (Module.finrank ℂ (replicaTargetSpan r target))) :
    (replicaTargetIncidenceCovariance μ r target state i i).re =
      ∫ x, ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ) ∂μ := by
  rw [replicaTargetIncidenceCovariance,
    replicaSubspaceIncidenceCovariance]
  change
    (∫ x,
      star (replicaSubspaceCoordinate r (replicaTargetSpan r target)
        (state x) i) *
      replicaSubspaceCoordinate r (replicaTargetSpan r target)
        (state x) i ∂μ).re =
      ∫ x, ‖replicaSubspaceCoordinate r (replicaTargetSpan r target)
        (state x) i‖ ^ (2 : ℕ) ∂μ
  rw [show
      (fun x =>
        star (replicaSubspaceCoordinate r (replicaTargetSpan r target)
          (state x) i) *
        replicaSubspaceCoordinate r (replicaTargetSpan r target)
          (state x) i) =
      (fun x =>
        ((‖replicaSubspaceCoordinate r (replicaTargetSpan r target)
          (state x) i‖ ^ (2 : ℕ) : ℝ) : ℂ)) by
    funext x
    rw [show star (replicaSubspaceCoordinate r
        (replicaTargetSpan r target) (state x) i) *
        replicaSubspaceCoordinate r (replicaTargetSpan r target) (state x) i =
      ((starRingEnd ℂ) (replicaSubspaceCoordinate r
        (replicaTargetSpan r target) (state x) i)) *
        replicaSubspaceCoordinate r (replicaTargetSpan r target) (state x) i
      from rfl, RCLike.conj_mul]
    norm_cast]
  exact (congrArg Complex.re
    (@integral_ofReal X _ μ ℂ _
      (fun x => ‖replicaSubspaceCoordinate r
        (replicaTargetSpan r target) (state x) i‖ ^ (2 : ℕ)))).trans
    (Complex.ofReal_re _)

/-- The quenched projection moment is exactly the trace of compressed
covariance. -/
theorem integral_replicaTargetProjectionMass_eq_sum_re_covariance_diag
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ)
    (hcoord : ∀ i,
      Integrable (fun x =>
        ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ)) μ) :
    (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) =
      ∑ i, (replicaTargetIncidenceCovariance μ r target state i i).re := by
  calc
    (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) =
        ∫ x, ∑ i,
          ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        replicaTargetProjectionMass_eq_sum_coordinate_norm_sq
          r target (state x)
    _ = ∑ i, ∫ x,
          ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ) ∂μ := by
      rw [integral_finsetSum Finset.univ]
      exact fun i _ => hcoord i
    _ = ∑ i,
        (replicaTargetIncidenceCovariance μ r target state i i).re := by
      apply Finset.sum_congr rfl
      intro i _
      exact (re_replicaTargetIncidenceCovariance_diag
        μ r target state i).symm

/-- **Quenched incidence--covariance law.**  The square of complete occupied
projection mass is bounded by occupied replica-image dimension times one
compressed covariance collision. -/
theorem sq_integral_replicaTargetProjectionMass_le_hilbert_mul_collision
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ)
    (hcoord : ∀ i,
      Integrable (fun x =>
        ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ)) μ) :
    (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) ^ (2 : ℕ) ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        replicaTargetIncidenceCollision μ r target state := by
  rw [integral_replicaTargetProjectionMass_eq_sum_re_covariance_diag
    μ r target state hcoord]
  simpa [replicaTargetIncidenceCollision,
    replicaSubspaceIncidenceCollision, replicaTargetIncidenceCovariance,
    Fintype.card_fin] using
    sq_sum_re_diag_le_card_mul_matrix_hilbertSchmidt
      (replicaTargetIncidenceCovariance μ r target state)

/-- Coordinate square-integrability supplies the projection-moment
integrability required by the complete-incidence theorem. -/
theorem integrable_replicaTargetProjectionMass_of_coordinates
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ)
    (hcoord : ∀ i,
      Integrable (fun x =>
        ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ)) μ) :
    Integrable
      (fun x => replicaTargetProjectionMass r target (state x)) μ := by
  apply (integrable_finsetSum Finset.univ
    (fun i _ => hcoord i)).congr
  exact Filter.Eventually.of_forall fun x =>
    (replicaTargetProjectionMass_eq_sum_coordinate_norm_sq
      r target (state x)).symm

/-- Repeating target labels does not change the complete capture event. -/
theorem completePureStateTargetCapture_duplicated
    {X C α : Type*} [Fintype α]
    (target : C → α → ℂ) (state : X → α → ℂ)
    (threshold : ℝ) :
    {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x)
          (duplicatedReplicaTarget target c)} =
      {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} := by
  ext x
  constructor
  · rintro ⟨c, hc⟩
    cases c with
    | inl c => exact ⟨c, hc⟩
    | inr c => exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨Sum.inl c, hc⟩

/-- At positive fidelity threshold, adjoining the zero residual of an exact
return does not change the complete capture event. -/
theorem completePureStateTargetCapture_withZero
    {X C α : Type*} [Fintype α]
    (target : C → α → ℂ) (state : X → α → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x)
          (replicaTargetWithZero target c)} =
      {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} := by
  ext x
  constructor
  · rintro ⟨c, hc⟩
    cases c with
    | none =>
        have hzero : finitePureStateFidelity (state x) (0 : α → ℂ) = 0 := by
          simp [finitePureStateFidelity, finiteComplexInner]
        rw [replicaTargetWithZero, hzero] at hc
        linarith
    | some c => exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨some c, hc⟩

/-- Compressed covariance collision depends only on the occupied replica span,
not on the target parameterization. -/
theorem replicaTargetIncidenceCollision_eq_of_span_eq
    {X C D α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ)
    (target : C → α → ℂ) (target' : D → α → ℂ)
    (state : X → α → ℂ)
    (hspan : replicaTargetSpan r target =
      replicaTargetSpan r target') :
    replicaTargetIncidenceCollision μ r target state =
      replicaTargetIncidenceCollision μ r target' state := by
  unfold replicaTargetIncidenceCollision
  rw [hspan]

/-- Duplicate circuit descriptions do not change compressed covariance
collision. -/
theorem replicaTargetIncidenceCollision_duplicated
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) :
    replicaTargetIncidenceCollision μ r
        (duplicatedReplicaTarget target) state =
      replicaTargetIncidenceCollision μ r target state :=
  replicaTargetIncidenceCollision_eq_of_span_eq
    μ r (duplicatedReplicaTarget target) target state
      (replicaTargetSpan_duplicated r target)

/-- Adjoining the zero residual of an exact return does not change compressed
covariance collision. -/
theorem replicaTargetIncidenceCollision_withZero
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ) :
    replicaTargetIncidenceCollision μ r
        (replicaTargetWithZero target) state =
      replicaTargetIncidenceCollision μ r target state :=
  replicaTargetIncidenceCollision_eq_of_span_eq
    μ r (replicaTargetWithZero target) target state
      (replicaTargetSpan_withZero hr target)

/-- **Complete quenched coarea-incidence bound.**  Capture by any target is
handled before squaring.  Thus no targetwise union appears: squared shortcut
mass times the matched replica threshold is bounded by occupied-image Hilbert
rank times one compressed covariance collision. -/
theorem quenchedReplica_incidenceCovariance_bound
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hcoord : ∀ i,
      Integrable (fun x =>
        ‖replicaTargetCoordinate r target (state x) i‖ ^ (2 : ℕ)) μ) :
    (μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} *
      threshold ^ r) ^ (2 : ℕ) ≤
      (replicaTargetHilbertNumber r target : ℝ) *
        replicaTargetIncidenceCollision μ r target state := by
  let E : Set X :=
    {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  let I : ℝ :=
    ∫ x, replicaTargetProjectionMass r target (state x) ∂μ
  have hint : Integrable
      (fun x => replicaTargetProjectionMass r target (state x)) μ :=
    integrable_replicaTargetProjectionMass_of_coordinates
      μ r target state hcoord
  have hcapture : μ.real E ≤ I / threshold ^ r := by
    exact measure_completeNormalizedPureStateTargetCapture_le_replicaProjectionMoment
      μ hr target state htarget threshold hthreshold hint
  have hscaled : μ.real E * threshold ^ r ≤ I :=
    (mul_comm (μ.real E) (threshold ^ r)) ▸
      (le_div_iff₀' (pow_pos hthreshold r)).mp hcapture
  have hmass_nonneg : 0 ≤ μ.real E := measureReal_nonneg
  have hsquare : (μ.real E * threshold ^ r) ^ (2 : ℕ) ≤ I ^ (2 : ℕ) :=
    pow_le_pow_left₀
      (mul_nonneg hmass_nonneg (pow_pos hthreshold r).le)
      hscaled 2
  calc
    (μ.real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ (2 : ℕ) =
        (μ.real E * threshold ^ r) ^ (2 : ℕ) := rfl
    _ ≤ I ^ (2 : ℕ) := hsquare
    _ ≤ (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        replicaTargetIncidenceCollision μ r target state :=
      sq_integral_replicaTargetProjectionMass_le_hilbert_mul_collision
        μ r target state hcoord
    _ = (replicaTargetHilbertNumber r target : ℝ) *
        replicaTargetIncidenceCollision μ r target state := by
      rw [replicaTargetHilbertNumber_eq_finrank_span]

end

end GaloisForLFunctions.HTGeometry
