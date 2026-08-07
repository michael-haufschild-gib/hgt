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

/-- Fixed finite orthonormal coordinates on the occupied replica target span. -/
noncomputable def replicaTargetOrthonormalBasis
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    OrthonormalBasis
      (Fin (Module.finrank ℂ (replicaTargetSpan r target))) ℂ
      (replicaTargetSpan r target) :=
  stdOrthonormalBasis ℂ (replicaTargetSpan r target)

/-- Coordinate of a replicated source vector along one occupied target-span
mode. -/
noncomputable def replicaTargetCoordinate
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (ψ : α → ℂ)
    (i : Fin (Module.finrank ℂ (replicaTargetSpan r target))) : ℂ :=
  inner ℂ
    ((replicaTargetOrthonormalBasis r target i :
      replicaTargetSpan r target) :
      EuclideanSpace ℂ (Fin r → α))
    (finitePureTensorPowerEuclidean r ψ)

/-- Parseval identifies projection mass with the sum of occupied-coordinate
energies. -/
theorem replicaTargetProjectionMass_eq_sum_coordinate_norm_sq
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (ψ : α → ℂ) :
    replicaTargetProjectionMass r target ψ =
      ∑ i, ‖replicaTargetCoordinate r target ψ i‖ ^ 2 := by
  let S := replicaTargetSpan r target
  let u := finitePureTensorPowerEuclidean r ψ
  let b := replicaTargetOrthonormalBasis r target
  change ‖S.orthogonalProjectionOnto u‖ ^ 2 = _
  rw [← b.sum_sq_norm_inner_right (S.orthogonalProjectionOnto u)]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simpa [replicaTargetCoordinate, b, S, u] using
    S.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) u

/-- Quenched covariance of occupied replica coordinates. -/
noncomputable def replicaTargetIncidenceCovariance
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) :
    Matrix
      (Fin (Module.finrank ℂ (replicaTargetSpan r target)))
      (Fin (Module.finrank ℂ (replicaTargetSpan r target))) ℂ :=
  fun i j => ∫ x,
    star (replicaTargetCoordinate r target (state x) i) *
      replicaTargetCoordinate r target (state x) j ∂μ

/-- Squared Hilbert--Schmidt energy of the quenched covariance compressed to
the occupied replica target image. -/
noncomputable def replicaTargetIncidenceCollision
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ) : ℝ :=
  ∑ i, ∑ j,
    ‖replicaTargetIncidenceCovariance μ r target state i j‖ ^ 2

/-- Trace versus Hilbert--Schmidt inequality in explicit finite coordinates. -/
theorem sq_sum_re_diag_le_card_mul_matrix_hilbertSchmidt
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    (∑ i, (A i i).re) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have hdiag :
      (∑ i, (A i i).re) ^ 2 ≤
        (Fintype.card ι : ℝ) * ∑ i, (A i i).re ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := fun i => (A i i).re))
  have hsum :
      (∑ i, (A i i).re ^ 2) ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    calc
      (A i i).re ^ 2 ≤ ‖A i i‖ ^ 2 := by
        simpa [pow_two, Complex.normSq_eq_norm_sq] using
          Complex.re_sq_le_normSq (A i i)
      _ ≤ ∑ j, ‖A i j‖ ^ 2 :=
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
      ∫ x, ‖replicaTargetCoordinate r target (state x) i‖ ^ 2 ∂μ := by
  rw [replicaTargetIncidenceCovariance]
  simp_rw [show ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) by
    intro z
    rw [show star z * z = ((starRingEnd ℂ) z) * z from rfl,
      RCLike.conj_mul]
    norm_cast]
  simpa using congrArg Complex.re
    (@integral_ofReal X _ μ ℂ _
      (fun x => ‖replicaTargetCoordinate r target (state x) i‖ ^ 2))

/-- The quenched projection moment is exactly the trace of compressed
covariance. -/
theorem integral_replicaTargetProjectionMass_eq_sum_re_covariance_diag
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) (r : ℕ) (target : C → α → ℂ)
    (state : X → α → ℂ)
    (hcoord : ∀ i,
      Integrable (fun x =>
        ‖replicaTargetCoordinate r target (state x) i‖ ^ 2) μ) :
    (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) =
      ∑ i, (replicaTargetIncidenceCovariance μ r target state i i).re := by
  calc
    (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) =
        ∫ x, ∑ i,
          ‖replicaTargetCoordinate r target (state x) i‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        replicaTargetProjectionMass_eq_sum_coordinate_norm_sq
          r target (state x)
    _ = ∑ i, ∫ x,
          ‖replicaTargetCoordinate r target (state x) i‖ ^ 2 ∂μ := by
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
        ‖replicaTargetCoordinate r target (state x) i‖ ^ 2) μ) :
    (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) ^ 2 ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        replicaTargetIncidenceCollision μ r target state := by
  rw [integral_replicaTargetProjectionMass_eq_sum_re_covariance_diag
    μ r target state hcoord]
  simpa [replicaTargetIncidenceCollision, Fintype.card_fin] using
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
        ‖replicaTargetCoordinate r target (state x) i‖ ^ 2) μ) :
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
        simp [replicaTargetWithZero, finitePureStateFidelity] at hc
        exact (not_lt_of_ge hc) hthreshold
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
  unfold replicaTargetIncidenceCollision replicaTargetIncidenceCovariance
    replicaTargetCoordinate replicaTargetOrthonormalBasis
  cases hspan
  rfl

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
        ‖replicaTargetCoordinate r target (state x) i‖ ^ 2) μ) :
    (μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} *
      threshold ^ r) ^ 2 ≤
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
  have hsquare : (μ.real E * threshold ^ r) ^ 2 ≤ I ^ 2 :=
    pow_le_pow_left₀
      (mul_nonneg hmass_nonneg (pow_pos hthreshold r).le)
      hscaled 2
  calc
    (μ.real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} *
        threshold ^ r) ^ 2 =
        (μ.real E * threshold ^ r) ^ 2 := rfl
    _ ≤ I ^ 2 := hsquare
    _ ≤ (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        replicaTargetIncidenceCollision μ r target state :=
      sq_integral_replicaTargetProjectionMass_le_hilbert_mul_collision
        μ r target state hcoord
    _ = (replicaTargetHilbertNumber r target : ℝ) *
        replicaTargetIncidenceCollision μ r target state := by
      rw [replicaTargetHilbertNumber_eq_finrank_span]

end

end GaloisForLFunctions.HTGeometry
