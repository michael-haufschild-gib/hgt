import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw

/-!
# Replica--Hilbert coarea incidence law

A complete union of approximate pure-state targets can be controlled without a
targetwise union bound.  Lift every occupied target to replica order `r`, take
their linear span, and project the replicated source state onto that one
subspace.  Capture by any target forces projection mass at least the `r`th
power of the fidelity threshold.

The same construction supplies the correct target-image invariant.  The
adjoint of the synthesis map evaluates replica observables on every target, so
its range rank equals the dimension of the target replica span.  This is the
finite-coordinate homogeneous Hilbert number of the occupied Veronese image.
It is invariant under duplicate labels.  At positive replica order, adjoining
the zero vector--the residual of an exact return--also changes neither the span
nor the projection mass.

Integrating the pointwise law gives a quenched incidence bound for every finite
measure.  Any coarea disintegration of the source measure therefore retains all
source fibre sheets, while the target side depends only on the occupied image.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinate replica tensor as a vector in the standard finite Hilbert
space. -/
def finitePureTensorPowerEuclidean {α : Type*} [Fintype α]
    (r : ℕ) (ψ : α → ℂ) : EuclideanSpace ℂ (Fin r → α) :=
  WithLp.toLp 2 (finitePureTensorPower r ψ)

/-- The standard Hilbert inner product agrees with the coordinate inner
product used by the pure-state replica API. -/
theorem inner_toLp_eq_finiteComplexInner {ι : Type*} [Fintype ι]
    (u v : ι → ℂ) :
    inner ℂ (WithLp.toLp 2 u) (WithLp.toLp 2 v) =
      finiteComplexInner u v := by
  simp [finiteComplexInner, PiLp.inner_apply, mul_comm]

/-- Replica inner products are powers of one-copy inner products in the
Euclidean realization. -/
theorem inner_finitePureTensorPowerEuclidean
    {α : Type*} [Fintype α] (r : ℕ) (ψ φ : α → ℂ) :
    inner ℂ (finitePureTensorPowerEuclidean r ψ)
        (finitePureTensorPowerEuclidean r φ) =
      finiteComplexInner ψ φ ^ r := by
  change inner ℂ (WithLp.toLp 2 (finitePureTensorPower r ψ))
    (WithLp.toLp 2 (finitePureTensorPower r φ)) = _
  rw [inner_toLp_eq_finiteComplexInner,
    finiteComplexInner_pureTensorPower]

/-- Every normalized target has normalized replica lift. -/
theorem norm_finitePureTensorPowerEuclidean_eq_one
    {α : Type*} [Fintype α] (r : ℕ) (ψ : α → ℂ)
    (hψ : finiteComplexInner ψ ψ = 1) :
    ‖finitePureTensorPowerEuclidean r ψ‖ = 1 := by
  have hinner :
      inner ℂ (finitePureTensorPowerEuclidean r ψ)
        (finitePureTensorPowerEuclidean r ψ) = 1 := by
    rw [inner_finitePureTensorPowerEuclidean, hψ, one_pow]
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖finitePureTensorPowerEuclidean r ψ‖ ^ (2 : ℕ) = 1 := by
    apply Complex.ofReal_injective
    simpa using hinner
  nlinarith [norm_nonneg (finitePureTensorPowerEuclidean r ψ)]

/-- Span of the occupied target image after replica lifting.  The span is
formed after the nonlinear lift, so it retains projective image geometry that
one-copy linear span can erase. -/
def replicaTargetSpan {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin r → α)) :=
  Submodule.span ℂ
    (Set.range fun c => finitePureTensorPowerEuclidean r (target c))

/-- Target replica span depends only on the occupied vector image, not on its
labels or their multiplicities. -/
theorem replicaTargetSpan_eq_of_range_eq
    {C D α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (target' : D → α → ℂ)
    (h : Set.range target = Set.range target') :
    replicaTargetSpan r target = replicaTargetSpan r target' := by
  unfold replicaTargetSpan
  congr 1
  ext v
  constructor
  · rintro ⟨c, rfl⟩
    have hc : target c ∈ Set.range target' := by
      rw [← h]
      exact Set.mem_range_self c
    rcases hc with ⟨d, hd⟩
    exact ⟨d, by
      simpa using congrArg (finitePureTensorPowerEuclidean r) hd⟩
  · rintro ⟨d, rfl⟩
    have hd : target' d ∈ Set.range target := by
      rw [h]
      exact Set.mem_range_self d
    rcases hd with ⟨c, hc⟩
    exact ⟨c, by
      simpa using congrArg (finitePureTensorPowerEuclidean r) hc⟩

/-- Two labeled copies of the same target family. -/
def duplicatedReplicaTarget {C α : Type*} (target : C → α → ℂ) :
    C ⊕ C → α → ℂ :=
  Sum.elim target target

/-- Duplicate target labels do not change replica target span. -/
theorem replicaTargetSpan_duplicated
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    replicaTargetSpan r (duplicatedReplicaTarget target) =
      replicaTargetSpan r target := by
  apply replicaTargetSpan_eq_of_range_eq
  ext z
  constructor
  · rintro ⟨c, rfl⟩
    cases c with
    | inl c => exact Set.mem_range_self c
    | inr c => exact Set.mem_range_self c
  · rintro ⟨c, rfl⟩
    exact ⟨Sum.inl c, rfl⟩

/-- At positive replica order, the tensor power of the zero vector is zero. -/
theorem finitePureTensorPower_zero
    {α : Type*} [Fintype α] {r : ℕ} (hr : 0 < r) :
    finitePureTensorPower r (0 : α → ℂ) = 0 := by
  classical
  funext x
  unfold finitePureTensorPower
  let i : Fin r := ⟨0, hr⟩
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- Euclidean replica lift of zero is zero at positive order. -/
theorem finitePureTensorPowerEuclidean_zero
    {α : Type*} [Fintype α] {r : ℕ} (hr : 0 < r) :
    finitePureTensorPowerEuclidean r (0 : α → ℂ) = 0 := by
  unfold finitePureTensorPowerEuclidean
  rw [finitePureTensorPower_zero hr]
  rfl

/-- Adjoin one zero target.  It models the transverse residual of an exact
return after the lag-resolved split. -/
def replicaTargetWithZero {C α : Type*} (target : C → α → ℂ) :
    Option C → α → ℂ
  | none => 0
  | some c => target c

/-- Exact-return zero contributes no replica target direction. -/
theorem replicaTargetSpan_withZero
    {C α : Type*} [Fintype α]
    {r : ℕ} (hr : 0 < r) (target : C → α → ℂ) :
    replicaTargetSpan r (replicaTargetWithZero target) =
      replicaTargetSpan r target := by
  unfold replicaTargetSpan
  rw [show
      Set.range (fun c =>
        finitePureTensorPowerEuclidean r (replicaTargetWithZero target c)) =
        Set.insert 0 (Set.range fun c =>
          finitePureTensorPowerEuclidean r (target c)) by
    ext v
    constructor
    · rintro ⟨c, rfl⟩
      cases c with
      | none =>
          change finitePureTensorPowerEuclidean r (0 : α → ℂ) ∈ _
          rw [finitePureTensorPowerEuclidean_zero hr]
          exact Set.mem_insert 0 _
      | some c =>
          exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_range_self c))
    · intro hv
      rcases Set.mem_insert_iff.mp hv with hv | hv
      · refine ⟨none, ?_⟩
        simpa [replicaTargetWithZero,
          finitePureTensorPowerEuclidean_zero hr, hv]
      · rcases hv with ⟨c, rfl⟩
        exact ⟨some c, rfl⟩]
  exact Submodule.span_insert_zero

/-- Synthesis of a coefficient vector into a linear combination of occupied
replica targets. -/
noncomputable def replicaTargetSynthesis
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    EuclideanSpace ℂ C →ₗ[ℂ] EuclideanSpace ℂ (Fin r → α) where
  toFun a := ∑ c, (a c) • finitePureTensorPowerEuclidean r (target c)
  map_add' a b := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z a := by
    simp [Finset.smul_sum, mul_smul]

/-- The synthesis range is exactly the replica target span. -/
theorem range_replicaTargetSynthesis
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    LinearMap.range (replicaTargetSynthesis r target) =
      replicaTargetSpan r target := by
  classical
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    exact Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self c))
  · apply Submodule.span_le.2
    intro v hv
    rcases hv with ⟨c, rfl⟩
    refine ⟨EuclideanSpace.single c 1, ?_⟩
    simp [replicaTargetSynthesis]

/-- Evaluation of a replica observable on every occupied target is the adjoint
of target synthesis. -/
noncomputable def replicaTargetEvaluation
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    EuclideanSpace ℂ (Fin r → α) →ₗ[ℂ] EuclideanSpace ℂ C :=
  LinearMap.adjoint (replicaTargetSynthesis r target)

/-- Coordinate formula: the evaluation map pairs an observable with each
Veronese target vector. -/
theorem replicaTargetEvaluation_apply
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (q : EuclideanSpace ℂ (Fin r → α)) (c : C) :
    (replicaTargetEvaluation r target q) c =
      inner ℂ (finitePureTensorPowerEuclidean r (target c)) q := by
  classical
  have h := LinearMap.adjoint_inner_right (replicaTargetSynthesis r target)
    (EuclideanSpace.single c 1) q
  simpa [replicaTargetEvaluation, replicaTargetSynthesis,
    EuclideanSpace.inner_single_left] using h

/-- Homogeneous Hilbert number of the occupied target image at replica order
`r`, realized as the rank of complete replica evaluation. -/
noncomputable def replicaTargetHilbertNumber
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (replicaTargetEvaluation r target))

/-- **Hilbert image law.**  Complete homogeneous evaluation rank is exactly
the dimension of the occupied replica target span. -/
theorem replicaTargetHilbertNumber_eq_finrank_span
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    replicaTargetHilbertNumber r target =
      Module.finrank ℂ (replicaTargetSpan r target) := by
  rw [replicaTargetHilbertNumber, replicaTargetEvaluation,
    LinearMap.finrank_range_adjoint, range_replicaTargetSynthesis]

/-- Hilbert number is invariant under duplicated target labels. -/
theorem replicaTargetHilbertNumber_duplicated
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    replicaTargetHilbertNumber r (duplicatedReplicaTarget target) =
      replicaTargetHilbertNumber r target := by
  rw [replicaTargetHilbertNumber_eq_finrank_span,
    replicaTargetHilbertNumber_eq_finrank_span,
    replicaTargetSpan_duplicated]

/-- Hilbert number is unchanged by adjoining an exact-return zero. -/
theorem replicaTargetHilbertNumber_withZero
    {C α : Type*} [Fintype C] [Fintype α]
    {r : ℕ} (hr : 0 < r) (target : C → α → ℂ) :
    replicaTargetHilbertNumber r (replicaTargetWithZero target) =
      replicaTargetHilbertNumber r target := by
  rw [replicaTargetHilbertNumber_eq_finrank_span,
    replicaTargetHilbertNumber_eq_finrank_span,
    replicaTargetSpan_withZero hr]

/-- Source reporter paired with the complete occupied target image. -/
noncomputable def replicaTargetProjectionMass
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (ψ : α → ℂ) : ℝ :=
  ‖(replicaTargetSpan r target).orthogonalProjectionOnto
      (finitePureTensorPowerEuclidean r ψ)‖ ^ (2 : ℕ)

/-- Projection mass is invariant under duplicate target labels. -/
theorem replicaTargetProjectionMass_duplicated
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ) (ψ : α → ℂ) :
    replicaTargetProjectionMass r (duplicatedReplicaTarget target) ψ =
      replicaTargetProjectionMass r target ψ := by
  simp [replicaTargetProjectionMass, replicaTargetSpan_duplicated]

/-- Projection mass is unchanged by adjoining an exact-return zero. -/
theorem replicaTargetProjectionMass_withZero
    {C α : Type*} [Fintype α]
    {r : ℕ} (hr : 0 < r) (target : C → α → ℂ) (ψ : α → ℂ) :
    replicaTargetProjectionMass r (replicaTargetWithZero target) ψ =
      replicaTargetProjectionMass r target ψ := by
  simp [replicaTargetProjectionMass, replicaTargetSpan_withZero hr]

/-- **Replica target-span domination.**  Fidelity with any target is bounded,
after the matched replica power, by one projection reporter for the complete
target family. -/
theorem finitePureStateFidelity_pow_le_replicaTargetProjectionMass
    {C α : Type*} [Fintype α]
    (r : ℕ) (target : C → α → ℂ)
    (ψ : α → ℂ) (c : C)
    (htarget : ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1) :
    finitePureStateFidelity ψ (target c) ^ r ≤
      replicaTargetProjectionMass r target ψ := by
  let S := replicaTargetSpan r target
  let u := finitePureTensorPowerEuclidean r ψ
  let v := finitePureTensorPowerEuclidean r (target c)
  have hv : v ∈ S :=
    Submodule.subset_span (Set.mem_range_self c)
  let vS : S := ⟨v, hv⟩
  have hproj :
      inner ℂ (S.orthogonalProjectionOnto u) vS = inner ℂ u v :=
    S.inner_orthogonalProjectionOnto_eq_of_mem_right vS u
  have hcs := norm_inner_le_norm (𝕜 := ℂ)
    (S.orthogonalProjectionOnto u) vS
  have hinner :
      ‖inner ℂ u v‖ ≤ ‖S.orthogonalProjectionOnto u‖ := by
    rw [← hproj]
    calc
      ‖inner ℂ (S.orthogonalProjectionOnto u) vS‖ ≤
          ‖S.orthogonalProjectionOnto u‖ * ‖vS‖ := hcs
      _ ≤ ‖S.orthogonalProjectionOnto u‖ * 1 := by
        gcongr
        simpa [vS, v] using htarget
      _ = ‖S.orthogonalProjectionOnto u‖ := mul_one _
  have hfid :
      finitePureStateFidelity ψ (target c) ^ r =
        ‖inner ℂ u v‖ ^ (2 : ℕ) := by
    rw [← finitePureStateFidelity_tensorPower r ψ (target c)]
    rw [finitePureStateFidelity, show inner ℂ u v =
      finiteComplexInner (finitePureTensorPower r ψ)
        (finitePureTensorPower r (target c)) by
          exact inner_toLp_eq_finiteComplexInner _ _]
  rw [hfid]
  exact pow_le_pow_left₀ (norm_nonneg _) hinner 2

/-- The complete target-capture union lies in one projection-mass
superlevel set. -/
theorem completePureStateTargetCapture_subset_replicaProjectionMass
    {X C α : Type*} [Fintype α]
    {r : ℕ} (_hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c,
      ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1)
    (threshold : ℝ) (hthreshold : 0 ≤ threshold) :
    {x | ∃ c,
      threshold ≤ finitePureStateFidelity (state x) (target c)} ⊆
      {x | threshold ^ r ≤
        replicaTargetProjectionMass r target (state x)} := by
  intro x hx
  rcases hx with ⟨c, hc⟩
  calc
    threshold ^ r ≤ finitePureStateFidelity (state x) (target c) ^ r :=
      pow_le_pow_left₀ hthreshold hc r
    _ ≤ replicaTargetProjectionMass r target (state x) :=
      finitePureStateFidelity_pow_le_replicaTargetProjectionMass
        r target (state x) c (htarget c)

/-- **Quenched incidence bound.**  The full approximate-target event is
bounded by one replica projection moment.  Source points are never quotiented,
so all fibre-sheet multiplicity remains inside the integral. -/
theorem measure_completePureStateTargetCapture_le_replicaProjectionMoment
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c,
      ‖finitePureTensorPowerEuclidean r (target c)‖ ≤ 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hint : Integrable
      (fun x => replicaTargetProjectionMass r target (state x)) μ) :
    μ.real {x | ∃ c,
      threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) /
        threshold ^ r := by
  let q : X → ℝ :=
    fun x => replicaTargetProjectionMass r target (state x)
  let E : Set X :=
    {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  let Q : Set X := {x | threshold ^ r ≤ q x}
  have hEQ : E ⊆ Q :=
    completePureStateTargetCapture_subset_replicaProjectionMass
      hr target state htarget threshold hthreshold.le
  have hmeas : μ.real E ≤ μ.real Q := measureReal_mono hEQ
  have hqnonneg : 0 ≤ᵐ[μ] q :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hint (threshold ^ r)
  have hprod : μ.real E * threshold ^ r ≤ ∫ x, q x ∂μ := by
    calc
      μ.real E * threshold ^ r ≤ μ.real Q * threshold ^ r := by
        gcongr
      _ = threshold ^ r * μ.real Q := mul_comm _ _
      _ ≤ ∫ x, q x ∂μ := hmarkov
  apply (le_div_iff₀' (pow_pos hthreshold r)).2
  simpa [E, q, mul_comm] using hprod

/-- Normalized-target form of the quenched incidence bound. -/
theorem measure_completeNormalizedPureStateTargetCapture_le_replicaProjectionMoment
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hint : Integrable
      (fun x => replicaTargetProjectionMass r target (state x)) μ) :
    μ.real {x | ∃ c,
      threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) /
        threshold ^ r := by
  apply measure_completePureStateTargetCapture_le_replicaProjectionMoment
    μ hr target state (fun c => ?_) threshold hthreshold hint
  rw [norm_finitePureTensorPowerEuclidean_eq_one r (target c) (htarget c)]

/-- **Replica--Hilbert complete incidence capstone.**  One theorem packages
the complete-union inclusion, quenched moment bound, and the exact occupied
image Hilbert rank. -/
theorem replicaHilbert_completeIncidence_bound
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hint : Integrable
      (fun x => replicaTargetProjectionMass r target (state x)) μ) :
    ({x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ⊆
      {x | threshold ^ r ≤
        replicaTargetProjectionMass r target (state x)}) ∧
    μ.real {x | ∃ c,
      threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      (∫ x, replicaTargetProjectionMass r target (state x) ∂μ) /
        threshold ^ r ∧
    replicaTargetHilbertNumber r target =
      Module.finrank ℂ (replicaTargetSpan r target) := by
  refine ⟨completePureStateTargetCapture_subset_replicaProjectionMass
      hr target state
        (fun c => by
          rw [norm_finitePureTensorPowerEuclidean_eq_one
            r (target c) (htarget c)])
      threshold hthreshold.le,
    measure_completeNormalizedPureStateTargetCapture_le_replicaProjectionMoment
      μ hr target state htarget threshold hthreshold hint,
    replicaTargetHilbertNumber_eq_finrank_span r target⟩

end

end GaloisForLFunctions.HTGeometry
