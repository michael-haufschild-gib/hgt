import GaloisForLFunctions.HTGeometry.MvPolynomialJacobianFDeriv
import GaloisForLFunctions.HTGeometry.QuenchedReplicaReturnExcisionLaw

/-!
# Maximal-volume replica target-skeleton law

A finite family which spans its occupied coordinate space contains a
maximal-volume ordered basis.  Cramer's rule bounds every coefficient of
every family member in that basis by one.  This is the finite-dimensional
endpoint skeleton needed to replace a complete circuit union by occupied
replica rank many genuine fixed-target moments.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Square coordinate matrix whose columns are an ordered tuple of targets. -/
def finiteTargetMatrix {C : Type*} {n : ℕ}
    (target : C → Fin n → ℂ) (b : Fin n → C) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ target (b j) i

/-- A spanning finite target family contains an ordered tuple with nonzero
coordinate determinant. -/
theorem exists_targetTuple_det_ne_zero_of_span_eq_top
    {C : Type*} [Fintype C] {n : ℕ} (target : C → Fin n → ℂ)
    (hspan : Submodule.span ℂ (Set.range target) = ⊤) :
    ∃ b : Fin n → C, (finiteTargetMatrix target b).det ≠ 0 := by
  classical
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let A : Matrix (Fin n) (Fin (Fintype.card C)) ℂ :=
    fun i j ↦ target (e.symm j) i
  have hspanA : Submodule.span ℂ (Set.range A.col) = ⊤ := by
    have hcol : Set.range A.col = Set.range target := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by ext i; rfl⟩
      · rintro ⟨c, rfl⟩
        refine ⟨e c, ?_⟩
        ext i
        simp [A]
    rw [hcol, hspan]
  have hsurj : Function.Surjective A.mulVec := by
    have hrange : LinearMap.range A.mulVecLin = ⊤ := by
      rw [A.range_mulVecLin, hspanA]
    have hs : Function.Surjective A.mulVecLin :=
      LinearMap.range_eq_top.mp hrange
    intro y
    obtain ⟨x, hx⟩ := hs y
    refine ⟨x, ?_⟩
    change A.mulVec x = y at hx
    exact hx
  obtain ⟨cols, hcols⟩ :=
    matrix_exists_submatrix_det_ne_zero_of_mulVec_surjective A hsurj
  refine ⟨fun j ↦ e.symm (cols j), ?_⟩
  change (A.submatrix id cols).det ≠ 0
  exact hcols

/-- Maximal-volume target skeleton.  Every target has coefficients of norm at
most one in the selected ordered basis. -/
theorem exists_maxVolumeTargetBasis_coeff_norm_le_one
    {C : Type*} [Fintype C] {n : ℕ} (target : C → Fin n → ℂ)
    (hspan : Submodule.span ℂ (Set.range target) = ⊤) :
    ∃ b : Fin n → C,
      (finiteTargetMatrix target b).det ≠ 0 ∧
      ∀ c : C, ∃ a : Fin n → ℂ,
        target c = ∑ j, a j • target (b j) ∧
        ∀ j, ‖a j‖ ≤ 1 := by
  classical
  obtain ⟨b₀, hb₀⟩ := exists_targetTuple_det_ne_zero_of_span_eq_top target hspan
  obtain ⟨b, -, hbmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin n → C))
    (fun d ↦ ‖(finiteTargetMatrix target d).det‖)
    ⟨b₀, Finset.mem_univ b₀⟩
  have hbdet : (finiteTargetMatrix target b).det ≠ 0 := by
    intro hbzero
    have hle := hbmax b₀ (Finset.mem_univ b₀)
    rw [hbzero, norm_zero] at hle
    exact (not_le_of_gt (norm_pos_iff.mpr hb₀)) hle
  refine ⟨b, hbdet, ?_⟩
  intro c
  let B := finiteTargetMatrix target b
  let a : Fin n → ℂ := (B⁻¹).mulVec (target c)
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hbdet
  refine ⟨a, ?_, ?_⟩
  · have hmul : B.mulVec a = target c := by
      change B.mulVec ((B⁻¹).mulVec (target c)) = target c
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B hunit,
        Matrix.one_mulVec]
    ext i
    simpa [B, finiteTargetMatrix, Matrix.mulVec, dotProduct, mul_comm] using
      (congrFun hmul i).symm
  · intro j
    let b' : Fin n → C := Function.update b j c
    have hupdate : B.updateCol j (target c) = finiteTargetMatrix target b' := by
      ext i k
      by_cases hkj : k = j
      · subst k
        simp [B, b', finiteTargetMatrix]
      · simp [B, b', finiteTargetMatrix, hkj]
    have hcramer : B.det * a j = (finiteTargetMatrix target b').det := by
      have h := congrFun (B.det_smul_inv_mulVec_eq_cramer (target c) hunit) j
      simpa [a, Matrix.cramer_apply, hupdate] using h
    have hnorm :
        ‖B.det‖ * ‖a j‖ = ‖(finiteTargetMatrix target b').det‖ := by
      rw [← norm_mul, hcramer]
    have hle := hbmax b' (Finset.mem_univ b')
    rw [← hnorm] at hle
    exact le_of_mul_le_mul_left (by
      simpa only [mul_one] using hle) (norm_pos_iff.mpr hbdet)

/-- An occupied replica target, regarded as a vector in its own span. -/
def replicaTargetVectorInSpan
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ)
    (c : C) : replicaTargetSpan r target :=
  ⟨finitePureTensorPowerEuclidean r (target c),
    Submodule.subset_span (Set.mem_range_self c)⟩

/-- Algebraic coordinate equivalence supplied by fixed orthonormal
coordinates on the occupied replica span. -/
noncomputable def replicaTargetCoordinateEquiv
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ) :
    replicaTargetSpan r target ≃ₗ[ℂ]
      (Fin (Module.finrank ℂ (replicaTargetSpan r target)) → ℂ) :=
  (replicaTargetOrthonormalBasis r target).repr.toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℂ
      (Fin (Module.finrank ℂ (replicaTargetSpan r target)) → ℂ))

/-- Occupied target endpoint in finite orthonormal coordinates. -/
noncomputable def replicaTargetCoordinateVector
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ)
    (c : C) :
    Fin (Module.finrank ℂ (replicaTargetSpan r target)) → ℂ :=
  replicaTargetCoordinateEquiv r target
    (replicaTargetVectorInSpan r target c)

/-- Occupied endpoint coordinates span their full Hilbert-number coordinate
space. -/
theorem span_replicaTargetCoordinateVector_eq_top
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ) :
    Submodule.span ℂ (Set.range (replicaTargetCoordinateVector r target)) = ⊤ := by
  let S := replicaTargetSpan r target
  let v : C → S := replicaTargetVectorInSpan r target
  let e : S ≃ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    replicaTargetCoordinateEquiv r target
  have hv : Submodule.span ℂ (Set.range v) = ⊤ := by
    apply (Submodule.span_range_subtype_eq_top_iff S
      (fun c ↦ Submodule.subset_span (Set.mem_range_self c))).2
    rfl
  calc
    Submodule.span ℂ (Set.range (replicaTargetCoordinateVector r target)) =
        (Submodule.span ℂ (Set.range v)).map e.toLinearMap := by
      rw [Submodule.map_span]
      congr 1
      ext x
      simp [v, e, replicaTargetCoordinateVector,
        replicaTargetCoordinateEquiv, replicaTargetVectorInSpan]
    _ = ⊤ := by
      rw [hv, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]

/-- The maximal-volume skeleton can be selected from actual occupied replica
endpoints.  Every lifted endpoint expands in that skeleton with coefficient
norm at most one. -/
theorem exists_replicaTarget_maxVolumeSkeleton
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    ∃ b : Fin (Module.finrank ℂ (replicaTargetSpan r target)) → C,
      ∀ c : C, ∃ a : Fin (Module.finrank ℂ (replicaTargetSpan r target)) → ℂ,
        finitePureTensorPowerEuclidean r (target c) =
            ∑ j, a j • finitePureTensorPowerEuclidean r (target (b j)) ∧
        ∀ j, ‖a j‖ ≤ 1 := by
  classical
  obtain ⟨b, -, hb⟩ := exists_maxVolumeTargetBasis_coeff_norm_le_one
    (replicaTargetCoordinateVector r target)
    (span_replicaTargetCoordinateVector_eq_top r target)
  refine ⟨b, ?_⟩
  intro c
  obtain ⟨a, ha, hnorm⟩ := hb c
  refine ⟨a, ?_, hnorm⟩
  have hsubtype :
      replicaTargetVectorInSpan r target c =
        ∑ j, a j • replicaTargetVectorInSpan r target (b j) := by
    apply (replicaTargetCoordinateEquiv r target).injective
    simpa [replicaTargetCoordinateVector, map_sum, map_smul] using ha
  simpa [replicaTargetVectorInSpan] using congrArg Subtype.val hsubtype

/-- Matched replica fidelity is the squared norm of the Hilbert-space inner
product of the two Euclidean tensor powers. -/
theorem finitePureStateFidelity_pow_eq_replica_inner_norm_sq
    {α : Type*} [Fintype α] (r : ℕ) (ψ φ : α → ℂ) :
    finitePureStateFidelity ψ φ ^ r =
      ‖inner ℂ (finitePureTensorPowerEuclidean r ψ)
        (finitePureTensorPowerEuclidean r φ)‖ ^ 2 := by
  rw [← finitePureStateFidelity_tensorPower r ψ φ]
  rw [finitePureStateFidelity, show
    inner ℂ (finitePureTensorPowerEuclidean r ψ)
        (finitePureTensorPowerEuclidean r φ) =
      finiteComplexInner (finitePureTensorPower r ψ)
        (finitePureTensorPower r φ) by
      exact inner_toLp_eq_finiteComplexInner _ _]

/-- A coefficient-one skeleton has the universal Hilbert-number Cauchy cost
against every observer vector. -/
theorem norm_inner_sq_le_finrank_mul_sum_skeleton
    {I : Type*} [Fintype I] {n : ℕ}
    (u w : EuclideanSpace ℂ I)
    (v : Fin n → EuclideanSpace ℂ I) (a : Fin n → ℂ)
    (hw : w = ∑ j, a j • v j) (ha : ∀ j, ‖a j‖ ≤ 1) :
    ‖inner ℂ u w‖ ^ 2 ≤
      (n : ℝ) * ∑ j, ‖inner ℂ u (v j)‖ ^ 2 := by
  rw [hw]
  simp_rw [inner_sum, inner_smul_right]
  have hsum :
      ‖∑ j, a j * inner ℂ u (v j)‖ ≤
        ∑ j, ‖inner ℂ u (v j)‖ := by
    calc
      ‖∑ j, a j * inner ℂ u (v j)‖ ≤
          ∑ j, ‖a j * inner ℂ u (v j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖inner ℂ u (v j)‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        calc
          ‖a j‖ * ‖inner ℂ u (v j)‖ ≤
              1 * ‖inner ℂ u (v j)‖ :=
            mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)
          _ = ‖inner ℂ u (v j)‖ := one_mul _
  calc
    ‖∑ j, a j * inner ℂ u (v j)‖ ^ 2 ≤
        (∑ j, ‖inner ℂ u (v j)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hsum 2
    _ ≤ (n : ℝ) * ∑ j, ‖inner ℂ u (v j)‖ ^ 2 := by
      simpa using (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun j : Fin n ↦ ‖inner ℂ u (v j)‖))

/-- **Pointwise complete-union skeleton law.**  Every occupied replica target
is controlled by at most the occupied replica rank many actual endpoint
moments. -/
theorem replicaTarget_maxVolumeSkeleton_pointwise
    {C α : Type*} [Fintype C] [Fintype α]
    (r : ℕ) (target : C → α → ℂ) :
    ∃ b : Fin (Module.finrank ℂ (replicaTargetSpan r target)) → C,
      ∀ (ψ : α → ℂ) (c : C),
        finitePureStateFidelity ψ (target c) ^ r ≤
          (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
            ∑ j, finitePureStateFidelity ψ (target (b j)) ^ r := by
  classical
  obtain ⟨b, hb⟩ := exists_replicaTarget_maxVolumeSkeleton r target
  refine ⟨b, ?_⟩
  intro ψ c
  obtain ⟨a, hvec, ha⟩ := hb c
  have hbound := norm_inner_sq_le_finrank_mul_sum_skeleton
    (u := finitePureTensorPowerEuclidean r ψ)
    (w := finitePureTensorPowerEuclidean r (target c))
    (v := fun j ↦ finitePureTensorPowerEuclidean r (target (b j)))
    a hvec ha
  rw [finitePureStateFidelity_pow_eq_replica_inner_norm_sq]
  calc
    ‖inner ℂ (finitePureTensorPowerEuclidean r ψ)
        (finitePureTensorPowerEuclidean r (target c))‖ ^ 2 ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ j, ‖inner ℂ (finitePureTensorPowerEuclidean r ψ)
            (finitePureTensorPowerEuclidean r (target (b j)))‖ ^ 2 := hbound
    _ = (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ j, finitePureStateFidelity ψ (target (b j)) ^ r := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact (finitePureStateFidelity_pow_eq_replica_inner_norm_sq
        r ψ (target (b j))).symm

/-- **Return-excised quenched maximal-volume incidence law.**  Recurrence is
paid once.  Off return, complete target capture is bounded by occupied replica
rank many genuine fixed-endpoint moments.  Integration is over the original
restricted source measure, hence all surviving fibre sheets keep their full
multiplicity. -/
theorem measure_completeTargetCapture_le_maxVolumeSkeletonMoments
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (_hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hint : ∀ c, Integrable
      (fun x ↦ finitePureStateFidelity (state x) (target c) ^ r)
        (μ.restrict returnSetᶜ)) :
    ∃ b : Fin (Module.finrank ℂ (replicaTargetSpan r target)) → C,
      μ.real {x | ∃ c,
          threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
        μ.real returnSet +
          ((Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
            ∑ j, ∫ x,
              finitePureStateFidelity (state x) (target (b j)) ^ r
                ∂(μ.restrict returnSetᶜ)) / threshold ^ r := by
  classical
  obtain ⟨b, hb⟩ := replicaTarget_maxVolumeSkeleton_pointwise r target
  refine ⟨b, ?_⟩
  let ν : Measure X := μ.restrict returnSetᶜ
  let E : Set X :=
    {x | ∃ c, threshold ≤ finitePureStateFidelity (state x) (target c)}
  let q : X → ℝ := fun x ↦
    (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
      ∑ j, finitePureStateFidelity (state x) (target (b j)) ^ r
  have hEQ : E ⊆ {x | threshold ^ r ≤ q x} := by
    intro x hx
    obtain ⟨c, hc⟩ := hx
    calc
      threshold ^ r ≤ finitePureStateFidelity (state x) (target c) ^ r :=
        pow_le_pow_left₀ hthreshold.le hc r
      _ ≤ q x := hb (state x) c
  have hintq : Integrable q ν := by
    dsimp [q, ν]
    exact (integrable_finsetSum Finset.univ fun j _ ↦ hint (b j)).const_mul _
  have hqnonneg : 0 ≤ᵐ[ν] q :=
    Filter.Eventually.of_forall fun x ↦ by
      dsimp [q]
      exact mul_nonneg (Nat.cast_nonneg _) <|
        Finset.sum_nonneg fun j _ ↦
          pow_nonneg (sq_nonneg _) r
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hintq (threshold ^ r)
  have hprod : threshold ^ r * ν.real E ≤ ∫ x, q x ∂ν := by
    calc
      threshold ^ r * ν.real E ≤
          threshold ^ r * ν.real {x | threshold ^ r ≤ q x} := by
        exact mul_le_mul_of_nonneg_left
          (measureReal_mono hEQ (by finiteness))
          (pow_nonneg hthreshold.le r)
      _ ≤ ∫ x, q x ∂ν := hmarkov
  have hresidual :
      ν.real E ≤
        ((Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ j, ∫ x,
            finitePureStateFidelity (state x) (target (b j)) ^ r ∂ν) /
              threshold ^ r := by
    apply (le_div_iff₀' (pow_pos hthreshold r)).2
    calc
      threshold ^ r * ν.real E ≤ ∫ x, q x ∂ν := hprod
      _ = (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ j, ∫ x,
            finitePureStateFidelity (state x) (target (b j)) ^ r ∂ν := by
        dsimp [q]
        rw [integral_const_mul]
        rw [integral_finsetSum Finset.univ
          (fun j _ ↦ by simpa [ν] using hint (b j))]
  have hcut := measureReal_capture_le_return_add_restrict_compl
    μ target state threshold returnSet hreturn
  exact hcut.trans (by
    simpa [E, ν] using add_le_add_left hresidual (μ.real returnSet))

/-- Uniform fixed-endpoint moment form.  The complete target union costs at
most the square of occupied replica rank, never target-label cardinality. -/
theorem measure_completeTargetCapture_le_hilbert_sq_mul_fixedMoment
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (fixedMoment : ℝ) (_hfixedMoment : 0 ≤ fixedMoment)
    (hint : ∀ c, Integrable
      (fun x ↦ finitePureStateFidelity (state x) (target c) ^ r)
        (μ.restrict returnSetᶜ))
    (hmoment : ∀ c,
      (∫ x, finitePureStateFidelity (state x) (target c) ^ r
        ∂(μ.restrict returnSetᶜ)) ≤ fixedMoment) :
    μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} ≤
      μ.real returnSet +
        ((Module.finrank ℂ (replicaTargetSpan r target) : ℝ) ^ 2 *
          fixedMoment) / threshold ^ r := by
  classical
  obtain ⟨b, hcap⟩ :=
    measure_completeTargetCapture_le_maxVolumeSkeletonMoments
      μ hr target state threshold hthreshold returnSet hreturn hint
  have hsum :
      (∑ j, ∫ x,
        finitePureStateFidelity (state x) (target (b j)) ^ r
          ∂(μ.restrict returnSetᶜ)) ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          fixedMoment := by
    calc
      (∑ j, ∫ x,
          finitePureStateFidelity (state x) (target (b j)) ^ r
            ∂(μ.restrict returnSetᶜ)) ≤
          ∑ _j : Fin (Module.finrank ℂ (replicaTargetSpan r target)),
            fixedMoment := by
        exact Finset.sum_le_sum fun j _ ↦ hmoment (b j)
      _ = (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          fixedMoment := by simp
  have hscaled :
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          (∑ j, ∫ x,
            finitePureStateFidelity (state x) (target (b j)) ^ r
              ∂(μ.restrict returnSetᶜ)) ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) ^ 2 *
          fixedMoment := by
    calc
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          (∑ j, ∫ x,
            finitePureStateFidelity (state x) (target (b j)) ^ r
              ∂(μ.restrict returnSetᶜ)) ≤
          (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
            ((Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
              fixedMoment) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
      _ = (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) ^ 2 *
          fixedMoment := by ring
  have hdiv :=
    (div_le_div_iff_of_pos_right (pow_pos hthreshold r)).2 hscaled
  exact hcap.trans (by
    simpa [add_comm] using add_le_add_left hdiv (μ.real returnSet))

end

end GaloisForLFunctions.HTGeometry
