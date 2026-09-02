import GaloisForLFunctions.HTGeometry.FiniteUnitaryEuclideanExponentialWordAnalytic
import GaloisForLFunctions.HTGeometry.MvPolynomialMatrixRankDefect
import GaloisForLFunctions.HTGeometry.AnalyticMatrixRankStratification
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import GaloisForLFunctions.HTGeometry.HallKrausDeterminantCapacity

/-!
# Haar-typical resource-filtered relation rank

Fixed orthonormal frames represent arbitrary finite-dimensional relation and observer subspaces.
The quotient block between the moving relation frame and fixed observer frame has the maximal
dimensionally allowed rank outside one Haar-null determinantal locus.  An explicit linear
equivalence identifies its kernel with the literal subspace intersection.
-/

open Set MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def framedHeadIndex {d : ℕ} (r : Fin (d + 1)) (i : Fin r) : Fin d :=
  ⟨i, by omega⟩

def framedTailIndex {d : ℕ} (q : Fin (d + 1)) (i : Fin (d - q)) : Fin d :=
  ⟨q + i, by omega⟩

def framedResourceBlock {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ)
    (r q : Fin (d + 1)) : Matrix (Fin (d - q)) (Fin r) ℂ :=
  fun i j => ((Q⁻¹ * U * R : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
    (framedTailIndex q i) (framedHeadIndex r j)

def framedTransverseRank {d : ℕ} (r q : Fin (d + 1)) : ℕ :=
  min (r : ℕ) (d - (q : ℕ))

def framedResourceMinor {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ)
    (r q : Fin (d + 1)) : ℂ :=
  ((framedResourceBlock R Q U r q).submatrix
    (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
    (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ))))).det

def framedAccessibleRelationRank {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ)
    (r q : Fin (d + 1)) : ℕ :=
  r - (framedResourceBlock R Q U r q).rank

theorem framedResourceBlock_rank_le_transverse {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ)
    (r q : Fin (d + 1)) :
    (framedResourceBlock R Q U r q).rank ≤ framedTransverseRank r q := by
  rw [framedTransverseRank, le_min_iff]
  exact ⟨Matrix.rank_le_width _, Matrix.rank_le_height _⟩

theorem framedAccessibleRelationRank_lower_bound {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ)
    (r q : Fin (d + 1)) :
    r + q - d ≤ framedAccessibleRelationRank R Q U r q := by
  have hrank := framedResourceBlock_rank_le_transverse R Q U r q
  simp only [framedAccessibleRelationRank, framedTransverseRank] at *
  omega

theorem framedAccessibleRelationRank_ne_lower_subset_minor_zero {d : ℕ}
    (R Q : Matrix.unitaryGroup (Fin d) ℂ)
    (r q : Fin (d + 1)) :
    {U | framedAccessibleRelationRank R Q U r q ≠ r + q - d} ⊆
      {U | framedResourceMinor R Q U r q = 0} := by
  intro U hU
  by_contra hminor
  have hunit : IsUnit
      ((framedResourceBlock R Q U r q).submatrix
        (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
        (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ))))) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.mpr hminor)
  have hsubrank :
      ((framedResourceBlock R Q U r q).submatrix
        (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
        (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ))))).rank =
          min (r : ℕ) (d - (q : ℕ)) := by
    simpa using Matrix.rank_of_isUnit _ hunit
  have hle := Matrix.rank_submatrix_le (framedResourceBlock R Q U r q)
    (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
    (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ))))
  have hrank := framedResourceBlock_rank_le_transverse R Q U r q
  have heq : (framedResourceBlock R Q U r q).rank =
      min (r : ℕ) (d - (q : ℕ)) := by
    rw [hsubrank] at hle
    exact le_antisymm hrank hle
  apply hU
  simp only [framedAccessibleRelationRank, heq]
  omega

def framedSourceSlice {d : ℕ} (r q : Fin (d + 1)) : Set (Fin d) :=
  {i | i.val < min (r : ℕ) (d - (q : ℕ))}

def framedTargetSlice {d : ℕ} (r q : Fin (d + 1)) : Set (Fin d) :=
  {i | (q : ℕ) ≤ i.val ∧ i.val < (q : ℕ) + min (r : ℕ) (d - (q : ℕ))}

noncomputable def framedSliceEquiv {d : ℕ} (r q : Fin (d + 1)) :
    framedSourceSlice r q ≃ framedTargetSlice r q where
  toFun i := ⟨⟨q + i.val, by
    have hi := i.property
    simp only [framedSourceSlice, Set.mem_setOf_eq] at hi
    have hq : (q : ℕ) ≤ d := by omega
    omega⟩, by
      have hi := i.property
      simp only [framedSourceSlice, Set.mem_setOf_eq] at hi
      simp only [framedTargetSlice, Set.mem_setOf_eq]
      omega⟩
  invFun i := ⟨⟨i.val - q, by
    have hi := i.property
    simp only [framedTargetSlice, Set.mem_setOf_eq] at hi
    have hid := i.val.isLt
    omega⟩, by
      have hi := i.property
      simp only [framedTargetSlice, Set.mem_setOf_eq] at hi
      simp only [framedSourceSlice, Set.mem_setOf_eq]
      omega⟩
  left_inv i := by ext; simp
  right_inv i := by
    ext
    have hi := i.property
    simp only [framedTargetSlice, Set.mem_setOf_eq] at hi
    simp
    omega

noncomputable def framedTransversePermutation {d : ℕ} (r q : Fin (d + 1)) :
    Equiv.Perm (Fin d) := by
  classical
  exact Equiv.extendSubtype (framedSliceEquiv r q)

theorem framedTransversePermutation_head {d : ℕ} (r q : Fin (d + 1))
    (i : Fin (min (r : ℕ) (d - (q : ℕ)))) :
    framedTransversePermutation r q (framedHeadIndex r (Fin.castLE (min_le_left _ _) i)) =
      framedTailIndex q (Fin.castLE (min_le_right _ _) i) := by
  classical
  change (Equiv.extendSubtype (framedSliceEquiv r q))
      (framedHeadIndex r (Fin.castLE (min_le_left _ _) i)) =
    framedTailIndex q (Fin.castLE (min_le_right _ _) i)
  rw [Equiv.extendSubtype_apply_of_mem]
  · rfl
  · simpa [framedSourceSlice, framedHeadIndex] using i.isLt

def framedTransverseWitness {d : ℕ} (R Q : Matrix.unitaryGroup (Fin d) ℂ)
    (r q : Fin (d + 1)) : Matrix.unitaryGroup (Fin d) ℂ :=
  Q * finiteUnitaryPermutation (framedTransversePermutation r q) * R⁻¹

theorem framedResourceMinor_witness {d : ℕ}
    (R Q : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    framedResourceMinor R Q (framedTransverseWitness R Q r q) r q = 1 := by
  classical
  simp only [framedResourceMinor]
  have hrelative : Q⁻¹ * (Q * finiteUnitaryPermutation (framedTransversePermutation r q) * R⁻¹) * R =
      finiteUnitaryPermutation (framedTransversePermutation r q) := by group
  have hblock :
      framedResourceBlock R Q (framedTransverseWitness R Q r q) r q =
        fun i j => (finiteUnitaryPermutation (framedTransversePermutation r q) :
          Matrix (Fin d) (Fin d) ℂ) (framedTailIndex q i) (framedHeadIndex r j) := by
    ext i j
    change ((Q⁻¹ * (Q * finiteUnitaryPermutation (framedTransversePermutation r q) * R⁻¹) * R :
      Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ)
        (framedTailIndex q i) (framedHeadIndex r j) = _
    rw [hrelative]
  rw [hblock]
  have hminor :
      Matrix.submatrix
        ((fun i j => (finiteUnitaryPermutation (framedTransversePermutation r q) :
          Matrix (Fin d) (Fin d) ℂ) (framedTailIndex q i) (framedHeadIndex r j)) :
          Matrix (Fin (d - q)) (Fin r) ℂ)
          (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
          (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ)))) = 1 := by
    ext i j
    simp [finiteUnitaryPermutation, framedTransversePermutation_head,
      framedTailIndex, Matrix.one_apply, Fin.ext_iff]
  rw [hminor, Matrix.det_one]

noncomputable def matrixEntryL2CLM {d : ℕ} (i j : Fin d) :
    Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun A => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 fun A => by simpa using norm_entry_le_l2_opNorm A i j

@[simp] theorem matrixEntryL2CLM_apply {d : ℕ} (i j : Fin d)
    (A : Matrix (Fin d) (Fin d) ℂ) : matrixEntryL2CLM i j A = A i j := rfl

theorem analyticAt_complex_normSq
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℂ} {x : X} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => Complex.normSq (f y)) x := by
  have hconj : AnalyticAt ℝ (fun y => starRingEnd ℂ (f y)) x :=
    AnalyticAt.comp (Complex.conjCLE.analyticAt (f x)) hf
  have hreal : AnalyticAt ℝ (fun y => (f y * starRingEnd ℂ (f y)).re) x :=
    AnalyticAt.comp (Complex.reCLM.analyticAt _) (hf.mul hconj)
  convert hreal using 1
  funext y
  rw [Complex.mul_conj]
  rfl

noncomputable def finiteUnitaryWordCoordinateEquiv
    (d N : ℕ) :
    (Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)))) ) → ℝ) ≃ₗ[ℝ]
      (Fin N → Fin (Module.finrank ℝ
        (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))) → ℝ) where
  toFun x i j := x (Fintype.equivFin _ (i, j))
  invFun X k := X (((Fintype.equivFin _).symm k).1)
    (((Fintype.equivFin _).symm k).2)
  left_inv x := by ext k; simp
  right_inv X := by ext i j; simp
  map_add' x y := by ext i j; rfl
  map_smul' c x := by ext i j; rfl

def finiteUnitaryReindexedExponentialWord (d N : ℕ)
    (x : Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)))) ) → ℝ) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  finiteUnitaryEuclideanExponentialWord (Fin d) N
    (finiteUnitaryWordCoordinateEquiv d N x)

theorem analyticAt_finiteUnitaryReindexedExponentialWord_coe (d N : ℕ)
    (x : Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)))) ) → ℝ) :
    AnalyticAt ℝ (fun y =>
      (finiteUnitaryReindexedExponentialWord d N y : Matrix (Fin d) (Fin d) ℂ)) x := by
  apply AnalyticAt.comp
    (analyticAt_finiteUnitaryEuclideanExponentialWord_coe N
      (finiteUnitaryWordCoordinateEquiv d N x))
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  exact (ContinuousLinearMap.proj (R := ℝ)
    (Fintype.equivFin (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)))) (i, j))).analyticAt x

theorem surjective_finiteUnitaryReindexedExponentialWord_of_word
    {d N : ℕ}
    (hN : ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∃ X, finiteUnitaryEuclideanExponentialWord (Fin d) N X = U) :
    Function.Surjective (finiteUnitaryReindexedExponentialWord d N) := by
  intro U
  obtain ⟨X, hX⟩ := hN U
  refine ⟨(finiteUnitaryWordCoordinateEquiv d N).symm X, ?_⟩
  simpa [finiteUnitaryReindexedExponentialWord] using hX

theorem analyticAt_framedResourceMinorNormSq_word {d N : ℕ}
    (R Q V : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1))
    (x : Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)))) ) → ℝ) :
    AnalyticAt ℝ (fun y => Complex.normSq
      (framedResourceMinor R Q
        (V * finiteUnitaryReindexedExponentialWord d N y) r q)) x := by
  have hword := analyticAt_finiteUnitaryReindexedExponentialWord_coe d N x
  have hrelative : AnalyticAt ℝ (fun y =>
      ((Q⁻¹ * V : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
        (finiteUnitaryReindexedExponentialWord d N y : Matrix (Fin d) (Fin d) ℂ) *
        (R : Matrix (Fin d) (Fin d) ℂ)) x :=
    (analyticAt_const.mul hword).mul analyticAt_const
  have hminorEntry : ∀ i j, AnalyticAt ℝ (fun y =>
      (framedResourceBlock R Q
        (V * finiteUnitaryReindexedExponentialWord d N y) r q).submatrix
          (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
          (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ)))) i j) x := by
    intro i j
    have hentry : AnalyticAt ℝ (fun y =>
      (((Q⁻¹ * V : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
          (finiteUnitaryReindexedExponentialWord d N y : Matrix (Fin d) (Fin d) ℂ) *
          (R : Matrix (Fin d) (Fin d) ℂ))
          (framedTailIndex q (Fin.castLE (min_le_right _ _) i))
          (framedHeadIndex r (Fin.castLE (min_le_left _ _) j))) x
        := AnalyticAt.comp
      (f := fun y =>
        (((Q⁻¹ * V : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) *
          (finiteUnitaryReindexedExponentialWord d N y : Matrix (Fin d) (Fin d) ℂ) *
          (R : Matrix (Fin d) (Fin d) ℂ)))
      (g := matrixEntryL2CLM
        (framedTailIndex q (Fin.castLE (min_le_right _ _) i))
        (framedHeadIndex r (Fin.castLE (min_le_left _ _) j)))
      (x := x)
      ((matrixEntryL2CLM
        (framedTailIndex q (Fin.castLE (min_le_right _ _) i))
        (framedHeadIndex r (Fin.castLE (min_le_left _ _) j))).analyticAt _)
      hrelative
    simpa [framedResourceBlock, mul_assoc] using hentry
  apply analyticAt_complex_normSq
  exact analyticAt_matrix_det_real hminorEntry

theorem continuous_finiteUnitaryReindexedExponentialWord (d N : ℕ) :
    Continuous (finiteUnitaryReindexedExponentialWord d N) := by
  rw [continuous_induced_rng]
  exact continuous_iff_continuousAt.2 fun x =>
    (analyticAt_finiteUnitaryReindexedExponentialWord_coe d N x).continuousAt

def finiteUnitaryWordCoordinateMeasure (d N : ℕ) (radius : ℝ) :
    Measure (Matrix.unitaryGroup (Fin d) ℂ) :=
  Measure.map (finiteUnitaryReindexedExponentialWord d N)
    (volume.restrict (Metric.closedBall 0 radius))

theorem finiteUnitaryWordCoordinateMeasure_apply_univ (d N : ℕ) (radius : ℝ) :
    finiteUnitaryWordCoordinateMeasure d N radius Set.univ =
      (volume : Measure (Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
        (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))))) → ℝ))
        (Metric.closedBall 0 radius) := by
  unfold finiteUnitaryWordCoordinateMeasure
  rw [Measure.map_apply (continuous_finiteUnitaryReindexedExponentialWord d N).measurable
    MeasurableSet.univ]
  simp only [Set.preimage_univ]
  exact Measure.restrict_apply_univ (Metric.closedBall 0 radius)

theorem finiteUnitaryWordCoordinateMeasure_univ_pos (d N : ℕ) {radius : ℝ}
    (hradius : 0 < radius) :
    0 < finiteUnitaryWordCoordinateMeasure d N radius Set.univ := by
  rw [finiteUnitaryWordCoordinateMeasure_apply_univ]
  exact Metric.measure_closedBall_pos volume 0 hradius

noncomputable instance finiteUnitaryWordCoordinateMeasure_isFinite
    (d N : ℕ) (radius : ℝ) :
    IsFiniteMeasure (finiteUnitaryWordCoordinateMeasure d N radius) where
  measure_univ_lt_top := by
    rw [finiteUnitaryWordCoordinateMeasure_apply_univ]
    exact measure_closedBall_lt_top

theorem finiteUnitaryWordCoordinateMeasure_eq_zero_of_preimage_null
    (d N : ℕ) (radius : ℝ)
    {s : Set (Matrix.unitaryGroup (Fin d) ℂ)} (hs : MeasurableSet s)
    (hzero : (volume : Measure (Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))))) → ℝ))
      ((finiteUnitaryReindexedExponentialWord d N) ⁻¹' s ∩
        Metric.closedBall 0 radius) = 0) :
    finiteUnitaryWordCoordinateMeasure d N radius s = 0 := by
  unfold finiteUnitaryWordCoordinateMeasure
  rw [Measure.map_apply (continuous_finiteUnitaryReindexedExponentialWord d N).measurable hs,
    Measure.restrict_apply
      ((continuous_finiteUnitaryReindexedExponentialWord d N).measurable hs)]
  exact hzero

theorem continuous_framedResourceMinor {d : ℕ}
    (R Q : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    Continuous (fun U => framedResourceMinor R Q U r q) := by
  let relative : Matrix.unitaryGroup (Fin d) ℂ → Matrix.unitaryGroup (Fin d) ℂ :=
    fun U => Q⁻¹ * U * R
  have hrelative : Continuous relative :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hentry (i j : Fin (min (r : ℕ) (d - (q : ℕ)))) :
      Continuous (fun U =>
        (framedResourceBlock R Q U r q).submatrix
          (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
          (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ)))) i j) := by
    change Continuous
      ((fun W : Matrix.unitaryGroup (Fin d) ℂ =>
        W (framedTailIndex q (Fin.castLE (min_le_right _ _) i))
          (framedHeadIndex r (Fin.castLE (min_le_left _ _) j))) ∘ relative)
    exact (continuous_finiteUnitaryEntry
      (framedTailIndex q (Fin.castLE (min_le_right _ _) i))
      (framedHeadIndex r (Fin.castLE (min_le_left _ _) j))).comp hrelative
  unfold framedResourceMinor
  rw [show (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      ((framedResourceBlock R Q U r q).submatrix
        (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
        (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ))))).det) =
      fun U => ∑ σ : Equiv.Perm (Fin (min (r : ℕ) (d - (q : ℕ)))),
        (Equiv.Perm.sign σ : ℂ) * ∏ i,
          (framedResourceBlock R Q U r q).submatrix
            (Fin.castLE (min_le_right (r : ℕ) (d - (q : ℕ))))
            (Fin.castLE (min_le_left (r : ℕ) (d - (q : ℕ)))) (σ i) i by
    funext U
    exact Matrix.det_apply' _]
  exact continuous_finset_sum _ fun σ _ =>
    continuous_const.mul (continuous_finset_prod _ fun i _ => hentry (σ i) i)

theorem finiteUnitaryHaar_framedResourceMinor_zero {d : ℕ}
    (R Q : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    finiteUnitaryHaar (Fin d) {U | framedResourceMinor R Q U r q = 0} = 0 := by
  obtain ⟨N, hN⟩ := exists_finiteUnitary_uniform_euclideanExponentialWord (Fin d)
  let s : Set (Matrix.unitaryGroup (Fin d) ℂ) :=
    {U | framedResourceMinor R Q U r q = 0}
  have hs : MeasurableSet s :=
    (isClosed_singleton.preimage
      (continuous_framedResourceMinor R Q r q)).measurableSet
  apply finiteUnitaryHaar_eq_zero_of_all_left_translates_null
    (finiteUnitaryWordCoordinateMeasure d N 1) hs
    (finiteUnitaryWordCoordinateMeasure_univ_pos d N (by norm_num))
  intro V
  apply finiteUnitaryWordCoordinateMeasure_eq_zero_of_preimage_null d N 1
    (measurable_const_mul V hs)
  let f : (Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))))) → ℝ) → ℝ :=
    fun x => Complex.normSq
      (framedResourceMinor R Q
        (V * finiteUnitaryReindexedExponentialWord d N x) r q)
  have hf : AnalyticOnNhd ℝ f Set.univ := by
    intro x _
    exact analyticAt_framedResourceMinorNormSq_word R Q V r q x
  have hsurj : Function.Surjective (finiteUnitaryReindexedExponentialWord d N) :=
    surjective_finiteUnitaryReindexedExponentialWord_of_word hN
  obtain ⟨x, hx⟩ := hsurj (V⁻¹ * framedTransverseWitness R Q r q)
  have hnonzero : f x ≠ 0 := by
    have hprod : V * finiteUnitaryReindexedExponentialWord d N x =
        framedTransverseWitness R Q r q := by
      rw [hx]
      group
    simp [f, hprod, framedResourceMinor_witness]
  have hfull : (volume : Measure (Fin (Fintype.card (Fin N × Fin (Module.finrank ℝ
      (selfAdjoint (Matrix (Fin d) (Fin d) ℂ))))) → ℝ))
      {x | f x = 0} = 0 :=
    analytic_zero_set_volume_fin _ f hf ⟨x, hnonzero⟩
  apply measure_mono_null (t := {x | f x = 0}) _ hfull
  intro x hxset
  rcases hxset with ⟨hxset, _⟩
  change framedResourceMinor R Q
    (V * finiteUnitaryReindexedExponentialWord d N x) r q = 0 at hxset
  simpa [f, hxset]

theorem finiteUnitaryHaar_framedAccessibleRelationRank_eq_grassmann {d : ℕ}
    (R Q : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    finiteUnitaryHaar (Fin d)
      {U | framedAccessibleRelationRank R Q U r q ≠ r + q - d} = 0 := by
  apply measure_mono_null
    (framedAccessibleRelationRank_ne_lower_subset_minor_zero R Q r q)
  exact finiteUnitaryHaar_framedResourceMinor_zero R Q r q

theorem unitaryColumnBasis_repr_unitaryColumnBasis {d : ℕ}
    (Q W : Matrix.unitaryGroup (Fin d) ℂ) (i j : Fin d) :
    (unitaryColumnBasis Q).equivFun (unitaryColumnBasis W j) i =
      ((Q⁻¹ * W : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ) i j := by
  classical
  have hvec : unitaryColumnBasis W j = ∑ k,
      (((Q⁻¹ * W : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) k j) • unitaryColumnBasis Q k := by
    ext a
    rw [unitaryColumnBasis_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      unitaryColumnBasis_apply]
    have hprod : Q * (Q⁻¹ * W) = W := by group
    have hprodMatrix :
        (Q : Matrix (Fin d) (Fin d) ℂ) *
          ((Q⁻¹ * W : Matrix.unitaryGroup (Fin d) ℂ) :
            Matrix (Fin d) (Fin d) ℂ) =
          (W : Matrix (Fin d) (Fin d) ℂ) := congrArg Subtype.val hprod
    symm
    calc
      ∑ x, (((Q⁻¹ * W : Matrix.unitaryGroup (Fin d) ℂ) :
          Matrix (Fin d) (Fin d) ℂ) x j) * (Q : Matrix (Fin d) (Fin d) ℂ) a x =
          ∑ x, (Q : Matrix (Fin d) (Fin d) ℂ) a x *
            ((Q⁻¹ * W : Matrix.unitaryGroup (Fin d) ℂ) :
              Matrix (Fin d) (Fin d) ℂ) x j := by
            apply Finset.sum_congr rfl
            intro x _
            exact mul_comm _ _
      _ = ((Q : Matrix (Fin d) (Fin d) ℂ) *
            ((Q⁻¹ * W : Matrix.unitaryGroup (Fin d) ℂ) :
              Matrix (Fin d) (Fin d) ℂ)) a j :=
            Matrix.mul_apply.symm
      _ = (W : Matrix (Fin d) (Fin d) ℂ) a j := by rw [hprodMatrix]
  have hcoord := congrArg
    (fun v => (unitaryColumnBasis Q).equivFun v i) hvec
  simp only [map_sum, map_smul, Module.Basis.equivFun_apply,
    Module.Basis.repr_self] at hcoord
  rw [Finset.sum_apply i Finset.univ] at hcoord
  rw [Finset.sum_eq_single i] at hcoord
  · simpa using hcoord
  · intro b _ hbi
    simp [hbi]
  · simp

def framedTailRestriction {d : ℕ} (q : Fin (d + 1)) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin (d - q) → ℂ) where
  toFun x i := x (framedTailIndex q i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def framedHeadSynthesis {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) :
    (Fin r → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun c := ∑ j, c j • unitaryColumnBasis U (framedHeadIndex r j)
  map_add' c e := by
    change (∑ j, (c j + e j) • unitaryColumnBasis U (framedHeadIndex r j)) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    change (∑ j, (a * c j) • unitaryColumnBasis U (framedHeadIndex r j)) =
      a • ∑ j, c j • unitaryColumnBasis U (framedHeadIndex r j)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]

noncomputable def framedTailCoordinates {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (q : Fin (d + 1)) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin (d - q) → ℂ) :=
  (framedTailRestriction q).comp (unitaryColumnBasis U).equivFun.toLinearMap

noncomputable def framedHilbertSubspace {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) :
    Submodule ℂ (Fin d → ℂ) :=
  LinearMap.ker (framedTailCoordinates U r)

@[simp] theorem framedHeadSynthesis_basisFun {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) (j : Fin r) :
    framedHeadSynthesis U r (Pi.basisFun ℂ (Fin r) j) =
      unitaryColumnBasis U (framedHeadIndex r j) := by
  classical
  simp [framedHeadSynthesis, Pi.basisFun_apply]

@[simp] theorem framedTailCoordinates_unitaryColumnBasis {d : ℕ}
    (Q W : Matrix.unitaryGroup (Fin d) ℂ) (q : Fin (d + 1))
    (i : Fin (d - q)) (j : Fin d) :
    framedTailCoordinates Q q (unitaryColumnBasis W j) i =
      ((Q⁻¹ * W : Matrix.unitaryGroup (Fin d) ℂ) :
        Matrix (Fin d) (Fin d) ℂ) (framedTailIndex q i) j := by
  exact unitaryColumnBasis_repr_unitaryColumnBasis Q W (framedTailIndex q i) j

theorem framedTailCoordinates_comp_framedHeadSynthesis {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    (framedTailCoordinates Q q).comp (framedHeadSynthesis (U * R) r) =
      (framedResourceBlock R Q U r q).mulVecLin := by
  classical
  apply (Pi.basisFun ℂ (Fin r)).ext
  intro j
  ext i
  change framedTailCoordinates Q q
      (framedHeadSynthesis (U * R) r (Pi.basisFun ℂ (Fin r) j)) i =
    (framedResourceBlock R Q U r q).mulVec
      (Pi.basisFun ℂ (Fin r) j) i
  rw [framedHeadSynthesis_basisFun, framedTailCoordinates_unitaryColumnBasis]
  simp only [framedResourceBlock, Matrix.mulVec, dotProduct,
    Pi.basisFun_apply, mul_assoc]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [Pi.single_apply, hbj]
  · simp

theorem unitaryColumnBasis_equivFun_framedHeadSynthesis {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1))
    (c : Fin r → ℂ) (i : Fin d) :
    (unitaryColumnBasis U).equivFun (framedHeadSynthesis U r c) i =
      if h : i.val < (r : ℕ) then c ⟨i.val, h⟩ else 0 := by
  classical
  change (unitaryColumnBasis U).equivFun
    (∑ j, c j • unitaryColumnBasis U (framedHeadIndex r j)) i = _
  rw [map_sum]
  simp only [map_smul]
  rw [Finset.sum_apply i Finset.univ]
  by_cases hi : i.val < (r : ℕ)
  · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin r)]
    · simp [unitaryColumnBasis_repr_unitaryColumnBasis, framedHeadIndex,
        Matrix.one_apply, Fin.ext_iff, hi]
    · intro b _ hbi
      have hne : i ≠ framedHeadIndex r b := by
        intro h
        apply hbi
        ext
        exact (congrArg Fin.val h).symm
      simp [unitaryColumnBasis_repr_unitaryColumnBasis, Matrix.one_apply,
        hne, hi]
    · simp
  · have hne (b : Fin r) : i ≠ framedHeadIndex r b := by
      intro h
      subst i
      exact hi b.isLt
    simp [unitaryColumnBasis_repr_unitaryColumnBasis, Matrix.one_apply,
      hne, hi]

theorem framedHeadSynthesis_injective {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) :
    Function.Injective (framedHeadSynthesis U r) := by
  intro c e hce
  ext j
  have h := congrArg
    (fun x => (unitaryColumnBasis U).equivFun x (framedHeadIndex r j)) hce
  simpa [unitaryColumnBasis_equivFun_framedHeadSynthesis,
    framedHeadIndex] using h

theorem framedHeadSynthesis_mem_framedHilbertSubspace {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1))
    (c : Fin r → ℂ) :
    framedHeadSynthesis U r c ∈ framedHilbertSubspace U r := by
  rw [framedHilbertSubspace, LinearMap.mem_ker]
  ext i
  change (unitaryColumnBasis U).equivFun (framedHeadSynthesis U r c)
    (framedTailIndex r i) = 0
  rw [unitaryColumnBasis_equivFun_framedHeadSynthesis]
  simp [framedTailIndex]

noncomputable def framedHeadSynthesisToSubspace {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) :
    (Fin r → ℂ) →ₗ[ℂ] framedHilbertSubspace U r :=
  (framedHeadSynthesis U r).codRestrict (framedHilbertSubspace U r)
    (framedHeadSynthesis_mem_framedHilbertSubspace U r)

theorem framedHeadSynthesisToSubspace_surjective {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) :
    Function.Surjective (framedHeadSynthesisToSubspace U r) := by
  intro x
  let c : Fin r → ℂ := fun j =>
    (unitaryColumnBasis U).equivFun x (framedHeadIndex r j)
  refine ⟨c, Subtype.ext ?_⟩
  apply (unitaryColumnBasis U).equivFun.injective
  ext i
  change (unitaryColumnBasis U).equivFun (framedHeadSynthesis U r c) i =
    (unitaryColumnBasis U).equivFun x i
  rw [unitaryColumnBasis_equivFun_framedHeadSynthesis]
  by_cases hi : i.val < (r : ℕ)
  · simp [hi, c, framedHeadIndex]
  · have hrle : (r : ℕ) ≤ d := by omega
    let k : Fin (d - r) := ⟨i.val - r, by omega⟩
    have hik : framedTailIndex r k = i := by
      ext
      simp [framedTailIndex, k]
      omega
    have hx := x.property
    change framedTailCoordinates U r x = 0 at hx
    have hxi := congrFun hx k
    change (unitaryColumnBasis U).equivFun x (framedTailIndex r k) = 0 at hxi
    rw [hik] at hxi
    simp [hi, hxi]

noncomputable def framedHeadEquivSubspace {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) :
    (Fin r → ℂ) ≃ₗ[ℂ] framedHilbertSubspace U r :=
  LinearEquiv.ofBijective (framedHeadSynthesisToSubspace U r)
    ⟨fun _ _ h => framedHeadSynthesis_injective U r (congrArg Subtype.val h),
      framedHeadSynthesisToSubspace_surjective U r⟩

theorem finrank_framedHilbertSubspace {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) :
    Module.finrank ℂ (framedHilbertSubspace U r) = r := by
  rw [← LinearEquiv.finrank_eq (framedHeadEquivSubspace U r)]
  simp

noncomputable def framedRelationCoefficientSubspace {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    Submodule ℂ (Fin r → ℂ) :=
  LinearMap.ker (framedResourceBlock R Q U r q).mulVecLin

noncomputable def framedHilbertIntersection {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    Submodule ℂ (Fin d → ℂ) :=
  framedHilbertSubspace (U * R) r ⊓ framedHilbertSubspace Q q

@[simp] theorem framedHeadEquivSubspace_apply_coe {d : ℕ}
    (U : Matrix.unitaryGroup (Fin d) ℂ) (r : Fin (d + 1)) (c : Fin r → ℂ) :
    ((framedHeadEquivSubspace U r c : framedHilbertSubspace U r) : Fin d → ℂ) =
      framedHeadSynthesis U r c := rfl

noncomputable def framedIntersectionCoordinates {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    framedHilbertIntersection R Q U r q →ₗ[ℂ]
      (Fin r → ℂ) :=
  (framedHeadEquivSubspace (U * R) r).symm.toLinearMap.comp
    (Submodule.inclusion (show framedHilbertIntersection R Q U r q ≤
      framedHilbertSubspace (U * R) r from inf_le_left))

theorem framedIntersectionCoordinates_mem_relation {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1))
    (x : framedHilbertIntersection R Q U r q) :
    framedIntersectionCoordinates R Q U r q x ∈
      framedRelationCoefficientSubspace R Q U r q := by
  change (framedResourceBlock R Q U r q).mulVecLin
    (framedIntersectionCoordinates R Q U r q x) = 0
  rw [← framedTailCoordinates_comp_framedHeadSynthesis R Q U r q]
  change framedTailCoordinates Q q
    (framedHeadSynthesis (U * R) r (framedIntersectionCoordinates R Q U r q x)) = 0
  have he := (framedHeadEquivSubspace (U * R) r).apply_symm_apply
    ((Submodule.inclusion (show framedHilbertIntersection R Q U r q ≤
      framedHilbertSubspace (U * R) r from inf_le_left)) x)
  have heval := congrArg Subtype.val he
  rw [framedHeadEquivSubspace_apply_coe] at heval
  change framedTailCoordinates Q q
    (framedHeadSynthesis (U * R) r
      ((framedHeadEquivSubspace (U * R) r).symm
        ((Submodule.inclusion (show framedHilbertIntersection R Q U r q ≤
          framedHilbertSubspace (U * R) r from inf_le_left)) x))) = 0
  rw [heval]
  exact x.property.2

noncomputable def framedRelationToIntersection {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    framedRelationCoefficientSubspace R Q U r q →ₗ[ℂ]
      framedHilbertIntersection R Q U r q where
  toFun c := ⟨framedHeadSynthesis (U * R) r c, ⟨
    framedHeadSynthesis_mem_framedHilbertSubspace (U * R) r c,
    by
      change framedTailCoordinates Q q (framedHeadSynthesis (U * R) r c) = 0
      change ((framedTailCoordinates Q q).comp
        (framedHeadSynthesis (U * R) r)) c = 0
      rw [framedTailCoordinates_comp_framedHeadSynthesis R Q U r q]
      exact c.property⟩⟩
  map_add' c e := by
    apply Subtype.ext
    exact map_add (framedHeadSynthesis (U * R) r)
      (c : Fin r → ℂ) (e : Fin r → ℂ)
  map_smul' a c := by
    apply Subtype.ext
    exact map_smul (framedHeadSynthesis (U * R) r) a (c : Fin r → ℂ)

noncomputable def framedIntersectionToRelation {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    framedHilbertIntersection R Q U r q →ₗ[ℂ]
      framedRelationCoefficientSubspace R Q U r q :=
  (framedIntersectionCoordinates R Q U r q).codRestrict
    (framedRelationCoefficientSubspace R Q U r q)
    (framedIntersectionCoordinates_mem_relation R Q U r q)

noncomputable def framedRelationEquivIntersection {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    framedRelationCoefficientSubspace R Q U r q ≃ₗ[ℂ]
      framedHilbertIntersection R Q U r q where
  toLinearMap := framedRelationToIntersection R Q U r q
  invFun := framedIntersectionToRelation R Q U r q
  left_inv c := by
    apply Subtype.ext
    change (framedHeadEquivSubspace (U * R) r).symm
      (framedHeadEquivSubspace (U * R) r c) = c
    exact (framedHeadEquivSubspace (U * R) r).symm_apply_apply c
  right_inv x := by
    apply Subtype.ext
    have he := (framedHeadEquivSubspace (U * R) r).apply_symm_apply
      ((Submodule.inclusion (show framedHilbertIntersection R Q U r q ≤
        framedHilbertSubspace (U * R) r from inf_le_left)) x)
    change framedHeadSynthesis (U * R) r
      ((framedHeadEquivSubspace (U * R) r).symm
        ((Submodule.inclusion (show framedHilbertIntersection R Q U r q ≤
          framedHilbertSubspace (U * R) r from inf_le_left)) x)) = x
    exact congrArg Subtype.val he

theorem range_mulVecLin_eq_span_cols_rect
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    A.mulVecLin.range = Submodule.span ℂ (Set.range A.col) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [show A.mulVecLin x = ∑ j, x j • A.col j by
      ext i
      simp [Matrix.mulVec, dotProduct, Matrix.col_apply, mul_comm]]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    let e : n → ℂ := fun i => if i = j then 1 else 0
    refine ⟨e, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, e, Matrix.col_apply]

theorem matrix_rank_eq_finrank_range_mulVecLin_rect
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) :
    A.rank = Module.finrank ℂ A.mulVecLin.range := by
  rw [range_mulVecLin_eq_span_cols_rect]
  exact Matrix.rank_eq_finrank_span_cols A

theorem finrank_framedRelationCoefficientSubspace {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    Module.finrank ℂ (framedRelationCoefficientSubspace R Q U r q) =
      framedAccessibleRelationRank R Q U r q := by
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (framedResourceBlock R Q U r q).mulVecLin
  rw [← matrix_rank_eq_finrank_range_mulVecLin_rect] at hrank
  have hdomain : Module.finrank ℂ (Fin r → ℂ) = r := by simp
  rw [hdomain] at hrank
  change Module.finrank ℂ (LinearMap.ker
    (framedResourceBlock R Q U r q).mulVecLin) =
      r - (framedResourceBlock R Q U r q).rank
  omega

theorem finrank_framedHilbertSubspace_inf_eq_accessibleRank {d : ℕ}
    (R Q U : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    Module.finrank ℂ (framedHilbertIntersection R Q U r q) =
        framedAccessibleRelationRank R Q U r q := by
  rw [← finrank_framedRelationCoefficientSubspace R Q U r q]
  exact (LinearEquiv.finrank_eq (framedRelationEquivIntersection R Q U r q)).symm

theorem finiteUnitaryHaar_framedHilbertSubspace_intersection_eq_grassmann {d : ℕ}
    (R Q : Matrix.unitaryGroup (Fin d) ℂ) (r q : Fin (d + 1)) :
    finiteUnitaryHaar (Fin d)
      {U | Module.finrank ℂ
        (framedHilbertIntersection R Q U r q) ≠
          r + q - d} = 0 := by
  simpa only [finrank_framedHilbertSubspace_inf_eq_accessibleRank] using
    finiteUnitaryHaar_framedAccessibleRelationRank_eq_grassmann R Q r q

end
end GaloisForLFunctions.HTGeometry
