import GaloisForLFunctions.RHTower.RouteEWeightedHallANOVA
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Route E weighted-Hall projection duality

This module formalizes the exact nonlinear reporter dual for the finite supported-kernel
marginal polytope.  No optimizer is assumed: compactness and convexity of the full real kernel
polytope produce it internally.
-/

namespace RHTower

open scoped BigOperators
open Set

/-- Finite source-predeclared relation, represented by nonempty target neighborhoods. -/
structure RouteEHallRelation (S T : Type*) [Fintype S] [Fintype T] where
  neighbors : S → Finset T
  neighbors_nonempty : ∀ s, (neighbors s).Nonempty

namespace RouteEHallRelation

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]

/-- Real row kernels supported on the predeclared relation. -/
def rawKernelSet (R : RouteEHallRelation S T) : Set (S → T → ℝ) :=
  {P | (∀ s t, 0 ≤ P s t) ∧
    (∀ s, ∑ t, P s t = 1) ∧
    (∀ s t, t ∉ R.neighbors s → P s t = 0)}

/-- Target output marginal of a raw supported kernel. -/
def rawOutput
    (_R : RouteEHallRelation S T) (D : RouteEHallANOVAData S T)
    (P : S → T → ℝ) (t : T) : ℝ :=
  ∑ s, D.sourceLaw s * P s t

omit [DecidableEq T] in theorem rawKernel_nonneg
    (R : RouteEHallRelation S T) {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet)
    (s : S) (t : T) :
    0 ≤ P s t :=
  hP.1 s t

omit [DecidableEq T] in theorem rawKernel_row_sum
    (R : RouteEHallRelation S T) {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet)
    (s : S) :
    ∑ t, P s t = 1 :=
  hP.2.1 s

omit [DecidableEq T] in theorem rawKernel_eq_zero_of_not_neighbor
    (R : RouteEHallRelation S T) {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet)
    (s : S) (t : T) (ht : t ∉ R.neighbors s) :
    P s t = 0 :=
  hP.2.2 s t ht

omit [DecidableEq T] in theorem rawKernel_le_one
    (R : RouteEHallRelation S T) {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet)
    (s : S) (t : T) :
    P s t ≤ 1 := by
  rw [← R.rawKernel_row_sum hP s]
  exact Finset.single_le_sum (fun u _hu => R.rawKernel_nonneg hP s u) (Finset.mem_univ t)

noncomputable def chosenNeighbor (R : RouteEHallRelation S T) (s : S) : T :=
  (R.neighbors_nonempty s).choose

omit [DecidableEq T] in theorem chosenNeighbor_mem (R : RouteEHallRelation S T) (s : S) :
    R.chosenNeighbor s ∈ R.neighbors s :=
  (R.neighbors_nonempty s).choose_spec

theorem rawKernelSet_nonempty (R : RouteEHallRelation S T) :
    R.rawKernelSet.Nonempty := by
  classical
  let P : S → T → ℝ := fun s t => if t = R.chosenNeighbor s then 1 else 0
  refine ⟨P, ?_⟩
  constructor
  · intro s t
    by_cases h : t = R.chosenNeighbor s <;> simp [P, h]
  constructor
  · intro s
    simp [P]
  · intro s t ht
    have hne : t ≠ R.chosenNeighbor s := fun h =>
      ht (h ▸ R.chosenNeighbor_mem s)
    simp [P, hne]

theorem isClosed_rawKernelSet (R : RouteEHallRelation S T) :
    IsClosed R.rawKernelSet := by
  have hnonneg : IsClosed {P : S → T → ℝ | ∀ s t, 0 ≤ P s t} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun t =>
      isClosed_le continuous_const (continuous_apply_apply s t)
  have hrow : IsClosed {P : S → T → ℝ | ∀ s, ∑ t, P s t = 1} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun s => isClosed_eq
      (continuous_finsetSum Finset.univ fun t _ht => continuous_apply_apply s t)
      continuous_const
  have hsupp :
      IsClosed {P : S → T → ℝ | ∀ s t, t ∉ R.neighbors s → P s t = 0} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro s
    apply isClosed_iInter
    intro t
    by_cases ht : t ∈ R.neighbors s
    · simp [ht]
    · simpa [ht] using isClosed_eq (continuous_apply_apply s t) continuous_const
  simpa [rawKernelSet, setOf_and] using hnonneg.inter (hrow.inter hsupp)

theorem isCompact_rawKernelSet (R : RouteEHallRelation S T) :
    IsCompact R.rawKernelSet := by
  have hsubset : R.rawKernelSet ⊆ Set.Icc (0 : S → T → ℝ) 1 := by
    intro P hP
    exact ⟨fun s t => R.rawKernel_nonneg hP s t,
      fun s t => R.rawKernel_le_one hP s t⟩
  have hcompact : IsCompact (Set.Icc (0 : S → T → ℝ) 1) := isCompact_Icc
  simpa [Set.inter_eq_right.mpr hsubset] using
    hcompact.inter_right R.isClosed_rawKernelSet

omit [DecidableEq T] in theorem convex_rawKernelSet (R : RouteEHallRelation S T) :
    Convex ℝ R.rawKernelSet := by
  intro P hP Q hQ a b ha hb hab
  constructor
  · intro s t
    exact add_nonneg (mul_nonneg ha (R.rawKernel_nonneg hP s t))
      (mul_nonneg hb (R.rawKernel_nonneg hQ s t))
  constructor
  · intro s
    simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, R.rawKernel_row_sum hP, R.rawKernel_row_sum hQ]
    simpa only [mul_one] using hab
  · intro s t ht
    simp [R.rawKernel_eq_zero_of_not_neighbor hP s t ht,
      R.rawKernel_eq_zero_of_not_neighbor hQ s t ht]

omit [DecidableEq T] in theorem rawOutput_sum
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet) :
    ∑ t, R.rawOutput D P t = 1 := by
  simp_rw [rawOutput]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, R.rawKernel_row_sum hP, mul_one]
  exact D.source_sum

omit [DecidableEq T] in theorem rawOutput_nonneg
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet) (t : T) :
    0 ≤ R.rawOutput D P t :=
  Finset.sum_nonneg fun s _hs =>
    mul_nonneg (D.source_pos s).le (R.rawKernel_nonneg hP s t)

omit [DecidableEq T] in private theorem continuous_rawOutput
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (t : T) :
    Continuous fun P : S → T → ℝ => R.rawOutput D P t := by
  unfold rawOutput
  exact continuous_finsetSum Finset.univ fun s _hs =>
    continuous_const.mul (continuous_apply_apply s t)

/-- Weighted Euclidean coordinate of a reachable target marginal. -/
noncomputable def standardizedOutput
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (P : S → T → ℝ) : EuclideanSpace ℝ T :=
  WithLp.toLp 2 fun t => (R.rawOutput D P t - D.targetLaw t) / Real.sqrt (D.targetLaw t)

/-- Weighted chi-square of a raw output marginal against the target law. -/
noncomputable def rawChiSquare
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (P : S → T → ℝ) : ℝ :=
  ∑ t, (R.rawOutput D P t - D.targetLaw t) ^ 2 / D.targetLaw t

omit [DecidableEq T] in theorem standardizedOutput_norm_sq
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (P : S → T → ℝ) :
    ‖standardizedOutput D R P‖ ^ 2 = rawChiSquare D R P := by
  rw [EuclideanSpace.real_norm_sq_eq]
  unfold standardizedOutput rawChiSquare
  apply Finset.sum_congr rfl
  intro t _ht
  have hβ : 0 < D.targetLaw t := D.target_pos t
  rw [div_pow, Real.sq_sqrt hβ.le]

omit [DecidableEq T] in private theorem continuous_standardizedOutput
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    Continuous (standardizedOutput D R) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : T => ℝ)).symm.continuous.comp
  rw [continuous_pi_iff]
  intro t
  exact ((continuous_rawOutput D R t).sub continuous_const).div_const _

/-- Compact convex set of standardized reachable marginals. -/
def standardizedMarginalSet
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    Set (EuclideanSpace ℝ T) :=
  standardizedOutput D R '' R.rawKernelSet

theorem standardizedMarginalSet_nonempty
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    (standardizedMarginalSet D R).Nonempty :=
  R.rawKernelSet_nonempty.image _

theorem isCompact_standardizedMarginalSet
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    IsCompact (standardizedMarginalSet D R) :=
  R.isCompact_rawKernelSet.image (continuous_standardizedOutput D R)

omit [DecidableEq T] in private theorem standardizedOutput_affine
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (P Q : S → T → ℝ) (a b : ℝ) (hab : a + b = 1) :
    standardizedOutput D R (a • P + b • Q) =
      a • standardizedOutput D R P + b • standardizedOutput D R Q := by
  have hout (t : T) :
      R.rawOutput D (a • P + b • Q) t =
        a * R.rawOutput D P t + b * R.rawOutput D Q t := by
    unfold rawOutput
    calc
      (∑ s, D.sourceLaw s * (a • P + b • Q) s t) =
          ∑ s, (a * (D.sourceLaw s * P s t) +
            b * (D.sourceLaw s * Q s t)) := by
        apply Finset.sum_congr rfl
        intro s _hs
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  apply PiLp.ext
  intro t
  simp only [standardizedOutput, WithLp.ofLp_toLp, PiLp.add_apply,
    PiLp.smul_apply, smul_eq_mul]
  rw [hout]
  have hsqrt : Real.sqrt (D.targetLaw t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (D.target_pos t))
  field_simp
  linear_combination D.targetLaw t * hab

omit [DecidableEq T] in theorem convex_standardizedMarginalSet
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    Convex ℝ (standardizedMarginalSet D R) := by
  rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ a b ha hb hab
  refine ⟨a • P + b • Q, R.convex_rawKernelSet hP hQ ha hb hab, ?_⟩
  exact standardizedOutput_affine D R P Q a b hab

theorem exists_standardized_projection
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    ∃ v ∈ standardizedMarginalSet D R,
      ‖(0 : EuclideanSpace ℝ T) - v‖ =
        ⨅ w : standardizedMarginalSet D R, ‖(0 : EuclideanSpace ℝ T) - w‖ :=
  exists_norm_eq_iInf_of_complete_convex
    (standardizedMarginalSet_nonempty D R)
    (isCompact_standardizedMarginalSet D R).isComplete
    (convex_standardizedMarginalSet D R) (0 : EuclideanSpace ℝ T)

/-- Canonical choice of nearest standardized reachable marginal. -/
noncomputable def projectionPoint
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    EuclideanSpace ℝ T :=
  (exists_standardized_projection D R).choose

theorem projectionPoint_mem
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    projectionPoint D R ∈ standardizedMarginalSet D R :=
  (exists_standardized_projection D R).choose_spec.1

theorem projectionPoint_isMin
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    ‖(0 : EuclideanSpace ℝ T) - projectionPoint D R‖ =
      ⨅ w : standardizedMarginalSet D R, ‖(0 : EuclideanSpace ℝ T) - w‖ :=
  (exists_standardized_projection D R).choose_spec.2

/-- Supported kernel realizing the canonical projection point. -/
noncomputable def projectionKernel
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) : S → T → ℝ :=
  (projectionPoint_mem D R).choose

theorem projectionKernel_mem
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    projectionKernel D R ∈ R.rawKernelSet :=
  (projectionPoint_mem D R).choose_spec.1

theorem standardizedOutput_projectionKernel
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    standardizedOutput D R (projectionKernel D R) = projectionPoint D R :=
  (projectionPoint_mem D R).choose_spec.2

/-- Squared weighted distance from target law to the reachable marginal polytope. -/
noncomputable def projectionDistanceSq
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) : ℝ :=
  ‖projectionPoint D R‖ ^ 2

/-- The chosen projection realizes the exact minimum chi-square. -/
theorem projectionDistanceSq_eq_rawChiSquare
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    projectionDistanceSq D R = rawChiSquare D R (projectionKernel D R) := by
  unfold projectionDistanceSq
  rw [← standardizedOutput_projectionKernel D R,
    standardizedOutput_norm_sq]

theorem projectionDistanceSq_nonneg
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    0 ≤ projectionDistanceSq D R := by
  unfold projectionDistanceSq
  positivity

/-- Exact finite optimum: projection distance is no larger than every supported-kernel
chi-square, with no assumed optimizer. -/
theorem projectionDistanceSq_le_rawChiSquare
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet) :
    projectionDistanceSq D R ≤ rawChiSquare D R P := by
  have hiInf :
      (⨅ w : standardizedMarginalSet D R,
          ‖(0 : EuclideanSpace ℝ T) - w‖) ≤
        ‖(0 : EuclideanSpace ℝ T) - standardizedOutput D R P‖ := by
    have hbdd : BddBelow (Set.range fun w : standardizedMarginalSet D R =>
        ‖(0 : EuclideanSpace ℝ T) - w‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd
      ⟨standardizedOutput D R P, ⟨P, hP, rfl⟩⟩
  have hnorm : ‖projectionPoint D R‖ ≤ ‖standardizedOutput D R P‖ := by
    rw [← norm_neg, ← zero_sub]
    rw [projectionPoint_isMin D R]
    simpa only [zero_sub, norm_neg] using hiInf
  unfold projectionDistanceSq
  rw [← standardizedOutput_norm_sq D R P]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm

/-- Zero projection distance exactly means an exact supported transport to the target law. -/
theorem projectionDistanceSq_eq_zero_iff
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    projectionDistanceSq D R = 0 ↔
      ∃ P ∈ R.rawKernelSet, ∀ t, R.rawOutput D P t = D.targetLaw t := by
  constructor
  · intro hzero
    refine ⟨projectionKernel D R, projectionKernel_mem D R, ?_⟩
    have hnorm : ‖projectionPoint D R‖ = 0 := by
      unfold projectionDistanceSq at hzero
      nlinarith [norm_nonneg (projectionPoint D R)]
    have hpoint : projectionPoint D R = 0 := norm_eq_zero.mp hnorm
    intro t
    have hcoord := congrArg (fun v : EuclideanSpace ℝ T => v t)
      ((standardizedOutput_projectionKernel D R).trans hpoint)
    simp only [standardizedOutput, WithLp.ofLp_toLp] at hcoord
    have hsqrt : Real.sqrt (D.targetLaw t) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (D.target_pos t))
    rcases (div_eq_zero_iff).mp hcoord with hnum | hden
    · exact sub_eq_zero.mp hnum
    · exact (hsqrt hden).elim
  · rintro ⟨P, hP, hout⟩
    apply le_antisymm
    · refine (projectionDistanceSq_le_rawChiSquare D R hP).trans_eq ?_
      unfold rawChiSquare
      simp [hout]
    · exact projectionDistanceSq_nonneg D R

/-- Normalized weighted Hall condition for the physical source and target laws. -/
def WeightedHall
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) : Prop :=
  ∀ U : Finset S,
    ∑ s ∈ U, D.sourceLaw s ≤
      ∑ t ∈ U.biUnion R.neighbors, D.targetLaw t

/-- Every exact supported transport satisfies normalized weighted Hall. -/
theorem weightedHall_of_exactTransport
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet)
    (hout : ∀ t, R.rawOutput D P t = D.targetLaw t) :
    WeightedHall D R := by
  intro U
  let N := U.biUnion R.neighbors
  have houtside (t : T) (ht : t ∉ N) :
      ∑ s ∈ U, D.sourceLaw s * P s t = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have htN : t ∉ R.neighbors s := by
      intro hts
      exact ht (Finset.mem_biUnion.mpr ⟨s, hs, hts⟩)
    rw [R.rawKernel_eq_zero_of_not_neighbor hP s t htN, mul_zero]
  calc
    (∑ s ∈ U, D.sourceLaw s) =
        ∑ s ∈ U, D.sourceLaw s * ∑ t, P s t := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [R.rawKernel_row_sum hP s, mul_one]
    _ = ∑ t, ∑ s ∈ U, D.sourceLaw s * P s t := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ t ∈ N, ∑ s ∈ U, D.sourceLaw s * P s t := by
      apply Eq.symm
      apply Finset.sum_subset
        (by intro t _ht; exact Finset.mem_univ t)
      intro t _htuniv htN
      exact houtside t htN
    _ ≤ ∑ t ∈ N, R.rawOutput D P t := by
      apply Finset.sum_le_sum
      intro t _ht
      unfold rawOutput
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (by intro s _hs; exact Finset.mem_univ s)
      intro s _hs _hsU
      exact mul_nonneg (D.source_pos s).le (R.rawKernel_nonneg hP s t)
    _ = ∑ t ∈ N, D.targetLaw t := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact hout t

/-- Every supported row kernel sends the mass of a source subset into its relation-neighbor
union.  This is the exact primal cut inequality before comparison with the target law. -/
theorem sourceSubset_le_rawOutput_neighborUnion
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet) (U : Finset S) :
    ∑ s ∈ U, D.sourceLaw s ≤
      ∑ t ∈ U.biUnion R.neighbors, R.rawOutput D P t := by
  classical
  let N := U.biUnion R.neighbors
  have houtside (t : T) (ht : t ∉ N) :
      ∑ s ∈ U, D.sourceLaw s * P s t = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have htN : t ∉ R.neighbors s := by
      intro hts
      exact ht (Finset.mem_biUnion.mpr ⟨s, hs, hts⟩)
    rw [R.rawKernel_eq_zero_of_not_neighbor hP s t htN, mul_zero]
  calc
    (∑ s ∈ U, D.sourceLaw s) =
        ∑ s ∈ U, D.sourceLaw s * ∑ t, P s t := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [R.rawKernel_row_sum hP s, mul_one]
    _ = ∑ t, ∑ s ∈ U, D.sourceLaw s * P s t := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ t ∈ N, ∑ s ∈ U, D.sourceLaw s * P s t := by
      apply Eq.symm
      apply Finset.sum_subset
        (by intro t _ht; exact Finset.mem_univ t)
      intro t _htuniv htN
      exact houtside t htN
    _ ≤ ∑ t ∈ N, R.rawOutput D P t := by
      apply Finset.sum_le_sum
      intro t _ht
      unfold rawOutput
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (by intro s _hs; exact Finset.mem_univ s)
      intro s _hs _hsU
      exact mul_nonneg (D.source_pos s).le (R.rawKernel_nonneg hP s t)

/-- Positive normalized weighted-Hall deficit of a source subset. -/
def weightedHallDeficit
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (U : Finset S) : ℝ :=
  max ((∑ s ∈ U, D.sourceLaw s) -
    ∑ t ∈ U.biUnion R.neighbors, D.targetLaw t) 0

theorem weightedHallDeficit_nonneg
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (U : Finset S) :
    0 ≤ weightedHallDeficit D R U := by
  exact le_max_right _ _

/-- **Sharp normalized Hall-deficit obstruction.**  Every source cut with target-neighbor mass
`b` forces projection chi-square at least `delta²/(b(1-b))`. -/
theorem weightedHallDeficit_sq_div_le_projectionDistanceSq
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (U : Finset S)
    (hb0 : 0 < ∑ t ∈ U.biUnion R.neighbors, D.targetLaw t)
    (hb1 : ∑ t ∈ U.biUnion R.neighbors, D.targetLaw t < 1) :
    (weightedHallDeficit D R U) ^ 2 /
        ((∑ t ∈ U.biUnion R.neighbors, D.targetLaw t) *
          (1 - ∑ t ∈ U.biUnion R.neighbors, D.targetLaw t)) ≤
      projectionDistanceSq D R := by
  classical
  let N := U.biUnion R.neighbors
  let P := projectionKernel D R
  let gamma : T → ℝ := R.rawOutput D P
  let residual : T → ℝ := fun t => gamma t - D.targetLaw t
  let b : ℝ := ∑ t ∈ N, D.targetLaw t
  let d : ℝ := ∑ t ∈ N, residual t
  let delta : ℝ := weightedHallDeficit D R U
  let Ncomp : Finset T := Finset.univ.filter fun t => t ∉ N
  have hP : P ∈ R.rawKernelSet := projectionKernel_mem D R
  have hsource := sourceSubset_le_rawOutput_neighborUnion D R hP U
  have hdeltaAbs : delta ≤ |d| := by
    by_cases hdef : (∑ s ∈ U, D.sourceLaw s) - b ≤ 0
    · have hdeltaZero : delta = 0 := by
        dsimp [delta, weightedHallDeficit, b, N]
        rw [max_eq_right]
        simpa [b, N] using hdef
      rw [hdeltaZero]
      exact abs_nonneg _
    · have hdefPos : 0 < (∑ s ∈ U, D.sourceLaw s) - b := lt_of_not_ge hdef
      have hdeltaEq : delta = (∑ s ∈ U, D.sourceLaw s) - b := by
        dsimp [delta, weightedHallDeficit, b, N]
        rw [max_eq_left]
        simpa [b, N] using hdefPos.le
      have hleD : (∑ s ∈ U, D.sourceLaw s) - b ≤ d := by
        dsimp [d, residual, gamma]
        rw [Finset.sum_sub_distrib]
        simpa [b, N] using sub_le_sub_right hsource b
      rw [hdeltaEq]
      exact hleD.trans (le_abs_self d)
  have hdeltaSq : delta ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs d]
    exact (sq_le_sq₀ (weightedHallDeficit_nonneg D R U) (abs_nonneg d)).2 hdeltaAbs
  have hb0' : 0 < b := by simpa [b, N] using hb0
  have hb1' : b < 1 := by simpa [b, N] using hb1
  have hbetaComp : ∑ t ∈ Ncomp, D.targetLaw t = 1 - b := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset T) (fun t => t ∈ N) D.targetLaw
    have hsplit' : b + ∑ t ∈ Ncomp, D.targetLaw t = 1 := by
      simpa [b, Ncomp, D.target_sum] using hsplit
    linarith
  have hresidualTotal : ∑ t, residual t = 0 := by
    dsimp [residual, gamma]
    rw [Finset.sum_sub_distrib, R.rawOutput_sum D hP, D.target_sum]
    ring
  have hresidualComp : ∑ t ∈ Ncomp, residual t = -d := by
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset T) (fun t => t ∈ N) residual
    have hsplit' : d + ∑ t ∈ Ncomp, residual t = 0 := by
      simpa [d, Ncomp] using hsplit.trans hresidualTotal
    linarith
  have hcsN : d ^ 2 / b ≤ ∑ t ∈ N, residual t ^ 2 / D.targetLaw t := by
    exact Finset.sq_sum_div_le_sum_sq_div N residual
      (fun t _ht => D.target_pos t)
  have hcsComp : d ^ 2 / (1 - b) ≤
      ∑ t ∈ Ncomp, residual t ^ 2 / D.targetLaw t := by
    have hcs := Finset.sq_sum_div_le_sum_sq_div Ncomp residual
      (fun t _ht => D.target_pos t)
    rw [hbetaComp, hresidualComp, neg_sq] at hcs
    exact hcs
  have henergySplit : rawChiSquare D R P =
      (∑ t ∈ N, residual t ^ 2 / D.targetLaw t) +
        ∑ t ∈ Ncomp, residual t ^ 2 / D.targetLaw t := by
    unfold rawChiSquare
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset T) (fun t => t ∈ N)
      (fun t => (R.rawOutput D P t - D.targetLaw t) ^ 2 / D.targetLaw t)
    simpa [residual, gamma, Ncomp] using hsplit.symm
  have hdEnergy : d ^ 2 / b + d ^ 2 / (1 - b) ≤ rawChiSquare D R P := by
    rw [henergySplit]
    exact add_le_add hcsN hcsComp
  have hdenom : 0 < b * (1 - b) := mul_pos hb0' (sub_pos.mpr hb1')
  calc
    delta ^ 2 / (b * (1 - b)) ≤ d ^ 2 / (b * (1 - b)) :=
      div_le_div_of_nonneg_right hdeltaSq hdenom.le
    _ = d ^ 2 / b + d ^ 2 / (1 - b) := by
      field_simp [ne_of_gt hb0', ne_of_gt (sub_pos.mpr hb1')]
      ring
    _ ≤ rawChiSquare D R P := hdEnergy
    _ = projectionDistanceSq D R :=
      (projectionDistanceSq_eq_rawChiSquare D R).symm

theorem projection_variational_inequality
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet) :
    inner ℝ (projectionPoint D R)
        (standardizedOutput D R P - projectionPoint D R) ≥ 0 := by
  have hchar :=
    (norm_eq_iInf_iff_real_inner_le_zero (convex_standardizedMarginalSet D R)
      (projectionPoint_mem D R)).1 (projectionPoint_isMin D R)
      (standardizedOutput D R P) ⟨P, hP, rfl⟩
  simpa [real_inner_comm] using neg_nonneg.mpr hchar

private theorem projection_variational_inequality_raw
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet) :
    0 ≤ ∑ t,
      ((R.rawOutput D (projectionKernel D R) t - D.targetLaw t) / D.targetLaw t) *
        (R.rawOutput D P t - R.rawOutput D (projectionKernel D R) t) := by
  have h := projection_variational_inequality D R hP
  rw [← standardizedOutput_projectionKernel D R] at h
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    WithLp.ofLp_sub, standardizedOutput, Pi.sub_apply] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro t _ht
  have hβ : 0 < D.targetLaw t := D.target_pos t
  have hsqrt : Real.sqrt (D.targetLaw t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hβ)
  field_simp [ne_of_gt hβ, hsqrt]
  rw [Real.sq_sqrt hβ.le]
  ring

/-! ## Exact reporter lower envelope -/

omit [DecidableEq T] in private theorem exists_neighbor_argmin
    (R : RouteEHallRelation S T) (f : T → ℝ) (s : S) :
    ∃ t ∈ R.neighbors s, ∀ u ∈ R.neighbors s, f t ≤ f u := by
  classical
  let image := (R.neighbors s).image f
  have himage : image.Nonempty := (R.neighbors_nonempty s).image f
  let m := image.min' himage
  have hm : m ∈ image := Finset.min'_mem image himage
  rcases Finset.mem_image.mp hm with ⟨t, ht, hft⟩
  refine ⟨t, ht, ?_⟩
  intro u hu
  rw [hft]
  exact Finset.min'_le image (f u) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)

noncomputable def neighborArgmin
    (R : RouteEHallRelation S T) (f : T → ℝ) (s : S) : T :=
  (R.exists_neighbor_argmin f s).choose

omit [DecidableEq T] in theorem neighborArgmin_mem
    (R : RouteEHallRelation S T) (f : T → ℝ) (s : S) :
    R.neighborArgmin f s ∈ R.neighbors s :=
  (R.exists_neighbor_argmin f s).choose_spec.1

omit [DecidableEq T] in theorem neighborArgmin_le
    (R : RouteEHallRelation S T) (f : T → ℝ) (s : S)
    {t : T} (ht : t ∈ R.neighbors s) :
    f (R.neighborArgmin f s) ≤ f t :=
  (R.exists_neighbor_argmin f s).choose_spec.2 t ht

/-- Nonlinear relation lower envelope `M_E f`. -/
noncomputable def reporterLowerEnvelope
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) : ℝ :=
  ∑ s, D.sourceLaw s * f (R.neighborArgmin f s)

/-! ## Finite upper-tail layer cake -/

private noncomputable def finiteUpperCutMass
    {I : Type*} [Fintype I] (weight height : I → ℝ) (z : ℝ) : ℝ :=
  ∑ i, if z ∈ Set.Ioo 0 (height i) then weight i else 0

private theorem finiteUpperCutMass_integrable
    {I : Type*} [Fintype I] (weight height : I → ℝ) :
    MeasureTheory.Integrable (finiteUpperCutMass weight height) := by
  classical
  unfold finiteUpperCutMass
  apply MeasureTheory.integrable_finsetSum Finset.univ
  intro i _hi
  have hfun : (fun z : ℝ => if z ∈ Set.Ioo 0 (height i) then weight i else 0) =
      (Set.Ioo 0 (height i)).indicator (fun _ => weight i) := by
    funext z
    by_cases hz : z ∈ Set.Ioo 0 (height i) <;> simp [hz]
  rw [hfun, MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
  exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioo])

/-- Finite layer cake for a nonnegative height function.  This is the exact bridge from all
strict upper cuts to a weighted first moment. -/
private theorem integral_finiteUpperCutMass
    {I : Type*} [Fintype I] (weight height : I → ℝ)
    (hheight : ∀ i, 0 ≤ height i) :
    (∫ z : ℝ, finiteUpperCutMass weight height z) =
      ∑ i, weight i * height i := by
  classical
  unfold finiteUpperCutMass
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    have hfun : (fun z : ℝ => if z ∈ Set.Ioo 0 (height i) then weight i else 0) =
        (Set.Ioo 0 (height i)).indicator (fun _ => weight i) := by
      funext z
      by_cases hz : z ∈ Set.Ioo 0 (height i) <;> simp [hz]
    rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioo,
      MeasureTheory.setIntegral_const]
    simp [MeasureTheory.Measure.real_def, Real.volume_Ioo, hheight i]
    ring
  · intro i _hi
    have hfun : (fun z : ℝ => if z ∈ Set.Ioo 0 (height i) then weight i else 0) =
        (Set.Ioo 0 (height i)).indicator (fun _ => weight i) := by
      funext z
      by_cases hz : z ∈ Set.Ioo 0 (height i) <;> simp [hz]
    rw [hfun, MeasureTheory.integrable_indicator_iff measurableSet_Ioo]
    exact MeasureTheory.integrableOn_const (by simp [Real.volume_Ioo])

/-- **Weighted Hall suffices for every nonlinear reporter inequality.**  The proof is a finite
layer-cake argument: every upper cut of the rowwise neighbor minimum has its whole neighbor union
inside the corresponding target upper cut, so weighted Hall compares all tails. -/
theorem reporterLowerEnvelope_le_target_of_weightedHall
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (hHall : WeightedHall D R) (f : T → ℝ) :
    reporterLowerEnvelope D R f ≤ ∑ t, D.targetLaw t * f t := by
  classical
  have hcardS : 0 < Fintype.card S := by
    by_contra h
    have hzero : Fintype.card S = 0 := Nat.eq_zero_of_not_pos h
    have huniv : (Finset.univ : Finset S) = ∅ := Finset.card_eq_zero.mp (by simpa using hzero)
    have hsum := D.source_sum
    rw [huniv] at hsum
    simp at hsum
  letI : Nonempty S := Fintype.card_pos_iff.mp hcardS
  let s₀ : S := Classical.choice (inferInstance : Nonempty S)
  letI : Nonempty T := ⟨R.chosenNeighbor s₀⟩
  obtain ⟨t₀, ht₀⟩ := Finite.exists_min f
  let c : ℝ := f t₀
  let sourceHeight : S → ℝ := fun s => f (R.neighborArgmin f s) - c
  let targetHeight : T → ℝ := fun t => f t - c
  have hsourceHeight : ∀ s, 0 ≤ sourceHeight s := by
    intro s
    dsimp [sourceHeight, c]
    exact sub_nonneg.mpr (ht₀ (R.neighborArgmin f s))
  have htargetHeight : ∀ t, 0 ≤ targetHeight t := by
    intro t
    dsimp [targetHeight, c]
    exact sub_nonneg.mpr (ht₀ t)
  have htail : ∀ z,
      finiteUpperCutMass D.sourceLaw sourceHeight z ≤
        finiteUpperCutMass D.targetLaw targetHeight z := by
    intro z
    by_cases hz : 0 < z
    · let U : Finset S := Finset.univ.filter fun s => z < sourceHeight s
      let A : Finset T := Finset.univ.filter fun t => z < targetHeight t
      have hneighbor : U.biUnion R.neighbors ⊆ A := by
        intro t ht
        rcases Finset.mem_biUnion.mp ht with ⟨s, hs, hst⟩
        have hzs : z < sourceHeight s := (Finset.mem_filter.mp hs).2
        have hmin : sourceHeight s ≤ targetHeight t := by
          dsimp [sourceHeight, targetHeight]
          exact sub_le_sub_right (R.neighborArgmin_le f s hst) c
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, hzs.trans_le hmin⟩
      have hcut := hHall U
      have htargetCut :
          ∑ t ∈ U.biUnion R.neighbors, D.targetLaw t ≤
            ∑ t ∈ A, D.targetLaw t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hneighbor
        intro t _htA _htN
        exact (D.target_pos t).le
      calc
        finiteUpperCutMass D.sourceLaw sourceHeight z =
            ∑ s ∈ U, D.sourceLaw s := by
          unfold finiteUpperCutMass
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro s _hs
          simp only [Set.mem_Ioo]
          by_cases hzs : z < sourceHeight s <;> simp [hz, hzs]
        _ ≤ ∑ t ∈ U.biUnion R.neighbors, D.targetLaw t := hcut
        _ ≤ ∑ t ∈ A, D.targetLaw t := htargetCut
        _ = finiteUpperCutMass D.targetLaw targetHeight z := by
          unfold finiteUpperCutMass
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro t _ht
          simp only [Set.mem_Ioo]
          by_cases hzt : z < targetHeight t <;> simp [hz, hzt]
    · unfold finiteUpperCutMass
      apply le_of_eq
      simp only [Set.mem_Ioo]
      simp [hz]
  have hintegral := MeasureTheory.integral_mono
    (finiteUpperCutMass_integrable D.sourceLaw sourceHeight)
    (finiteUpperCutMass_integrable D.targetLaw targetHeight) htail
  rw [integral_finiteUpperCutMass D.sourceLaw sourceHeight hsourceHeight,
    integral_finiteUpperCutMass D.targetLaw targetHeight htargetHeight] at hintegral
  have hsourceShift :
      (∑ s, D.sourceLaw s * sourceHeight s) = reporterLowerEnvelope D R f - c := by
    unfold reporterLowerEnvelope
    dsimp [sourceHeight]
    calc
      (∑ s, D.sourceLaw s * (f (R.neighborArgmin f s) - c)) =
          (∑ s, D.sourceLaw s * f (R.neighborArgmin f s)) -
            c * ∑ s, D.sourceLaw s := by
        rw [mul_comm c, Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro s _hs
        ring
      _ = (∑ s, D.sourceLaw s * f (R.neighborArgmin f s)) - c := by
        rw [D.source_sum]
        ring
  have htargetShift :
      (∑ t, D.targetLaw t * targetHeight t) =
        (∑ t, D.targetLaw t * f t) - c := by
    dsimp [targetHeight]
    calc
      (∑ t, D.targetLaw t * (f t - c)) =
          (∑ t, D.targetLaw t * f t) - c * ∑ t, D.targetLaw t := by
        rw [mul_comm c, Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      _ = (∑ t, D.targetLaw t * f t) - c := by
        rw [D.target_sum]
        ring
  rw [hsourceShift, htargetShift] at hintegral
  linarith

theorem reporterLowerEnvelope_le_kernel
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (f : T → ℝ) {P : S → T → ℝ} (hP : P ∈ R.rawKernelSet) :
    reporterLowerEnvelope D R f ≤ ∑ t, f t * R.rawOutput D P t := by
  have hrow (s : S) :
      f (R.neighborArgmin f s) ≤ ∑ t, P s t * f t := by
    calc
      f (R.neighborArgmin f s) =
          ∑ t, P s t * f (R.neighborArgmin f s) := by
        rw [← Finset.sum_mul, R.rawKernel_row_sum hP s, one_mul]
      _ ≤ ∑ t, P s t * f t := by
        apply Finset.sum_le_sum
        intro t _ht
        by_cases ht : t ∈ R.neighbors s
        · exact mul_le_mul_of_nonneg_left (R.neighborArgmin_le f s ht)
            (R.rawKernel_nonneg hP s t)
        · simp [R.rawKernel_eq_zero_of_not_neighbor hP s t ht]
  calc
    reporterLowerEnvelope D R f ≤
        ∑ s, D.sourceLaw s * ∑ t, P s t * f t := by
      apply Finset.sum_le_sum
      intro s _hs
      exact mul_le_mul_of_nonneg_left (hrow s) (D.source_pos s).le
    _ = ∑ t, f t * R.rawOutput D P t := by
      unfold rawOutput
      calc
        (∑ s, D.sourceLaw s * ∑ t, P s t * f t) =
            ∑ s, ∑ t, D.sourceLaw s * P s t * f t := by
          apply Finset.sum_congr rfl
          intro s _hs
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t _ht
          ring
        _ = ∑ t, ∑ s, D.sourceLaw s * P s t * f t := Finset.sum_comm
        _ = ∑ t, f t * ∑ s, D.sourceLaw s * P s t := by
          apply Finset.sum_congr rfl
          intro t _ht
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _hs
          ring

noncomputable def argminKernel
    (R : RouteEHallRelation S T) (f : T → ℝ) : S → T → ℝ :=
  fun s t => if t = R.neighborArgmin f s then 1 else 0

theorem argminKernel_mem
    (R : RouteEHallRelation S T) (f : T → ℝ) :
    R.argminKernel f ∈ R.rawKernelSet := by
  classical
  constructor
  · intro s t
    by_cases h : t = R.neighborArgmin f s <;> simp [argminKernel, h]
  constructor
  · intro s
    simp [argminKernel]
  · intro s t ht
    have hne : t ≠ R.neighborArgmin f s := fun h =>
      ht (h ▸ R.neighborArgmin_mem f s)
    simp [argminKernel, hne]

theorem reporterLowerEnvelope_eq_argminKernel
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) :
    reporterLowerEnvelope D R f =
      ∑ t, f t * R.rawOutput D (R.argminKernel f) t := by
  unfold reporterLowerEnvelope rawOutput argminKernel
  classical
  calc
    (∑ s, D.sourceLaw s * f (R.neighborArgmin f s)) =
        ∑ s, ∑ t,
          D.sourceLaw s * (if t = R.neighborArgmin f s then 1 else 0) * f t := by
      apply Finset.sum_congr rfl
      intro s _hs
      simp
    _ = ∑ t, ∑ s,
          D.sourceLaw s * (if t = R.neighborArgmin f s then 1 else 0) * f t :=
      Finset.sum_comm
    _ = ∑ t, f t * ∑ s,
          D.sourceLaw s * (if t = R.neighborArgmin f s then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      ring

/-- Reporter selected by the canonical projection. -/
noncomputable def projectionReporter
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (t : T) : ℝ :=
  (R.rawOutput D (projectionKernel D R) t - D.targetLaw t) / D.targetLaw t

theorem projectionReporter_centered
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    ∑ t, D.targetLaw t * projectionReporter D R t = 0 := by
  unfold projectionReporter
  have hβ (t : T) : D.targetLaw t ≠ 0 := ne_of_gt (D.target_pos t)
  simp_rw [mul_div_cancel₀ _ (hβ _), Finset.sum_sub_distrib,
    R.rawOutput_sum D (projectionKernel_mem D R), D.target_sum, sub_self]

theorem projectionReporter_secondMoment
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    ∑ t, D.targetLaw t * (projectionReporter D R t) ^ 2 =
      projectionDistanceSq D R := by
  unfold projectionDistanceSq projectionReporter
  rw [← standardizedOutput_projectionKernel D R,
    EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro t _ht
  have hβ : 0 < D.targetLaw t := D.target_pos t
  have hsqrt : Real.sqrt (D.targetLaw t) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hβ)
  simp only [standardizedOutput, WithLp.ofLp_toLp]
  rw [div_pow, div_pow, Real.sq_sqrt hβ.le]
  field_simp [ne_of_gt hβ]

theorem reporterLowerEnvelope_projectionReporter
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    reporterLowerEnvelope D R (projectionReporter D R) =
      ∑ t, projectionReporter D R t *
        R.rawOutput D (projectionKernel D R) t := by
  apply le_antisymm
  · exact reporterLowerEnvelope_le_kernel D R _ (projectionKernel_mem D R)
  · rw [reporterLowerEnvelope_eq_argminKernel D R]
    have hvar := projection_variational_inequality_raw D R
      (R.argminKernel_mem (projectionReporter D R))
    change 0 ≤ ∑ t, projectionReporter D R t *
      (R.rawOutput D (R.argminKernel (projectionReporter D R)) t -
        R.rawOutput D (projectionKernel D R) t) at hvar
    have hrearrange :
        (∑ t, projectionReporter D R t *
          (R.rawOutput D (R.argminKernel (projectionReporter D R)) t -
            R.rawOutput D (projectionKernel D R) t)) =
          (∑ t, projectionReporter D R t *
            R.rawOutput D (R.argminKernel (projectionReporter D R)) t) -
          ∑ t, projectionReporter D R t *
            R.rawOutput D (projectionKernel D R) t := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    rw [hrearrange] at hvar
    linarith

/-- The canonical projection reporter's nonlinear gap is exactly the squared projection
distance. -/
theorem projectionReporter_gap_eq_projectionDistanceSq
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    reporterLowerEnvelope D R (projectionReporter D R) -
        ∑ t, D.targetLaw t * projectionReporter D R t =
      projectionDistanceSq D R := by
  rw [reporterLowerEnvelope_projectionReporter D R,
    projectionReporter_centered D R, sub_zero]
  calc
    (∑ t, projectionReporter D R t *
        R.rawOutput D (projectionKernel D R) t) =
        ∑ t, (D.targetLaw t * (projectionReporter D R t) ^ 2 +
          D.targetLaw t * projectionReporter D R t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      unfold projectionReporter
      have hβ : D.targetLaw t ≠ 0 := ne_of_gt (D.target_pos t)
      field_simp
      ring
    _ = (∑ t, D.targetLaw t * (projectionReporter D R t) ^ 2) +
        ∑ t, D.targetLaw t * projectionReporter D R t :=
      Finset.sum_add_distrib
    _ = projectionDistanceSq D R := by
      rw [projectionReporter_secondMoment D R, projectionReporter_centered D R, add_zero]

/-- **Weighted Hall sufficiency.**  Normalized weighted Hall forces the canonical projection
distance to vanish and hence constructs an exact supported transport internally. -/
theorem exactTransport_of_weightedHall
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T)
    (hHall : WeightedHall D R) :
    ∃ P ∈ R.rawKernelSet, ∀ t, R.rawOutput D P t = D.targetLaw t := by
  have hlower := reporterLowerEnvelope_le_target_of_weightedHall
    D R hHall (projectionReporter D R)
  have hgap := projectionReporter_gap_eq_projectionDistanceSq D R
  have hle : projectionDistanceSq D R ≤ 0 := by
    rw [← hgap]
    linarith
  have hzero : projectionDistanceSq D R = 0 :=
    le_antisymm hle (projectionDistanceSq_nonneg D R)
  exact (projectionDistanceSq_eq_zero_iff D R).mp hzero

/-- Exact finite weighted Hall theorem for positive normalized source and target laws. -/
theorem weightedHall_iff_exactTransport
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    WeightedHall D R ↔
      ∃ P ∈ R.rawKernelSet, ∀ t, R.rawOutput D P t = D.targetLaw t := by
  constructor
  · exact exactTransport_of_weightedHall D R
  · rintro ⟨P, hP, hout⟩
    exact weightedHall_of_exactTransport D R hP hout

/-- Weighted Hall is exactly the zero set of the chi-square projection distance. -/
theorem weightedHall_iff_projectionDistanceSq_eq_zero
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    WeightedHall D R ↔ projectionDistanceSq D R = 0 := by
  rw [projectionDistanceSq_eq_zero_iff D R]
  exact weightedHall_iff_exactTransport D R

/-- Nonlinear reporter objective from equation (12). -/
noncomputable def reporterObjective
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) : ℝ :=
  2 * (reporterLowerEnvelope D R f - ∑ t, D.targetLaw t * f t) -
    ∑ t, D.targetLaw t * (f t) ^ 2

/-- Exact projection duality: squared projection distance is greatest reporter objective value,
and the canonical projection reporter attains it. -/
theorem projection_reporter_duality
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    IsGreatest (Set.range (reporterObjective D R)) (projectionDistanceSq D R) := by
  constructor
  · refine ⟨projectionReporter D R, ?_⟩
    unfold reporterObjective
    rw [reporterLowerEnvelope_projectionReporter D R,
      projectionReporter_centered D R,
      projectionReporter_secondMoment D R]
    have hid :
        (∑ t, projectionReporter D R t *
          R.rawOutput D (projectionKernel D R) t) =
          projectionDistanceSq D R := by
      calc
        _ = ∑ t, D.targetLaw t * (projectionReporter D R t) ^ 2 +
            ∑ t, D.targetLaw t * projectionReporter D R t := by
          apply Eq.symm
          calc
            _ = ∑ t, (D.targetLaw t * (projectionReporter D R t) ^ 2 +
                D.targetLaw t * projectionReporter D R t) := by
              rw [Finset.sum_add_distrib]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro t _ht
              unfold projectionReporter
              have hβ : D.targetLaw t ≠ 0 := ne_of_gt (D.target_pos t)
              field_simp
              ring
        _ = _ := by rw [projectionReporter_secondMoment D R,
          projectionReporter_centered D R, add_zero]
    rw [hid]
    ring
  · rintro y ⟨f, rfl⟩
    unfold reporterObjective
    have hlower := reporterLowerEnvelope_le_kernel D R f (projectionKernel_mem D R)
    have hsquare :
        2 * (∑ t, f t *
            (R.rawOutput D (projectionKernel D R) t - D.targetLaw t)) -
            ∑ t, D.targetLaw t * (f t) ^ 2 ≤
          projectionDistanceSq D R := by
      have hβsum :
          (∑ t, f t *
            (R.rawOutput D (projectionKernel D R) t - D.targetLaw t)) =
          ∑ t, D.targetLaw t * f t * projectionReporter D R t := by
        apply Finset.sum_congr rfl
        intro t _ht
        unfold projectionReporter
        have hβ : D.targetLaw t ≠ 0 := ne_of_gt (D.target_pos t)
        field_simp
      rw [hβsum, ← projectionReporter_secondMoment D R]
      calc
        2 * (∑ t, D.targetLaw t * f t * projectionReporter D R t) -
            ∑ t, D.targetLaw t * f t ^ 2 =
            ∑ t, (2 * D.targetLaw t * f t * projectionReporter D R t -
              D.targetLaw t * f t ^ 2) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro t _ht
          ring
        _ ≤ ∑ t, D.targetLaw t * projectionReporter D R t ^ 2 := by
          apply Finset.sum_le_sum
          intro t _ht
          have hβ := (D.target_pos t).le
          nlinarith [mul_nonneg hβ
            (sq_nonneg (f t - projectionReporter D R t))]
    have hrearrange :
        (∑ t, f t * R.rawOutput D (projectionKernel D R) t) -
            ∑ t, D.targetLaw t * f t =
          ∑ t, f t *
            (R.rawOutput D (projectionKernel D R) t - D.targetLaw t) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    rw [← hrearrange] at hsquare
    linarith

/-! ## Homogeneous reporter dual -/

/-- Target-law reporter mean. -/
def reporterMean (D : RouteEHallANOVAData S T) (f : T → ℝ) : ℝ :=
  ∑ t, D.targetLaw t * f t

/-- Target-law reporter variance. -/
def reporterVariance (D : RouteEHallANOVAData S T) (f : T → ℝ) : ℝ :=
  ∑ t, D.targetLaw t * (f t - reporterMean D f) ^ 2

/-- Positive nonlinear reporter gap. -/
noncomputable def reporterPositiveGap
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) : ℝ :=
  max (reporterLowerEnvelope D R f - reporterMean D f) 0

/-- Totalized homogeneous reporter quotient.  Zero-variance reporters receive value zero, which
also covers the degenerate one-target case without adding a nontriviality hypothesis. -/
noncomputable def homogeneousReporterRatio
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) : ℝ :=
  reporterPositiveGap D R f / Real.sqrt (reporterVariance D f)

omit [DecidableEq T] in theorem reporterVariance_nonneg
    (D : RouteEHallANOVAData S T) (f : T → ℝ) :
    0 ≤ reporterVariance D f := by
  unfold reporterVariance
  exact Finset.sum_nonneg fun t _ht => mul_nonneg (D.target_pos t).le (sq_nonneg _)

omit [DecidableEq T] in theorem reporterPositiveGap_nonneg
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) :
    0 ≤ reporterPositiveGap D R f := by
  exact le_max_right _ _

theorem reporterVariance_projectionReporter
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    reporterVariance D (projectionReporter D R) = projectionDistanceSq D R := by
  unfold reporterVariance reporterMean
  rw [projectionReporter_centered D R]
  simp only [sub_zero]
  exact projectionReporter_secondMoment D R

theorem reporterPositiveGap_projectionReporter
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    reporterPositiveGap D R (projectionReporter D R) = projectionDistanceSq D R := by
  unfold reporterPositiveGap reporterMean
  rw [projectionReporter_gap_eq_projectionDistanceSq D R,
    max_eq_left (projectionDistanceSq_nonneg D R)]

/-- Every reporter gap is bounded by covariance with the canonical projection reporter. -/
theorem reporterGap_le_projectionCovariance
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) :
    reporterLowerEnvelope D R f - reporterMean D f ≤
      ∑ t, D.targetLaw t * (f t - reporterMean D f) * projectionReporter D R t := by
  have hlower := reporterLowerEnvelope_le_kernel D R f (projectionKernel_mem D R)
  have hraw :
      (∑ t, f t * R.rawOutput D (projectionKernel D R) t) - reporterMean D f =
        ∑ t, D.targetLaw t * f t * projectionReporter D R t := by
    unfold reporterMean
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    unfold projectionReporter
    have hβ : D.targetLaw t ≠ 0 := ne_of_gt (D.target_pos t)
    field_simp
  have hcenter :
      (∑ t, D.targetLaw t * f t * projectionReporter D R t) =
        ∑ t, D.targetLaw t * (f t - reporterMean D f) * projectionReporter D R t := by
    have hzero := projectionReporter_centered D R
    calc
      (∑ t, D.targetLaw t * f t * projectionReporter D R t) =
          (∑ t, D.targetLaw t * (f t - reporterMean D f) *
            projectionReporter D R t) +
            reporterMean D f * ∑ t, D.targetLaw t * projectionReporter D R t := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      _ = _ := by rw [hzero, mul_zero, add_zero]
  rw [← hcenter, ← hraw]
  linarith

/-- Weighted Cauchy--Schwarz for the centered reporter and canonical projection reporter. -/
theorem abs_projectionCovariance_le_sqrt_variance_mul_sqrt_distance
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) :
    |∑ t, D.targetLaw t * (f t - reporterMean D f) * projectionReporter D R t| ≤
      Real.sqrt (reporterVariance D f) * Real.sqrt (projectionDistanceSq D R) := by
  let a : T → ℝ := fun t =>
    Real.sqrt (D.targetLaw t) * |f t - reporterMean D f|
  let b : T → ℝ := fun t =>
    Real.sqrt (D.targetLaw t) * |projectionReporter D R t|
  calc
    |∑ t, D.targetLaw t * (f t - reporterMean D f) * projectionReporter D R t| ≤
        ∑ t, |D.targetLaw t * (f t - reporterMean D f) * projectionReporter D R t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t, a t * b t := by
      apply Finset.sum_congr rfl
      intro t _ht
      dsimp [a, b]
      rw [abs_mul, abs_mul, abs_of_pos (D.target_pos t)]
      have hsqrt : Real.sqrt (D.targetLaw t) * Real.sqrt (D.targetLaw t) =
          D.targetLaw t := Real.mul_self_sqrt (D.target_pos t).le
      calc
        D.targetLaw t * |f t - reporterMean D f| * |projectionReporter D R t| =
            (Real.sqrt (D.targetLaw t) * Real.sqrt (D.targetLaw t)) *
              |f t - reporterMean D f| * |projectionReporter D R t| := by rw [hsqrt]
        _ = Real.sqrt (D.targetLaw t) * |f t - reporterMean D f| *
              (Real.sqrt (D.targetLaw t) * |projectionReporter D R t|) := by ring
    _ ≤ Real.sqrt (∑ t, a t ^ 2) * Real.sqrt (∑ t, b t ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
    _ = Real.sqrt (reporterVariance D f) * Real.sqrt (projectionDistanceSq D R) := by
      congr 1
      · unfold reporterVariance
        apply congrArg Real.sqrt
        apply Finset.sum_congr rfl
        intro t _ht
        dsimp [a]
        rw [mul_pow, sq_abs, Real.sq_sqrt (D.target_pos t).le]
      · rw [← reporterVariance_projectionReporter D R]
        apply congrArg Real.sqrt
        unfold reporterVariance
        rw [show reporterMean D (projectionReporter D R) = 0 by
          exact projectionReporter_centered D R]
        apply Finset.sum_congr rfl
        intro t _ht
        dsimp [b]
        rw [sub_zero, mul_pow, sq_abs, Real.sq_sqrt (D.target_pos t).le]

/-- Exact all-reporter inequality with optimal constant `sqrt projectionDistanceSq`. -/
theorem reporterGap_le_sqrt_projectionDistanceSq_mul_sqrt_variance
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) :
    reporterLowerEnvelope D R f - reporterMean D f ≤
      Real.sqrt (projectionDistanceSq D R) * Real.sqrt (reporterVariance D f) := by
  let covariance :=
    ∑ t, D.targetLaw t * (f t - reporterMean D f) * projectionReporter D R t
  calc
    reporterLowerEnvelope D R f - reporterMean D f ≤ covariance :=
      reporterGap_le_projectionCovariance D R f
    _ ≤ |covariance| := le_abs_self covariance
    _ ≤ Real.sqrt (reporterVariance D f) * Real.sqrt (projectionDistanceSq D R) :=
      abs_projectionCovariance_le_sqrt_variance_mul_sqrt_distance D R f
    _ = Real.sqrt (projectionDistanceSq D R) * Real.sqrt (reporterVariance D f) :=
      mul_comm _ _

/-- Homogeneous reporter quotient is bounded by projection distance, including zero variance. -/
theorem homogeneousReporterRatio_le_sqrt_projectionDistanceSq
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) (f : T → ℝ) :
    homogeneousReporterRatio D R f ≤ Real.sqrt (projectionDistanceSq D R) := by
  let gap := reporterLowerEnvelope D R f - reporterMean D f
  let covariance :=
    ∑ t, D.targetLaw t * (f t - reporterMean D f) * projectionReporter D R t
  have hgapCov : gap ≤ covariance := reporterGap_le_projectionCovariance D R f
  have hcovAbs : |covariance| ≤
      Real.sqrt (reporterVariance D f) * Real.sqrt (projectionDistanceSq D R) :=
    abs_projectionCovariance_le_sqrt_variance_mul_sqrt_distance D R f
  have hpositiveGap : reporterPositiveGap D R f ≤ |covariance| := by
    unfold reporterPositiveGap
    dsimp [gap] at hgapCov
    rw [max_le_iff]
    exact ⟨hgapCov.trans (le_abs_self covariance), abs_nonneg covariance⟩
  by_cases hvar : reporterVariance D f = 0
  · unfold homogeneousReporterRatio
    rw [hvar, Real.sqrt_zero, div_zero]
    exact Real.sqrt_nonneg _
  · have hvarPos : 0 < reporterVariance D f :=
      lt_of_le_of_ne (reporterVariance_nonneg D f) (Ne.symm hvar)
    have hsqrtPos : 0 < Real.sqrt (reporterVariance D f) := Real.sqrt_pos.2 hvarPos
    unfold homogeneousReporterRatio
    apply (div_le_iff₀ hsqrtPos).2
    calc
      reporterPositiveGap D R f ≤ |covariance| := hpositiveGap
      _ ≤ Real.sqrt (reporterVariance D f) * Real.sqrt (projectionDistanceSq D R) :=
        hcovAbs
      _ = Real.sqrt (projectionDistanceSq D R) * Real.sqrt (reporterVariance D f) :=
        mul_comm _ _

/-- **Exact homogeneous reporter duality.**  Squared-distance zero is handled by the zero
reporter; positive distance is attained by the canonical projection reporter. -/
theorem projection_homogeneous_reporter_duality
    (D : RouteEHallANOVAData S T) (R : RouteEHallRelation S T) :
    IsGreatest (Set.range (homogeneousReporterRatio D R))
      (Real.sqrt (projectionDistanceSq D R)) := by
  constructor
  · by_cases hzero : projectionDistanceSq D R = 0
    · refine ⟨fun _ => 0, ?_⟩
      rw [hzero, Real.sqrt_zero]
      unfold homogeneousReporterRatio reporterPositiveGap reporterVariance reporterMean
      simp [reporterLowerEnvelope]
    · refine ⟨projectionReporter D R, ?_⟩
      unfold homogeneousReporterRatio
      rw [reporterPositiveGap_projectionReporter D R,
        reporterVariance_projectionReporter D R]
      have hdPos : 0 < projectionDistanceSq D R :=
        lt_of_le_of_ne (projectionDistanceSq_nonneg D R) (Ne.symm hzero)
      have hsqrtPos : 0 < Real.sqrt (projectionDistanceSq D R) := Real.sqrt_pos.2 hdPos
      apply (div_eq_iff (ne_of_gt hsqrtPos)).2
      exact (Real.mul_self_sqrt hdPos.le).symm
  · rintro _ ⟨f, rfl⟩
    exact homogeneousReporterRatio_le_sqrt_projectionDistanceSq D R f

end RouteEHallRelation

end RHTower
