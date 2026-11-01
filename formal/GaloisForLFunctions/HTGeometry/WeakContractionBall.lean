import GaloisForLFunctions.HTGeometry.WeakHilbertCompactness
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Weak compactness of finite-column contraction balls

A map from a finite-dimensional Euclidean space is represented by its
columns in a finite Hilbert product. Contractivity is a family of weakly
closed convex norm inequalities. Each column has norm at most one, so the
whole contraction ball is weakly compact.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset Set
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry.WeakContraction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {m : ℕ}

/-- Hilbert space of finite column families. -/
abbrev Columns (H : Type*) (m : ℕ) := PiLp 2 (fun _ : Fin m => H)

/-- Evaluation of a column family at a fixed coefficient vector. -/
def columnEvaluation (x : EuclideanSpace ℂ (Fin m)) : Columns H m →L[ℂ] H :=
  ∑ i, x i • PiLp.proj 2 (fun _ : Fin m => H) i

theorem columnEvaluation_apply (x : EuclideanSpace ℂ (Fin m)) (z : Columns H m) :
    columnEvaluation x z = ∑ i, x i • z i := by
  simp [columnEvaluation]

theorem columnEvaluation_single (i : Fin m) (z : Columns H m) :
    columnEvaluation (PiLp.single 2 i (1 : ℂ)) z = z i := by
  simp [columnEvaluation_apply, PiLp.single_apply]

/-- Linear operator represented by a column family. -/
def columnOperator (z : Columns H m) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] H where
  toFun x := ∑ i, x i • z i
  map_add' x y := by
    change (∑ i, (x i + y i) • z i) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i, (c * x i) • z i) = c • ∑ i, x i • z i
    simp only [Finset.smul_sum, mul_smul]

theorem columnOperator_apply (z : Columns H m) (x : EuclideanSpace ℂ (Fin m)) :
    columnOperator z x = columnEvaluation x z := (columnEvaluation_apply x z).symm

/-- The standard Euclidean vectors reconstruct every coefficient vector. -/
theorem sum_single_basis (x : EuclideanSpace ℂ (Fin m)) :
    (∑ i, x i • PiLp.single 2 i (1 : ℂ)) = x := by
  apply PiLp.ext
  intro j
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero]
  simp

/-- Columns of a linear operator on the finite Euclidean space. -/
def toColumns (L : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] H) : Columns H m :=
  WithLp.toLp 2 (fun i => L (PiLp.single 2 i (1 : ℂ)))

theorem columnOperator_toColumns (L : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] H) :
    columnOperator (toColumns L) = L := by
  apply LinearMap.ext
  intro x
  change (∑ i, x i • L (PiLp.single 2 i (1 : ℂ))) = L x
  calc
    _ = L (∑ i, x i • PiLp.single 2 i (1 : ℂ)) := by
      rw [map_sum]
      simp only [map_smul]
    _ = L x := congrArg L (sum_single_basis x)

theorem toColumns_columnOperator (z : Columns H m) : toColumns (columnOperator z) = z := by
  apply PiLp.ext
  intro i
  change columnOperator z (PiLp.single 2 i (1 : ℂ)) = z i
  rw [columnOperator_apply, columnEvaluation_single]

/-- Evaluation is jointly continuous for weak columns and a finite-dimensional input. -/
theorem continuous_evaluation : Continuous
    (fun p : WeakSpace ℂ (Columns H m) × EuclideanSpace ℂ (Fin m) =>
      WeakSpace.map (columnEvaluation p.2) p.1) := by
  have h : (fun p : WeakSpace ℂ (Columns H m) × EuclideanSpace ℂ (Fin m) =>
      WeakSpace.map (columnEvaluation p.2) p.1) =
      (fun p => ∑ i, p.2 i • WeakSpace.map (PiLp.proj 2 (fun _ : Fin m => H) i) p.1) := by
    funext p
    apply (toWeakSpace ℂ H).symm.injective
    change columnEvaluation p.2 ((toWeakSpace ℂ (Columns H m)).symm p.1) =
      (toWeakSpace ℂ H).symm
        (∑ i, p.2 i • WeakSpace.map (PiLp.proj 2 (fun _ : Fin m => H) i) p.1)
    rw [columnEvaluation_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  rw [h]
  apply continuous_finset_sum
  intro i _
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin m => ℂ) i).continuous.comp continuous_snd).smul
    ((WeakSpace.map (PiLp.proj 2 (fun _ : Fin m => H) i)).continuous.comp continuous_fst)

/-- Contractive operators, with the weak topology on their columns. -/
def ball : Set (WeakSpace ℂ (Columns H m)) :=
  {z | ∀ x : EuclideanSpace ℂ (Fin m),
    ‖columnEvaluation x ((toWeakSpace ℂ (Columns H m)).symm z)‖ ≤ ‖x‖}

theorem ball_eq_iInter : ball (H := H) (m := m) =
    ⋂ x : EuclideanSpace ℂ (Fin m),
      (WeakSpace.map (columnEvaluation (H := H) x)) ⁻¹' weakHilbertBall ‖x‖ := by
  ext z
  simp only [ball, mem_setOf_eq, mem_iInter, Set.mem_preimage, weakHilbertBall] <;> rfl

theorem convex_ball : Convex ℝ (ball (H := H) (m := m)) := by
  rw [ball_eq_iInter]
  apply convex_iInter
  intro x
  exact (convex_weakHilbertBall ‖x‖).linear_preimage
    ((WeakSpace.map (columnEvaluation (H := H) x)).toLinearMap.restrictScalars ℝ)

theorem nonempty_ball : (ball (H := H) (m := m)).Nonempty := by
  refine ⟨0, fun x => ?_⟩
  simp only [map_zero, norm_zero]
  exact norm_nonneg x

variable [CompleteSpace H]

theorem isClosed_ball : IsClosed (ball (H := H) (m := m)) := by
  rw [ball_eq_iInter]
  apply isClosed_iInter
  intro x
  exact (isCompact_weakHilbertBall ‖x‖).isClosed.preimage
    (WeakSpace.map (columnEvaluation (H := H) x)).continuous

omit [CompleteSpace H] in
/-- Each column of a contraction has norm at most one. -/
theorem norm_column_le_one {z : WeakSpace ℂ (Columns H m)} (hz : z ∈ ball) (i : Fin m) :
    ‖((toWeakSpace ℂ (Columns H m)).symm z) i‖ ≤ 1 := by
  have h := hz (PiLp.single 2 i (1 : ℂ))
  simpa only [columnEvaluation_single, PiLp.norm_single, norm_one] using h

omit [CompleteSpace H] in
theorem ball_subset_weakHilbertBall : ball (H := H) (m := m) ⊆
    weakHilbertBall ((m : ℝ) + 1) := by
  intro z hz
  have hs : ‖(toWeakSpace ℂ (Columns H m)).symm z‖ ^ 2 ≤ (m : ℝ) := by
    calc
      _ = ∑ i : Fin m, ‖((toWeakSpace ℂ (Columns H m)).symm z) i‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 _ _
      _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h := norm_column_le_one hz i
        nlinarith only [h, norm_nonneg (((toWeakSpace ℂ (Columns H m)).symm z) i)]
      _ = (m : ℝ) := by simp
  change ‖(toWeakSpace ℂ (Columns H m)).symm z‖ ≤ (m : ℝ) + 1
  nlinarith only [hs, Nat.cast_nonneg (α := ℝ) m, sq_nonneg (m : ℝ),
    norm_nonneg ((toWeakSpace ℂ (Columns H m)).symm z)]

/-- The contraction ball is compact for the weak topology on its finite column space. -/
theorem isCompact_ball : IsCompact (ball (H := H) (m := m)) :=
  (isCompact_weakHilbertBall ((m : ℝ) + 1)).of_isClosed_subset isClosed_ball
    ball_subset_weakHilbertBall

#print axioms isCompact_ball

end GaloisForLFunctions.HTGeometry.WeakContraction
