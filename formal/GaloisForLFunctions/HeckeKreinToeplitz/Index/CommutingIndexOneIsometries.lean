import GaloisForLFunctions.HeckeKreinToeplitz.Index.ProjectiveHilbertBall

/-!
# A common nonpositive line for commuting index-one isometries

A nonunit eigenvalue has a one-dimensional eigenspace, preserved by every
commuting operator. Otherwise projective fixed sets are convex affine
eigensets. Compact-convex fixed points give the finite intersection property,
and weak compactness gives a common nonpositive eigenline.
-/

noncomputable section
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The affine chart of an eigenspace, normalized by the last coordinate. -/
def eigenSet (T : (H × ℂ) ≃L[ℂ] (H × ℂ)) (a : ℂ) : Set (WeakSpace ℂ H) :=
  {x | firstAffine T.toContinuousLinearMap x = a • x ∧
    lastAffine T.toContinuousLinearMap x = a}

theorem mem_eigenSet_iff (T : (H × ℂ) ≃L[ℂ] (H × ℂ)) (a : ℂ) (x : WeakSpace ℂ H) :
    x ∈ eigenSet T a ↔ T ((toWeakSpace ℂ H).symm x, 1) =
      a • ((toWeakSpace ℂ H).symm x, 1) := by
  constructor
  · intro hx
    apply Prod.ext
    · exact congrArg (toWeakSpace ℂ H).symm hx.1
    · change (T ((toWeakSpace ℂ H).symm x, 1)).2 = a * 1
      rw [mul_one]
      exact hx.2
  · intro hx
    constructor
    · exact congrArg (fun v : H × ℂ => toWeakSpace ℂ H v.1) hx
    · change (T ((toWeakSpace ℂ H).symm x, 1)).2 = a
      simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using congrArg Prod.snd hx

theorem isClosed_eigenSet (T : (H × ℂ) ≃L[ℂ] (H × ℂ)) (a : ℂ) :
    IsClosed (eigenSet T a) :=
  (isClosed_eq (continuous_firstAffine T.toContinuousLinearMap)
    (continuous_const.smul continuous_id)).inter
      (isClosed_eq (continuous_lastAffine T.toContinuousLinearMap) continuous_const)

theorem convex_eigenSet (T : (H × ℂ) ≃L[ℂ] (H × ℂ)) (a : ℂ) :
    Convex ℝ (eigenSet T a) := by
  intro x hx y hy r s _ _ hrs
  rw [mem_eigenSet_iff] at hx hy ⊢
  have he : ((toWeakSpace ℂ H).symm (r • x + s • y), (1 : ℂ)) =
      r • ((toWeakSpace ℂ H).symm x, (1 : ℂ)) +
        s • ((toWeakSpace ℂ H).symm y, (1 : ℂ)) := by
    apply Prod.ext
    · rfl
    · change (1 : ℂ) = r • (1 : ℂ) + s • (1 : ℂ)
      rw [← add_smul, hrs, one_smul]
  have hreal (c : ℝ) (v : H × ℂ) : T (c • v) = c • T v :=
    (T.toContinuousLinearMap.restrictScalars ℝ).map_smul c v
  rw [he, map_add, hreal, hreal, hx, hy, smul_add]
  congr 1
  · exact smul_comm r a _
  · exact smul_comm s a _

/-- Commuting isometries preserve each normalized affine eigenset. -/
theorem ballAction_mem_eigenSet
    (T S : (H × ℂ) ≃L[ℂ] (H × ℂ))
    (hS : ∀ v w, pairing (S v) (S w) = pairing v w)
    (hcomm : ∀ v, T (S v) = S (T v))
    {a : ℂ} (x : weakHilbertBall (H := H) 1) (hx : x.val ∈ eigenSet T a) :
    (ballAction S hS x).val ∈ eigenSet T a := by
  rw [mem_eigenSet_iff] at hx ⊢
  rw [ballAction_normalized_vector, map_smul, hcomm, hx, map_smul]
  exact smul_comm _ _ _

private theorem common_eigenSet_nonempty [CompleteSpace H] {I : Type*}
    (T : I → (H × ℂ) ≃L[ℂ] (H × ℂ))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (hcomm : ∀ i j v, T i (T j v) = T j (T i v))
    (z : I → H) (a : I → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (ha : ∀ i, ‖a i‖ = 1)
    (heig : ∀ i, T i (z i, 1) = a i • (z i, 1)) :
    (weakHilbertBall (H := H) 1 ∩ ⋂ i, eigenSet (T i) (a i)).Nonempty := by
  classical
  apply (isCompact_weakHilbertBall (H := H) 1).inter_iInter_nonempty
    (fun i => eigenSet (T i) (a i)) (fun i => isClosed_eigenSet (T i) (a i))
  intro s
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.notMem_empty, iInter_of_empty, iInter_univ, inter_univ] using
        (nonempty_weakHilbertBall (H := H) zero_le_one)
  | @insert i s _ ih =>
      let C : Set (WeakSpace ℂ H) :=
        weakHilbertBall 1 ∩ ⋂ j ∈ s, eigenSet (T j) (a j)
      have hCc : IsCompact C := (isCompact_weakHilbertBall 1).inter_right
        (isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eigenSet (T j) (a j))
      have hCv : Convex ℝ C := by
        intro x hx y hy r q hr hq hrq
        refine ⟨convex_weakHilbertBall 1 hx.1 hy.1 hr hq hrq, mem_iInter.mpr fun j =>
          mem_iInter.mpr fun hj => ?_⟩
        exact convex_eigenSet (T j) (a j)
          (mem_iInter.mp (mem_iInter.mp hx.2 j) hj)
          (mem_iInter.mp (mem_iInter.mp hy.2 j) hj) hr hq hrq
      let incl : C → weakHilbertBall (H := H) 1 := fun x => ⟨x.val, x.property.1⟩
      have hincl : Continuous incl := continuous_subtype_val.subtype_mk _
      let F : C → C := fun x =>
        ⟨(ballAction (T i) (hT i) (incl x)).val,
          (ballAction (T i) (hT i) (incl x)).property,
          mem_iInter.mpr fun j => mem_iInter.mpr fun hj =>
            ballAction_mem_eigenSet (T j) (T i) (hT i) (hcomm j i) (incl x)
              (mem_iInter.mp (mem_iInter.mp x.property.2 j) hj)⟩
      have hF : Continuous F :=
        (continuous_subtype_val.comp ((continuous_ballAction (T i) (hT i)).comp hincl)).subtype_mk _
      obtain ⟨x, hx⟩ := exists_fixedPoint_weakHilbert_convex hCc ih hCv F hF
      have hfix : ballAction (T i) (hT i) (incl x) = incl x :=
        Subtype.ext (congrArg (fun y : C => y.val) hx)
      have hex := eigenvector_of_ballAction_fixed (T i) (hT i) hfix
      have hval : lastAffine (T i).toContinuousLinearMap x.val = a i :=
        eigenvalue_eq_of_normalized_nonpositive (T i).toContinuousLinearMap.toLinearMap
          (hT i) (hz i) (incl x).property (ha i) (heig i) hex
      have hnew : x.val ∈ eigenSet (T i) (a i) := by
        rw [mem_eigenSet_iff]
        rwa [hval] at hex
      refine ⟨x.val, x.property.1, mem_iInter.mpr fun j => mem_iInter.mpr fun hj => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hnew
      · exact mem_iInter.mp (mem_iInter.mp x.property.2 j) hj

/-- Commuting isometries of a complete space with one negative direction share a nonpositive line. -/
theorem exists_common_normalized_nonpositive_eigenvector [CompleteSpace H] {I : Type*}
    (T : I → (H × ℂ) ≃L[ℂ] (H × ℂ))
    (hT : ∀ i v w, pairing (T i v) (T i w) = pairing v w)
    (hcomm : ∀ i j v, T i (T j v) = T j (T i v)) :
    ∃ z : H, ‖z‖ ≤ 1 ∧ ∀ i, ∃ a : ℂ, a ≠ 0 ∧ T i (z, 1) = a • (z, 1) := by
  classical
  choose z hz a ha0 heig using fun i => exists_normalized_nonpositive_eigenvector (T i) (hT i)
  by_cases hu : ∀ i, ‖a i‖ = 1
  · obtain ⟨x, hx, he⟩ := common_eigenSet_nonempty T hT hcomm z a hz hu heig
    refine ⟨(toWeakSpace ℂ H).symm x, hx, fun i => ⟨a i, ha0 i, ?_⟩⟩
    exact (mem_eigenSet_iff (T i) (a i) x).mp (mem_iInter.mp he i)
  · obtain ⟨i, hi⟩ := not_forall.mp hu
    have hv0 : (z i, (1 : ℂ)) ≠ 0 := fun h => one_ne_zero (congrArg Prod.snd h)
    refine ⟨z i, hz i, fun j => ?_⟩
    have hw : T i (T j (z i, 1)) = a i • T j (z i, 1) := by
      rw [hcomm, heig, map_smul]
    have hline := eigenvector_eq_scalar_mul_of_nonunit
      (T i).toContinuousLinearMap.toLinearMap (hT i) hi (heig i) hw hv0
    have hnorm : T j (z i, 1) = (T j (z i, 1)).2 • (z i, 1) := by
      simpa only [div_one] using hline
    have hne : (T j (z i, 1)).2 ≠ 0 := by
      intro he
      rw [he, zero_smul] at hnorm
      exact hv0 ((T j).injective (hnorm.trans (map_zero (T j)).symm))
    exact ⟨(T j (z i, 1)).2, hne, hnorm⟩

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
