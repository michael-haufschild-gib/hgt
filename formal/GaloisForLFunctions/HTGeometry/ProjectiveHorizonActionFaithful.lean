import GaloisForLFunctions.HTGeometry.ProjectiveHorizonChartTranscendence

/-!
# Faithfulness of the prolonged action

The homogeneous jet coordinates are linearly independent over the constants, so a unimodular matrix
acting trivially on the homogeneous jet field already acts trivially on each jet coordinate, and its
inverse is the identity matrix.

Faithfulness is the field-theoretic form of the generic freeness of the prolonged action: the
observer group injects into the automorphisms of the jet field, so its parameter count is the
codimension of the horizon field.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

omit [Fintype n] [DecidableEq n] in
/-- The homogeneous jet coordinates are linearly independent over the constants. -/
theorem linearIndependent_freeCoordinate :
    LinearIndependent K (freeCoordinate K (n × ℕ)) :=
  (algebraicIndependent_freeCoordinate K (n × ℕ)).linearIndependent

omit [Fintype n] [DecidableEq n] in
/-- The zeroth-order homogeneous jet coordinates are linearly independent over the constants. -/
theorem linearIndependent_freeCoordinate_zero :
    LinearIndependent K (fun m : n => freeCoordinate K (n × ℕ) (m, 0)) :=
  (linearIndependent_freeCoordinate (K := K)).comp (fun m : n => (m, 0))
    (fun _ _ hab => congrArg Prod.fst hab)

/-- **Faithfulness of the prolonged action.**  A unimodular matrix acting trivially on the
homogeneous jet field is the identity: an observer is determined by its effect on jets.  This is
the generic-freeness input behind the codimension count. -/
theorem linearJetAction_faithful {g : SpecialLinearGroup n K}
    (hg : ∀ f : HomogeneousJetField n K, g • f = f) : g = 1 := by
  have hcoeff : ∀ k m : n,
      ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k m = (1 : Matrix n n K) k m := by
    intro k m
    have hfix := hg (freeCoordinate K (n × ℕ) (k, 0))
    rw [linearJetAction_freeCoordinate] at hfix
    have h1 : ∑ q : n, ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k q •
        freeCoordinate K (n × ℕ) (q, 0) = freeCoordinate K (n × ℕ) (k, 0) := by
      rw [← hfix]
      exact Finset.sum_congr rfl fun q _ => Algebra.smul_def _ _
    have h2 : ∑ q : n, ((1 : Matrix n n K) k q) • freeCoordinate K (n × ℕ) (q, 0) =
        freeCoordinate K (n × ℕ) (k, 0) := by
      rw [Finset.sum_eq_single k]
      · rw [Matrix.one_apply_eq, one_smul]
      · intro q _ hq
        rw [Matrix.one_apply_ne (Ne.symm hq), zero_smul]
      · intro hcon
        exact absurd (Finset.mem_univ k) hcon
    have hsum : ∑ q : n, (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k q -
        (1 : Matrix n n K) k q) • freeCoordinate K (n × ℕ) (q, 0) = 0 := by
      rw [Finset.sum_congr rfl fun q _ => sub_smul _ _ _, Finset.sum_sub_distrib, h1, h2,
        sub_self]
    exact sub_eq_zero.1 (linearIndependent_iff'.1 (linearIndependent_freeCoordinate_zero (K := K))
      Finset.univ _ hsum m (Finset.mem_univ m))
  have hinv : (g⁻¹ : SpecialLinearGroup n K) = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one]
    ext k m
    exact hcoeff k m
  exact inv_eq_one.1 hinv

/-- The observer group of any covector span acts faithfully. -/
theorem chartSubsetStabilizer_faithful {s : Set n} {g : SpecialLinearGroup n K}
    (_ : g ∈ chartSubsetStabilizer (K := K) s)
    (hfix : ∀ f : HomogeneousJetField n K, g • f = f) : g = 1 :=
  linearJetAction_faithful hfix

/-- **Injectivity of the observer action.**  Distinct unimodular matrices act differently on the
homogeneous jet field. -/
theorem linearJetFieldEquiv_injective :
    Function.Injective (linearJetFieldEquiv (n := n) (K := K)) := by
  intro g h hgh
  have hone : ∀ f : HomogeneousJetField n K, (g * h⁻¹) • f = f := by
    intro f
    rw [mul_smul, linearJetAction_apply, linearJetAction_apply]
    have hinv : linearJetFieldEquiv (h⁻¹ : SpecialLinearGroup n K) =
        (linearJetFieldEquiv h).symm := by
      refine AlgEquiv.ext fun z => ?_
      have hcomp : linearJetFieldEquiv (h * h⁻¹) z =
          linearJetFieldEquiv h (linearJetFieldEquiv h⁻¹ z) :=
        linearJetFieldEquiv_mul_apply h h⁻¹ z
      rw [mul_inv_cancel, linearJetFieldEquiv_one_apply] at hcomp
      exact (AlgEquiv.eq_symm_apply _).2 hcomp.symm
    rw [hinv, hgh]
    exact (linearJetFieldEquiv h).apply_symm_apply f
  have := linearJetAction_faithful hone
  exact mul_inv_eq_one.1 this

end

end GaloisForLFunctions.HTGeometry
