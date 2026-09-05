import GaloisForLFunctions.HTGeometry.StaticOrbitNetBellmanLaw
import GaloisForLFunctions.HTGeometry.Arxiv2608BellmanShorelineTwoHalfCells

/-!
# Cross-polytope certificate for N-COMP in arXiv:2608.29060

The paper's computable upper bound uses the convex hull of signed standard basis vectors and its
centered inradius `1 / √D`. This module constructs an explicit convex combination for every point
of the `ℓ¹` unit ball, derives inclusion of the Euclidean ball of radius `1 / √D`, and records the
equivalent uniform support lower bound. No polytope library characterization is assumed.
-/

noncomputable section

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Signed standard basis indexed by coordinate and Boolean sign. -/
def bellmanShorelineSignedBasisPoint (D : ℕ) (ib : Fin D × Bool) :
    EuclideanSpace ℝ (Fin D) :=
  if ib.2 then EuclideanSpace.single ib.1 1 else -EuclideanSpace.single ib.1 1

/-- Convex hull of signed standard basis vectors. -/
def bellmanShorelineCrossPolytope (D : ℕ) : Set (EuclideanSpace ℝ (Fin D)) :=
  convexHull ℝ (Set.range (bellmanShorelineSignedBasisPoint D))

/-- Every vector of coordinate `ℓ¹` norm at most one belongs to cross-polytope. -/
theorem bellmanShoreline_mem_crossPolytope_of_l1_le_one
    {D : ℕ} (hD : 0 < D) (x : EuclideanSpace ℝ (Fin D))
    (hx : ∑ i, |x i| ≤ 1) : x ∈ bellmanShorelineCrossPolytope D := by
  let i0 : Fin D := ⟨0, hD⟩
  let delta : ℝ := 1 - ∑ i, |x i|
  let w : Fin D × Bool → ℝ := fun ib =>
    if ib.2 then (x ib.1)⁺ + (if ib.1 = i0 then delta / 2 else 0)
    else (x ib.1)⁻ + (if ib.1 = i0 then delta / 2 else 0)
  apply mem_convexHull_of_exists_fintype w (bellmanShorelineSignedBasisPoint D)
  · intro ib
    dsimp [w]
    split_ifs <;> positivity
  · rw [Fintype.sum_prod_type]
    have hpair : ∀ i : Fin D, ∑ b : Bool, w (i, b) =
        |x i| + (if i = i0 then delta else 0) := by
      intro i
      rw [Fintype.sum_bool]
      simp only [w, Bool.false_eq_true, ↓reduceIte]
      have habs := posPart_add_negPart (x i)
      split_ifs <;> linarith
    calc
      ∑ i : Fin D, ∑ b : Bool, w (i, b) =
          ∑ i : Fin D, (|x i| + (if i = i0 then delta else 0)) :=
        Finset.sum_congr rfl (fun i _ => hpair i)
      _ = 1 := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq']
        dsimp [delta]
        ring
  · intro ib
    exact Set.mem_range_self ib
  · ext k
    change EuclideanSpace.projₗ k
      (∑ ib : Fin D × Bool, w ib • bellmanShorelineSignedBasisPoint D ib) = x k
    rw [map_sum]
    simp_rw [map_smul]
    change (∑ ib : Fin D × Bool,
      w ib * (bellmanShorelineSignedBasisPoint D ib) k) = x k
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    simp only [w, bellmanShorelineSignedBasisPoint, Bool.false_eq_true, ↓reduceIte,
      PiLp.single_apply, PiLp.neg_apply]
    rw [Finset.sum_eq_single k]
    · simpa [sub_eq_add_neg] using posPart_sub_negPart (x k)
    · intro b _ hbk
      simp [Ne.symm hbk]
    · intro hk
      exact (hk (Finset.mem_univ k)).elim

/-- Euclidean ball of radius `1 / √D` lies in `D`-dimensional cross-polytope. -/
theorem bellmanShoreline_closedBall_subset_crossPolytope
    {D : ℕ} (hD : 0 < D) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin D)) (Real.sqrt D)⁻¹ ⊆
      bellmanShorelineCrossPolytope D := by
  intro x hx
  apply bellmanShoreline_mem_crossPolytope_of_l1_le_one hD x
  have hsum := HTGeometry.sum_abs_le_sqrt_card_mul_norm x
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  calc
    ∑ i, |x i| ≤ Real.sqrt D * ‖x‖ := hsum
    _ ≤ Real.sqrt D * (Real.sqrt D)⁻¹ :=
      mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg _)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))

/-- Cross-polytope is compact as convex hull of finite generator set. -/
theorem bellmanShoreline_crossPolytope_isCompact (D : ℕ) :
    IsCompact (bellmanShorelineCrossPolytope D) := by
  exact Set.finite_range (bellmanShorelineSignedBasisPoint D) |>.isCompact_convexHull ℝ

/-- Every unit direction sees cross-polytope support at least `1 / √D`. -/
theorem bellmanShoreline_crossPolytope_support_lower
    {D : ℕ} (hD : 0 < D) (n : EuclideanSpace ℝ (Fin D)) (hn : ‖n‖ = 1) :
    (Real.sqrt D)⁻¹ ≤ bellmanShorelineSupport (bellmanShorelineCrossPolytope D) n := by
  let x := (Real.sqrt D)⁻¹ • n
  have hxBall : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin D)) (Real.sqrt D)⁻¹ := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), hn, mul_one]
  have hx := bellmanShoreline_closedBall_subset_crossPolytope hD hxBall
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin D) => inner ℝ n y) :=
    continuous_const.inner continuous_id
  have hbdd := (bellmanShoreline_crossPolytope_isCompact D).bddAbove_image
    hcont.continuousOn
  have hxsupport : inner ℝ n x ≤
      bellmanShorelineSupport (bellmanShorelineCrossPolytope D) n :=
    le_csSup hbdd ⟨x, hx, rfl⟩
  simpa [x, real_inner_smul_right, real_inner_self_eq_norm_sq, hn] using hxsupport

end GaloisForLFunctions.HTGeometry

end
