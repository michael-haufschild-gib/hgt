import GaloisForLFunctions.HTGeometry.ShortExactRankConservation

/-!
# Common-character fusion conservation

A finite family of source labels can fuse to one common scalar response through the summation
map.  On a reciprocal character double, the canonical invariant hyperbolic form splits exactly
into the one-dimensional fused response and the centered label kernel.  This is the algebraic
signature-conservation identity underlying common-divisor scalarization.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- Scalar fusion of a finite real label packet. -/
def finiteLabelFusion {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i

/-- Linear-map form of finite scalar fusion. -/
def finiteLabelFusionLinearMap (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun := finiteLabelFusion
  map_add' := by
    intro x y
    simp [finiteLabelFusion, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [finiteLabelFusion, Finset.mul_sum]

/-- Mean label coordinate of a nonempty finite packet. -/
def finiteLabelMean {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  finiteLabelFusion x / (n : ℝ)

/-- Transverse label coordinate after removing the fused mean. -/
def finiteLabelCentered {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i - finiteLabelMean x

/-- Every label is reconstructed exactly from its fused mean and centered coordinate. -/
theorem finiteLabel_mean_add_centered {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    finiteLabelMean x + finiteLabelCentered x i = x i := by
  simp [finiteLabelCentered]

/-- Finite scalar fusion is onto for every nonempty packet. -/
theorem finiteLabelFusionLinearMap_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (finiteLabelFusionLinearMap n) := by
  intro y
  let i : Fin n := ⟨0, hn⟩
  refine ⟨Pi.single i y, ?_⟩
  simp [finiteLabelFusionLinearMap, finiteLabelFusion, i]

/-- The transverse fibre of scalar fusion has codimension one. -/
theorem finiteLabelFusionLinearMap_finrank_ker {n : ℕ} (hn : 0 < n) :
    Module.finrank ℝ (LinearMap.ker (finiteLabelFusionLinearMap n)) = n - 1 := by
  have hrange : LinearMap.range (finiteLabelFusionLinearMap n) = ⊤ :=
    LinearMap.range_eq_top.mpr (finiteLabelFusionLinearMap_surjective hn)
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (finiteLabelFusionLinearMap n)
  rw [hrange, finrank_top, Module.finrank_fin_fun] at hrank
  norm_num at hrank
  omega

/-- Canonical cross pairing on the reciprocal double of a finite label packet. -/
def reciprocalLabelForm {n : ℕ}
    (v w : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, (v.1 i * w.2 i + v.2 i * w.1 i)

/-- Quadratic value of the reciprocal-label cross pairing. -/
def reciprocalLabelQuadratic {n : ℕ}
    (v : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  reciprocalLabelForm v v

/-- Reflected real-character action with opposite exponential rates on the two label copies. -/
def reflectedLabelAction {n : ℕ} (a t : ℝ)
    (v : (Fin n → ℝ) × (Fin n → ℝ)) :
    (Fin n → ℝ) × (Fin n → ℝ) :=
  (fun i => Real.exp (a * t) * v.1 i,
    fun i => Real.exp (-(a * t)) * v.2 i)

/-- Centered label coordinates lie in the kernel of scalar fusion. -/
theorem finiteLabelFusion_centered {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) :
    finiteLabelFusion (finiteLabelCentered x) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [finiteLabelFusion]
  simp only [finiteLabelCentered, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [finiteLabelMean, finiteLabelFusion]
  field_simp
  ring

/-- Euclidean label pairing splits into its fused mean and centered transverse part. -/
theorem finiteLabel_inner_fusion_decomposition {n : ℕ} (hn : 0 < n)
    (x y : Fin n → ℝ) :
    ∑ i, x i * y i =
      finiteLabelFusion x * finiteLabelFusion y / (n : ℝ) +
        ∑ i, finiteLabelCentered x i * finiteLabelCentered y i := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx (i : Fin n) :
      x i = finiteLabelMean x + finiteLabelCentered x i := by
    simp [finiteLabelCentered]
  have hy (i : Fin n) :
      y i = finiteLabelMean y + finiteLabelCentered y i := by
    simp [finiteLabelCentered]
  calc
    ∑ i, x i * y i =
        ∑ i, (finiteLabelMean x + finiteLabelCentered x i) *
          (finiteLabelMean y + finiteLabelCentered y i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [← hx i, ← hy i]
    _ = (n : ℝ) * finiteLabelMean x * finiteLabelMean y +
          finiteLabelMean x * finiteLabelFusion (finiteLabelCentered y) +
          finiteLabelFusion (finiteLabelCentered x) * finiteLabelMean y +
          ∑ i, finiteLabelCentered x i * finiteLabelCentered y i := by
            simp only [mul_add, add_mul, Finset.sum_add_distrib,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              ← Finset.mul_sum, ← Finset.sum_mul, finiteLabelFusion]
            ring
    _ = (n : ℝ) * finiteLabelMean x * finiteLabelMean y +
          ∑ i, finiteLabelCentered x i * finiteLabelCentered y i := by
            rw [finiteLabelFusion_centered hn x,
              finiteLabelFusion_centered hn y]
            ring
    _ = finiteLabelFusion x * finiteLabelFusion y / (n : ℝ) +
          ∑ i, finiteLabelCentered x i * finiteLabelCentered y i := by
            rw [finiteLabelMean, finiteLabelMean]
            field_simp

/-- The reciprocal quadratic form is twice the Euclidean cross pairing of the two labels. -/
theorem reciprocalLabelQuadratic_eq {n : ℕ}
    (x y : Fin n → ℝ) :
    reciprocalLabelQuadratic (x, y) = 2 * ∑ i, x i * y i := by
  rw [reciprocalLabelQuadratic, reciprocalLabelForm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Common-character fusion conservation.** The reciprocal source form is the sum of one
fused hyperbolic block and the full centered transverse-label form. -/
theorem reciprocalLabelQuadratic_fusion_conservation {n : ℕ} (hn : 0 < n)
    (x y : Fin n → ℝ) :
    reciprocalLabelQuadratic (x, y) =
      2 * (finiteLabelFusion x * finiteLabelFusion y / (n : ℝ)) +
        2 * ∑ i, finiteLabelCentered x i * finiteLabelCentered y i := by
  rw [reciprocalLabelQuadratic_eq,
    finiteLabel_inner_fusion_decomposition hn]
  ring

/-- The reciprocal-label cross pairing is invariant under opposite exponential characters. -/
theorem reciprocalLabelForm_reflectedLabelAction_invariant {n : ℕ}
    (a t : ℝ) (v w : (Fin n → ℝ) × (Fin n → ℝ)) :
    reciprocalLabelForm (reflectedLabelAction a t v)
        (reflectedLabelAction a t w) =
      reciprocalLabelForm v w := by
  have hcancel : Real.exp (a * t) * Real.exp (-(a * t)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hcancel' : Real.exp (-(a * t)) * Real.exp (a * t) = 1 := by
    rw [mul_comm]
    exact hcancel
  rw [reciprocalLabelForm, reciprocalLabelForm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [reflectedLabelAction]
  rw [show Real.exp (a * t) * v.1 i * (Real.exp (-(a * t)) * w.2 i) =
      (Real.exp (a * t) * Real.exp (-(a * t))) * (v.1 i * w.2 i) by ring,
    show Real.exp (-(a * t)) * v.2 i * (Real.exp (a * t) * w.1 i) =
      (Real.exp (-(a * t)) * Real.exp (a * t)) * (v.2 i * w.1 i) by ring,
    hcancel, hcancel']
  ring

/-- Scalar fusion intertwines the positive half of the reflected character action. -/
theorem finiteLabelFusion_reflectedLabelAction_fst {n : ℕ}
    (a t : ℝ) (v : (Fin n → ℝ) × (Fin n → ℝ)) :
    finiteLabelFusion (reflectedLabelAction a t v).1 =
      Real.exp (a * t) * finiteLabelFusion v.1 := by
  simp only [finiteLabelFusion, reflectedLabelAction, Finset.mul_sum]

/-- Scalar fusion intertwines the reciprocal half of the reflected character action. -/
theorem finiteLabelFusion_reflectedLabelAction_snd {n : ℕ}
    (a t : ℝ) (v : (Fin n → ℝ) × (Fin n → ℝ)) :
    finiteLabelFusion (reflectedLabelAction a t v).2 =
      Real.exp (-(a * t)) * finiteLabelFusion v.2 := by
  simp only [finiteLabelFusion, reflectedLabelAction, Finset.mul_sum]

/-- Diagonal label vectors are positive directions of the reciprocal form. -/
theorem reciprocalLabelQuadratic_diag {n : ℕ} (x : Fin n → ℝ) :
    reciprocalLabelQuadratic (x, x) = 2 * ∑ i, x i ^ (2 : ℕ) := by
  rw [reciprocalLabelQuadratic_eq]
  congr 2
  funext i
  ring

/-- Anti-diagonal label vectors are negative directions of the reciprocal form. -/
theorem reciprocalLabelQuadratic_antidiag {n : ℕ} (x : Fin n → ℝ) :
    reciprocalLabelQuadratic (x, fun i => -x i) = -2 * ∑ i, x i ^ (2 : ℕ) := by
  rw [reciprocalLabelQuadratic_eq]
  have hsum : ∑ i, x i * -x i = -(∑ i, x i ^ (2 : ℕ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- A nonzero finite label vector has strictly positive squared mass. -/
theorem finiteLabel_sum_sq_pos {n : ℕ} {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < ∑ i, x i ^ (2 : ℕ) := by
  have hex : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  apply Finset.sum_pos' (fun i _ => sq_nonneg (x i))
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

/-- Every nonzero label vector supplies a strict positive reciprocal direction. -/
theorem reciprocalLabelQuadratic_diag_pos {n : ℕ} {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    0 < reciprocalLabelQuadratic (x, x) := by
  rw [reciprocalLabelQuadratic_diag]
  exact mul_pos (by norm_num) (finiteLabel_sum_sq_pos hx)

/-- Every nonzero label vector supplies a strict negative reciprocal direction. -/
theorem reciprocalLabelQuadratic_antidiag_neg {n : ℕ} {x : Fin n → ℝ}
    (hx : x ≠ 0) :
    reciprocalLabelQuadratic (x, fun i => -x i) < 0 := by
  rw [reciprocalLabelQuadratic_antidiag]
  exact mul_neg_of_neg_of_pos (by norm_num) (finiteLabel_sum_sq_pos hx)

end

end HTGeometry
