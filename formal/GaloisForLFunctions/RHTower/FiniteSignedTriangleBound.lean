import GaloisForLFunctions.RHTower.SignedTriangleCollectiveGap

/-!
# Combining every triangle without counting any edge twice

An edge belongs to `n-2` distinct triangles. An exact subtraction of repeated
vertices gives this sharp edge count. The corresponding normalization gives
an unconditional collective correction for any real symmetric form.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteSignedOffDiagonal (M : ι → ι → ℝ) (i j : ι) : ℝ := if i = j then 0 else M i j

def finiteSignedQuadratic (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, ∑ j, M i j * x i * x j

def finiteSignedSeparateLower (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, (M i i - ∑ j, |finiteSignedOffDiagonal M i j|) * x i ^ 2

def finiteSignedTriangleCorrection (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, ∑ j, ∑ k, signedTriangleGain (finiteSignedOffDiagonal M i j)
    (finiteSignedOffDiagonal M i k) (finiteSignedOffDiagonal M j k) *
      (x i ^ 2 + x j ^ 2 + x k ^ 2)) / (6 * max 1 ((Fintype.card ι : ℝ) - 2))

theorem finiteSignedTriangleCorrection_nonneg (M : ι → ι → ℝ) (x : ι → ℝ) :
    0 ≤ finiteSignedTriangleCorrection M x := by
  unfold finiteSignedTriangleCorrection
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ =>
    mul_nonneg (signedTriangleGain_nonneg _ _ _) (by positivity)

theorem finiteSignedQuadratic_diagonal_off (M : ι → ι → ℝ) (x : ι → ℝ) :
    finiteSignedQuadratic M x = (∑ i, M i i * x i ^ 2) +
      ∑ i, ∑ j, finiteSignedOffDiagonal M i j * x i * x j := by
  unfold finiteSignedQuadratic
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ j, ((if i = j then M i i * x i ^ 2 else 0) +
        finiteSignedOffDiagonal M i j * x i * x j) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j
      · subst j
        simp only [finiteSignedOffDiagonal, ite_true, zero_mul, add_zero]
        ring
      · simp only [h, if_false, finiteSignedOffDiagonal, zero_add]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem finiteSignedQuadratic_edge_decomposition (M : ι → ι → ℝ)
    (hsym : ∀ i j, M i j = M j i) (x : ι → ℝ) :
    finiteSignedQuadratic M x = finiteSignedSeparateLower M x +
      (∑ i, ∑ j, signedEdgePenalty (finiteSignedOffDiagonal M i j) (x i) (x j)) / 2 := by
  have hoff (i j : ι) : finiteSignedOffDiagonal M i j = finiteSignedOffDiagonal M j i := by
    unfold finiteSignedOffDiagonal
    by_cases h : i = j
    · subst j; rfl
    · simp only [h, Ne.symm h, if_false, hsym i j]
  have hswap : (∑ i, ∑ j, |finiteSignedOffDiagonal M i j| * x j ^ 2) =
      ∑ i, ∑ j, |finiteSignedOffDiagonal M i j| * x i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hoff j i]
  have he : (∑ i, ∑ j, signedEdgePenalty (finiteSignedOffDiagonal M i j) (x i) (x j)) =
      (∑ i, ∑ j, |finiteSignedOffDiagonal M i j| * x i ^ 2) +
      (∑ i, ∑ j, |finiteSignedOffDiagonal M i j| * x j ^ 2) +
      2 * (∑ i, ∑ j, finiteSignedOffDiagonal M i j * x i * x j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold signedEdgePenalty
    ring
  rw [hswap] at he
  have hl : finiteSignedSeparateLower M x = (∑ i, M i i * x i ^ 2) -
      ∑ i, ∑ j, |finiteSignedOffDiagonal M i j| * x i ^ 2 := by
    simp only [finiteSignedSeparateLower, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [finiteSignedQuadratic_diagonal_off, hl]
  linarith only [he]

omit [DecidableEq ι] in
theorem sum_triangle_edges (E : ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ k, (E i j + E i k + E j k)) =
      3 * Fintype.card ι * (∑ i, ∑ j, E i j) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

theorem sum_triangle_edges_distinct_bound (E : ι → ι → ℝ) (T : ι → ι → ι → ℝ)
    (hsym : ∀ i j, E i j = E j i) (hdiag : ∀ i, E i i = 0)
    (hzero : ∀ i j k, i = j ∨ i = k ∨ j = k → T i j k = 0)
    (hbound : ∀ i j k, T i j k ≤ E i j + E i k + E j k) :
    (∑ i, ∑ j, ∑ k, T i j k) + 6 * (∑ i, ∑ j, E i j) ≤
      3 * Fintype.card ι * (∑ i, ∑ j, E i j) := by
  have hp (i j k : ι) : T i j k + (if i = j then 2 * E i k else 0) +
      (if i = k then 2 * E i j else 0) + (if j = k then 2 * E i j else 0) ≤
      E i j + E i k + E j k := by
    by_cases hij : i = j
    · subst j
      rw [hzero i i k (Or.inl rfl)]
      by_cases hik : i = k
      · subst k; simp [hdiag]
      · simp only [ite_true, hik, if_false, hdiag, zero_add, add_zero]
        linarith
    · by_cases hik : i = k
      · subst k
        rw [hzero i j i (Or.inr (Or.inl rfl))]
        simp only [hij, Ne.symm hij, if_false, ite_true, hdiag, zero_add, add_zero, hsym j i]
        linarith
      · by_cases hjk : j = k
        · subst k
          rw [hzero i j j (Or.inr (Or.inr rfl))]
          simp only [hij, if_false, ite_true, hdiag, zero_add, add_zero]
          linarith
        · simpa only [hij, hik, hjk, if_false, add_zero] using hbound i j k
  have h₁ : (∑ i, ∑ j, ∑ k, if i = j then 2 * E i k else 0) = 2 * (∑ i, ∑ j, E i j) := by
    calc
      _ = ∑ i, ∑ k, ∑ j, if i = j then 2 * E i k else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := by simp [Finset.mul_sum]
  have h₂ : (∑ i, ∑ j, ∑ k, if i = k then 2 * E i j else 0) = 2 * (∑ i, ∑ j, E i j) := by
    simp [Finset.mul_sum]
  have h₃ : (∑ i, ∑ j, ∑ k, if j = k then 2 * E i j else 0) = 2 * (∑ i, ∑ j, E i j) := by
    simp [Finset.mul_sum]
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) fun k _ => hp i j k
  rw [sum_triangle_edges] at h
  simp only [Finset.sum_add_distrib] at h
  rw [h₁, h₂, h₃] at h
  linarith only [h]

/-- Every finite real symmetric form admits this explicit collective improvement. -/
theorem finiteSignedTriangle_lower (M : ι → ι → ℝ)
    (hsym : ∀ i j, M i j = M j i) (x : ι → ℝ) :
    finiteSignedSeparateLower M x + finiteSignedTriangleCorrection M x ≤ finiteSignedQuadratic M x := by
  let E i j := signedEdgePenalty (finiteSignedOffDiagonal M i j) (x i) (x j)
  let T i j k := signedTriangleGain (finiteSignedOffDiagonal M i j)
    (finiteSignedOffDiagonal M i k) (finiteSignedOffDiagonal M j k) *
      (x i ^ 2 + x j ^ 2 + x k ^ 2)
  have heSym (i j : ι) : E i j = E j i := by
    by_cases h : i = j
    · subst j; rfl
    · simp only [E, finiteSignedOffDiagonal, h, Ne.symm h, if_false, hsym j i, signedEdgePenalty]
      ring
  have heDiag (i : ι) : E i i = 0 := by simp [E, finiteSignedOffDiagonal, signedEdgePenalty]
  have htZero (i j k : ι) (h : i = j ∨ i = k ∨ j = k) : T i j k = 0 := by
    apply mul_eq_zero_of_left
    apply signedTriangleGain_eq_zero_of_zero
    rcases h with rfl | rfl | rfl <;> simp [finiteSignedOffDiagonal]
  have h := sum_triangle_edges_distinct_bound E T heSym heDiag htZero
    (fun i j k => signedTriangleGain_lower _ _ _ _ _ _)
  have he : 0 ≤ ∑ i, ∑ j, E i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => signedEdgePenalty_nonneg _ _ _
  have hm := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) ((Fintype.card ι : ℝ) - 2)) he
  rw [finiteSignedQuadratic_edge_decomposition M hsym]
  apply add_le_add le_rfl
  unfold finiteSignedTriangleCorrection
  apply (div_le_iff₀ (by positivity : 0 < 6 * max 1 ((Fintype.card ι : ℝ) - 2))).mpr
  change (∑ i, ∑ j, ∑ k, T i j k) ≤ (∑ i, ∑ j, E i j) / 2 * _
  nlinarith only [h, hm]

/-- A selected triangle keeps its contribution in every larger source family. -/
theorem single_triangle_le_finiteSignedTriangleCorrection
    (M : ι → ι → ℝ) (x : ι → ℝ) (i j k : ι) :
    signedTriangleGain (finiteSignedOffDiagonal M i j)
      (finiteSignedOffDiagonal M i k) (finiteSignedOffDiagonal M j k) *
      (x i ^ 2 + x j ^ 2 + x k ^ 2) / (6 * max 1 ((Fintype.card ι : ℝ) - 2)) ≤
      finiteSignedTriangleCorrection M x := by
  let T (i j k : ι) := signedTriangleGain (finiteSignedOffDiagonal M i j)
    (finiteSignedOffDiagonal M i k) (finiteSignedOffDiagonal M j k) *
      (x i ^ 2 + x j ^ 2 + x k ^ 2)
  have hT (i j k : ι) : 0 ≤ T i j k :=
    mul_nonneg (signedTriangleGain_nonneg _ _ _) (by positivity)
  have h₁ : T i j k ≤ ∑ k, T i j k :=
    Finset.single_le_sum (fun k _ => hT i j k) (Finset.mem_univ k)
  have h₂ : (∑ k, T i j k) ≤ ∑ j, ∑ k, T i j k :=
    Finset.single_le_sum (fun j _ => Finset.sum_nonneg fun k _ => hT i j k) (Finset.mem_univ j)
  have h₃ : (∑ j, ∑ k, T i j k) ≤ ∑ i, ∑ j, ∑ k, T i j k :=
    Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => hT i j k) (Finset.mem_univ i)
  exact div_le_div_of_nonneg_right (h₁.trans (h₂.trans h₃)) (by positivity)

end RHTower
