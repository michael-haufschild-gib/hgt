import GaloisForLFunctions.RHTower.FiniteSignedTriangleBound
import GaloisForLFunctions.RHTower.FiniteTriangleRankOneLoss
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod

/-!
# Whole-clique collective correction

The sum of all pair squares retains the square of the total coefficient sum.
The minimum positive off-diagonal weight turns this identity into a collective
lower bound. No sign hypothesis is needed: a nonpositive edge makes the common
positive weight zero. This complements, rather than replaces, triangle gains.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem sum_pair_add_sq (x : ι → ℝ) :
    (∑ i, ∑ j, (x i + x j) ^ 2) =
      2 * Fintype.card ι * (∑ i, x i ^ 2) + 2 * (∑ i, x i) ^ 2 := by
  have hprod : (∑ i, ∑ j, x i * x j) = (∑ i, x i) ^ 2 := by
    rw [pow_two, Finset.sum_mul_sum]
  calc
    _ = (∑ i : ι, ∑ j : ι, x i ^ 2) + (∑ i : ι, ∑ j : ι, x j ^ 2) +
        2 * (∑ i, ∑ j, x i * x j) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [hprod]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
      ring

theorem sum_offDiagonal_pair_add_sq (x : ι → ℝ) :
    (∑ i, ∑ j, if i = j then 0 else (x i + x j) ^ 2) =
      2 * ((Fintype.card ι : ℝ) - 2) * (∑ i, x i ^ 2) + 2 * (∑ i, x i) ^ 2 := by
  have he (i j : ι) : (if i = j then 0 else (x i + x j) ^ 2) =
      (x i + x j) ^ 2 - (if i = j then 4 * x i ^ 2 else 0) := by
    by_cases h : i = j
    · subst j; simp; ring
    · simp [h]
  simp_rw [he]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    ← Finset.mul_sum]
  rw [sum_pair_add_sq]
  ring

def finiteSignedCliqueGain (M : ι → ι → ℝ) : ℝ :=
  if h : (Finset.univ : Finset ι).offDiag.Nonempty then
    (Finset.univ : Finset ι).offDiag.inf' h (fun ij => max (M ij.1 ij.2) 0)
  else 0

omit [DecidableEq ι] in
theorem finiteSignedCliqueGain_nonneg (M : ι → ι → ℝ) : 0 ≤ finiteSignedCliqueGain M := by
  unfold finiteSignedCliqueGain
  split_ifs with h
  · exact (Finset.le_inf'_iff _ _).mpr fun ij _ => le_max_right _ _
  · exact le_rfl

omit [DecidableEq ι] in
theorem finiteSignedCliqueGain_le (M : ι → ι → ℝ) {i j : ι} (hij : i ≠ j) :
    finiteSignedCliqueGain M ≤ max (M i j) 0 := by
  have hmem : (i, j) ∈ (Finset.univ : Finset ι).offDiag := by simpa using hij
  rw [finiteSignedCliqueGain, dif_pos ⟨(i, j), hmem⟩]
  exact Finset.inf'_le _ hmem

omit [DecidableEq ι] in
theorem finiteSignedCliqueGain_pos (M : ι → ι → ℝ)
    (h : (Finset.univ : Finset ι).offDiag.Nonempty)
    (hp : ∀ i j, i ≠ j → 0 < M i j) : 0 < finiteSignedCliqueGain M := by
  rw [finiteSignedCliqueGain, dif_pos h]
  apply (Finset.lt_inf'_iff _).mpr
  intro ij hij
  exact (hp ij.1 ij.2 (Finset.mem_offDiag.mp hij).2.2).trans_le (le_max_left _ _)

def finiteSignedCliqueCorrection (M : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  finiteSignedCliqueGain M *
    (((Fintype.card ι : ℝ) - 2) * (∑ i, x i ^ 2) + (∑ i, x i) ^ 2)

theorem finiteSignedCliqueCorrection_nonneg (M : ι → ι → ℝ) (x : ι → ℝ) :
    0 ≤ finiteSignedCliqueCorrection M x := by
  have h := sum_offDiagonal_pair_add_sq x
  have hn : 0 ≤ ∑ i, ∑ j, if i = j then (0 : ℝ) else (x i + x j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by split_ifs <;> positivity
  unfold finiteSignedCliqueCorrection
  apply mul_nonneg (finiteSignedCliqueGain_nonneg M)
  linarith only [h, hn]

theorem finiteSignedClique_lower (M : ι → ι → ℝ)
    (hsym : ∀ i j, M i j = M j i) (x : ι → ℝ) :
    finiteSignedSeparateLower M x + finiteSignedCliqueCorrection M x ≤ finiteSignedQuadratic M x := by
  have hpoint (i j : ι) : finiteSignedCliqueGain M * (if i = j then 0 else (x i + x j) ^ 2) ≤
      signedEdgePenalty (finiteSignedOffDiagonal M i j) (x i) (x j) := by
    by_cases h : i = j
    · subst j; simp [finiteSignedOffDiagonal, signedEdgePenalty]
    · simp only [h, if_false, finiteSignedOffDiagonal]
      exact (mul_le_mul_of_nonneg_right (finiteSignedCliqueGain_le M h) (sq_nonneg _)).trans
        (signedEdgePenalty_pos_part (M i j) (x i) (x j))
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
  simp only [← Finset.mul_sum] at h
  rw [sum_offDiagonal_pair_add_sq] at h
  rw [finiteSignedQuadratic_edge_decomposition M hsym]
  unfold finiteSignedCliqueCorrection
  linarith only [h]

/-- Either collective estimate may be used, without losing the other one. -/
theorem finiteSigned_triangle_clique_lower (M : ι → ι → ℝ)
    (hsym : ∀ i j, M i j = M j i) (x : ι → ℝ) :
    finiteSignedSeparateLower M x +
      max (finiteSignedTriangleCorrection M x) (finiteSignedCliqueCorrection M x) ≤
      finiteSignedQuadratic M x := by
  have ht := finiteSignedTriangle_lower M hsym x
  have hc := finiteSignedClique_lower M hsym x
  rcases le_total (finiteSignedTriangleCorrection M x) (finiteSignedCliqueCorrection M x) with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

omit [DecidableEq ι] in
theorem finiteSignedCliqueGain_constant {p : ℝ} (hp : 0 ≤ p)
    (h : (Finset.univ : Finset ι).offDiag.Nonempty) :
    finiteSignedCliqueGain (fun _ _ : ι => p) = p := by
  rw [finiteSignedCliqueGain, dif_pos h]
  simp only [max_eq_left hp, Finset.inf'_const]

/-- Whole-clique accounting recovers every rank-one constant form exactly. -/
theorem finiteSignedClique_constant_exact {p : ℝ} (hp : 0 ≤ p)
    (h : (Finset.univ : Finset ι).offDiag.Nonempty) (x : ι → ℝ) :
    finiteSignedSeparateLower (fun _ _ : ι => p) x +
      finiteSignedCliqueCorrection (fun _ _ : ι => p) x =
      finiteSignedQuadratic (fun _ _ : ι => p) x := by
  rw [finiteSignedSeparateLower_constant hp, finiteSignedQuadratic_constant]
  unfold finiteSignedCliqueCorrection
  rw [finiteSignedCliqueGain_constant hp h]
  ring

end RHTower
