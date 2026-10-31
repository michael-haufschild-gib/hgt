import GaloisForLFunctions.BiarithmeticGeometry.Affine.PolynomialQuadrature

/-!
# Separated rational grids for polynomial quadrature

Geometrically nested blocks of nonzero integer nodes are disjoint and fit inside any
prescribed positive interval. Every finite family of nonzero slopes has a common such interval.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The `i+1`st node in the `t`th geometrically shrinking block. -/
def quadratureTranslationNode {n : ℕ} (ε : ℚ) (i : Fin n) (t : ℕ) : ℚ :=
  ε * ((i.val + 1 : ℕ) : ℚ) / (n + 1 : ℚ) ^ (t + 1)

/-- Each block lies between consecutive geometric radii. -/
theorem quadratureTranslationNode_block_bounds {n : ℕ} {ε : ℚ} (hε : 0 < ε)
    (i : Fin n) (t : ℕ) :
    ε / (n + 1 : ℚ) ^ (t + 1) ≤ quadratureTranslationNode ε i t ∧
      quadratureTranslationNode ε i t < ε / (n + 1 : ℚ) ^ t := by
  have hL : (0 : ℚ) < n + 1 := by positivity
  have hs : (1 : ℚ) ≤ ((i.val + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos i.val
  have hsL : (((i.val + 1 : ℕ) : ℚ)) < n + 1 := by exact_mod_cast Nat.succ_lt_succ i.isLt
  constructor
  · exact div_le_div_of_nonneg_right
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hε.le)
      (pow_pos hL (t + 1)).le
  · calc
      quadratureTranslationNode ε i t < ε * (n + 1 : ℚ) / (n + 1 : ℚ) ^ (t + 1) :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsL hε) (pow_pos hL _)
      _ = ε / (n + 1 : ℚ) ^ t := by
        rw [pow_succ]
        field_simp [hL.ne']

/-- All nodes are positive and smaller than the chosen radius. -/
theorem quadratureTranslationNode_pos_lt {n : ℕ} {ε : ℚ} (hε : 0 < ε)
    (i : Fin n) (t : ℕ) : 0 < quadratureTranslationNode ε i t ∧
      quadratureTranslationNode ε i t < ε := by
  have hL : (1 : ℚ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  constructor
  · unfold quadratureTranslationNode
    positivity
  · apply (quadratureTranslationNode_block_bounds hε i t).2.trans_le
    simpa only [div_one] using
      div_le_div_of_nonneg_left hε.le (zero_lt_one : (0 : ℚ) < 1) (one_le_pow₀ hL)

/-- Every node of a later block lies strictly below every node of an earlier block. -/
theorem quadratureTranslationNode_lt_of_block_lt {n : ℕ} {ε : ℚ} (hε : 0 < ε)
    (i j : Fin n) {t u : ℕ} (htu : t < u) :
    quadratureTranslationNode ε j u < quadratureTranslationNode ε i t := by
  have hL : (1 : ℚ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hpow : (n + 1 : ℚ) ^ (t + 1) ≤ (n + 1 : ℚ) ^ u :=
    pow_le_pow_right₀ hL htu
  exact (quadratureTranslationNode_block_bounds hε j u).2.trans_le
    ((div_le_div_of_nonneg_left hε.le (pow_pos (zero_lt_one.trans_le hL) _) hpow).trans
      (quadratureTranslationNode_block_bounds hε i t).1)

/-- Distinct node indices give distinct rational translations, across all blocks. -/
theorem quadratureTranslationNode_injective {n : ℕ} {ε : ℚ} (hε : 0 < ε) :
    Function.Injective (fun x : Fin n × ℕ => quadratureTranslationNode ε x.1 x.2) := by
  intro x y h
  have ht : x.2 = y.2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (quadratureTranslationNode_lt_of_block_lt hε x.1 y.1 hlt)) h.symm
    · exact (ne_of_lt (quadratureTranslationNode_lt_of_block_lt hε y.1 x.1 hgt)) h
  apply Prod.ext ?_ ht
  apply Fin.ext
  have hL : (n + 1 : ℚ) ≠ 0 := by positivity
  have he := h
  dsimp only [quadratureTranslationNode] at he
  rw [ht] at he
  field_simp [hL] at he
  have hiNat : x.1.val + 1 = y.1.val + 1 := by exact_mod_cast he
  exact Nat.add_right_cancel hiNat

/-- A finite family of nonzero rational slopes has a common positive lower radius. -/
theorem exists_positive_lt_abs_slopes {ι : Type*} [Fintype ι] (a : ι → ℚ)
    (ha : ∀ i, a i ≠ 0) : ∃ ε : ℚ, 0 < ε ∧ ∀ i, ε < |a i| := by
  let S : ℚ := 1 + ∑ i, |a i|⁻¹
  have hsum : 0 ≤ ∑ i, |a i|⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (abs_nonneg _)
  have hS : 0 < S := by dsimp only [S]; linarith only [hsum]
  refine ⟨1 / S, one_div_pos.mpr hS, ?_⟩
  intro i
  have hai : 0 < |a i| := abs_pos.mpr (ha i)
  have hb : |a i|⁻¹ ≤ ∑ j, |a j|⁻¹ :=
    Finset.single_le_sum (fun j _ => inv_nonneg.mpr (abs_nonneg (a j))) (Finset.mem_univ i)
  have hb' : |a i|⁻¹ < S := by dsimp only [S]; linarith only [hb]
  apply (div_lt_iff₀ hS).mpr
  have hm := mul_lt_mul_of_pos_right hb' hai
  simpa only [inv_mul_cancel₀ hai.ne', mul_comm] using hm

#print axioms quadratureTranslationNode_injective
#print axioms exists_positive_lt_abs_slopes
end GaloisForLFunctions.BiarithmeticGeometry
