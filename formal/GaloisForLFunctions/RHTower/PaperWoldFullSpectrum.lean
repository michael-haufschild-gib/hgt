import GaloisForLFunctions.RHTower.PaperWoldFullOperator

/-! # Directed spectrum and surviving signs of the full Wold interaction -/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped BigOperators ENNReal InnerProductSpace

theorem paperWoldMaskedOperator_pow_vanish (p : PaperWoldStrictHalf) (mask : PaperWoldMask)
    (k N : ℕ) (x : PaperWoldHistory) (hx : ∀ j, N ≤ j → x j = 0) :
    ∀ n, N ≤ n + k → (paperWoldMaskedOperator p mask ^ k) x n = 0 := by
  induction k with
  | zero => intro n hn; simpa using hx n (by simpa using hn)
  | succ k ih =>
      intro n hn
      rw [pow_succ']
      change paperWoldMaskedOperator p mask ((paperWoldMaskedOperator p mask ^ k) x) n = 0
      rw [paperWoldMaskedOperator_apply]
      trans ∑' _ : ℕ, (0 : ℂ)
      · apply tsum_congr
        intro j
        by_cases hnj : n < j
        · rw [ih j (by omega), mul_zero]
        · rw [paperWoldMaskedKernel_lower p mask (by omega), zero_mul]
      · exact tsum_zero

theorem paperWoldMaskedOperator_pow_prefix_zero (p : PaperWoldStrictHalf) (mask : PaperWoldMask)
    (N k : ℕ) (hk : N ≤ k) :
    (paperWoldMaskedOperator p mask ^ k) * paperWoldPrefixProjection N = 0 := by
  ext x n
  apply paperWoldMaskedOperator_pow_vanish p mask k N (paperWoldPrefixProjection N x)
    (fun j hj => by simp [not_lt_of_ge hj]) n (by omega)

theorem paperWoldMaskedOperator_spectrum_subset (p : PaperWoldStrictHalf) (mask : PaperWoldMask) :
    spectrum ℂ (paperWoldMaskedOperator p mask) ⊆ {0} := by
  intro z hz
  exact QuasinilpotentLowering.eq_zero_of_mem_spectrum_of_isCompactOperator
    (paperWoldMaskedOperator p mask) paperWoldPrefixProjection paperWoldPrefixProjection_complement_norm
    paperWoldPrefixProjection_complement_strong
    (fun N k hk => paperWoldMaskedOperator_pow_prefix_zero p mask N k (by omega))
    (paperWoldMaskedOperator_compact p mask) hz

def paperWoldFullSymmetric (p : PaperWoldStrictHalf) : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  paperWoldFullOperator p + ContinuousLinearMap.adjoint (paperWoldFullOperator p)

theorem paperWoldFullSymmetric_compact (p : PaperWoldStrictHalf) :
    IsCompactOperator (paperWoldFullSymmetric p) :=
  (paperWoldMaskedOperator_compact p paperWoldFullMask).add
    (isCompactOperator_adjoint_rectangular _ (paperWoldMaskedOperator_compact p paperWoldFullMask))

theorem paperWoldFullSymmetric_selfAdjoint (p : PaperWoldStrictHalf) :
    ContinuousLinearMap.adjoint (paperWoldFullSymmetric p) = paperWoldFullSymmetric p := by
  simp [paperWoldFullSymmetric, add_comm]

theorem paperWoldFullSymmetric_traceCost (p : PaperWoldStrictHalf) :
    compactOperatorTraceCost PaperWoldHistory (paperWoldFullSymmetric p) = 0 :=
  (compactOperatorTraceCost_eq_zero_iff _).mpr (paperWoldFullSymmetric_compact p)

theorem paperWoldFullSymmetric_quadratic (p : PaperWoldStrictHalf) (x : PaperWoldHistory) :
    (inner ℂ x (paperWoldFullSymmetric p x)).re =
      2 * (inner ℂ x (paperWoldFullOperator p x)).re := by
  rw [paperWoldFullSymmetric, add_apply, inner_add_right,
    Complex.add_re, ContinuousLinearMap.adjoint_inner_right]
  have hs : (inner ℂ (paperWoldFullOperator p x) x).re =
      (inner ℂ x (paperWoldFullOperator p x)).re :=
    inner_re_symm (𝕜 := ℂ) (paperWoldFullOperator p x) x
  rw [hs]
  ring

theorem paperWoldFullOperator_adjacent_form (p : PaperWoldStrictHalf) (n : ℕ) (a b : ℂ) :
    inner ℂ (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ))
      (paperWoldFullOperator p (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ))) =
      star a * b * (paperWoldInteraction p.nearParameters n (n + 1) : ℂ) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one, starRingEnd_apply,
    paperWoldFullOperator_single, paperWoldFullKernel, Nat.lt_irrefl, if_false,
    Nat.lt_succ_self, if_true, show ¬ n + 1 < n by omega, mul_zero, add_zero, zero_add]
  ring

theorem paperWoldFullSymmetric_adjacent_form (p : PaperWoldStrictHalf) (n : ℕ) (a b : ℂ) :
    (inner ℂ (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ))
      (paperWoldFullSymmetric p (a • lp.single 2 n (1 : ℂ) + b • lp.single 2 (n + 1) (1 : ℂ)))).re =
      2 * (star a * b).re * paperWoldInteraction p.nearParameters n (n + 1) := by
  rw [paperWoldFullSymmetric_quadratic, paperWoldFullOperator_adjacent_form]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

theorem paperWoldFullSymmetric_both_signs (p : PaperWoldStrictHalf) :
    (∃ x : PaperWoldHistory, 0 < (inner ℂ x (paperWoldFullSymmetric p x)).re) ∧
      (∃ y : PaperWoldHistory, (inner ℂ y (paperWoldFullSymmetric p y)).re < 0) := by
  constructor
  · refine ⟨(1 : ℂ) • lp.single 2 6 (1 : ℂ) + (1 : ℂ) • lp.single 2 7 (1 : ℂ), ?_⟩
    rw [paperWoldFullSymmetric_adjacent_form p 6 1 1]
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) (paperWoldCompositeInteraction_pos p.nearParameters)
  · refine ⟨(1 : ℂ) • lp.single 2 6 (1 : ℂ) + (-1 : ℂ) • lp.single 2 7 (1 : ℂ), ?_⟩
    rw [paperWoldFullSymmetric_adjacent_form p 6 1 (-1)]
    simp only [star_one, one_mul, Complex.neg_re, Complex.one_re]
    nlinarith [paperWoldCompositeInteraction_pos p.nearParameters]

theorem paperWoldFullOperator_package (p : PaperWoldStrictHalf) :
    (paperWoldFullOperator p).IsHilbertSchmidt ∧
      IsCompactOperator (paperWoldFullOperator p) ∧ paperWoldFullOperator p ≠ 0 ∧
      spectrum ℂ (paperWoldFullOperator p) ⊆ {0} ∧
      compactOperatorTraceCost PaperWoldHistory (paperWoldFullOperator p) = 0 ∧
      (∃ x : PaperWoldHistory, 0 < (inner ℂ x (paperWoldFullSymmetric p x)).re) ∧
      (∃ y : PaperWoldHistory, (inner ℂ y (paperWoldFullSymmetric p y)).re < 0) :=
  ⟨paperWoldMaskedOperator_isHilbertSchmidt p _, paperWoldMaskedOperator_compact p _,
    paperWoldFullOperator_ne_zero p, paperWoldMaskedOperator_spectrum_subset p _,
    paperWoldMaskedOperator_traceCost p _, paperWoldFullSymmetric_both_signs p⟩

end
end RHTower
