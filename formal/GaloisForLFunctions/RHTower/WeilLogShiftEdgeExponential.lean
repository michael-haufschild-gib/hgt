import GaloisForLFunctions.RHTower.WeilLogShiftBinomialExponential
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointDomination
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMeanBinomialBound

/-! Uniform exponential moments for the actual centered finite Weil edge index. -/

open scoped BigOperators
open Set

namespace RHTower

theorem finiteWeilCanonicalMixture_scaled_exponential_bound (r t : ℕ) (a : ℝ) :
    (∑ j : Fin (r + 2), finiteWeilCanonicalMixture r (2 * (r + 1) ^ 2 + t) (1 / 2) j *
      Real.exp (a * ((j : ℝ) - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ))) ≤
      4 * Real.exp (a ^ 2 / 8) := by
  calc
    _ ≤ ∑ j : Fin (r + 2),
        (4 * (((r + 1).choose (j : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1))) *
          Real.exp (a * ((j : ℝ) - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
        (finiteWeilCanonicalMixture_midpoint_binomial_domination r t j) (Real.exp_pos _).le
    _ = 4 * ∑ j : Fin (r + 2), (((r + 1).choose (j : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) *
        Real.exp (a * ((j : ℝ) - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (finiteWeil_binomial_scaled_exponential_bound r a) (by norm_num)

theorem finiteWeilCanonicalEdge_arithmetic_exponential_bound (r t : ℕ) (a : ℝ) :
    (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i *
      Real.exp (a * ((i : ℝ) - (r : ℝ) / 2) / Real.sqrt (r + 1 : ℕ))) ≤
      4 * Real.exp (a ^ 2 / 8) := by
  let f (j : Fin (r + 2)) :=
    Real.exp (a * ((j : ℝ) - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ))
  have hpoint (i : Fin (r + 1)) :
      Real.exp (a * ((i : ℝ) - (r : ℝ) / 2) / Real.sqrt (r + 1 : ℕ)) ≤
        (f i.castSucc + f i.succ) / 2 := by
    have h := convexOn_exp.2
      (mem_univ (a * ((i : ℝ) - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ)))
      (mem_univ (a * ((i : ℝ) + 1 - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ)))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul] at h
    have he : (1 / 2 : ℝ) * (a * ((i : ℝ) - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ)) +
        (1 / 2 : ℝ) * (a * ((i : ℝ) + 1 - (r + 1 : ℕ) / 2) / Real.sqrt (r + 1 : ℕ)) =
        a * ((i : ℝ) - (r : ℝ) / 2) / Real.sqrt (r + 1 : ℕ) := by
      push_cast
      ring
    rw [he] at h
    dsimp [f]
    push_cast at h ⊢
    linarith
  calc
    _ ≤ ∑ i, finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i *
        ((f i.castSucc + f i.succ) / 2) := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hpoint i) (finiteWeilCanonicalEdgeMass_pos _ _ _).le
    _ = (∑ i, finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i *
        (f i.castSucc + f i.succ)) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ j, finiteWeilCanonicalMixture r (2 * (r + 1) ^ 2 + t) (1 / 2) j * f j :=
      (finiteWeilCanonicalMixture_midpoint_edge_pairing _ _ f).symm
    _ ≤ _ := finiteWeilCanonicalMixture_scaled_exponential_bound r t a

theorem finiteWeilCanonicalEdgeIndexMean_sqrt_shift_bound (r t : ℕ) :
    |(finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2) /
      Real.sqrt (r + 1 : ℕ)| ≤ 1 := by
  have hw : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((2 * (r + 1) ^ 2 + t + 2 : ℕ) : ℝ) := by
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) t]
  have hn : (1 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hs : 0 < Real.sqrt (r + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_nonneg hs.le]
  apply (div_le_iff₀ hs).mpr
  simp only [one_mul]
  exact (finiteWeilCanonicalEdgeIndexMean_binomial_bound r _ hw).trans
    (Real.sqrt_le_sqrt (by linarith))

theorem finiteWeilCanonicalEdge_centered_exponential_bound (r t : ℕ) (a : ℝ) :
    (∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i *
      Real.exp (a * (((i : ℝ) - finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t)) /
        Real.sqrt (r + 1 : ℕ)))) ≤ 4 * Real.exp (|a| + a ^ 2 / 8) := by
  let z := (finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) - (r : ℝ) / 2) /
    Real.sqrt (r + 1 : ℕ)
  have hz : |z| ≤ 1 := finiteWeilCanonicalEdgeIndexMean_sqrt_shift_bound r t
  have haz : -a * z ≤ |a| := by
    have h : |a * z| ≤ |a| := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz (abs_nonneg a)
    linarith [(abs_le.mp h).1]
  calc
    _ = Real.exp (-a * z) *
        ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t) i *
          Real.exp (a * ((i : ℝ) - (r : ℝ) / 2) / Real.sqrt (r + 1 : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he : a * (((i : ℝ) - finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t)) /
          Real.sqrt (r + 1 : ℕ)) = -a * z +
          a * ((i : ℝ) - (r : ℝ) / 2) / Real.sqrt (r + 1 : ℕ) := by dsimp [z]; ring
      rw [he, Real.exp_add]
      ring
    _ ≤ Real.exp (-a * z) * (4 * Real.exp (a ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_left (finiteWeilCanonicalEdge_arithmetic_exponential_bound r t a)
        (Real.exp_pos _).le
    _ ≤ Real.exp |a| * (4 * Real.exp (a ^ 2 / 8)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr haz) (by positivity)
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]

end RHTower
