import GaloisForLFunctions.RHTower.MobiusReciprocalPrimitiveRatio
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# Absolute control of power-unbalanced reciprocal pairs

For the coupled-order kernel `(mn)^2/(m+n)^(5+δ)`, the sector
`m^3 ≤ n^2` has bounded total positive mass whenever `δ > 0`.
Thus only power-balanced pairs can carry an unbounded signed energy.
-/

open Finset
namespace RHTower
noncomputable section

private theorem sum_sq_Icc_le_cube (D : ℕ) :
    ∑ m ∈ Finset.Icc 1 D, (m : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 := by
  induction D with
  | zero => simp
  | succ D ih =>
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · subst h0
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have hD : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast h0
      have hcast : ((D + 1 : ℕ) : ℝ) = (D : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      nlinarith [ih]

private theorem sum_sq_cubic_unbalanced_le (N n : ℕ) :
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2),
        (m : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
  let D := Nat.nthRoot 3 (n ^ 2)
  have hsubset :
      (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2) ⊆
        Finset.Icc 1 D := by
    intro m hm
    obtain ⟨hmN, hm3⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hmN).1,
        (Nat.le_nthRoot_iff (by norm_num : (3 : ℕ) ≠ 0)).2 hm3⟩
  have hD : D ^ 3 ≤ n ^ 2 := by
    dsimp [D]
    rw [Nat.pow_nthRoot_le_iff]
    left
    norm_num
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 D, (m : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ ≤ (D : ℝ) ^ 3 := sum_sq_Icc_le_cube D
    _ ≤ (n : ℝ) ^ 2 := by exact_mod_cast hD

/-- Positive mass of one power-unbalanced half of the finite reciprocal matrix. -/
def unbalancedReciprocalPairMass (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2),
      ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
        (((m : ℝ) + (n : ℝ)) ^ (5 + δ))

/-- The entire unbalanced finite sector is dominated by one convergent p-series. -/
theorem unbalancedReciprocalPairMass_le_pSeries
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    unbalancedReciprocalPairMass δ N ≤
      ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 + δ)) := by
  unfold unbalancedReciprocalPairMass
  apply Finset.sum_le_sum
  intro n hn
  have hnNat : 0 < n := (Finset.mem_Icc.mp hn).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hp : 0 < 5 + δ := by linarith
  have hdenpos : 0 < (n : ℝ) ^ (5 + δ) := Real.rpow_pos_of_pos hnR _
  let S := (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2)
  have hterm (m : ℕ) (hm : m ∈ S) :
      ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
          (((m : ℝ) + (n : ℝ)) ^ (5 + δ)) ≤
        ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) / (n : ℝ) ^ (5 + δ) := by
    have hbase : (n : ℝ) ≤ (m : ℝ) + n := by
      have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hden : (n : ℝ) ^ (5 + δ) ≤
        ((m : ℝ) + (n : ℝ)) ^ (5 + δ) :=
      Real.rpow_le_rpow hnR.le hbase hp.le
    exact div_le_div_of_nonneg_left (by positivity) hdenpos hden
  have hsum := sum_sq_cubic_unbalanced_le N n
  have hfactor :
      (∑ m ∈ S, ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) / (n : ℝ) ^ (5 + δ)) =
        (∑ m ∈ S, (m : ℝ) ^ 2) *
          ((n : ℝ) ^ 2 / (n : ℝ) ^ (5 + δ)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  have hpow : (n : ℝ) ^ (5 + δ) =
      (n : ℝ) ^ (4 : ℕ) * (n : ℝ) ^ (1 + δ) := by
    rw [show 5 + δ = 4 + (1 + δ) by ring, Real.rpow_add hnR]
    norm_num
  have hne : (n : ℝ) ^ (1 + δ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnR _)
  calc
    (∑ m ∈ S, ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
        (((m : ℝ) + (n : ℝ)) ^ (5 + δ))) ≤
      ∑ m ∈ S, ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) / (n : ℝ) ^ (5 + δ) :=
        Finset.sum_le_sum hterm
    _ = (∑ m ∈ S, (m : ℝ) ^ 2) *
          ((n : ℝ) ^ 2 / (n : ℝ) ^ (5 + δ)) := hfactor
    _ ≤ (n : ℝ) ^ 2 *
          ((n : ℝ) ^ 2 / (n : ℝ) ^ (5 + δ)) :=
        mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = (n : ℝ) ^ (-(1 + δ)) := by
      rw [hpow, Real.rpow_neg hnR.le]
      field_simp [ne_of_gt hnR, hne]

/-- A cutoff-independent ceiling for the positive mass of one unbalanced sector. -/
theorem unbalancedReciprocalPairMass_bounded
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ N : ℕ, unbalancedReciprocalPairMass δ N ≤ C := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + δ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine ⟨∑' n : ℕ, (n : ℝ) ^ (-(1 + δ)), fun N => ?_⟩
  exact (unbalancedReciprocalPairMass_le_pSeries δ hδ N).trans
    (hs.sum_le_tsum (Finset.Icc 1 N) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _))

/-- Literal Möbius contribution of the same power-unbalanced sector. -/
def unbalancedReciprocalSignedEnergy (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2),
      mobiusRealCoefficient m * mobiusRealCoefficient n *
        (((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
          (((m : ℝ) + (n : ℝ)) ^ (5 + δ)))

/-- No Möbius cancellation is needed in the unbalanced sector. -/
theorem abs_unbalancedReciprocalSignedEnergy_le_mass
    (δ : ℝ) (N : ℕ) :
    |unbalancedReciprocalSignedEnergy δ N| ≤
      unbalancedReciprocalPairMass δ N := by
  have hmu (k : ℕ) : |mobiusRealCoefficient k| ≤ 1 := by
    unfold mobiusRealCoefficient
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := k)
  unfold unbalancedReciprocalSignedEnergy unbalancedReciprocalPairMass
  calc
    |∑ n ∈ Finset.Icc 1 N,
        ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2),
          mobiusRealCoefficient m * mobiusRealCoefficient n *
            (((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
              (((m : ℝ) + (n : ℝ)) ^ (5 + δ)))| ≤
      ∑ n ∈ Finset.Icc 1 N,
        |∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2),
          mobiusRealCoefficient m * mobiusRealCoefficient n *
            (((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
              (((m : ℝ) + (n : ℝ)) ^ (5 + δ)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2),
            |mobiusRealCoefficient m * mobiusRealCoefficient n *
              (((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
                (((m : ℝ) + (n : ℝ)) ^ (5 + δ)))| := by
        apply Finset.sum_le_sum
        intro n hn
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
          ∑ m ∈ (Finset.Icc 1 N).filter (fun m => m ^ 3 ≤ n ^ 2),
            ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
              (((m : ℝ) + (n : ℝ)) ^ (5 + δ)) := by
        apply Finset.sum_le_sum
        intro n hn
        apply Finset.sum_le_sum
        intro m hm
        let K : ℝ := ((m : ℝ) ^ 2 * (n : ℝ) ^ 2) /
          (((m : ℝ) + (n : ℝ)) ^ (5 + δ))
        have hK : 0 ≤ K := by dsimp [K]; positivity
        have hprod : |mobiusRealCoefficient m| * |mobiusRealCoefficient n| ≤ 1 := by
          calc
            _ ≤ 1 * |mobiusRealCoefficient n| :=
              mul_le_mul_of_nonneg_right (hmu m) (abs_nonneg _)
            _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (hmu n) (by norm_num)
            _ = 1 := by ring
        change |mobiusRealCoefficient m * mobiusRealCoefficient n * K| ≤ K
        rw [abs_mul, abs_mul, abs_of_nonneg hK]
        nlinarith [mul_le_mul_of_nonneg_right hprod hK]

/-- The signed unbalanced contribution has one cutoff-independent ceiling in absolute value. -/
theorem abs_unbalancedReciprocalSignedEnergy_bounded
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ N : ℕ, |unbalancedReciprocalSignedEnergy δ N| ≤ C := by
  obtain ⟨C, hC⟩ := unbalancedReciprocalPairMass_bounded δ hδ
  exact ⟨C, fun N =>
    (abs_unbalancedReciprocalSignedEnergy_le_mass δ N).trans (hC N)⟩

/-- The two power-unbalanced sectors intersect only in the unit pair. -/
theorem cubic_unbalanced_overlap_only_one {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hmn : m ^ 3 ≤ n ^ 2) (hnm : n ^ 3 ≤ m ^ 2) :
    m = 1 ∧ n = 1 := by
  have hprod : m ^ 3 * n ^ 3 ≤ n ^ 2 * m ^ 2 := Nat.mul_le_mul hmn hnm
  have hk : (m * n) ^ 3 ≤ (m * n) ^ 2 := by
    simpa [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hprod
  have hmnOne : m * n = 1 := by
    have hp : 0 < m * n := Nat.mul_pos hm hn
    nlinarith [hk]
  constructor <;> nlinarith [hm, hn, hmnOne]

end
end RHTower
