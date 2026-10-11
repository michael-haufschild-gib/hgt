import GaloisForLFunctions.RHTower.WeilLogShiftOrderedTransport
import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticMassComparison

/-! Exact adjacent transport on the canonical logarithmic nodes, without a width hypothesis. -/

open scoped BigOperators NNReal

noncomputable section
namespace RHTower

def finiteWeilCanonicalLogTransportCost (r k : ℕ) : ℝ :=
  ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
    (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc)

theorem finiteWeilCanonicalCoupling_log_cost (r k : ℕ) :
    finiteWeilCouplingCost (finiteWeilCanonicalCoupling r k)
      (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) =
        finiteWeilCanonicalLogTransportCost r k :=
  finiteWeilCanonicalCoupling_ordered_cost r k _ (finiteWeilClusterLogNodes_strictMono r k).monotone

theorem finiteWeilCanonicalLogTransportCost_bounds (r k : ℕ) :
    1 / ((k + r + 3 : ℕ) : ℝ) ≤ finiteWeilCanonicalLogTransportCost r k ∧
      finiteWeilCanonicalLogTransportCost r k ≤ 1 / ((k + 2 : ℕ) : ℝ) := by
  have hA : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hU : (0 : ℝ) < ((k + r + 3 : ℕ) : ℝ) := by positivity
  have hgap (i : Fin (r + 1)) := finiteWeilClusterLogNodes_gap_comparison r k i.succ i.castSucc
  have hs (i : Fin (r + 1)) :
      ((k + 2 : ℕ) : ℝ) *
          (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc) ≤ 1 ∧
        1 ≤ ((k + r + 3 : ℕ) : ℝ) *
          (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc) := by
    have hp : 0 < finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc :=
      sub_pos.mpr (finiteWeilClusterLogNodes_strictMono r k
        (show i.castSucc < i.succ from by change i.val < i.val + 1; omega))
    have hd : |finiteWeilArithmeticNodes r i.succ - finiteWeilArithmeticNodes r i.castSucc| = 1 := by
      simp [finiteWeilArithmeticNodes]
    simpa only [abs_of_nonneg (le_of_lt hp), hd] using hgap i
  have hupper : ((k + 2 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCost r k ≤ 1 := by
    calc
      _ = ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
          (((k + 2 : ℕ) : ℝ) *
            (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc)) := by
        simp only [finiteWeilCanonicalLogTransportCost, Finset.mul_sum, mul_left_comm]
      _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * 1 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hs i).1 (le_of_lt (finiteWeilCanonicalEdgeMass_pos r k i))
      _ = 1 := by simp only [mul_one]; exact finiteWeilCanonicalEdgeMass_sum r k
  have hlower : 1 ≤ ((k + r + 3 : ℕ) : ℝ) * finiteWeilCanonicalLogTransportCost r k := by
    calc
      1 = ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i * 1 := by
        simp only [mul_one]; exact (finiteWeilCanonicalEdgeMass_sum r k).symm
      _ ≤ ∑ i : Fin (r + 1), finiteWeilCanonicalEdgeMass r k i *
          (((k + r + 3 : ℕ) : ℝ) *
            (finiteWeilClusterLogNodes r k i.succ - finiteWeilClusterLogNodes r k i.castSucc)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hs i).2 (le_of_lt (finiteWeilCanonicalEdgeMass_pos r k i))
      _ = _ := by simp only [finiteWeilCanonicalLogTransportCost, Finset.mul_sum, mul_left_comm]
  constructor
  · apply (div_le_iff₀ hU).mpr
    linarith only [hlower]
  · apply (le_div_iff₀ hA).mpr
    linarith only [hupper]

theorem finiteWeilCanonicalLogTransportCost_pos (r k : ℕ) :
    0 < finiteWeilCanonicalLogTransportCost r k := by
  exact lt_of_lt_of_le (by positivity) (finiteWeilCanonicalLogTransportCost_bounds r k).1

theorem finiteWeilCanonicalTransport_log_minimum_iff (r k : ℕ)
    (gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
      (finiteWeilCanonicalNegativeNNProfile r k)) :
    finiteWeilCouplingCost gamma
      (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) =
      finiteWeilCanonicalLogTransportCost r k ↔ gamma = finiteWeilCanonicalCoupling r k := by
  rw [← finiteWeilCanonicalCoupling_log_cost]
  exact finiteWeilCanonicalTransport_ordered_minimum_iff r k _
    (finiteWeilClusterLogNodes_strictMono r k) gamma

theorem finiteWeilCanonicalTransport_log_unique_minimizer (r k : ℕ) :
    ∃! gamma : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
        (finiteWeilCanonicalNegativeNNProfile r k),
      ∀ eta : HTGeometry.FiniteNNCoupling (finiteWeilCanonicalPositiveNNProfile r k)
          (finiteWeilCanonicalNegativeNNProfile r k),
        finiteWeilCouplingCost gamma
            (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) ≤
          finiteWeilCouplingCost eta
            (fun u v => |finiteWeilClusterLogNodes r k u - finiteWeilClusterLogNodes r k v|) :=
  finiteWeilCanonicalTransport_ordered_unique_minimizer r k _ (finiteWeilClusterLogNodes_strictMono r k)

end RHTower
