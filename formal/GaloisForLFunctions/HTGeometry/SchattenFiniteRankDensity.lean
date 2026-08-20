/-
# Finite-rank operators are dense in every Schatten class

The greedy truncation at order `N` leaves an operator whose `k`-th approximation number is at most
the `(N+k)`-th singular value of the original: the difference of two greedy truncations is a greedy
block, of rank at most the length of the block, and subtracting it turns the order-`N` error into
the order-`(N+k)` error.  Summing the `p`-th powers leaves a tail of a convergent series, so the
Schatten norm of the error vanishes.

Main results:
* `greedyTrunc_add` — the greedy truncations telescope.
* `approxNumber_sub_greedyTrunc_le` — **`a_k(T − T_N) ≤ s_{N+k}(T)`**.
* `tendsto_schattenNorm_sub_greedyTrunc` — **finite-rank density in every Schatten norm**.
-/
import GaloisForLFunctions.RHTower.SchattenTwoIdentity
import GaloisForLFunctions.HTGeometry.SchattenNorm

open ContinuousLinearMap Filter Topology RHTower

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

theorem greedyTrunc_add (T : H →L[ℂ] H) (N k : ℕ) :
    greedyTrunc T (N + k) = greedyTrunc T N + ∑ m ∈ Finset.Ico N (N + k),
      (innerSL ℂ (svVec (energyOp T) m)).smulRight (T (svVec (energyOp T) m)) := by
  classical
  rw [greedyTrunc, greedyTrunc, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) (Nat.le_add_right N k)]

theorem hasRankLE_greedyTrunc_sub (T : H →L[ℂ] H) (N k : ℕ) :
    HasRankLE (greedyTrunc T (N + k) - greedyTrunc T N) k := by
  classical
  have hblock := hasRankLE_greedyBlock T (Finset.Ico N (N + k))
  rw [Nat.card_Ico] at hblock
  have hcard : N + k - N = k := by omega
  rw [hcard] at hblock
  have heq : greedyTrunc T (N + k) - greedyTrunc T N
      = ∑ m ∈ Finset.Ico N (N + k),
        (innerSL ℂ (svVec (energyOp T) m)).smulRight (T (svVec (energyOp T) m)) := by
    rw [greedyTrunc_add T N k]
    abel
  rw [heq]
  exact hblock

/-- **The approximation numbers of the greedy error are shifted singular values.** -/
theorem approxNumber_sub_greedyTrunc_le (hcpt : IsCompactOperator T) (N k : ℕ) :
    approxNumber (T - greedyTrunc T N) k ≤ singVal T (N + k) := by
  have heq : (T - greedyTrunc T N) - (greedyTrunc T (N + k) - greedyTrunc T N)
      = T - greedyTrunc T (N + k) := by abel
  calc approxNumber (T - greedyTrunc T N) k
      ≤ ‖(T - greedyTrunc T N) - (greedyTrunc T (N + k) - greedyTrunc T N)‖ :=
        approxNumber_le _ k _ (hasRankLE_greedyTrunc_sub T N k)
    _ = ‖T - greedyTrunc T (N + k)‖ := by rw [heq]
    _ ≤ singVal T (N + k) := norm_sub_greedyTrunc_le hcpt (N + k)

theorem summable_singVal_rpow {p : ℝ} (hcpt : IsCompactOperator T)
    (hT : MemSchattenClass p T) : Summable fun n => singVal T n ^ p := by
  refine hT.congr fun n => ?_
  rw [approxNumber_eq_singVal hcpt n]

theorem memSchattenClass_sub_greedyTrunc {p : ℝ} (hp : 0 < p) (hcpt : IsCompactOperator T)
    (hT : MemSchattenClass p T) (N : ℕ) :
    MemSchattenClass p (T - greedyTrunc T N) := by
  have hshift : Summable fun k => singVal T (N + k) ^ p :=
    ((summable_singVal_rpow hcpt hT).comp_injective
      (add_right_injective N)).congr fun k => rfl
  refine hshift.of_nonneg_of_le (fun k => Real.rpow_nonneg (approxNumber_nonneg _ k) p)
    fun k => ?_
  exact Real.rpow_le_rpow (approxNumber_nonneg _ k)
    (approxNumber_sub_greedyTrunc_le hcpt N k) hp.le

theorem tsum_rpow_approxNumber_sub_greedyTrunc_le {p : ℝ} (hp : 0 < p)
    (hcpt : IsCompactOperator T) (hT : MemSchattenClass p T) (N : ℕ) :
    (∑' k, approxNumber (T - greedyTrunc T N) k ^ p) ≤ ∑' k, singVal T (N + k) ^ p := by
  have hshift : Summable fun k => singVal T (N + k) ^ p :=
    ((summable_singVal_rpow hcpt hT).comp_injective
      (add_right_injective N)).congr fun k => rfl
  refine (memSchattenClass_sub_greedyTrunc hp hcpt hT N).tsum_le_tsum ?_ hshift
  intro k
  exact Real.rpow_le_rpow (approxNumber_nonneg _ k)
    (approxNumber_sub_greedyTrunc_le hcpt N k) hp.le

/-- **The tail of the singular-value series vanishes.** -/
theorem tendsto_tsum_singVal_rpow_shift {p : ℝ} (T : H →L[ℂ] H) :
    Tendsto (fun N => ∑' k, singVal T (N + k) ^ p) atTop (nhds 0) := by
  have hcongr : ∀ N : ℕ, (∑' k, singVal T (N + k) ^ p) = ∑' k, singVal T (k + N) ^ p := by
    intro N
    exact tsum_congr fun k => by rw [Nat.add_comm]
  simp only [hcongr]
  exact tendsto_sum_nat_add fun n => singVal T n ^ p

/-- **Finite-rank density in every Schatten norm.** -/
theorem tendsto_schattenNorm_sub_greedyTrunc {p : ℝ} (hp : 0 < p)
    (hcpt : IsCompactOperator T) (hT : MemSchattenClass p T) :
    Tendsto (fun N => schattenNorm p (T - greedyTrunc T N)) atTop (nhds 0) := by
  have hinner : Tendsto (fun N => ∑' k, approxNumber (T - greedyTrunc T N) k ^ p) atTop
      (nhds 0) := by
    refine squeeze_zero (fun N => tsum_nonneg fun k =>
      Real.rpow_nonneg (approxNumber_nonneg _ k) p)
      (fun N => tsum_rpow_approxNumber_sub_greedyTrunc_le hp hcpt hT N)
      (tendsto_tsum_singVal_rpow_shift T)
  have hcont : ContinuousAt (fun x : ℝ => x ^ (1 / p)) 0 :=
    Real.continuousAt_rpow_const 0 (1 / p) (Or.inr (by positivity))
  have hcomp := hcont.tendsto.comp hinner
  rw [Real.zero_rpow (by positivity : (1 : ℝ) / p ≠ 0)] at hcomp
  exact hcomp

end

end GaloisForLFunctions.HTGeometry
