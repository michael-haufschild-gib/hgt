import GaloisForLFunctions.RHTower.Suzuki.SuzukiLatticeSharpMoment

/-!
# Two elementary comparisons for the weighted estimate

The `ℓ²` norm is monotone under pointwise domination, and the shell weight `⟨r⟩^m` is dominated by
the coordinate moments of order `m`: Jensen's inequality for sums of powers, applied to the `d+1`
numbers `1, |r_1|, …, |r_d|`, is exactly the statement that no single coordinate can be small while
the shell index is large.
-/

open Finset
open scoped ENNReal

noncomputable section

namespace RHTower

variable {P : Type*} [Fintype P] [DecidableEq P]

local notation "H" => lp (fun _ : (P → ℤ) => ℂ) 2

omit [Fintype P] [DecidableEq P] in
/-- The `ℓ²` norm is monotone under pointwise domination. -/
theorem norm_le_of_pointwise_le {u v : H}
    (h : ∀ r : P → ℤ, ‖((u : H) : (P → ℤ) → ℂ) r‖ ≤ ‖((v : H) : (P → ℤ) → ℂ) r‖) :
    ‖u‖ ≤ ‖v‖ := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow hp, lp.norm_eq_tsum_rpow hp]
  refine Real.rpow_le_rpow ?_ ?_ (by positivity)
  · exact tsum_nonneg fun r => by positivity
  · refine Summable.tsum_le_tsum ?_ ((memℓp_gen_iff hp).mp (lp.memℓp u))
      ((memℓp_gen_iff hp).mp (lp.memℓp v))
    intro r
    exact Real.rpow_le_rpow (norm_nonneg _) (h r) (by norm_num)
omit [DecidableEq P] in
/-- **The shell weight is dominated by the coordinate moments.** -/
theorem orbitLength_pow_le (m : ℕ) (r : P → ℤ) :
    (1 + (orbitLength r : ℝ)) ^ (m + 1)
      ≤ ((Fintype.card P : ℝ) + 1) ^ m * (1 + ∑ p, |((r p : ℤ) : ℝ)| ^ (m + 1)) := by
  classical
  set g : Option P → ℝ := fun o => Option.rec (1 : ℝ) (fun p => |((r p : ℤ) : ℝ)|) o with hgdef
  have hg0 : ∀ i ∈ (Finset.univ : Finset (Option P)), 0 ≤ g i := by
    intro i _
    cases i with
    | none => simp [hgdef]
    | some p => simp [hgdef]
  have hsum : ∑ i ∈ (Finset.univ : Finset (Option P)), g i = 1 + (orbitLength r : ℝ) := by
    rw [Fintype.sum_option]
    congr 1
    rw [orbitLength]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    show |((r p : ℤ) : ℝ)| = (((r p).natAbs : ℕ) : ℝ)
    simp [Int.cast_abs]
  have hsumpow : ∑ i ∈ (Finset.univ : Finset (Option P)), g i ^ (m + 1)
      = 1 + ∑ p, |((r p : ℤ) : ℝ)| ^ (m + 1) := by
    rw [Fintype.sum_option]
    simp [hgdef]
  have hcard : ((Finset.univ : Finset (Option P)).card : ℝ) = (Fintype.card P : ℝ) + 1 := by
    rw [Finset.card_univ, Fintype.card_option]
    push_cast
    ring
  have hbase := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Option P))) (f := g)
    hg0 m
  rw [hsum, hsumpow, hcard] at hbase
  exact hbase

end RHTower
