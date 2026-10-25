import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The geometric future-tail operator on summable coefficients

The future-tail kernel is a subfamily of a summable product. Nonnegative
double summation gives the exact geometric bound needed for one-prime
division away from critical contact.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The geometric sum of coefficients strictly after the current cell. -/
def geometricFutureTail (b : ℝ) (g : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑' s : ℕ, (b : ℂ) ^ (s + 1) * g (m + s + 1)

private theorem summable_geometricSucc {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) :
    Summable (fun s : ℕ => b ^ (s + 1)) := by
  simpa only [pow_succ] using (summable_geometric_of_lt_one hb0 hb1).mul_right b

/-- Joint summability follows from an injective subfamily of the full product majorant. -/
theorem summable_geometricFutureMajorant {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) :
    Summable (fun p : ℕ × ℕ => ‖g (p.1 + p.2 + 1)‖ * b ^ (p.2 + 1)) := by
  have hprod : Summable (fun p : ℕ × ℕ => ‖g p.1‖ * b ^ (p.2 + 1)) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (norm_nonneg _) (pow_nonneg hb0 _))]
    refine ⟨fun r => (summable_geometricSucc hb0 hb1).mul_left ‖g r‖, ?_⟩
    simp only [tsum_mul_left]
    exact hg.mul_right _
  have hinj : Function.Injective (fun p : ℕ × ℕ => (p.1 + p.2 + 1, p.2)) := by
    rintro ⟨m, s⟩ ⟨n, t⟩ h
    change (m + s + 1, s) = (n + t + 1, t) at h
    have hh := Prod.mk.inj h
    exact Prod.ext (by omega) hh.2
  exact Summable.comp_injective
    (f := fun p : ℕ × ℕ => ‖g p.1‖ * b ^ (p.2 + 1))
    (i := fun p : ℕ × ℕ => (p.1 + p.2 + 1, p.2)) hprod hinj

private theorem norm_geometricFutureTerm {b : ℝ} (hb0 : 0 ≤ b) (g : ℕ → ℂ) (m s : ℕ) :
    ‖(b : ℂ) ^ (s + 1) * g (m + s + 1)‖ = ‖g (m + s + 1)‖ * b ^ (s + 1) := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0, mul_comm]

private theorem summable_norm_geometricFutureTerms {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) (m : ℕ) :
    Summable (fun s : ℕ => ‖(b : ℂ) ^ (s + 1) * g (m + s + 1)‖) := by
  have hs := ((summable_prod_of_nonneg
    (fun p : ℕ × ℕ => mul_nonneg (norm_nonneg (g (p.1 + p.2 + 1)))
      (pow_nonneg hb0 (p.2 + 1)))).mp (summable_geometricFutureMajorant hb0 hb1 hg)).1 m
  exact hs.congr fun s => (norm_geometricFutureTerm hb0 g m s).symm

theorem norm_geometricFutureTail_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) (m : ℕ) :
    ‖geometricFutureTail b g m‖ ≤ ∑' s : ℕ, ‖g (m + s + 1)‖ * b ^ (s + 1) := by
  simpa only [geometricFutureTail, norm_geometricFutureTerm hb0] using
    norm_tsum_le_tsum_norm (summable_norm_geometricFutureTerms hb0 hb1 hg m)

/-- Removing the first future coefficient gives the exact backward resolvent recurrence. -/
theorem geometricFutureTail_recurrence {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) (m : ℕ) :
    geometricFutureTail b g m =
      (b : ℂ) * g (m + 1) + (b : ℂ) * geometricFutureTail b g (m + 1) := by
  have hs := (summable_norm_geometricFutureTerms hb0 hb1 hg m).of_norm
  calc
    _ = (b : ℂ) * g (m + 1) +
        ∑' s : ℕ, (b : ℂ) ^ (s + 1 + 1) * g (m + (s + 1) + 1) := by
      rw [geometricFutureTail, hs.tsum_eq_zero_add]
      simp only [zero_add, Nat.add_zero, pow_one]
    _ = _ := by
      rw [geometricFutureTail, ← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro s
      rw [show m + (s + 1) + 1 = (m + 1) + s + 1 by omega, pow_succ]
      ring

/-- The future-tail operator preserves absolute coefficient summability. -/
theorem summable_norm_geometricFutureTail {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) :
    Summable (fun m : ℕ => ‖geometricFutureTail b g m‖) := by
  have hs := ((summable_prod_of_nonneg
    (fun p : ℕ × ℕ => mul_nonneg (norm_nonneg (g (p.1 + p.2 + 1)))
      (pow_nonneg hb0 (p.2 + 1)))).mp (summable_geometricFutureMajorant hb0 hb1 hg)).2
  exact hs.of_nonneg_of_le (fun m => norm_nonneg _) (norm_geometricFutureTail_le hb0 hb1 hg)

/-- The geometric future-tail mass costs at most `b/(1-b)` times the original coefficient mass. -/
theorem tsum_norm_geometricFutureTail_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1)
    {g : ℕ → ℂ} (hg : Summable fun r => ‖g r‖) :
    (∑' m : ℕ, ‖geometricFutureTail b g m‖) ≤ (b / (1 - b)) * ∑' r : ℕ, ‖g r‖ := by
  let F : ℕ × ℕ → ℝ := fun p => ‖g (p.1 + p.2 + 1)‖ * b ^ (p.2 + 1)
  have hF : Summable F := summable_geometricFutureMajorant hb0 hb1 hg
  have hF0 : 0 ≤ F := fun p => mul_nonneg (norm_nonneg _) (pow_nonneg hb0 _)
  have hflip : Summable (fun p : ℕ × ℕ => F (p.2, p.1)) :=
    (Equiv.prodComm ℕ ℕ).summable_iff.mpr hF
  have hswap : (∑' m : ℕ, ∑' s : ℕ, F (m, s)) = ∑' s : ℕ, ∑' m : ℕ, F (m, s) := by
    rw [← hF.tsum_prod, ← hflip.tsum_prod]
    exact ((Equiv.prodComm ℕ ℕ).tsum_eq F).symm
  have htail (s : ℕ) : (∑' m : ℕ, ‖g (m + s + 1)‖) ≤ ∑' r : ℕ, ‖g r‖ := by
    have he := hg.sum_add_tsum_nat_add (s + 1)
    have hp := sum_nonneg (fun r (_ : r ∈ range (s + 1)) => norm_nonneg (g r))
    have he' : (∑ r ∈ range (s + 1), ‖g r‖) +
        (∑' m : ℕ, ‖g (m + s + 1)‖) = ∑' r : ℕ, ‖g r‖ := by
      simpa only [Nat.add_assoc] using he
    linarith only [he', hp]
  have hgsum : (∑' s : ℕ, b ^ (s + 1)) = b / (1 - b) := by
    simp only [pow_succ, tsum_mul_right]
    rw [tsum_geometric_of_lt_one hb0 hb1]
    ring
  calc
    _ ≤ ∑' m : ℕ, ∑' s : ℕ, F (m, s) :=
      (summable_norm_geometricFutureTail hb0 hb1 hg).tsum_le_tsum
        (norm_geometricFutureTail_le hb0 hb1 hg) ((summable_prod_of_nonneg hF0).mp hF).2
    _ = ∑' s : ℕ, ∑' m : ℕ, F (m, s) := hswap
    _ ≤ ∑' s : ℕ, (∑' r : ℕ, ‖g r‖) * b ^ (s + 1) := by
      apply (((summable_prod_of_nonneg (fun p : ℕ × ℕ => hF0 (p.2, p.1))).mp hflip).2).tsum_le_tsum
      · intro s
        simp only [F, tsum_mul_right]
        exact mul_le_mul_of_nonneg_right (htail s) (pow_nonneg hb0 _)
      · exact (summable_geometricSucc hb0 hb1).mul_left _
    _ = _ := by rw [tsum_mul_left, hgsum, mul_comm]

end GaloisForLFunctions.BiarithmeticGeometry
