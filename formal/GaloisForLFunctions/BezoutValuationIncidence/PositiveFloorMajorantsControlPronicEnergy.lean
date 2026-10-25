import GaloisForLFunctions.BezoutValuationIncidence.UniformFloorMeansAndMovingVaughanGrams
import GaloisForLFunctions.BiarithmeticGeometry.PronicEnergyDomain
import Mathlib.Analysis.Normed.Group.Tannery

/-!
A positive reciprocal majorant bounds centered floor prefixes cellwise.
Summable square envelopes then transport pointwise convergence to total
pronic energy and to every moving finite horizon.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A positive reciprocal majorant dominates the centered floor prefix cell by cell. -/
theorem abs_weightCenteredPrefix_le_abs_majorant {a b : ℕ → ℝ}
    (hb : Summable (fun d : ℕ => b d / d)) (hab : ∀ d, |a d| ≤ b d)
    {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix a (∑' d : ℕ, a d / d) n| ≤
      |weightCenteredPrefix b (∑' d : ℕ, b d / d) n| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have heq (w : ℕ → ℝ) : weightCenteredPrefix w (∑' d : ℕ, w d / d) n =
      (pmFloorAverage w n - ∑' d : ℕ, w d / d) * n := by
    rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
      pmFloorAverage, sub_mul, div_mul_cancel₀ _ hn0.ne']
  have hD : 0 ≤ pmFloorMeanDefect b n :=
    pmFloorMeanDefect_nonneg (fun d => (abs_nonneg _).trans (hab d)) hb n
  have heqb : |weightCenteredPrefix b (∑' d : ℕ, b d / d) n| = pmFloorMeanDefect b n * n := by
    rw [heq, abs_mul, Nat.abs_cast, abs_sub_comm, abs_of_nonneg hD]
  rw [heqb, heq, abs_mul, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right (abs_pmFloorAverage_sub_density_le hb hab n) hn0.le

/-- Bounded finite pronic norm gives summability of the unshifted positive-cell series. -/
theorem summable_sq_div_pronicSeq_of_pronicNorm_bound {f : ℕ → ℝ}
    (hf : ∃ C : ℝ, ∀ T : ℕ, pronicNorm f T ≤ C) :
    Summable (fun n : ℕ => f n ^ 2 / (pronicSeq n : ℝ)) := by
  have hs := (BiarithmeticGeometry.bounded_pronicNorm_iff_summable f).mp hf
  have heq : (fun n : ℕ => f (n + 1) ^ 2 / (pronicSeq (n + 1) : ℝ)) =
      BiarithmeticGeometry.pronicCellEnergy f := by
    funext n
    simp only [BiarithmeticGeometry.pronicCellEnergy, pronicSeq, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  apply (summable_nat_add_iff 1).mp
  rwa [heq]

/-- A common square-cell bound controls every mixed cell by the elementary quadratic inequality. -/
theorem abs_pair_div_le_common_square_bound {x y d B : ℝ} (hd : 0 ≤ d)
    (hx : x ^ 2 / d ≤ B) (hy : y ^ 2 / d ≤ B) : |x * y / d| ≤ B := by
  have hxy : |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith only [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  calc
    _ = |x * y| / d := by rw [abs_div, abs_of_nonneg hd]
    _ ≤ ((x ^ 2 + y ^ 2) / 2) / d := div_le_div_of_nonneg_right hxy hd
    _ = (x ^ 2 / d + y ^ 2 / d) / 2 := by ring
    _ ≤ B := by linarith only [hx, hy]


private theorem norm_pronic_square_sub_le_four {x y B : ℝ} {n : ℕ}
    (hx : x ^ 2 / (pronicSeq n : ℝ) ≤ B) (hy : y ^ 2 / (pronicSeq n : ℝ) ≤ B) :
    ‖(x - y) ^ 2 / (pronicSeq n : ℝ)‖ ≤ 4 * B := by
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (x - y) ^ 2 / (pronicSeq n : ℝ))]
  have hpoly : (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
    nlinarith only [sq_nonneg (x + y)]
  calc
    _ ≤ (2 * x ^ 2 + 2 * y ^ 2) / (pronicSeq n : ℝ) :=
      div_le_div_of_nonneg_right hpoly (Nat.cast_nonneg _)
    _ = 2 * (x ^ 2 / (pronicSeq n : ℝ)) + 2 * (y ^ 2 / (pronicSeq n : ℝ)) := by ring
    _ ≤ 4 * B := by linarith only [hx, hy]

/-- Cellwise limits under one summable square envelope converge in total pronic square distance. -/
theorem tendsto_tsum_pronic_square_sub_of_summable_envelope
    {f : ℕ → ℕ → ℝ} {F g : ℕ → ℝ} (hg : Summable g)
    (hpoint : ∀ n, Tendsto (fun t => f t n) atTop (𝓝 (F n)))
    (hbound : ∀ t n, f t n ^ 2 / (pronicSeq n : ℝ) ≤ g n) :
    Tendsto (fun t => ∑' n : ℕ, (f t n - F n) ^ 2 / (pronicSeq n : ℝ)) atTop (𝓝 0) := by
  have hF (n : ℕ) : F n ^ 2 / (pronicSeq n : ℝ) ≤ g n :=
    le_of_tendsto' (((hpoint n).pow 2).div_const (pronicSeq n : ℝ)) (fun t => hbound t n)
  have hdom (t n : ℕ) : ‖(f t n - F n) ^ 2 / (pronicSeq n : ℝ)‖ ≤ 4 * g n :=
    norm_pronic_square_sub_le_four (hbound t n) (hF n)
  have hlim := tendsto_tsum_of_dominated_convergence (hg.mul_left 4)
    (g := fun _ : ℕ => (0 : ℝ)) (fun n => ?_) (Eventually.of_forall hdom)
  · simpa only [tsum_zero] using hlim
  · simpa only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] using
      (((hpoint n).sub tendsto_const_nhds).pow 2).div_const (pronicSeq n : ℝ)

/-- The same summable envelope controls pronic norm convergence at every moving finite horizon. -/
theorem tendsto_pronicNorm_sub_at_moving_horizon_of_summable_envelope
    {f : ℕ → ℕ → ℝ} {F g : ℕ → ℝ} (hg : Summable g)
    (hpoint : ∀ n, Tendsto (fun t => f t n) atTop (𝓝 (F n)))
    (hbound : ∀ t n, f t n ^ 2 / (pronicSeq n : ℝ) ≤ g n) (H : ℕ → ℕ) :
    Tendsto (fun t => pronicNorm (fun n => f t n - F n) (H t)) atTop (𝓝 0) := by
  have hF (n : ℕ) : F n ^ 2 / (pronicSeq n : ℝ) ≤ g n :=
    le_of_tendsto' (((hpoint n).pow 2).div_const (pronicSeq n : ℝ)) (fun t => hbound t n)
  have hsum (t : ℕ) : Summable (fun n => (f t n - F n) ^ 2 / (pronicSeq n : ℝ)) :=
    (hg.mul_left 4).of_norm_bounded (fun n => norm_pronic_square_sub_le_four (hbound t n) (hF n))
  have hlim := (tendsto_tsum_pronic_square_sub_of_summable_envelope hg hpoint hbound).sqrt
  rw [Real.sqrt_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun t => pronicNorm_nonneg _ _) ?_ hlim
  apply Eventually.of_forall
  intro t
  apply Real.sqrt_le_sqrt
  change (∑ n ∈ Icc 1 (H t), (f t n - F n) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤ _
  simpa only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
    (hsum t).sum_le_tsum (Icc 1 (H t)) (fun n _ => by positivity)

#print axioms tendsto_tsum_pronic_square_sub_of_summable_envelope
#print axioms tendsto_pronicNorm_sub_at_moving_horizon_of_summable_envelope
#print axioms abs_pair_div_le_common_square_bound
#print axioms abs_weightCenteredPrefix_le_abs_majorant
#print axioms summable_sq_div_pronicSeq_of_pronicNorm_bound
end GaloisForLFunctions.BezoutValuationIncidence
