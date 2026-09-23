import GaloisForLFunctions.RHTower.Sieve.RamarePartitionedLadder
import GaloisForLFunctions.RHTower.Sieve.RamareRoughSetSplit

/-!
# The Möbius mean square over a window, split into three frequency regions

The window carries three different arguments, and nothing forces them to use the same designated
prime range:

* the **disc** `|w| ≤ w₀`, where every prime polynomial is essentially its own cardinality and the
  saving has to come from the Möbius sum itself;
* the **small** part of the annulus, where a chosen family of prime blocks is small by definition of
  the frequency set — there the mean value theorem finishes the job with no arithmetic;
* the **large** part, where that family fails, and a *second*, higher prime range supplies a
  pointwise zero-free-region bound while the smallness of the set is spent through
  Halász–Montgomery.

Because `Sieve/RamareRoughSetSplit.setIntegral_normSq_logPoly_moebius_le_ramare_rough` is
set-parametric, the two ranges never have to be combined into a single decomposition: each is used
only on the region where it is useful, and each pays its own rough class only there.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The small part of the annulus attached to a frequency set. -/
def annulusSmall (T : Set ℝ) (w₀ : ℝ) : Set ℝ := T \ Set.Icc (-w₀) w₀

/-- The large part of the annulus attached to a frequency set. -/
def annulusLarge (T : Set ℝ) (W w₀ : ℝ) : Set ℝ := (Set.Icc (-W) W \ T) \ Set.Icc (-w₀) w₀

theorem measurableSet_annulusSmall {T : Set ℝ} (hTm : MeasurableSet T) (w₀ : ℝ) :
    MeasurableSet (annulusSmall T w₀) := hTm.diff measurableSet_Icc

theorem measurableSet_annulusLarge {T : Set ℝ} (hTm : MeasurableSet T) (W w₀ : ℝ) :
    MeasurableSet (annulusLarge T W w₀) :=
  (measurableSet_Icc.diff hTm).diff measurableSet_Icc

theorem annulusSmall_subset {T : Set ℝ} {W : ℝ} (hTs : T ⊆ Set.Icc (-W) W) (w₀ : ℝ) :
    annulusSmall T w₀ ⊆ Set.Icc (-W) W := fun _ hu => hTs hu.1

theorem annulusLarge_subset (T : Set ℝ) (W w₀ : ℝ) :
    annulusLarge T W w₀ ⊆ Set.Icc (-W) W := fun _ hu => hu.1.1

/-- **The window is the disc plus the two halves of the annulus.** -/
theorem integral_Icc_normSq_logPoly_moebius_le_partition (M : ℕ) {W w₀ : ℝ} (hwW : w₀ ≤ W)
    {T : Set ℝ} (hTm : MeasurableSet T) (hTs : T ⊆ Set.Icc (-W) W)
    {Bdisc Bsmall Blarge : ℝ}
    (hdisc : (∫ w in Set.Icc (-w₀) w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ)) ≤ Bdisc)
    (hsmall : (∫ w in annulusSmall T w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ)) ≤ Bsmall)
    (hlarge : (∫ w in annulusLarge T W w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ)) ≤ Blarge) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ))
      ≤ Bdisc + Bsmall + Blarge := by
  have hcont : Continuous fun w : ℝ =>
      ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  rw [setIntegral_split_three hcont hwW hTm hTs]
  exact add_le_add (add_le_add hdisc hsmall) hlarge

/-- The large half of the annulus sits inside the cut window, which is where every
zero-free-region estimate is stated. -/
theorem annulusLarge_subset_annulus (T : Set ℝ) (W w₀ : ℝ) :
    annulusLarge T W w₀ ⊆ Set.Icc (-W) W \ Set.Icc (-w₀) w₀ :=
  fun _ hu => ⟨hu.1.1, hu.2⟩

end

end RHTower.Sieve
