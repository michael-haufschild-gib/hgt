import GaloisForLFunctions.RHTower.LogarithmicFiniteEntryProfile
import GaloisForLFunctions.RHTower.LogarithmicSawtoothCorrelation

/-!
# The actual arithmetic content of the Möbius sawtooth profile

On its full prefix the sawtooth profile is exactly a harmonic Möbius
sum, the polar unit, and half the Mertens sum. The square-root truncation
agrees with this full profile on the first half of logarithmic time.
-/

noncomputable section
open scoped BigOperators
open ArithmeticFunction

namespace RHTower

theorem logarithmicMobiusInverse_floor_exp {T : ℝ} (hT : 0 ≤ T) :
    logarithmicMobiusInverse (fun t => (⌊Real.exp t⌋₊ : ℝ)) T = 1 := by
  have heq : (fun t => (⌊Real.exp t⌋₊ : ℝ)) = logarithmicDilationSum (fun _ => 1) := by
    funext t
    simp [logarithmicDilationSum, logarithmicWeightedDilation, Nat.card_Icc]
  rw [heq, logarithmicMobiusInverse_dilationSum _ hT]

theorem logarithmicMobiusInverse_centeredSawtooth {T : ℝ} (hT : 0 ≤ T) :
    logarithmicMobiusInverse logarithmicCenteredSawtooth T =
      Real.exp T * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (moebius n : ℝ) / n) - 1 -
        (1 / 2) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (moebius n : ℝ) := by
  have hb (t : ℝ) : logarithmicCenteredSawtooth t =
      Real.exp t - (⌊Real.exp t⌋₊ : ℝ) - 1 / 2 := by
    rw [logarithmicCenteredSawtooth, Int.fract,
      natCast_floor_eq_intCast_floor (Real.exp_pos t).le]
  have he : (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
      (moebius n : ℝ) * Real.exp (T - Real.log n)) =
        Real.exp T * ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, (moebius n : ℝ) / n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [Real.exp_sub, Real.exp_log hnpos]
    ring
  have hf := logarithmicMobiusInverse_floor_exp hT
  unfold logarithmicMobiusInverse logarithmicWeightedDilation at hf ⊢
  simp_rw [hb, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, he, hf, ← Finset.sum_mul]
  ring

theorem logarithmicShortMobiusInverse_centeredSawtooth_of_cutoff_le (U : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (hU : ⌊Real.exp t⌋₊ ≤ U) :
    logarithmicShortMobiusInverse U logarithmicCenteredSawtooth t =
      Real.exp t * (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, (moebius n : ℝ) / n) - 1 -
        (1 / 2) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, (moebius n : ℝ) := by
  rw [logarithmicShortMobiusInverse_eq_full_of_cutoff_le U _ hU,
    logarithmicMobiusInverse_centeredSawtooth ht]

theorem logarithmicShortMobiusInverse_centeredSawtooth_first_half
    {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T / 2) :
    logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth t =
      Real.exp t * (∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, (moebius n : ℝ) / n) - 1 -
        (1 / 2) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp t⌋₊, (moebius n : ℝ) :=
  logarithmicShortMobiusInverse_centeredSawtooth_of_cutoff_le _ ht
    (Nat.floor_mono (Real.exp_le_exp.mpr htT))

end RHTower
