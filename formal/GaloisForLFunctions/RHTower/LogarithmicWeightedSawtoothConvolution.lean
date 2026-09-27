import GaloisForLFunctions.RHTower.LogarithmicFiniteSawtoothConvolution

/-!
# The logarithmic weight in the signed reciprocal convolution

Symmetry of the finite square transfers half the product logarithm to
one coefficient. Thus the complete linearly weighted correlation is a
pairing of the ordinary profile with its centered logarithmic moment.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RHTower

private theorem symmetric_weight_average (S : Finset ℕ) (k : ℕ → ℕ → ℝ)
    (f : ℕ → ℝ) (hk : ∀ a b, k a b = k b a) :
    (∑ a ∈ S, ∑ b ∈ S, (f a + f b) / 2 * k a b) =
      ∑ a ∈ S, ∑ b ∈ S, f a * k a b := by
  have hs : (∑ a ∈ S, ∑ b ∈ S, f b * k a b) =
      ∑ a ∈ S, ∑ b ∈ S, f a * k a b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hk b a]
  have hd : 2 * (∑ a ∈ S, ∑ b ∈ S, (f a + f b) / 2 * k a b) =
      (∑ a ∈ S, ∑ b ∈ S, f a * k a b) +
        ∑ a ∈ S, ∑ b ∈ S, f b * k a b := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  linarith only [hs, hd]

theorem weighted_reciprocalSawtooth_square_eq_profile_integral (w : ℕ → ℝ) (T : ℝ) :
    (∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
      ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
        w a * w b * ((T - Real.log (a * b : ℕ) - 2) / 2 *
          logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ)))) =
      ∫ s in (0 : ℝ)..T,
        logarithmicFiniteEntryProfile (fun n => w n * (T / 2 - 1 - Real.log n))
          ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth s *
            logarithmicFiniteEntryProfile w ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth (T - s) := by
  let S := Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊
  let k := fun a b : ℕ => w a * w b *
    logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ))
  let f := fun n : ℕ => T / 2 - 1 - Real.log n
  have hk (a b : ℕ) : k a b = k b a := by
    dsimp only [k]
    rw [Nat.mul_comm b a]
    ring
  rw [integral_logarithmicFiniteEntryProfile_pair]
  calc
    _ = ∑ a ∈ S, ∑ b ∈ S, (f a + f b) / 2 * k a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hap : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
      have hbp : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
      dsimp only [f, k]
      rw [Nat.cast_mul, Real.log_mul hap.ne' hbp.ne']
      ring
    _ = ∑ a ∈ S, ∑ b ∈ S, f a * k a b := symmetric_weight_average S k f hk
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [f, k]
      ring

end RHTower
