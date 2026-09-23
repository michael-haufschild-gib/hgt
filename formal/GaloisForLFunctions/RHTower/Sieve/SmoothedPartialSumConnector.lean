import GaloisForLFunctions.RHTower.Sieve.ConvolutionSmoothingError
import GaloisForLFunctions.RHTower.Sieve.HalaszPerronAssembly

/-!
# From the smoothed sum to the sharp partial sum

The Halász assembly of the corpus bounds the *smoothly* cut series `∑ₙ f(n)w(n)`, whereas a mean value
theorem is a statement about the sharp partial sum `∑_{n ≤ K} f(n)`.  The two differ only on the
transition window `(K, ⌊K+H⌋]`, whose length is at most `H`, so for `‖f‖ ≤ 1`

`‖∑_{n ≤ K} f(n)‖ ≤ B/(2π) + H`   whenever   `2π‖∑ₙ f(n)w(n)‖ ≤ B`.

Two facts make this unconditional: the smooth cutoff vanishes past `K + H`, so its weighted series is a
finite sum, and the window law bounds the disturbance by the window length times the coefficient size.
Instantiating `B` by the assembled Halász bound turns it into an explicit bound for the partial sums of a
bounded multiplicative function, with the removal of the smoothing costing exactly the width `H`.
-/

noncomputable section
namespace RHTower.Sieve
open Finset GaloisForLFunctions

/-- The smooth cutoff has finite support, so its weighted series is a finite sum. -/
theorem tsum_mul_smoothWeight_eq_sum_range {a : ℕ → ℂ} {H : ℝ} (hH : 0 < H) (K m : ℕ)
    (hm : (K : ℝ) + H ≤ (m : ℝ)) :
    ∑' n : ℕ, a n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)
      = ∑ n ∈ Finset.range m, a n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ) := by
  exact HTGeometry.tsum_mul_smoothWeight_eq_sum_range_real hH m hm

/-- The window `(K, ⌊K+H⌋]` is no longer than its width. -/
theorem card_smoothing_window_le {K : ℕ} {H : ℝ} (hH : 0 < H) :
    ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) ≤ H := by
  rcases le_or_gt K ⌊(K : ℝ) + H⌋₊ with h | h
  · rw [Nat.cast_sub h]
    have hfl : ((⌊(K : ℝ) + H⌋₊ : ℕ) : ℝ) ≤ (K : ℝ) + H :=
      Nat.floor_le (by positivity)
    linarith
  · rw [Nat.sub_eq_zero_of_le h.le]
    simpa using hH.le

/-- **From a smoothed bound to a sharp one.**  Any bound on the smoothly cut series transfers to the
sharp partial sum at the cost of the window width: for `‖f‖ ≤ 1`,

`‖∑_{n ≤ K} f(n)‖ ≤ B/(2π) + H`   whenever `2π‖∑ₙ f(n)w(n)‖ ≤ B`.

This is what makes a bound for the smoothed sum a mean value theorem. -/
theorem norm_partialSum_le_of_smoothed_bound {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {K : ℕ} {H : ℝ} (hH : 0 < H) {B : ℝ}
    (hB : (2 * Real.pi) * ‖∑' n : ℕ, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ ≤ B) :
    ‖∑ n ∈ Finset.range (K + 1), f n‖ ≤ B / (2 * Real.pi) + H := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set m : ℕ := ⌊(K : ℝ) + H⌋₊ + 1 with hmdef
  have hm : (K : ℝ) + H ≤ (m : ℝ) := by
    have h := Nat.lt_floor_add_one ((K : ℝ) + H)
    rw [hmdef]
    push_cast
    linarith
  have hsum := tsum_mul_smoothWeight_eq_sum_range (a := f) hH K m hm
  have hwin : ‖(∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
      - ∑ n ∈ Finset.range (K + 1), f n‖ ≤ ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) * 1 :=
    norm_weighted_sub_partialSum_le_uniform hH K m hm fun n _ _ => hbdd n
  have hsmooth : ‖∑' n : ℕ, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖ ≤ B / (2 * Real.pi) := by
    rw [le_div_iff₀ hpi, mul_comm]
    exact hB
  have hsplit : ‖∑ n ∈ Finset.range (K + 1), f n‖
      ≤ ‖∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
        + ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) * 1 := by
    have h := norm_sub_norm_le (∑ n ∈ Finset.range (K + 1), f n)
      (∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
    have hrev : ‖(∑ n ∈ Finset.range (K + 1), f n)
        - ∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ)‖
        = ‖(∑ n ∈ Finset.range m, f n * ((HTGeometry.smoothWeight (K : ℝ) H (n : ℝ) : ℝ) : ℂ))
            - ∑ n ∈ Finset.range (K + 1), f n‖ := norm_sub_rev _ _
    rw [hrev] at h
    linarith [h, hwin]
  rw [← hsum] at hsplit
  have hwidth : ((⌊(K : ℝ) + H⌋₊ - K : ℕ) : ℝ) * 1 ≤ H := by
    rw [mul_one]
    exact card_smoothing_window_le hH
  linarith [hsplit, hsmooth, hwidth]

/-- **The Halász bound for the sharp partial sum.**  The corpus's smoothed assembly, transported to the
partial sum of a bounded multiplicative function by the window connector: the whole right-hand side is
explicit in the prime range `z`, the distance level `δ`, the height `T` and the cutoff data `K, H`, and the
only cost of removing the smoothing is the window width `H`. -/
theorem exists_norm_partialSum_le_halasz {f : ℕ → ℂ}
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz2 : 2 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    (hWz : 0 < logSqWeight z) {K : ℕ} (hK : 0 < K) {H : ℝ} (hH : 0 < H)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∑ n ∈ Finset.range (K + 1), f n‖
        ≤ ((((K : ℝ) + H) ^ σ / σ) * ((1 + 1 / (σ - 1)) *
                Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ (2 : ℕ)) * (2 * T)
              + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
                ((2 * T * Real.log (z : ℝ) / Real.pi + 1) *
                  (2 * Real.sqrt (2 * Real.pi ^ (2 : ℕ) * δ ^ (2 : ℕ) / logSqWeight z))))
            + (1 + 1 / (σ - 1)) * Real.exp (7 / 2) *
                (C * (Real.pi - 2 * Real.arctan T))) / (2 * Real.pi) + H := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  obtain ⟨C, hC0, hbound⟩ :=
    exists_norm_tsum_mul_smoothWeight_le hf1 hmul hbdd hf0 hσ hz2 hδ hWz hKR hH hT
  exact ⟨C, hC0, norm_partialSum_le_of_smoothed_bound hbdd hH hbound⟩

end RHTower.Sieve
end
