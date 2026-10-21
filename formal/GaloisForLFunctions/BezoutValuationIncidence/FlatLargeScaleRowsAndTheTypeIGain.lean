import GaloisForLFunctions.BezoutValuationIncidence.TwoSidedSignLawOfTheSecondOrderKernel

/-!
# Flat large-scale rows and the Type-I gain

Take the large-scale row flat on an interval, `c'(n) = n` on `[A+1, A+L]` (`b_n = 1` in
`Σ a_p b_n 𝒢(p, n)`). Its weighted transform is `S(ζ) = Σ_{A < n ≤ A+L} ζⁿ/n`. Abel summation against the
geometric partial sums `|Σ ζʲ| ≤ 2/|ζ - 1|` gives `|S(ζ)| ≤ 2/((A+1)|ζ - 1|)`. On the nontrivial `p`-th
roots `|ζ - 1| ≥ 4/p`, so `σ_p ≤ p/(2(A+1))`. The Fourier form of the exact loss then gives, for every
row `c` on primes,

`|B(c, c') + m R' + β H'| ≤ (π²/144) Σ_p |c(p)| p²/(A+1) + (Σ_I 1/n)/6 · Σ_p |c(p)|/p
  + ¾ Σ_p |c(p)| p² Σ_I 1/n²`.

Against the rank-two remainder bound `≍ (Σ |c(p)| p) L/A` the gain is `≍ P/L + P/A`. For arbitrary
small-scale coefficients on primes `p ∼ P` and the flat large scale on `[Q, 2Q]` this is `≍ P/Q`, so
the cross-scale form has diagonal quality for `Q ≥ P^{3/2}` (exponent `θ` up to `4/3`). Together with
the Kuzmin–Landau gain for flat small scales: a Type-I row at either scale passes the Type-II barrier
`P^{5/3}`.
-/

open Finset Filter Topology Complex RHTower RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- The flat large-scale row `c'(n) = n` on `[A+1, A+L]`. -/
def flatLargeRow (A L : ℕ) (n : ℕ) : ℝ := if n ∈ Icc (A + 1) (A + L) then (n : ℝ) else 0

theorem norm_geom_partial_le {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) (k : ℕ) :
    ‖∑ j ∈ range k, ζ ^ j‖ ≤ 2 / ‖ζ - 1‖ := by
  rw [geom_sum_eq h1, norm_div]
  have hpos : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  refine div_le_div_of_nonneg_right ?_ hpos.le
  calc ‖ζ ^ k - 1‖ ≤ ‖ζ ^ k‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hζ, one_pow, norm_one]; norm_num

/-- `|Σ_{A < n ≤ A+L} ζⁿ/n| ≤ 2/((A+1)|ζ - 1|)`. -/
theorem norm_rowTransform_flatLargeRow_le {N A L : ℕ} (hAL : A + L ≤ N) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (h1 : ζ ≠ 1) :
    ‖rowTransform N (flatLargeRow A L) ζ‖ ≤ 2 / (((A : ℝ) + 1) * ‖ζ - 1‖) := by
  have hsub : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  have hre : rowTransform N (flatLargeRow A L) ζ =
      ∑ m ∈ range L, (((1 / ((A : ℝ) + 1 + m)) : ℝ) : ℂ) * (ζ ^ (A + 1) * ζ ^ m) := by
    rw [rowTransform, ← sum_subset hsub fun n _ hn => by simp [flatLargeRow, hn]]
    rw [show Icc (A + 1) (A + L) = Ico (A + 1) (A + 1 + L) by ext; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, show A + 1 + L - (A + 1) = L by omega]
    refine sum_congr rfl fun m hm => ?_
    have hmem : A + 1 + m ∈ Icc (A + 1) (A + L) := by
      have := mem_range.mp hm; exact mem_Icc.mpr ⟨by omega, by omega⟩
    rw [flatLargeRow, if_pos hmem, pow_add]
    have h0 : (0 : ℝ) < ((A + 1 + m : ℕ) : ℝ) := by positivity
    push_cast
    field_simp
  rw [hre]
  have hanti : Antitone fun m : ℕ => 1 / ((A : ℝ) + 1 + m) := fun a b hab => by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hpart : ∀ k, ‖∑ j ∈ range k, ζ ^ (A + 1) * ζ ^ j‖ ≤ 2 / ‖ζ - 1‖ := fun k => by
    rw [← mul_sum, norm_mul, norm_pow, hζ, one_pow, one_mul]
    exact norm_geom_partial_le hζ h1 k
  have h := norm_sum_amplitude_phase_le hanti (fun m => by positivity) hpart L
  calc ‖∑ m ∈ range L, (((1 / ((A : ℝ) + 1 + m)) : ℝ) : ℂ) * (ζ ^ (A + 1) * ζ ^ m)‖
      ≤ 1 / ((A : ℝ) + 1 + ((0 : ℕ) : ℝ)) * (2 / ‖ζ - 1‖) := h
    _ = 2 / (((A : ℝ) + 1) * ‖ζ - 1‖) := by rw [Nat.cast_zero, add_zero]; field_simp

/-- **The Type-I gain at the large scale.** For a row `c` on primes `S ≤ N` and the flat large-scale row
on `[A+1, A+L] ⊆ [1, N]`:
`|B + m R' + β H'| ≤ (π²/144) Σ_p |c(p)| p²/(A+1) + (Σ_I 1/n)/6 · Σ_p |c(p)|/p + ¾ Σ_d |c(d)| d² Σ_I 1/n²`. -/
theorem abs_rowBilinear_flatLargeRow_le {N A L : ℕ} {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N) {c : ℕ → ℝ} (hsupp : ∀ n, c n ≠ 0 → n ∈ S)
    (hAL : A + L ≤ N) :
    |rowBilinear N c (flatLargeRow A L) + rowMean N c * vonMangoldtReadout N (flatLargeRow A L) +
        rowBeta N c * finiteHarmonicSum N (flatLargeRow A L)| ≤
      Real.pi ^ 2 / 144 * (∑ p ∈ S, |c p| * (p : ℝ) ^ 2) / ((A : ℝ) + 1) +
        (∑ n ∈ Icc (A + 1) (A + L), 1 / (n : ℝ)) / 6 * ∑ p ∈ S, |c p| / p +
        3 / 4 * (∑ d ∈ Icc 1 N, |c d| * (d : ℝ) ^ 2) * ∑ n ∈ Icc (A + 1) (A + L), 1 / (n : ℝ) ^ 2 := by
  have hsub : Icc (A + 1) (A + L) ⊆ Icc 1 N := Icc_subset_Icc (by omega) hAL
  set σ : ℕ → ℝ := fun p => (p : ℝ) / (2 * ((A : ℝ) + 1))
  have hσ : ∀ p ∈ S, ∀ ζ ∈ nontrivialRoots p, ‖rowTransform N (flatLargeRow A L) ζ‖ ≤ σ p := by
    intro p hp ζ hζ
    have hp2 := (hS p hp).1.two_le
    have hprim : ζ ∈ primitiveRoots p ℂ := by
      rw [primitiveRoots_prime_eq_image (hS p hp).1, ← nontrivialRoots_eq_image (hS p hp).1.pos]
      exact hζ
    have h4 := four_div_le_norm_sub_one hp2 hprim
    have hn := norm_eq_one_of_mem_nontrivialRoots (hS p hp).1.pos hζ
    have h1 := ((mem_nontrivialRoots (hS p hp).1.pos).mp hζ).1
    refine (norm_rowTransform_flatLargeRow_le hAL hn h1).trans ?_
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hS p hp).1.pos
    simp only [σ]
    have hz : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (4 : ℝ) ≤ p * ‖ζ - 1‖ := by rwa [div_le_iff₀ hpR, mul_comm] at h4
    nlinarith [(by positivity : (0 : ℝ) ≤ (A : ℝ) + 1)]
  have h := abs_rowBilinear_add_mean_add_beta_le_fourier hS hsupp σ hσ
  have hS₀ : ∑ n ∈ Icc 1 N, |flatLargeRow A L n| / (n : ℝ) ^ 2 =
      ∑ n ∈ Icc (A + 1) (A + L), 1 / (n : ℝ) := by
    rw [← sum_subset hsub fun n _ hn => by simp [flatLargeRow, hn]]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := mem_Icc.mp hn; omega : 0 < n)
    rw [flatLargeRow, if_pos hn, abs_of_pos hn0]; field_simp
  have hS₃ : ∑ n ∈ Icc 1 N, |flatLargeRow A L n| / (n : ℝ) ^ 3 =
      ∑ n ∈ Icc (A + 1) (A + L), 1 / (n : ℝ) ^ 2 := by
    rw [← sum_subset hsub fun n _ hn => by simp [flatLargeRow, hn]]
    refine sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := mem_Icc.mp hn; omega : 0 < n)
    rw [flatLargeRow, if_pos hn, abs_of_pos hn0]; field_simp
  rw [hS₀, hS₃] at h
  have hσsum : ∑ p ∈ S, |c p| * (p : ℝ) * σ p =
      (∑ p ∈ S, |c p| * (p : ℝ) ^ 2) / (2 * ((A : ℝ) + 1)) := by
    rw [sum_div]
    refine sum_congr rfl fun p _ => ?_
    simp only [σ]
    field_simp
  rw [hσsum] at h
  refine h.trans (le_of_eq ?_)
  have hA : (0 : ℝ) < (A : ℝ) + 1 := by positivity
  field_simp
  ring

end

end GaloisForLFunctions.BezoutValuationIncidence
