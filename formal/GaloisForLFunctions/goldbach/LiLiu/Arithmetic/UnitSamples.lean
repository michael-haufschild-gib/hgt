import GaloisForLFunctions.goldbach.LiLiu.FiniteProjection
import GaloisForLFunctions.goldbach.LiLiu.MellinWeight
import GaloisForLFunctions.goldbach.LiLiu.ArithmeticKernel
import GaloisForLFunctions.RHTower.SelbergKloostermanCongruence

/-! # The arithmetic diagonal after Mellin inversion -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex ArithmeticFunction Finset MetaplecticMobiusDescent.CubicEisenstein
open scoped Classical ComplexConjugate
noncomputable section

theorem tsum_coprime_eq_sum_units (N : ℕ) [NeZero N] (f : ℕ → ℂ)
    (hf : ∀ k, N ≤ k → f k = 0) :
    (∑' k : ℕ, if k.Coprime N then f k else 0) = ∑ u : (ZMod N)ˣ, f (u : ZMod N).val := by
  rw [tsum_eq_sum (s := range N), ← RHTower.SelbergKloostermanCongruence.sum_range_units N
    (fun r => f r.val)]
  · apply sum_congr rfl
    intro k hk
    simp only [ZMod.val_natCast_of_lt (mem_range.mp hk), ZMod.isUnit_iff_coprime]
  · intro k hk
    simp [hf k (le_of_not_gt (fun h => hk (mem_range.mpr h)))]

theorem weight_sample_zero {N k : ℕ} (hN : 0 < N) (hk : N ≤ k) (φ : TestWeight) :
    φ ((k:ℝ)/N) = 0 := by
  by_contra! hn
  have hb := (φ.supported hn).2
  have h1 : 1 ≤ (k:ℝ)/N := (one_le_div (Nat.cast_pos.mpr hN)).mpr (by exact_mod_cast hk)
  linarith only [hb,h1]

/-- The two factors of the companion contribute k/N, cancelling the diagonal denominator k. -/
theorem diagonal_samples (N : ℕ) [NeZero N] (φ : TestWeight) :
    (∑' k : ℕ, (diagonalCoefficient N k / k) *
      (companion φ ((k:ℝ)/N) * conj (companion φ ((k:ℝ)/N)))) = (diagonal φ N : ℂ) := by
  let f (k : ℕ) : ℂ := (coefficient φ N k : ℂ)^2 / N
  have hN : 0 < N := NeZero.pos N
  have he (k : ℕ) : diagonalCoefficient N k / k *
      (companion φ ((k:ℝ)/N) * conj (companion φ ((k:ℝ)/N))) =
      if k.Coprime N then f k else 0 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [f,coefficient]
    by_cases hu : k.Coprime N
    · have hs : (Real.sqrt ((k:ℝ)/N) : ℂ)^2 = (k:ℂ)/N := by
        rw [← Complex.ofReal_pow,Real.sq_sqrt (div_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg N)),
          Complex.ofReal_div]
        simp only [Complex.ofReal_natCast]
      simp only [diagonalCoefficient,if_pos hu,companion,Vstar,map_mul,conj_ofReal,
        f,coefficient,Complex.ofReal_mul]
      have h0 : (k:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
      have hN0 : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
      calc
        _ = (Λ k:ℂ)^2 / k * ((Real.sqrt ((k:ℝ)/N):ℂ)^2 * (φ ((k:ℝ)/N):ℂ)^2) := by ring
        _ = _ := by rw [hs]; field_simp [h0,hN0]
    · simp [diagonalCoefficient,hu]
  simp_rw [he]
  rw [tsum_coprime_eq_sum_units N f (fun k hk => by simp [f, coefficient, weight_sample_zero hN hk φ])]
  simp only [diagonal,f,Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_pow,Complex.ofReal_natCast,
    Finset.sum_div]

#print axioms diagonal_samples
end
end GaloisForLFunctions.Goldbach.LiLiu
