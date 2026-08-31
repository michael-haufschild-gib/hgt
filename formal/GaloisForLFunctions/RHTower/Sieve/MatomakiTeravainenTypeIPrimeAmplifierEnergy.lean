import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifier
import GaloisForLFunctions.RHTower.Sieve.PrimePowerSupport

/-!
# Coefficient energy of the Matomäki--Teräväinen prime amplifier

The Section 5.1 amplifier is the `ell`th power of the indicator of primes in `(P,2P]`.
Prime-factor uniqueness bounds each convolution fibre by `ell ^ ell`; the unraised indicator has
energy at most `P`.  Consequently the complete raised coefficient vector, and every literal Watt
block cut from it, have energy at most `ell ^ ell * P ^ ell`.  Under the source schedule
`ell ≤ P ^ rho`, this is exactly at most `(P ^ ell) ^ (1 + rho)`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The literal Type-I prime coefficient vector is prime-supported. -/
theorem mtTypeIPrimeCoeff_prime_support (P : ℕ) :
    ∀ j : Fin (2 * P), mtTypeIPrimeCoeff P j ≠ 0 →
      Nat.Prime ((j : ℕ) + 1) := by
  intro j hj
  rw [mtTypeIPrimeCoeff] at hj
  split at hj
  next h => exact h.1
  next => exact (hj rfl).elim

/-- The unraised prime-indicator energy is at most the length `P` of `(P,2P]`. -/
theorem sum_normSq_mtTypeIPrimeCoeff_le (P : ℕ) :
    ∑ j : Fin (2 * P), ‖mtTypeIPrimeCoeff P j‖ ^ 2 ≤ (P : ℝ) := by
  classical
  let S : Finset (Fin (2 * P)) :=
    Finset.univ.filter fun j => P < (j : ℕ) + 1
  have hterm : ∀ j : Fin (2 * P),
      ‖mtTypeIPrimeCoeff P j‖ ^ 2 ≤ if j ∈ S then (1 : ℝ) else 0 := by
    intro j
    rw [mtTypeIPrimeCoeff]
    by_cases h : Nat.Prime ((j : ℕ) + 1) ∧ P < (j : ℕ) + 1
    · rw [if_pos h, norm_one, one_pow, if_pos]
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h.2⟩
    · rw [if_neg h, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
  have hcard : S.card ≤ P := by
    let f : Fin (2 * P) → ℕ := fun j => (j : ℕ) - P
    have hmaps : ∀ j ∈ S, f j ∈ Finset.range P := by
      intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_range]
      dsimp only [f]
      omega
    have hinj : Set.InjOn f S := by
      intro i hi j hj hij
      change i ∈ S at hi
      change j ∈ S at hj
      rw [Finset.mem_filter] at hi hj
      apply Fin.ext
      dsimp only [f] at hij
      omega
    exact (Finset.card_le_card_of_injOn f hmaps hinj).trans_eq (Finset.card_range P)
  calc
    ∑ j : Fin (2 * P), ‖mtTypeIPrimeCoeff P j‖ ^ 2
        ≤ ∑ j : Fin (2 * P), if j ∈ S then (1 : ℝ) else 0 :=
          Finset.sum_le_sum fun j _ => hterm j
    _ = (S.card : ℝ) := by rw [Finset.sum_boole]; simp [S]
    _ ≤ (P : ℝ) := by exact_mod_cast hcard

/-- Complete raised prime coefficient sequence, extended to natural anchors. -/
def mtTypeIPrimeRaisedCoeff (P ell : ℕ) : ℕ → ℂ :=
  anchoredCoeff ((2 * P) ^ ell) (convPow (2 * P) ell (mtTypeIPrimeCoeff P))

/-- Complete coefficient energy of the powered prime amplifier. -/
theorem sum_normSq_mtTypeIPrimeRaisedCoeff_le (P ell : ℕ) :
    ∑ j : Fin ((2 * P) ^ ell),
        ‖convPow (2 * P) ell (mtTypeIPrimeCoeff P) j‖ ^ 2 ≤
      (ell : ℝ) ^ ell * (P : ℝ) ^ ell := by
  have hraw := primePowerSupportSum_normSq_convPow_le_of_prime_support
    (2 * P) ell (mtTypeIPrimeCoeff P) (mtTypeIPrimeCoeff_prime_support P)
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => sq_nonneg _)
      (sum_normSq_mtTypeIPrimeCoeff_le P) ell) (by positivity))

/-- Every exact Watt block cut from the powered prime amplifier inherits the complete energy. -/
theorem sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_le (P ell B : ℕ) :
    ∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 ≤
      (ell : ℝ) ^ ell * (P : ℝ) ^ ell := by
  have hsubset : Finset.Ioc B (2 * B) ⊆ Finset.Ico (B + 1) (2 * (B + 1)) := by
    intro m hm
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hm ⊢
    omega
  have hcut :
      (∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2) ≤
        ∑ m ∈ Finset.Ico (B + 1) (2 * (B + 1)),
          ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun m _ _ => sq_nonneg _)
  have hfull := sum_normSq_anchoredCoeff_Ico_le ((2 * P) ^ ell) (B + 1)
    (convPow (2 * P) ell (mtTypeIPrimeCoeff P))
  exact hcut.trans (by
    simpa [mtTypeIPrimeRaisedCoeff] using
      (hfull.trans (sum_normSq_mtTypeIPrimeRaisedCoeff_le P ell)))

/-- The schedule inequality `ell ≤ P^rho` absorbs the complete fibre multiplicity into the
source's arbitrarily small power of the raised length. -/
theorem mtTypeIPrimeRaisedCoeff_energy_absorb
    {P ell : ℕ} {rho : ℝ} (hP : 1 ≤ P)
    (hell : (ell : ℝ) ≤ (P : ℝ) ^ rho) :
    (ell : ℝ) ^ ell * (P : ℝ) ^ ell ≤
      (((P ^ ell : ℕ) : ℝ)) ^ (1 + rho) := by
  have hP0 : (0 : ℝ) ≤ P := by positivity
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hP)
  have hpow : (ell : ℝ) ^ ell ≤ ((P : ℝ) ^ rho) ^ ell :=
    pow_le_pow_left₀ (by positivity) hell ell
  calc
    (ell : ℝ) ^ ell * (P : ℝ) ^ ell
        ≤ ((P : ℝ) ^ rho) ^ ell * (P : ℝ) ^ ell :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (P : ℝ) ^ (rho * (ell : ℝ)) * (P : ℝ) ^ (ell : ℝ) := by
      rw [← Real.rpow_natCast ((P : ℝ) ^ rho) ell,
        ← Real.rpow_mul hP0 rho (ell : ℝ), Real.rpow_natCast]
    _ = (P : ℝ) ^ ((ell : ℝ) * (1 + rho)) := by
      rw [← Real.rpow_add hPpos]
      congr 1
      ring
    _ = (((P ^ ell : ℕ) : ℝ)) ^ (1 + rho) := by
      push_cast
      rw [← Real.rpow_natCast (P : ℝ) ell,
        ← Real.rpow_mul hP0 (ell : ℝ) (1 + rho)]

/-- Source-scale form of the energy bound for every literal powered-prime Watt block. -/
theorem sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_le_rpow
    {P ell B : ℕ} {rho : ℝ} (hP : 1 ≤ P)
    (hell : (ell : ℝ) ≤ (P : ℝ) ^ rho) :
    ∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 ≤
      (((P ^ ell : ℕ) : ℝ)) ^ (1 + rho) :=
  (sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_le P ell B).trans
    (mtTypeIPrimeRaisedCoeff_energy_absorb hP hell)

end

end RHTower.Sieve
