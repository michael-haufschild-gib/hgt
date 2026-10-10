import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimeEnergy
import GaloisForLFunctions.HTGeometry.PaperPrimeTransportConormal

/-!
# Exact energy-improvement criterion on the divisor-preserving time domain

The real admissible times for the positive half-plane are
(-∞,0] ∪ {1} ∪ [2,∞). The literal transported source has a strictly lower
finite Gamma--Hankel energy at an admissible time exactly when its signed
mixed term B satisfies B<0 or E(p-free)<2B. This pays the optimization and
analytic-domain interaction without assuming either arithmetic inequality.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

noncomputable section

/-- Exact real parameter chambers for preservation on Re(s)>0. -/
theorem paperPrimeTransportRealTime_iff (p : Nat.Primes) (t : ℝ) :
    (t : ℂ) ∈ paperPrimeTransportParameters p 0 ↔ t ≤ 0 ∨ t = 1 ∨ 2 ≤ t := by
  have hn : ‖(1 : ℂ) - (t : ℂ)‖ = |1 - t| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  change ((t : ℂ) = 1 ∨ (p : ℝ) ^ (-(0 : ℝ)) ≤ ‖1 - (t : ℂ)‖) ↔ _
  rw [neg_zero, Real.rpow_zero, hn]
  constructor
  · rintro (ht | ht)
    · right; left
      exact_mod_cast ht
    · rcases le_total t 1 with h | h
      · left
        rw [abs_of_nonneg (by linarith)] at ht
        linarith
      · right; right
        rw [abs_of_nonpos (by linarith)] at ht
        linarith
  · rintro (ht | ht | ht)
    · right
      rw [abs_of_nonneg (by linarith)]
      linarith
    · left
      exact_mod_cast ht
    · right
      rw [abs_of_nonpos (by linarith)]
      linarith

/-- A concrete second nontrivial time with a fully paid analytic-unit domain. -/
def paperPrimeNegativeOneParameters (p : Nat.Primes) : paperPrimeTransportParameters p 0 :=
  ⟨(-1 : ℝ), (paperPrimeTransportRealTime_iff p (-1)).mpr (Or.inl (by linarith))⟩

/-- Exact arithmetic criterion for an improving time that also preserves divisor and conormal. -/
theorem paperMoebiusPrimeEnergy_admissible_improvement_iff (p : Nat.Primes) (N : ℕ)
    (r : {r : ℝ // 0 < r}) :
    (∃ t : ℝ, (t : ℂ) ∈ paperPrimeTransportParameters p 0 ∧
      paperMoebiusPrimeEnergy p t N r < finiteMobiusGammaHankelEnergy N r) ↔
      paperMoebiusPrimeEnergyCross p N r < 0 ∨
        finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r <
          2 * paperMoebiusPrimeEnergyCross p N r := by
  let A := finiteMobiusGammaHankelEnergy N r
  let B := paperMoebiusPrimeEnergyCross p N r
  let Q := finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r
  have hQ : 0 ≤ Q := finiteGammaHankelEnergy_nonneg _ N r.property
  have hCS : B ^ 2 ≤ A * Q := paperGammaHankelPairing_sq_le _ _ N r
  have hE (t : ℝ) : paperMoebiusPrimeEnergy p t N r = A - 2 * t * B + t ^ 2 * Q :=
    paperMoebiusPrimeEnergy_eq p t N r
  change (∃ t : ℝ, (t : ℂ) ∈ paperPrimeTransportParameters p 0 ∧
    paperMoebiusPrimeEnergy p t N r < A) ↔ B < 0 ∨ Q < 2 * B
  constructor
  · rintro ⟨t, ht, he⟩
    rw [hE] at he
    rcases (paperPrimeTransportRealTime_iff p t).mp ht with ht | ht | ht
    · left
      by_contra hB
      have hB' := le_of_not_gt hB
      have hm : 2 * t * B ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hB'
      have hq := mul_nonneg (sq_nonneg t) hQ
      linarith
    · subst t
      right
      norm_num only [one_pow, mul_one, one_mul] at he
      linarith
    · right
      have htpos : 0 < t := by linarith
      have hs : t * (t * Q) < t * (2 * B) := by nlinarith only [he]
      have hm : t * Q < 2 * B := (mul_lt_mul_iff_right₀ htpos).mp hs
      have hq : Q ≤ t * Q := by
        have hprod := mul_nonneg (show 0 ≤ t - 1 by linarith) hQ
        nlinarith only [hprod]
      exact lt_of_le_of_lt hq hm
  · rintro (hB | hQB)
    · have hQpos : 0 < Q := by
        by_contra h
        have hQzero := le_antisymm (le_of_not_gt h) hQ
        rw [hQzero, mul_zero] at hCS
        nlinarith
      refine ⟨paperMoebiusPrimeEnergyOptimalTime p N r, ?_, ?_⟩
      · apply (paperPrimeTransportRealTime_iff p _).mpr
        left
        exact (div_neg_of_neg_of_pos hB hQpos).le
      · have hv := paperMoebiusPrimeEnergy_minimum_value p N r
        change paperMoebiusPrimeEnergy p (paperMoebiusPrimeEnergyOptimalTime p N r) N r =
          A - B ^ 2 / Q at hv
        rw [hv]
        have hpos := div_pos (sq_pos_of_ne_zero (ne_of_lt hB)) hQpos
        linarith
    · refine ⟨1, (paperPrimeTransportRealTime_iff p 1).mpr (Or.inr (Or.inl rfl)), ?_⟩
      rw [hE]
      norm_num only [one_pow, mul_one, one_mul]
      linarith

/-- The exact interval of signed mixed terms that blocks every admissible strict improvement. -/
theorem paperMoebiusPrimeEnergy_admissible_floor_iff (p : Nat.Primes) (N : ℕ)
    (r : {r : ℝ // 0 < r}) :
    (∀ t : ℝ, (t : ℂ) ∈ paperPrimeTransportParameters p 0 →
      finiteMobiusGammaHankelEnergy N r ≤ paperMoebiusPrimeEnergy p t N r) ↔
      0 ≤ paperMoebiusPrimeEnergyCross p N r ∧
        2 * paperMoebiusPrimeEnergyCross p N r ≤
          finiteGammaHankelEnergy (paperPrimeFreeRealCoefficient p) N r := by
  have h := not_congr (paperMoebiusPrimeEnergy_admissible_improvement_iff p N r)
  push Not at h
  exact h

/-- Two concrete conormal-preserving times cannot both strictly lower the original energy. -/
theorem paperPrimeOppositeConormalEnergy (p : Nat.Primes) (N : ℕ)
    (r : {r : ℝ // 0 < r}) :
    paperPrimeTransportXiIdeal p 0 ⟨1, Or.inl rfl⟩ = paperPrimeOriginalXiIdeal 0 ∧
      paperPrimeTransportXiIdeal p 0 (paperPrimeNegativeOneParameters p) =
        paperPrimeOriginalXiIdeal 0 ∧
      (finiteMobiusGammaHankelEnergy N r ≤ paperMoebiusPrimeEnergy p 1 N r ∨
        finiteMobiusGammaHankelEnergy N r ≤ paperMoebiusPrimeEnergy p (-1) N r) :=
  ⟨paperPrimeTransportXiIdeal_eq p 0 _, paperPrimeTransportXiIdeal_eq p 0 _,
    paperMoebiusPrimeEnergy_one_or_neg_one p N r⟩

end

end GaloisForLFunctions.HTGeometry
