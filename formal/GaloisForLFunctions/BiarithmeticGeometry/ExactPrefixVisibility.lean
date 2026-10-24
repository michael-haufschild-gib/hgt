import GaloisForLFunctions.BezoutValuationIncidence.CompletePeriodQuadraticFormsSignInvarianceAndTransHorizonSeparation

/-!
# Exact signed visibility inside a complete-period observation fibre

Complete-period quadratic data fix Selberg magnitudes. For any chosen finite prefix, the sum of
the absolute signed mode contributions is its exact remaining range radius. Independent signs
attain both endpoints while preserving all complete-period lag covariances and the mean.
-/

noncomputable section

open Finset RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Independent real signs, with the constant Selberg coordinate fixed. -/
def prefixSign (σ : ℕ → Bool) (q : ℕ) : ℝ :=
  if q = 1 then 1 else if σ q then 1 else -1

theorem prefixSign_one (σ : ℕ → Bool) : prefixSign σ 1 = 1 := by
  simp [prefixSign]

theorem prefixSign_sq (σ : ℕ → Bool) (q : ℕ) : prefixSign σ q ^ 2 = 1 := by
  unfold prefixSign
  split_ifs <;> norm_num

theorem abs_prefixSign (σ : ℕ → Bool) (q : ℕ) : |prefixSign σ q| = 1 := by
  unfold prefixSign
  split_ifs <;> norm_num

/-- The precise mode-resolved visibility of a finite prefix. -/
def prefixVisibility (N M : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Icc 2 N, |(pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q|

/-- The prefix reads each Selberg sign linearly. -/
theorem prefix_readout_sign (N M : ℕ) (c : ℕ → ℝ) (σ : ℕ → Bool) :
    sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign σ)) =
      ∑ q ∈ Icc 2 N, prefixSign σ q *
        ((pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q) := by
  rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal]
  apply sum_congr rfl
  intro q hq
  have hq1 : q ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega,
    (mem_Icc.mp hq).2⟩
  rw [selbergMultiplesCoord_scaledSelbergRow c (prefixSign σ) hq1]
  ring

/-- No independent sign choice exceeds the sum of its absolute mode contributions. -/
theorem abs_prefix_readout_sign_le (N M : ℕ) (c : ℕ → ℝ) (σ : ℕ → Bool) :
    |sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign σ))| ≤
      prefixVisibility N M c := by
  rw [prefix_readout_sign]
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  simp only [abs_mul, abs_prefixSign, one_mul, prefixVisibility]

/-- Independent signs attain both endpoints of the exact prefix range. -/
theorem prefix_visibility_extrema (N M : ℕ) (c : ℕ → ℝ) :
    ∃ σ τ : ℕ → Bool,
      sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign σ)) =
        prefixVisibility N M c ∧
      sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign τ)) =
        -prefixVisibility N M c := by
  classical
  let σ : ℕ → Bool := fun q => decide
    (0 ≤ (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q)
  refine ⟨σ, fun q => !(σ q), ?_, ?_⟩
  · rw [prefix_readout_sign]
    apply sum_congr rfl
    intro q hq
    have hq1 : q ≠ 1 := by have := (mem_Icc.mp hq).1; omega
    by_cases h : 0 ≤ (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q
    · simp [prefixSign, σ, hq1, h, abs_of_nonneg h]
    · simp [prefixSign, σ, hq1, h, abs_of_neg (lt_of_not_ge h)]
  · rw [prefix_readout_sign, prefixVisibility, ← sum_neg_distrib]
    apply sum_congr rfl
    intro q hq
    have hq1 : q ≠ 1 := by have := (mem_Icc.mp hq).1; omega
    by_cases h : 0 ≤ (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q
    · simp [prefixSign, σ, hq1, h, abs_of_nonneg h]
    · simp [prefixSign, σ, hq1, h, abs_of_neg (lt_of_not_ge h)]

/-- Every sign choice has the original complete-period covariance data. -/
theorem prefix_sign_periodCovariance (N : ℕ) (c : ℕ → ℝ) (σ : ℕ → Bool) :
    ∀ g ∈ Icc 1 N,
      TwoLagSieve.periodCovariance N (scaledSelbergRow N c (prefixSign σ)) g =
        TwoLagSieve.periodCovariance N c g := by
  apply (sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq N _ _).mp
  intro q hq
  have hq1 : q ∈ Icc 1 N := mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega,
    (mem_Icc.mp hq).2⟩
  exact sq_selbergMultiplesCoord_scaledSelbergRow c hq1 (prefixSign_sq σ q)

theorem prefix_sign_mean {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (σ : ℕ → Bool) :
    finiteHarmonicSum N (scaledSelbergRow N c (prefixSign σ)) =
      finiteHarmonicSum N c :=
  finiteHarmonicSum_scaledSelbergRow hN c (prefixSign_one σ)

/-- The exact prefix diameter of the sign fibre is twice its mode-resolved visibility. -/
theorem prefix_visibility_diameter (N M : ℕ) (c : ℕ → ℝ) :
    (∃ σ τ : ℕ → Bool,
      sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign σ)) -
        sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign τ)) =
          2 * prefixVisibility N M c) ∧
    ∀ σ τ : ℕ → Bool,
      |sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign σ)) -
        sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign τ))| ≤
          2 * prefixVisibility N M c := by
  constructor
  · obtain ⟨σ, τ, hσ, hτ⟩ := prefix_visibility_extrema N M c
    exact ⟨σ, τ, by rw [hσ, hτ]; ring⟩
  · intro σ τ
    have hσ := abs_prefix_readout_sign_le N M c σ
    have hτ := abs_prefix_readout_sign_le N M c τ
    have htri := abs_sub_le
      (sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign σ))) 0
      (sievePrefixDiscrepancy N M (scaledSelbergRow N c (prefixSign τ)))
    simp only [sub_zero, zero_sub, abs_neg] at htri
    linarith only [htri, hσ, hτ]

theorem prefixVisibility_nonneg (N M : ℕ) (c : ℕ → ℝ) :
    0 ≤ prefixVisibility N M c :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- Every row in the full covariance fibre obeys the same sharp visibility bound. -/
theorem abs_prefix_readout_le_of_covariance_eq (N M : ℕ) (c d : ℕ → ℝ)
    (hcov : ∀ g ∈ Icc 1 N,
      TwoLagSieve.periodCovariance N d g = TwoLagSieve.periodCovariance N c g) :
    |sievePrefixDiscrepancy N M d| ≤ prefixVisibility N M c := by
  have hsq := (sq_selbergMultiplesCoord_eq_iff_periodCovariance_eq N d c).mpr hcov
  rw [sievePrefixDiscrepancy_eq_ramanujan_diagonal]
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  apply sum_congr rfl
  intro q hq
  rw [abs_mul, abs_mul, (sq_eq_sq_iff_abs_eq_abs _ _).mp (hsq q hq)]

/-- A prefix is determined by complete-period covariance exactly when every visible mode vanishes.
In that case its centered value is zero throughout the entire covariance fibre. -/
theorem prefix_covariance_determines_iff (N M : ℕ) (c : ℕ → ℝ) :
    (∀ d : ℕ → ℝ,
      (∀ g ∈ Icc 1 N,
        TwoLagSieve.periodCovariance N d g = TwoLagSieve.periodCovariance N c g) →
      sievePrefixDiscrepancy N M d = sievePrefixDiscrepancy N M c) ↔
      prefixVisibility N M c = 0 := by
  constructor
  · intro h
    obtain ⟨σ, τ, hσ, hτ⟩ := prefix_visibility_extrema N M c
    have heqσ := h _ (prefix_sign_periodCovariance N c σ)
    have heqτ := h _ (prefix_sign_periodCovariance N c τ)
    linarith only [hσ, hτ, heqσ, heqτ]
  · intro h d hcov
    have hd := abs_prefix_readout_le_of_covariance_eq N M c d hcov
    have hc := abs_prefix_readout_le_of_covariance_eq N M c c (fun _ _ => rfl)
    rw [h] at hd hc
    rw [abs_nonpos_iff.mp hd, abs_nonpos_iff.mp hc]

/-- Vanishing visibility is a mode-by-mode condition, with the exact finite-prefix primitive. -/
theorem prefixVisibility_eq_zero_iff (N M : ℕ) (c : ℕ → ℝ) :
    prefixVisibility N M c = 0 ↔
      ∀ q ∈ Icc 2 N,
        (pmRamanujanPrimitive q M).re * selbergMultiplesCoord N c q = 0 := by
  rw [prefixVisibility, sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)]
  simp only [abs_eq_zero]

end GaloisForLFunctions.BiarithmeticGeometry
