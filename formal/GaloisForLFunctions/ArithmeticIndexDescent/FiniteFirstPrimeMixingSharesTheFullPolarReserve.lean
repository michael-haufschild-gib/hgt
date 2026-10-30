import GaloisForLFunctions.ArithmeticIndexDescent.TheFullNonfirstSourceRetainsAlmostAllGamma
import GaloisForLFunctions.ArithmeticIndexDescent.EveryIntegerPrimeLagHasGammaSmallMixedTails

/-!+# Joint payment of finitely many first-prime mixed sources

A fixed finite first-prime sum is small on high details in the original
complete-profile Gamma norm. It shares the proved nonfirst payment while
retaining both original polar moments and every coarse coefficient.
-/

noncomputable section
open MeasureTheory Finset
open RHTower
namespace GaloisForLFunctions.ArithmeticIndexDescent
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry HTGeometry

/-- Only first powers occur in this finite mixed source. -/
def finiteFirstPrimeMixedSource (P : Finset Nat.Primes) (d q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ p ∈ P, integerMixedSource (p : ℕ) d q X X

private def finiteFirstPrimeMixedCost (P : Finset Nat.Primes) : ℝ :=
  ∑ p ∈ P, 2 * (2 * ArithmeticFunction.vonMangoldt (p : ℕ) / Real.sqrt (p : ℝ))

theorem finiteFirstPrimeMixed_tail_bound (P : Finset Nat.Primes) (d q : ℕ → ℝ)
    {A : ℕ} (hA : 1 ≤ A) (X : ℕ) :
    |finiteFirstPrimeMixedSource P (fun a => if A ≤ a then d a else 0) q X| ≤
      finiteFirstPrimeMixedCost P *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ p ∈ P, (2 * (2 * ArithmeticFunction.vonMangoldt (p : ℕ) /
        Real.sqrt (p : ℝ))) *
        (levyEnergy (completePairProfile q d X) / cellGammaWeight A) :=
      sum_le_sum fun p _ => abs_integerMixed_tail_le_gamma_div_weight d q hA p.property.two_le X
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- A finite first-prime family has one common detail head at every cell horizon. -/
theorem exists_finiteFirstPrimeMixed_gamma_small_tail (P : Finset Nat.Primes)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (d q : ℕ → ℝ) (X : ℕ),
      |finiteFirstPrimeMixedSource P (fun a => if A ≤ a then d a else 0) q X| ≤
        δ * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp (finiteFirstPrimeMixedCost P / δ))
  have hA1 : 1 ≤ A := by
    have hp : (0 : ℝ) < A := (Real.exp_pos _).trans hA
    exact Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hp.ne')
  have hl := Real.log_lt_log (Real.exp_pos _) hA
  rw [Real.log_exp] at hl
  have hcoef : finiteFirstPrimeMixedCost P / cellGammaWeight A ≤ δ := by
    apply (div_le_iff₀ (cellGammaWeight_pos hA1)).mpr
    have h := (div_le_iff₀ hδ).mp (hl.le.trans (log_le_cellGammaWeight hA1))
    simpa only [mul_comm] using h
  refine ⟨A, hA1, fun d q X => ?_⟩
  have hE := levyEnergy_nonneg_bv (completePairProfile_bv q d X)
    (completePairProfile_compact q d X)
  calc
    _ ≤ _ := finiteFirstPrimeMixed_tail_bound P d q hA1 X
    _ = (finiteFirstPrimeMixedCost P / cellGammaWeight A) *
        levyEnergy (completePairProfile q d X) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hE

/-- The exact full-polar nonfirst source augmented by the finite first-prime mixed sum. -/
def finiteFirstPrimeFullPolarSource (P : Finset Nat.Primes) (q d : ℕ → ℝ) (X : ℕ) : ℝ :=
  fullPolarNonfirstSourceForm q d X - finiteFirstPrimeMixedSource P d q X

/-- The joint source keeps almost all original Gamma energy and its exact full pole. -/
theorem exists_finiteFirstPrime_fullPolar_gamma_approximation
    (P : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a, a < A → d a = 0) →
      |finiteFirstPrimeFullPolarSource P q d X -
        (levyEnergy (completePairProfile q d X) +
          (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
            2 * sinhHalfMoment (completePairProfile q d X) ^ 2))| ≤
        ε * levyEnergy (completePairProfile q d X) := by
  obtain ⟨A₀, hA₀, h₀⟩ := exists_fullPolarNonfirst_gamma_approximation (ε / 2)
    (by positivity)
  obtain ⟨A₁, _, h₁⟩ := exists_finiteFirstPrimeMixed_gamma_small_tail P
    (by positivity : 0 < ε / 2)
  refine ⟨max A₀ A₁, hA₀.trans (le_max_left _ _), fun q d X hd => ?_⟩
  have he₀ := h₀ q d X (fun a ha => hd a (ha.trans_le (le_max_left _ _)))
  have he₁ := h₁ d q X
  have htail : (fun a => if A₁ ≤ a then d a else 0) = d := by
    funext a
    split_ifs with ha
    · rfl
    · exact (hd a ((lt_of_not_ge ha).trans_le (le_max_right _ _))).symm
  rw [htail] at he₁
  have he : finiteFirstPrimeFullPolarSource P q d X -
      (levyEnergy (completePairProfile q d X) +
        (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2)) =
      (fullPolarNonfirstSourceForm q d X -
        (levyEnergy (completePairProfile q d X) +
          (2 * coshHalfMoment (completePairProfile q d X) ^ 2 -
            2 * sinhHalfMoment (completePairProfile q d X) ^ 2))) -
        finiteFirstPrimeMixedSource P d q X := by
    unfold finiteFirstPrimeFullPolarSource
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add he₀ he₁).trans_eq (by ring))

/-- A single finite detail head pays first-prime mixing and the entire nonfirst source jointly. -/
theorem exists_finiteFirstPrime_fullPolar_completeGamma_reserve
    (P : Finset Nat.Primes) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ (q d : ℕ → ℝ) (X : ℕ),
      (∀ a, a < A → d a = 0) →
      (1 - ε) * levyEnergy (completePairProfile q d X) +
          2 * coshHalfMoment (completePairProfile q d X) ^ 2 ≤
        finiteFirstPrimeFullPolarSource P q d X +
          2 * sinhHalfMoment (completePairProfile q d X) ^ 2 := by
  obtain ⟨A, hA, h⟩ := exists_finiteFirstPrime_fullPolar_gamma_approximation P hε
  refine ⟨A, hA, fun q d X hd => ?_⟩
  have he := (abs_le.mp (h q d X hd)).1
  linarith only [he]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_finiteFirstPrimeMixed_gamma_small_tail
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_finiteFirstPrime_fullPolar_completeGamma_reserve
