import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionOver
import GaloisForLFunctions.RHTower.Sieve.ExponentialJet
import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionHigherLogCoefficient
import GaloisForLFunctions.RHTower.Sieve.SelbergCorrectionHigherLogNumerator

/-!
# Exact all-order logarithmic-jet identity for the Selberg factorization

The deformation variable is formal.  Thus this module proves an identity in `PowerSeries ℝ`, not
an analytic identity near a parameter value.  Extracting its `k`-th coefficient gives the exact
`k`-th logarithmic Leibniz formula with no convergence premise.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

def selbergLocalJetParameter (p : ℕ) : PowerSeries ℝ :=
  PowerSeries.C (1 / (p : ℝ)) * exponentialJet (Real.log (p : ℝ))

/-- Deformed reciprocal diagonal factor `(1-qE·XY)⁻¹`. -/
def selbergLocalDiagonalJet (p i j : ℕ) : PowerSeries ℝ :=
  if i = j then selbergLocalJetParameter p ^ i else 0

/-- Constant formal lift of `(1-X/p)(1-Y/p)`. -/
def selbergLocalMoebiusJet (p i j : ℕ) : PowerSeries ℝ :=
  PowerSeries.C (localMoebiusPairFactor p i j)

/-- Deformed denominator `1-qE·XY`. -/
def selbergLocalEulerDenominatorJet (p i j : ℕ) : PowerSeries ℝ :=
  additiveBivariateMonomialOver 0 0 1 i j -
    additiveBivariateMonomialOver 1 1 (selbergLocalJetParameter p) i j

/-- Literal local original factor `1-qX-qY+qE·XY`. -/
def selbergLocalOriginalJet (p i j : ℕ) : PowerSeries ℝ :=
  additiveBivariateMonomialOver 0 0 1 i j +
    additiveBivariateMonomialOver 1 0 (-(PowerSeries.C (1 / (p : ℝ)))) i j +
    additiveBivariateMonomialOver 0 1 (-(PowerSeries.C (1 / (p : ℝ)))) i j +
    additiveBivariateMonomialOver 1 1 (selbergLocalJetParameter p) i j

/-- Deformed local principal factor. -/
def selbergLocalPrincipalJet (p : ℕ) : ℕ → ℕ → PowerSeries ℝ :=
  additiveBivariateConvolutionOver (selbergLocalDiagonalJet p)
    (selbergLocalMoebiusJet p)

/-- The deformed diagonal factor and denominator are exact convolution inverses. -/
theorem additiveBivariateConvolutionOver_localDiagonalJet_denominator (p : ℕ) :
    additiveBivariateConvolutionOver (selbergLocalDiagonalJet p)
        (selbergLocalEulerDenominatorJet p) =
      (additiveBivariateOneOver : ℕ → ℕ → PowerSeries ℝ) := by
  have hden : selbergLocalEulerDenominatorJet p = fun i j =>
      additiveBivariateOneOver i j -
        additiveBivariateDiagonalMonomialOver (selbergLocalJetParameter p) i j := by
    funext i j
    simp [selbergLocalEulerDenominatorJet, additiveBivariateOneOver,
      additiveBivariateDiagonalMonomialOver, additiveBivariateMonomialOver]
  rw [hden]
  rw [additiveBivariateConvolutionOver_sub_right,
    additiveBivariateConvolutionOver_one_right,
    additiveBivariateConvolutionOver_diagonalMonomial_right]
  funext i j
  rw [additiveBivariateDiagonalShiftOver]
  rcases i.eq_zero_or_pos with rfl | hi
  · rcases j.eq_zero_or_pos with rfl | hj
    · simp [selbergLocalDiagonalJet, additiveBivariateOneOver]
    · simp [selbergLocalDiagonalJet, additiveBivariateOneOver,
        Nat.ne_of_gt hj, (Nat.ne_of_gt hj).symm]
  rcases j.eq_zero_or_pos with rfl | hj
  · simp [selbergLocalDiagonalJet, additiveBivariateOneOver, Nat.ne_of_gt hi]
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [if_neg (by omega)]
  by_cases hij : i = j
  · subst j
    simp [selbergLocalDiagonalJet, additiveBivariateOneOver, pow_succ]
    ring
  · simp [selbergLocalDiagonalJet, additiveBivariateOneOver, hij]

private theorem coeff_additiveBivariateConvolutionOver_constant_right
    (k : ℕ) (f : ℕ → ℕ → PowerSeries ℝ) (g : ℕ → ℕ → ℝ) (i j : ℕ) :
    PowerSeries.coeff k
        (additiveBivariateConvolutionOver f (fun a b => PowerSeries.C (g a b)) i j) =
      additiveBivariateConvolution (fun a b => PowerSeries.coeff k (f a b)) g i j := by
  rw [additiveBivariateConvolutionOver, additiveBivariateConvolution]
  simp only [map_sum, PowerSeries.coeff_mul_C]

private theorem coeff_selbergLocalOriginalJet_zero {p : ℕ} (hp : p.Prime) (i j : ℕ) :
    PowerSeries.coeff 0 (selbergLocalOriginalJet p i j) =
      selbergLocalOriginal p i j := by
  rw [selbergLocalOriginal_eq_polynomial hp]
  by_cases h00 : i = 0 ∧ j = 0
  · rcases h00 with ⟨rfl, rfl⟩
    simp [selbergLocalOriginalJet, selbergLocalOriginalPolynomial,
      additiveBivariateMonomialOver]
  by_cases h10 : i = 1 ∧ j = 0
  · rcases h10 with ⟨rfl, rfl⟩
    simp [selbergLocalOriginalJet, selbergLocalOriginalPolynomial,
      additiveBivariateMonomialOver]
  by_cases h01 : i = 0 ∧ j = 1
  · rcases h01 with ⟨rfl, rfl⟩
    simp [selbergLocalOriginalJet, selbergLocalOriginalPolynomial,
      additiveBivariateMonomialOver]
  by_cases h11 : i = 1 ∧ j = 1
  · rcases h11 with ⟨rfl, rfl⟩
    simp [selbergLocalOriginalJet, selbergLocalOriginalPolynomial,
      additiveBivariateMonomialOver, selbergLocalJetParameter, coeff_exponentialJet]
  · simp [selbergLocalOriginalJet, selbergLocalOriginalPolynomial,
      additiveBivariateMonomialOver, h00, h10, h01, h11]

private theorem coeff_selbergLocalEulerDenominatorJet_zero (p i j : ℕ) :
    PowerSeries.coeff 0 (selbergLocalEulerDenominatorJet p i j) =
      selbergLocalEulerDenominator p i j := by
  have hexp0 : PowerSeries.constantCoeff (exponentialJet (Real.log (p : ℝ))) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  by_cases h11 : i = 1 ∧ j = 1
  · rcases h11 with ⟨rfl, rfl⟩
    simp [selbergLocalEulerDenominatorJet, selbergLocalEulerDenominator,
      additiveBivariateOne, additiveBivariateMonomialOver, additiveBivariateDiagonalMonomial,
      selbergLocalJetParameter, PowerSeries.coeff_zero_eq_constantCoeff, hexp0]
  · simp [selbergLocalEulerDenominatorJet, selbergLocalEulerDenominator,
      additiveBivariateOne, additiveBivariateMonomialOver, additiveBivariateDiagonalMonomial,
      PowerSeries.coeff_zero_eq_constantCoeff, h11]

private theorem coeff_convolutionOver_zero_eq_convolution
    (f g : ℕ → ℕ → PowerSeries ℝ) (i j : ℕ) :
    PowerSeries.coeff 0 (additiveBivariateConvolutionOver f g i j) =
      additiveBivariateConvolution
        (fun a b => PowerSeries.coeff 0 (f a b))
        (fun a b => PowerSeries.coeff 0 (g a b)) i j := by
  rw [additiveBivariateConvolutionOver, additiveBivariateConvolution]
  simp only [map_sum, PowerSeries.coeff_zero_eq_constantCoeff, map_mul]

private theorem localCorrection_base_numerator {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolution (selbergLocalCorrection p)
        (localMoebiusPairFactor p) =
      additiveBivariateConvolution (selbergLocalOriginal p)
        (selbergLocalEulerDenominator p) := by
  have hprincipal := additiveBivariateConvolution_localCorrection_principal hp
  have hprincipalDef := selbergLocalPrincipal_eq_convolution hp
  have hinv := additiveBivariateConvolution_localDiagonal_eulerDenominator hp
  rw [hprincipalDef] at hprincipal
  calc
    additiveBivariateConvolution (selbergLocalCorrection p)
        (localMoebiusPairFactor p) =
      additiveBivariateConvolution
        (additiveBivariateConvolution (selbergLocalCorrection p)
          (localMoebiusPairFactor p)) additiveBivariateOne := by
            rw [additiveBivariateConvolution_one_right]
    _ = additiveBivariateConvolution
        (additiveBivariateConvolution (selbergLocalCorrection p)
          (localMoebiusPairFactor p))
        (additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
          (selbergLocalEulerDenominator p)) := by rw [hinv]
    _ = additiveBivariateConvolution
        (additiveBivariateConvolution (selbergLocalCorrection p)
          (additiveBivariateConvolution (selbergLocalDiagonalReciprocal p)
            (selbergLocalMoebiusReciprocalPair p)))
        (selbergLocalEulerDenominator p) := by
          rw [localMoebiusPairFactor_eq hp]
          apply bivariateCoefficientSeries_injective
          simp only [bivariateCoefficientSeries_convolution]
          ring
    _ = additiveBivariateConvolution (selbergLocalOriginal p)
        (selbergLocalEulerDenominator p) := by rw [hprincipal]

private def selbergLocalNumeratorJet (p i j : ℕ) : PowerSeries ℝ :=
  let q := PowerSeries.C (1 / (p : ℝ))
  let z := selbergLocalJetParameter p
  additiveBivariateMonomialOver 0 0 1 i j +
    additiveBivariateMonomialOver 1 0 (-q) i j +
    additiveBivariateMonomialOver 0 1 (-q) i j +
    additiveBivariateMonomialOver 2 1 (q * z) i j +
    additiveBivariateMonomialOver 1 2 (q * z) i j +
    additiveBivariateMonomialOver 2 2 (-(z ^ (2 : ℕ))) i j

private theorem convolution_originalJet_denominator_eq_numerator (p : ℕ) :
    additiveBivariateConvolutionOver (selbergLocalOriginalJet p)
        (selbergLocalEulerDenominatorJet p) = selbergLocalNumeratorJet p := by
  change additiveBivariateConvolutionOver
      (fun i j =>
        additiveBivariateMonomialOver 0 0 1 i j +
          additiveBivariateMonomialOver 1 0 (-(PowerSeries.C (1 / (p : ℝ)))) i j +
          additiveBivariateMonomialOver 0 1 (-(PowerSeries.C (1 / (p : ℝ)))) i j +
          additiveBivariateMonomialOver 1 1 (selbergLocalJetParameter p) i j)
      (fun i j => additiveBivariateMonomialOver 0 0 1 i j -
        additiveBivariateMonomialOver 1 1 (selbergLocalJetParameter p) i j) =
    fun i j =>
      additiveBivariateMonomialOver 0 0 1 i j +
        additiveBivariateMonomialOver 1 0 (-(PowerSeries.C (1 / (p : ℝ)))) i j +
        additiveBivariateMonomialOver 0 1 (-(PowerSeries.C (1 / (p : ℝ)))) i j +
        additiveBivariateMonomialOver 2 1
          (PowerSeries.C (1 / (p : ℝ)) * selbergLocalJetParameter p) i j +
        additiveBivariateMonomialOver 1 2
          (PowerSeries.C (1 / (p : ℝ)) * selbergLocalJetParameter p) i j +
        additiveBivariateMonomialOver 2 2 (-(selbergLocalJetParameter p ^ (2 : ℕ))) i j
  simp only [additiveBivariateConvolutionOver_sub_right,
    additiveBivariateConvolutionOver_add_left,
    additiveBivariateConvolutionOver_monomial]
  funext i j
  simp only [additiveBivariateMonomialOver]
  split_ifs <;> ring

private theorem coeff_succ_selbergLocalNumeratorJet
    (k p i j : ℕ) :
    PowerSeries.coeff (k + 1) (selbergLocalNumeratorJet p i j) =
      selbergCorrectionLogPowerNumerator (k + 1) p i j /
        ((k + 1).factorial : ℝ) := by
  have hfac : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
  have htwo : exponentialJet (Real.log (p : ℝ)) ^ (2 : ℕ) =
      exponentialJet (2 * Real.log (p : ℝ)) := by
    rw [← exponentialJet_nat_mul]
    norm_num
  have hzsq : selbergLocalJetParameter p ^ (2 : ℕ) =
      PowerSeries.C ((1 / (p : ℝ)) ^ (2 : ℕ)) *
        exponentialJet (2 * Real.log (p : ℝ)) := by
    rw [selbergLocalJetParameter, mul_pow, map_pow, htwo]
  simp only [selbergLocalNumeratorJet, additiveBivariateMonomialOver]
  by_cases hi21 : i = 2 ∧ j = 1
  · rcases hi21 with ⟨rfl, rfl⟩
    simp [selbergLocalJetParameter, PowerSeries.coeff_C_mul, coeff_exponentialJet,
      selbergCorrectionLogPowerNumerator, div_eq_mul_inv]
    ring
  by_cases hi12 : i = 1 ∧ j = 2
  · rcases hi12 with ⟨rfl, rfl⟩
    simp [selbergLocalJetParameter, PowerSeries.coeff_C_mul, coeff_exponentialJet,
      selbergCorrectionLogPowerNumerator, div_eq_mul_inv]
    ring
  by_cases hi22 : i = 2 ∧ j = 2
  · rcases hi22 with ⟨rfl, rfl⟩
    simp [hzsq, PowerSeries.coeff_C_mul,
      coeff_exponentialJet, selbergCorrectionLogPowerNumerator, div_eq_mul_inv]
    ring
  · rw [selbergCorrectionLogPowerNumerator]
    split_ifs <;> simp_all

private theorem coeff_succ_originalJet_denominator
    (k p i j : ℕ) :
    PowerSeries.coeff (k + 1)
        (additiveBivariateConvolutionOver (selbergLocalOriginalJet p)
          (selbergLocalEulerDenominatorJet p) i j) =
      selbergCorrectionLogPowerNumerator (k + 1) p i j /
        ((k + 1).factorial : ℝ) := by
  rw [convolution_originalJet_denominator_eq_numerator]
  exact coeff_succ_selbergLocalNumeratorJet k p i j

/-- Numerator identity for the complete correction jet. -/
theorem additiveBivariateConvolutionOver_localCorrectionJet_moebius
    {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolutionOver (selbergCorrectionJetLocal p)
        (selbergLocalMoebiusJet p) =
      additiveBivariateConvolutionOver (selbergLocalOriginalJet p)
        (selbergLocalEulerDenominatorJet p) := by
  funext i j
  ext k
  rcases k with _ | k
  · rw [coeff_convolutionOver_zero_eq_convolution,
      coeff_convolutionOver_zero_eq_convolution]
    simp_rw [coeff_selbergCorrectionJetLocal_zero,
      coeff_selbergLocalOriginalJet_zero hp,
      coeff_selbergLocalEulerDenominatorJet_zero]
    simp only [selbergLocalMoebiusJet, PowerSeries.coeff_C]
    change additiveBivariateConvolution (selbergLocalCorrection p)
        (localMoebiusPairFactor p) i j = _
    exact congrFun (congrFun (localCorrection_base_numerator hp) i) j
  · rw [show selbergLocalMoebiusJet p =
        fun a b => PowerSeries.C (localMoebiusPairFactor p a b) from rfl,
      coeff_additiveBivariateConvolutionOver_constant_right]
    simp_rw [coeff_selbergCorrectionJetLocal_succ]
    have hfac : ((k + 1).factorial : ℝ) ≠ 0 := by positivity
    rw [show additiveBivariateConvolution
        (fun a b => selbergCorrectionLogPowerLocal (k + 1) p a b /
          ((k + 1).factorial : ℝ)) (localMoebiusPairFactor p) i j =
        additiveBivariateConvolution (selbergCorrectionLogPowerLocal (k + 1) p)
          (localMoebiusPairFactor p) i j / ((k + 1).factorial : ℝ) by
          rw [additiveBivariateConvolution, additiveBivariateConvolution,
            Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro b hb
          field_simp [hfac]]
    rw [additiveBivariateConvolution_selbergCorrectionLogPowerLocal_moebius
      (k + 1) hp]
    exact coeff_succ_originalJet_denominator k p i j |>.symm

/-- Exact local factorization of every logarithmic jet. -/
theorem additiveBivariateConvolutionOver_localCorrectionJet_principal
    {p : ℕ} (hp : p.Prime) :
    additiveBivariateConvolutionOver (selbergCorrectionJetLocal p)
        (selbergLocalPrincipalJet p) = selbergLocalOriginalJet p := by
  rw [selbergLocalPrincipalJet]
  calc
    additiveBivariateConvolutionOver (selbergCorrectionJetLocal p)
        (additiveBivariateConvolutionOver (selbergLocalDiagonalJet p)
          (selbergLocalMoebiusJet p)) =
      additiveBivariateConvolutionOver
        (additiveBivariateConvolutionOver (selbergCorrectionJetLocal p)
          (selbergLocalMoebiusJet p)) (selbergLocalDiagonalJet p) := by
            apply bivariateCoefficientSeriesOver_injective
            simp only [bivariateCoefficientSeriesOver_convolution]
            ring
    _ = additiveBivariateConvolutionOver
        (additiveBivariateConvolutionOver (selbergLocalOriginalJet p)
          (selbergLocalEulerDenominatorJet p)) (selbergLocalDiagonalJet p) := by
            rw [additiveBivariateConvolutionOver_localCorrectionJet_moebius hp]
    _ = additiveBivariateConvolutionOver (selbergLocalOriginalJet p)
        (additiveBivariateConvolutionOver (selbergLocalEulerDenominatorJet p)
          (selbergLocalDiagonalJet p)) :=
            additiveBivariateConvolutionOver_assoc _ _ _
    _ = selbergLocalOriginalJet p := by
      rw [additiveBivariateConvolutionOver_comm
          (selbergLocalEulerDenominatorJet p) (selbergLocalDiagonalJet p),
        additiveBivariateConvolutionOver_localDiagonalJet_denominator,
        additiveBivariateConvolutionOver_one_right]

end

end RHTower.Sieve
