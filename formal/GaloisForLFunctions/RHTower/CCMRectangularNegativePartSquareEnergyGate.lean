import GaloisForLFunctions.RHTower.CCMRectangularNegativePartEnergyGate

/-!
# Weighted square energy of the negative rectangular tail proves RH

This module gives the negative-part Dirichlet-energy gate an `L²` predecessor.  Weighted
Cauchy--Schwarz shows that square summability of the negative observable values against every
weight `n ^ (-1-epsilon)` implies ordinary negative-part Dirichlet summability with the same
weight.  The result is a direct interface for Gram, covariance, and Hilbert-space estimates.
-/

open Complex LSeries

namespace RHTower

noncomputable section

/-- The real weighted Dirichlet term, with the unused index zero explicitly removed. -/
def realDirichletWeightedTerm (f : ℕ → ℝ) (sigma : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f n / (n : ℝ) ^ sigma

/-- Weighted Cauchy--Schwarz: if the square coefficients are summable against `n^-sigma` for
`sigma > 1`, then the original nonnegative coefficients define an absolutely convergent L-series
at `sigma`. -/
theorem LSeriesSummable_of_squareWeightedTerm_summable
    {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {sigma : ℝ} (hsigma : 1 < sigma)
    (h2 : Summable (realDirichletWeightedTerm (fun n => (f n) ^ 2) sigma)) :
    LSeriesSummable (fun n => ((f n : ℝ) : ℂ)) (sigma : ℂ) := by
  let u : ℕ → ℝ := fun n =>
    if n = 0 then 0 else f n / (n : ℝ) ^ (sigma / 2)
  let v : ℕ → ℝ := fun n =>
    if n = 0 then 0 else 1 / (n : ℝ) ^ (sigma / 2)
  have hu0 : ∀ n, 0 ≤ u n := by
    intro n
    dsimp only [u]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hv0 : ∀ n, 0 ≤ v n := by
    intro n
    dsimp only [v]
    split_ifs
    · exact le_rfl
    · positivity
  have hu2 : Summable (fun n => u n ^ (2 : ℝ)) := by
    apply h2.congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp [u, realDirichletWeightedTerm]
    · have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      dsimp only [u]
      rw [if_neg hn, Real.rpow_two, div_pow,
        realDirichletWeightedTerm, if_neg hn]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR]
      congr 1
      norm_num
  have hv2 : Summable (fun n => v n ^ (2 : ℝ)) := by
    have hzeta : Summable (fun n : ℕ => 1 / (n : ℝ) ^ sigma) :=
      Real.summable_one_div_nat_rpow.mpr hsigma
    apply hzeta.congr
    intro n
    by_cases hn : n = 0
    · subst n
      have hsigma0 : 0 < sigma := by linarith
      dsimp only [v]
      rw [if_pos rfl, Real.rpow_two, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      simp only [Nat.cast_zero]
      rw [Real.zero_rpow hsigma0.ne', div_zero]
    · have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      dsimp only [v]
      rw [if_neg hn, Real.rpow_two, div_pow, one_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR]
      congr 1
      norm_num
  have huv : Summable (fun n => u n * v n) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
      hu0 hv0 hu2 hv2
  change Summable (LSeries.term (fun n => ((f n : ℝ) : ℂ)) (sigma : ℂ))
  apply huv.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp [u, v]
  · rw [LSeries.term_of_ne_zero hn, norm_div, norm_real,
      Real.norm_of_nonneg (hf n)]
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hden : (n : ℝ) ^ sigma =
        (n : ℝ) ^ (sigma / 2) * (n : ℝ) ^ (sigma / 2) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring
    dsimp only [u, v]
    rw [if_neg hn, if_neg hn,
      Complex.norm_cpow_real, Complex.norm_natCast, hden]
    have hhalfpos : 0 < (n : ℝ) ^ (sigma / 2) :=
      Real.rpow_pos_of_pos hnpos _
    field_simp
    exact le_rfl

/-- Source-facing square-energy condition on the negative part of one actual rectangular Weil
tail.  This is a literal weighted `L²` target. -/
def XiRectangularWeilTailNegativePartSquareEnergy (L : ℝ) (N : ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    Summable
      (realDirichletWeightedTerm
        (fun n => (xiRectangularWeilTailNegativePart L N n) ^ 2)
        (1 + epsilon))

/-- Weighted square energy implies the negative-part Dirichlet-energy condition. -/
theorem xiRectangularWeilTailNegativePartEnergy_of_squareEnergy
    {L : ℝ} {N : ℕ}
    (h2 : XiRectangularWeilTailNegativePartSquareEnergy L N) :
    XiRectangularWeilTailNegativePartEnergy L N := by
  intro epsilon hepsilon
  exact LSeriesSummable_of_squareWeightedTerm_summable
    (xiRectangularWeilTailNegativePart_nonneg L N)
    (by linarith) (h2 epsilon hepsilon)

/-- Weighted `L²` control of the negative part of one actual rectangular Weil family proves RH. -/
theorem riemannHypothesis_of_xiRectangularWeilTailNegativePartSquareEnergy
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (h2 : XiRectangularWeilTailNegativePartSquareEnergy L N) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_xiRectangularWeilTailNegativePartEnergy hL hN
    (xiRectangularWeilTailNegativePartEnergy_of_squareEnergy h2)

end

end RHTower
