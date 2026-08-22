import GaloisForLFunctions.RHTower.EulerSquarefreeWickReplicaDensityOrientation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Completed matrix landing of the Euler--Wick replica

The EWQ density has the canonical Euler logarithm on both diagonal entries and the unsquared
quadratic residue character on both off-diagonal entries.  The latter is not literally the
modulo-twelve Dirichlet Euler logarithm at the ramified primes: the unit-residue profile assigns
the value one at `2` and `3`, while the Dirichlet character vanishes there.

This module resolves that discrepancy coefficient-for-coefficient.  The off-diagonal exponential
is exactly

`L(s, χ₁₂) * (1 - 2⁻ˢ)⁻¹ * (1 - 3⁻ˢ)⁻¹`

on `Re(s) > 1`, and both repair factors are nonzero there.  Diagonalizing the two-channel source in
the fixed Pauli-X basis then gives completed eigenchannels `Xi * C` and `Xi * C⁻¹`.  Their
determinant is exactly `Xi²`: the ordered matrix channel retains the EWQ orientation, while every
determinant scalarization erases it.  No divisor is selected anywhere in the construction.
-/

namespace GaloisForLFunctions.RHTower

open Complex LSeries ArithmeticFunction
open GaloisForLFunctions.HTGeometry
open scoped LSeries.notation

noncomputable section

def ewqPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩
def ewqPrimeThree : Nat.Primes := ⟨3, Nat.prime_three⟩

theorem quadraticResidueProductPrimeCoefficient_eq_one_of_not_isUnit
    (p : Nat.Primes) (hp : ¬ IsUnit ((p.1 : ℕ) : ZMod 12)) :
    quadraticResidueProductPrimeCoefficient p = 1 := by
  simp [quadraticResidueProductPrimeCoefficient, quadraticResiduePrimeProfile,
    coprimePrimeUnitResidueProfile, primeUnitResidueProfile, hp,
    quadraticResidueFstObservable, quadraticResidueSndObservable]

theorem not_isUnit_mod_twelve_iff_eq_two_or_three (p : Nat.Primes) :
    ¬ IsUnit ((p.1 : ℕ) : ZMod 12) ↔ p = ewqPrimeTwo ∨ p = ewqPrimeThree := by
  rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd p.2, not_not]
  constructor
  · intro hp
    have hp' : (p : ℕ) ∣ 3 * 4 := by norm_num at hp ⊢; exact hp
    rcases p.2.dvd_mul.mp hp' with h3 | h4
    · have heq : (p : ℕ) = 3 :=
        (Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.2.ne_one
      right
      exact Subtype.ext heq
    · have h4' : (p : ℕ) ∣ 2 * 2 := by norm_num at h4 ⊢; exact h4
      rcases p.2.dvd_mul.mp h4' with h2 | h2
      all_goals
        have heq : (p : ℕ) = 2 :=
          (Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left p.2.ne_one
        left
        exact Subtype.ext heq
  · rintro (rfl | rfl) <;> norm_num [ewqPrimeTwo, ewqPrimeThree]

theorem quadraticResidueProductPrimeCoefficient_eq_piecewise (p : Nat.Primes) :
    quadraticResidueProductPrimeCoefficient p =
      if p = ewqPrimeTwo ∨ p = ewqPrimeThree then 1
      else quadraticCharacterTwelve ((p.1 : ℕ) : ZMod 12) := by
  by_cases hp : IsUnit ((p.1 : ℕ) : ZMod 12)
  · rw [quadraticResidueProductPrimeCoefficient_eq_quadraticCharacterTwelve_of_isUnit p hp]
    simp [hp, ← not_isUnit_mod_twelve_iff_eq_two_or_three]
  · rw [quadraticResidueProductPrimeCoefficient_eq_one_of_not_isUnit p hp]
    simp [hp, ← not_isUnit_mod_twelve_iff_eq_two_or_three]

theorem norm_eulerWickQuadraticEulerLogCharacterSource_le_one (n : ℕ) :
    ‖eulerWickQuadraticEulerLogCharacterSource n‖ ≤ 1 := by
  by_cases hpow : IsPrimePow n
  · let x : PrimePowerClockIndex := Nat.Primes.prodNatEquiv.symm ⟨n, hpow⟩
    have hx := congrArg Subtype.val
      (Nat.Primes.prodNatEquiv.apply_symm_apply ⟨n, hpow⟩)
    have hn : (x.1 : Nat) ^ (x.2 + 1) = n := by
      simpa only [x, Nat.Primes.coe_prodNatEquiv_apply] using! hx
    rw [← hn]
    have hcoord := primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile
      eulerWickQuadraticEulerLogReplica x
    change eulerWickQuadraticEulerLogCharacterSource
      ((x.1 : Nat) ^ (x.2 + 1)) = eulerWickQuadraticEulerLogReplica x at hcoord
    rw [hcoord]
    rw [eulerWickQuadraticEulerLogReplica, norm_div]
    have hchar : ‖eulerWickQuadraticDepthCharacter x‖ = 1 := by
      rcases eulerWickQuadraticDepthCharacter_eq_one_or_neg_one x with h | h <;>
        rw [h] <;> norm_num
    rw [hchar, one_div]
    have hden : (1 : ℝ) ≤ ‖(((x.2 + 1 : ℕ) : ℂ))‖ := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le x.2)
    exact inv_le_one_of_one_le₀ hden
  · simp [eulerWickQuadraticEulerLogCharacterSource,
      arithmeticFunctionOfPrimePowerProfile, hpow]

theorem eulerWickQuadraticEulerLogCharacterSource_summable
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable eulerWickQuadraticEulerLogCharacterSource s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (fun n _ => norm_eulerWickQuadraticEulerLogCharacterSource_le_one n) hs

theorem LSeries_eulerWickQuadraticEulerLogCharacterSource_eq_primeLog
    {s : ℂ} (hs : 1 < s.re) :
    LSeries eulerWickQuadraticEulerLogCharacterSource s =
      ∑' p : Nat.Primes,
        -Complex.log (1 - quadraticResidueProductPrimeCoefficient p * (p : ℂ) ^ (-s)) := by
  rw [LSeries]
  have hsum : Summable (LSeries.term eulerWickQuadraticEulerLogCharacterSource s) :=
    eulerWickQuadraticEulerLogCharacterSource_summable hs
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers hsum]
  · apply tsum_congr
    intro p
    have hnorm :
        ‖quadraticResidueProductPrimeCoefficient p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul]
      have hp_le := quadraticResidueProductPrimeCoefficient_norm_le_one p
      have hpow_lt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (by exact_mod_cast p.prop.pos), Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.prop.one_lt) (by linarith)
      calc
        ‖quadraticResidueProductPrimeCoefficient p‖ * ‖(p : ℂ) ^ (-s)‖ ≤
            1 * ‖(p : ℂ) ^ (-s)‖ :=
          mul_le_mul_of_nonneg_right hp_le (norm_nonneg _)
        _ < 1 := by simpa using hpow_lt
    have hseries := Complex.hasSum_taylorSeries_neg_log hnorm
    rw [← hseries.tsum_eq, hseries.summable.tsum_eq_zero_add]
    simp only [Nat.cast_zero, div_zero, zero_add]
    apply tsum_congr
    intro k
    rw [LSeries.term_of_ne_zero (pow_ne_zero (k + 1) p.prop.ne_zero)]
    have hcoord := primePowerCoordinateProfile_arithmeticFunctionOfPrimePowerProfile
      eulerWickQuadraticEulerLogReplica (p, k)
    change eulerWickQuadraticEulerLogCharacterSource ((p : Nat) ^ (k + 1)) =
      eulerWickQuadraticEulerLogReplica (p, k) at hcoord
    rw [hcoord, eulerWickQuadraticEulerLogReplica, eulerWickQuadraticDepthCharacter]
    rw [mul_pow]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    rw [← Complex.cpow_nat_mul]
    rw [show ((k + 1 : ℕ) : ℂ) * (-s) = -(((k + 1 : ℕ) : ℂ) * s) by ring,
      Complex.cpow_neg]
    push_cast
    ring
  · intro n hn
    by_contra hpp
    change ¬ IsPrimePow n at hpp
    apply hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0]
      simp [eulerWickQuadraticEulerLogCharacterSource,
        arithmeticFunctionOfPrimePowerProfile, hpp]

theorem summable_eulerWickQuadraticPrimeLog
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun p : Nat.Primes =>
      -Complex.log (1 - quadraticResidueProductPrimeCoefficient p * (p : ℂ) ^ (-s)) := by
  have hmajorant : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-s.re) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  have hterm : Summable fun p : Nat.Primes =>
      quadraticResidueProductPrimeCoefficient p * (p : ℂ) ^ (-s) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hmajorant
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast p.prop.pos),
      Complex.neg_re]
    exact mul_le_of_le_one_left (by positivity)
      (quadraticResidueProductPrimeCoefficient_norm_le_one p)
  exact hterm.clog_one_sub.neg

theorem eulerWickQuadraticPrimeLog_eq_characterLog_add_ramified
    {s : ℂ} (hs : 1 < s.re) :
    (∑' p : Nat.Primes,
        -Complex.log (1 - quadraticResidueProductPrimeCoefficient p * (p : ℂ) ^ (-s))) =
      -Complex.log (1 - (2 : ℂ) ^ (-s)) +
      -Complex.log (1 - (3 : ℂ) ^ (-s)) +
      ∑' p : Nat.Primes,
        -Complex.log (1 - quadraticCharacterTwelve p * (p : ℂ) ^ (-s)) := by
  let S : Finset Nat.Primes := {ewqPrimeTwo, ewqPrimeThree}
  let f : Nat.Primes → ℂ := fun p =>
    -Complex.log (1 - quadraticResidueProductPrimeCoefficient p * (p : ℂ) ^ (-s))
  let g : Nat.Primes → ℂ := fun p =>
    -Complex.log (1 - quadraticCharacterTwelve p * (p : ℂ) ^ (-s))
  have hf : Summable f := summable_eulerWickQuadraticPrimeLog hs
  have hg : Summable g :=
    DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow quadraticCharacterTwelve hs
  have hfg : ∀ p : Nat.Primes, p ∉ S → f p = g p := by
    intro p hp
    have hp' : ¬(p = ewqPrimeTwo ∨ p = ewqPrimeThree) := by
      simpa [S] using hp
    dsimp only [f, g]
    rw [quadraticResidueProductPrimeCoefficient_eq_piecewise, if_neg hp']
  have hcomp :
      (∑' p : {p : Nat.Primes // p ∈ (↑S : Set Nat.Primes)ᶜ}, f p) =
        ∑' p : {p : Nat.Primes // p ∈ (↑S : Set Nat.Primes)ᶜ}, g p := by
    apply tsum_congr
    intro p
    exact hfg p.1 p.2
  have hsplitf := hf.sum_add_tsum_compl (s := S)
  have hsplitg := hg.sum_add_tsum_compl (s := S)
  rw [hcomp] at hsplitf
  have hχtwo : quadraticCharacterTwelve (2 : ℕ) = 0 := by
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  have hχthree : quadraticCharacterTwelve (3 : ℕ) = 0 := by
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    norm_num
  have hχtwoP : quadraticCharacterTwelve ewqPrimeTwo = 0 := by
    simpa [ewqPrimeTwo] using hχtwo
  have hχthreeP : quadraticCharacterTwelve ewqPrimeThree = 0 := by
    simpa [ewqPrimeThree] using hχthree
  have htwo_ne_three : ewqPrimeTwo ≠ ewqPrimeThree := by
    intro h
    have := congrArg Subtype.val h
    norm_num [ewqPrimeTwo, ewqPrimeThree] at this
  have hg2 : g ewqPrimeTwo = 0 := by
    dsimp only [g]
    rw [hχtwoP]
    simp
  have hg3 : g ewqPrimeThree = 0 := by
    dsimp only [g]
    rw [hχthreeP]
    simp
  have hSg : ∑ p ∈ S, g p = 0 := by
    change ∑ p ∈ ({ewqPrimeTwo, ewqPrimeThree} : Finset Nat.Primes), g p = 0
    rw [Finset.sum_insert (by simpa using htwo_ne_three), Finset.sum_singleton,
      hg2, hg3, add_zero]
  have hSf : ∑ p ∈ S, f p =
      -Complex.log (1 - (2 : ℂ) ^ (-s)) +
        -Complex.log (1 - (3 : ℂ) ^ (-s)) := by
    have ha2 : quadraticResidueProductPrimeCoefficient ewqPrimeTwo = 1 := by
      apply quadraticResidueProductPrimeCoefficient_eq_one_of_not_isUnit
      intro hunit
      have hc := (ZMod.isUnit_iff_coprime 2 12).mp hunit
      norm_num at hc
    have ha3 : quadraticResidueProductPrimeCoefficient ewqPrimeThree = 1 := by
      apply quadraticResidueProductPrimeCoefficient_eq_one_of_not_isUnit
      intro hunit
      have hc := (ZMod.isUnit_iff_coprime 3 12).mp hunit
      norm_num at hc
    have hf2 : f ewqPrimeTwo = -Complex.log (1 - (2 : ℂ) ^ (-s)) := by
      dsimp only [f]
      rw [ha2]
      simp [ewqPrimeTwo]
    have hf3 : f ewqPrimeThree = -Complex.log (1 - (3 : ℂ) ^ (-s)) := by
      dsimp only [f]
      rw [ha3]
      simp [ewqPrimeThree]
    change ∑ p ∈ ({ewqPrimeTwo, ewqPrimeThree} : Finset Nat.Primes), f p = _
    rw [Finset.sum_insert (by simpa using htwo_ne_three), Finset.sum_singleton,
      hf2, hf3]
  have hcompg :
      (∑' p : {p : Nat.Primes // p ∈ (↑S : Set Nat.Primes)ᶜ}, g p) =
        ∑' p : Nat.Primes, g p := by
    rw [← hsplitg, hSg, zero_add]
  rw [hcompg] at hsplitf
  change (∑' p : Nat.Primes, f p) =
    -Complex.log (1 - (2 : ℂ) ^ (-s)) +
      -Complex.log (1 - (3 : ℂ) ^ (-s)) + ∑' p : Nat.Primes, g p
  rw [← hsplitf, hSf]

private theorem one_sub_two_cpow_ne_zero {s : ℂ} (hs : 1 < s.re) :
    1 - (2 : ℂ) ^ (-s) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hnorm := congrArg norm h
  rw [norm_one] at hnorm
  change (1 : ℝ) = ‖((2 : ℝ) : ℂ) ^ (-s)‖ at hnorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re] at hnorm
  have hlt : (2 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

private theorem one_sub_three_cpow_ne_zero {s : ℂ} (hs : 1 < s.re) :
    1 - (3 : ℂ) ^ (-s) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hnorm := congrArg norm h
  rw [norm_one] at hnorm
  change (1 : ℝ) = ‖((3 : ℝ) : ℂ) ^ (-s)‖ at hnorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num), Complex.neg_re] at hnorm
  have hlt : (3 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

theorem exp_LSeries_eulerWickQuadraticEulerLogCharacterSource_eq
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries eulerWickQuadraticEulerLogCharacterSource s) =
      DirichletCharacter.LFunction quadraticCharacterTwelve s *
        (1 - (2 : ℂ) ^ (-s))⁻¹ * (1 - (3 : ℂ) ^ (-s))⁻¹ := by
  rw [LSeries_eulerWickQuadraticEulerLogCharacterSource_eq_primeLog hs,
    eulerWickQuadraticPrimeLog_eq_characterLog_add_ramified hs,
    Complex.exp_add, Complex.exp_add,
    DirichletCharacter.LSeries_eulerProduct_exp_log quadraticCharacterTwelve hs,
    ← DirichletCharacter.LFunction_eq_LSeries quadraticCharacterTwelve hs]
  rw [Complex.exp_neg, Complex.exp_log (one_sub_two_cpow_ne_zero hs),
    Complex.exp_neg, Complex.exp_log (one_sub_three_cpow_ne_zero hs)]
  ring

/-- The exact analytic off-diagonal EWQ carrier, including its two ramified local repairs. -/
def eulerWickQuadraticCorrectedLFunction (s : ℂ) : ℂ :=
  DirichletCharacter.LFunction quadraticCharacterTwelve s *
    (1 - (2 : ℂ) ^ (-s))⁻¹ * (1 - (3 : ℂ) ^ (-s))⁻¹

theorem exp_LSeries_eulerWickQuadraticEulerLogCharacterSource_eq_correctedL
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries eulerWickQuadraticEulerLogCharacterSource s) =
      eulerWickQuadraticCorrectedLFunction s := by
  exact exp_LSeries_eulerWickQuadraticEulerLogCharacterSource_eq hs

theorem eulerWickQuadraticCorrectedLFunction_ne_zero
    {s : ℂ} (hs : 1 < s.re) :
    eulerWickQuadraticCorrectedLFunction s ≠ 0 := by
  rw [← exp_LSeries_eulerWickQuadraticEulerLogCharacterSource_eq_correctedL hs]
  exact Complex.exp_ne_zero _

/-- Pauli-X positive eigenchannel of the analytic two-replica logarithm. -/
def eulerWickReplicaAnalyticEigenvaluePlus (s : ℂ) : ℂ :=
  Complex.exp (LSeries eulerWickQuadraticReplicaDiagonalSource s +
    LSeries eulerWickQuadraticEulerLogCharacterSource s)

/-- Pauli-X negative eigenchannel of the analytic two-replica logarithm. -/
def eulerWickReplicaAnalyticEigenvalueMinus (s : ℂ) : ℂ :=
  Complex.exp (LSeries eulerWickQuadraticReplicaDiagonalSource s -
    LSeries eulerWickQuadraticEulerLogCharacterSource s)

theorem eulerWickReplicaAnalyticEigenvaluePlus_eq
    {s : ℂ} (hs : 1 < s.re) :
    eulerWickReplicaAnalyticEigenvaluePlus s =
      riemannZeta s * eulerWickQuadraticCorrectedLFunction s := by
  rw [eulerWickReplicaAnalyticEigenvaluePlus, Complex.exp_add,
    exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_riemannZeta hs,
    exp_LSeries_eulerWickQuadraticEulerLogCharacterSource_eq_correctedL hs]

theorem eulerWickReplicaAnalyticEigenvalueMinus_eq
    {s : ℂ} (hs : 1 < s.re) :
    eulerWickReplicaAnalyticEigenvalueMinus s =
      riemannZeta s * (eulerWickQuadraticCorrectedLFunction s)⁻¹ := by
  rw [eulerWickReplicaAnalyticEigenvalueMinus, sub_eq_add_neg, Complex.exp_add,
    Complex.exp_neg,
    exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_riemannZeta hs,
    exp_LSeries_eulerWickQuadraticEulerLogCharacterSource_eq_correctedL hs]

/-- Determinant channel of the analytic Pauli splitting forgets the EWQ orientation exactly. -/
theorem eulerWickReplicaAnalyticEigenvaluePlus_mul_minus
    {s : ℂ} (hs : 1 < s.re) :
    eulerWickReplicaAnalyticEigenvaluePlus s *
      eulerWickReplicaAnalyticEigenvalueMinus s = riemannZeta s ^ 2 := by
  rw [eulerWickReplicaAnalyticEigenvaluePlus_eq hs,
    eulerWickReplicaAnalyticEigenvalueMinus_eq hs,
    inv_eq_one_div]
  field_simp [eulerWickQuadraticCorrectedLFunction_ne_zero hs]

/-- Completed Pauli-X eigenbasis landing of the two-channel EWQ source. -/
def eulerWickReplicaCompletedEigenMatrix (s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![
    _root_.RHTower.archFactor s * eulerWickReplicaAnalyticEigenvaluePlus s,
    _root_.RHTower.archFactor s * eulerWickReplicaAnalyticEigenvalueMinus s]

theorem eulerWickReplicaCompletedEigenMatrix_apply_zero_zero
    {s : ℂ} (hs : 1 < s.re) :
    eulerWickReplicaCompletedEigenMatrix s 0 0 =
      _root_.RHTower.xi s * eulerWickQuadraticCorrectedLFunction s := by
  rw [eulerWickReplicaCompletedEigenMatrix, Matrix.diagonal_apply_eq]
  simp only [Matrix.cons_val_zero]
  rw [eulerWickReplicaAnalyticEigenvaluePlus_eq hs]
  have hxi := archFactor_mul_exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_xi hs
  rw [exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_riemannZeta hs] at hxi
  rw [← mul_assoc, hxi]

theorem eulerWickReplicaCompletedEigenMatrix_apply_one_one
    {s : ℂ} (hs : 1 < s.re) :
    eulerWickReplicaCompletedEigenMatrix s 1 1 =
      _root_.RHTower.xi s * (eulerWickQuadraticCorrectedLFunction s)⁻¹ := by
  rw [eulerWickReplicaCompletedEigenMatrix, Matrix.diagonal_apply_eq]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [eulerWickReplicaAnalyticEigenvalueMinus_eq hs]
  have hxi := archFactor_mul_exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_xi hs
  rw [exp_LSeries_eulerWickQuadraticReplicaDiagonal_eq_riemannZeta hs] at hxi
  rw [← mul_assoc, hxi]

/-- **Completed matrix landing.** The determinant is exactly Xi squared; the unsquared
orientation survives only in the ordered Pauli eigenchannels. -/
theorem det_eulerWickReplicaCompletedEigenMatrix
    {s : ℂ} (hs : 1 < s.re) :
    (eulerWickReplicaCompletedEigenMatrix s).det = _root_.RHTower.xi s ^ 2 := by
  rw [Matrix.det_fin_two]
  rw [eulerWickReplicaCompletedEigenMatrix_apply_zero_zero hs,
    eulerWickReplicaCompletedEigenMatrix_apply_one_one hs]
  have h01 : eulerWickReplicaCompletedEigenMatrix s 0 1 = 0 := by
    simp [eulerWickReplicaCompletedEigenMatrix]
  have h10 : eulerWickReplicaCompletedEigenMatrix s 1 0 = 0 := by
    simp [eulerWickReplicaCompletedEigenMatrix]
  rw [h01, h10, zero_mul, sub_zero, inv_eq_one_div]
  field_simp [eulerWickQuadraticCorrectedLFunction_ne_zero hs]

end

end GaloisForLFunctions.RHTower
