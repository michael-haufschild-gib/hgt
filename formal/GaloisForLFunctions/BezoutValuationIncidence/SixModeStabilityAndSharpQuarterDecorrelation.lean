import GaloisForLFunctions.BezoutValuationIncidence.ExactSuccessorMomentRegionAndUniversalInequalities
import GaloisForLFunctions.HTGeometry.CrystallographicRestriction

/-!
# Divisor-six stability and sharp quarter-decorrelation

The maximal positive successor covariance is rigid: only the harmonic and divisor-six
coordinates survive equality. The variance away from six is at most twice the defect in
half-decorrelation, and the factor two is optimal.

A canonical idempotent operation on sieve weights deletes exactly the six-coordinate.
It preserves the harmonic mean and removes precisely the corresponding contributions
from both quadratic forms. The projected centered covariance is at most one quarter of
its variance. A symbolic divisor-ten family proves that this constant is also optimal.

The arithmetic gap uses the corpus classification of totients at most two; realization
uses the existing finite Ramanujan inverse. Every capstone covers arbitrary levels and
real weights. These bounds concern the periodic quadratic forms, not finite-prefix
signed discrepancies.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

private theorem six_values : Nat.totient 6 = 2 ∧ moebiusReal 6 = 1 := by
  have ht := wall11_totient_degeneracy_broken_by_bezout.2.1
  have hm := wall11_totient_degeneracy_broken_by_bezout.2.2.2
  rw [ht] at hm
  exact ⟨ht, by norm_num at hm ⊢; linarith⟩

/-- The next positive covariance eigenvalue is at most one quarter, away from six. -/
theorem four_mul_moebiusReal_le_totient_of_ne_six {e : ℕ}
    (he : 2 ≤ e) (h6 : e ≠ 6) :
    4 * moebiusReal e ≤ (Nat.totient e : ℝ) := by
  by_cases hsmall : Nat.totient e ≤ 2
  · rcases (GaloisForLFunctions.HTGeometry.totient_le_two_iff (by omega)).mp hsmall with
      h | h | h | h | h
    · omega
    · subst e
      have hm : moebiusReal 2 = -1 := by
        simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
      rw [hm]
      have ht : (0 : ℝ) ≤ (Nat.totient 2 : ℝ) := Nat.cast_nonneg _
      linarith
    · subst e
      have hm : moebiusReal 3 = -1 := by
        simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_three]
      rw [hm]
      have ht : (0 : ℝ) ≤ (Nat.totient 3 : ℝ) := Nat.cast_nonneg _
      linarith
    · subst e
      have ht := wall11_totient_degeneracy_broken_by_bezout.1
      have hm := wall11_totient_degeneracy_broken_by_bezout.2.2.1
      rw [ht] at hm ⊢
      norm_num at hm ⊢
      linarith
    · exact (h6 h).elim
  · have hgt : 2 < e := by
      by_contra h
      have he2 : e = 2 := by omega
      subst e
      exact hsmall (by rw [Nat.totient_two]; omega)
    obtain ⟨k, hk⟩ := Nat.totient_even hgt
    have ht : 4 ≤ Nat.totient e := by omega
    have htr : (4 : ℝ) ≤ (Nat.totient e : ℝ) := by exact_mod_cast ht
    have hm := (moebiusReal_le_one e).2
    linarith

/-- The truncated divisor transform has no coordinates outside its level. -/
theorem selbergMultiplesCoord_eq_zero_of_notMem {N e : ℕ} (c : ℕ → ℝ)
    (he : e ∉ Finset.Icc 1 N) : selbergMultiplesCoord N c e = 0 := by
  unfold selbergMultiplesCoord
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hdI, hed⟩ := Finset.mem_filter.mp hd
  obtain ⟨hdpos, hdN⟩ := Finset.mem_Icc.mp hdI
  have hepos : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    have hd0 : d = 0 := Nat.eq_zero_of_zero_dvd (he0 ▸ hed)
    omega
  exact (he (Finset.mem_Icc.mpr
    ⟨hepos, (Nat.le_of_dvd hdpos hed).trans hdN⟩)).elim

/-- A diagonal splits at six even when the level is smaller than six. -/
theorem sum_selberg_diagonal_split_six (N : ℕ) (w c : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 2 N, w e * (selbergMultiplesCoord N c e)^2) =
      (∑ e ∈ (Finset.Icc 2 N).erase 6, w e * (selbergMultiplesCoord N c e)^2) +
        w 6 * (selbergMultiplesCoord N c 6)^2 := by
  by_cases h6 : 6 ∈ Finset.Icc 2 N
  · exact (Finset.sum_erase_add _ _ h6).symm
  · have hc : selbergMultiplesCoord N c 6 = 0 :=
      selbergMultiplesCoord_eq_zero_of_notMem c (by simpa using h6)
    rw [Finset.erase_eq_of_notMem h6, hc]
    simp

/-- Variance orthogonal to the unique positive endpoint mode. -/
def varianceAwayFromSix (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ (Finset.Icc 2 N).erase 6,
    (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e)^2

/-- Defect in the universal half-decorrelation bound. -/
def halfDecorrelationDefect (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  sieveVariance N c - 2 *
    (bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2)

/-- Exact separation of the six-mode from the remaining variance. -/
theorem sieveVariance_eq_away_add_six (N : ℕ) (c : ℕ → ℝ) :
    sieveVariance N c = varianceAwayFromSix N c +
      2 * (selbergMultiplesCoord N c 6)^2 := by
  unfold sieveVariance varianceAwayFromSix
  rw [sum_selberg_diagonal_split_six, six_values.1]
  norm_num

/-- The half-decorrelation defect has a diagonal supported away from six. -/
theorem halfDecorrelationDefect_eq_diagonal (N : ℕ) (c : ℕ → ℝ) :
    halfDecorrelationDefect N c =
      ∑ e ∈ (Finset.Icc 2 N).erase 6,
        ((Nat.totient e : ℝ) - 2 * moebiusReal e) *
          (selbergMultiplesCoord N c e)^2 := by
  unfold halfDecorrelationDefect sieveVariance
  rw [bezout_sub_harmonic_sq_eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hz : ((Nat.totient 6 : ℝ) - 2 * moebiusReal 6) *
      (selbergMultiplesCoord N c 6)^2 = 0 := by
    rw [six_values.1, six_values.2]
    norm_num
  rw [Finset.sum_erase (Finset.Icc 2 N)
    (f := fun e : ℕ => ((Nat.totient e : ℝ) - 2 * moebiusReal e) *
      (selbergMultiplesCoord N c e)^2) (a := 6) hz]
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- Near half-decorrelation forces quantitative concentration on divisor six. -/
theorem varianceAwayFromSix_le_twice_defect (N : ℕ) (c : ℕ → ℝ) :
    varianceAwayFromSix N c ≤ 2 * halfDecorrelationDefect N c := by
  rw [halfDecorrelationDefect_eq_diagonal]
  unfold varianceAwayFromSix
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  obtain ⟨he6, heI⟩ := Finset.mem_erase.mp he
  have h := four_mul_moebiusReal_le_totient_of_ne_six
    (Finset.mem_Icc.mp heI).1 he6
  have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (selbergMultiplesCoord N c e))
  nlinarith

/-- Equality in half-decorrelation is exactly the constant-plus-six coordinate space. -/
theorem halfDecorrelationDefect_eq_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    halfDecorrelationDefect N c = 0 ↔
      ∀ e ∈ (Finset.Icc 2 N).erase 6, selbergMultiplesCoord N c e = 0 := by
  constructor
  · intro h
    have hle := varianceAwayFromSix_le_twice_defect N c
    rw [h, mul_zero] at hle
    have hnon : 0 ≤ varianceAwayFromSix N c := by
      exact Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hz : varianceAwayFromSix N c = 0 := le_antisymm hle hnon
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e (_ : e ∈ (Finset.Icc 2 N).erase 6) =>
        mul_nonneg (Nat.cast_nonneg (Nat.totient e) : (0 : ℝ) ≤ _) (sq_nonneg _))).mp hz
    intro e he
    have hp : 0 < (Nat.totient e : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr
        (show 0 < e from by have := (Finset.mem_Icc.mp (Finset.mem_erase.mp he).2).1; omega)
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (hterms e he)).resolve_left (ne_of_gt hp))
  · intro h
    rw [halfDecorrelationDefect_eq_diagonal]
    apply Finset.sum_eq_zero
    intro e he
    rw [h e he, zero_pow (by omega), mul_zero]

/-- The six-coordinate is the complete correction to the quarter bound. -/
theorem successor_quarter_bound_with_six_correction (N : ℕ) (c : ℕ → ℝ) :
    4 * (bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2) ≤
      sieveVariance N c + 2 * (selbergMultiplesCoord N c 6)^2 := by
  have h := varianceAwayFromSix_le_twice_defect N c
  have hs := sieveVariance_eq_away_add_six N c
  unfold halfDecorrelationDefect at h
  linarith

/-- Canonical projection deleting the exceptional six-coordinate. -/
def removeSixMode (N : ℕ) (c : ℕ → ℝ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff
    (fun e => if e = 6 then 0 else selbergMultiplesCoord N c e) N

/-- The projection changes exactly one coordinate, at every truncation level. -/
theorem selbergMultiplesCoord_removeSixMode (N e : ℕ) (c : ℕ → ℝ) :
    selbergMultiplesCoord N (removeSixMode N c) e =
      if e = 6 then 0 else selbergMultiplesCoord N c e := by
  unfold removeSixMode
  rw [selbergMultiplesCoord_ramanujan_inverse]
  by_cases he : e ∈ Finset.Icc 1 N
  · rw [if_pos he]
  · rw [if_neg he, selbergMultiplesCoord_eq_zero_of_notMem c he]
    simp

/-- Removing the exceptional mode is an actual idempotent operation on weights. -/
theorem removeSixMode_idempotent (N : ℕ) (c : ℕ → ℝ) :
    removeSixMode N (removeSixMode N c) = removeSixMode N c := by
  change pmRamanujanResidueCoeff _ N = pmRamanujanResidueCoeff _ N
  apply congrArg (fun y => pmRamanujanResidueCoeff y N)
  funext e
  rw [selbergMultiplesCoord_removeSixMode]
  split_ifs <;> rfl

/-- Removing six preserves the harmonic mean. -/
theorem finiteHarmonicSum_removeSixMode (N : ℕ) (c : ℕ → ℝ) :
    finiteHarmonicSum N (removeSixMode N c) = finiteHarmonicSum N c := by
  rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    selbergMultiplesCoord_removeSixMode]
  simp [selbergMultiplesCoord_one_eq_finiteHarmonicSum]

/-- Exact variance left after removing the endpoint mode. -/
theorem sieveVariance_removeSixMode (N : ℕ) (c : ℕ → ℝ) :
    sieveVariance N (removeSixMode N c) = varianceAwayFromSix N c := by
  unfold sieveVariance varianceAwayFromSix
  rw [← Finset.sum_erase (Finset.Icc 2 N)
    (f := fun e : ℕ => (Nat.totient e : ℝ) *
      (selbergMultiplesCoord N (removeSixMode N c) e)^2) (a := 6)
    (show (Nat.totient 6 : ℝ) * (selbergMultiplesCoord N (removeSixMode N c) 6)^2 = 0
      from by simp [selbergMultiplesCoord_removeSixMode])]
  apply Finset.sum_congr rfl
  intro e he
  rw [selbergMultiplesCoord_removeSixMode, if_neg (Finset.mem_erase.mp he).1]

/-- The exact covariance removed is the square of the six-coordinate. -/
theorem successor_covariance_removeSixMode (N : ℕ) (c : ℕ → ℝ) :
    bezoutCoprimeQuadraticForm N (removeSixMode N c) -
        (finiteHarmonicSum N (removeSixMode N c))^2 =
      bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2 -
        (selbergMultiplesCoord N c 6)^2 := by
  rw [bezout_sub_harmonic_sq_eq, bezout_sub_harmonic_sq_eq,
    sum_selberg_diagonal_split_six, sum_selberg_diagonal_split_six]
  have hzero : selbergMultiplesCoord N (removeSixMode N c) 6 = 0 := by
    simp [selbergMultiplesCoord_removeSixMode]
  rw [hzero, six_values.2]
  simp only [zero_pow (show (2 : ℕ) ≠ 0 by omega), mul_zero, add_zero, one_mul]
  have hs : (∑ e ∈ (Finset.Icc 2 N).erase 6,
      moebiusReal e * (selbergMultiplesCoord N (removeSixMode N c) e)^2) =
      ∑ e ∈ (Finset.Icc 2 N).erase 6, moebiusReal e * (selbergMultiplesCoord N c e)^2 := by
    apply Finset.sum_congr rfl
    intro e he
    rw [selbergMultiplesCoord_removeSixMode, if_neg (Finset.mem_erase.mp he).1]
  rw [hs]
  ring

/-- An unconditional quarter-decorrelation bound on canonically projected weights. -/
theorem removeSixMode_quarter_decorrelation (N : ℕ) (c : ℕ → ℝ) :
    4 * (bezoutCoprimeQuadraticForm N (removeSixMode N c) -
      (finiteHarmonicSum N (removeSixMode N c))^2) ≤
        sieveVariance N (removeSixMode N c) := by
  have h := successor_quarter_bound_with_six_correction N (removeSixMode N c)
  simpa [selbergMultiplesCoord_removeSixMode] using h


/-- Both original quadratic forms lose precisely their six-mode contributions. -/
theorem removeSixMode_form_losses (N : ℕ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N (removeSixMode N c) =
        selbergTotientDiagonalForm N c - 2 * (selbergMultiplesCoord N c 6)^2 ∧
      bezoutCoprimeQuadraticForm N (removeSixMode N c) =
        bezoutCoprimeQuadraticForm N c - (selbergMultiplesCoord N c 6)^2 := by
  have hm := finiteHarmonicSum_removeSixMode N c
  have hv := sieveVariance_removeSixMode N c
  have hs := sieveVariance_eq_away_add_six N c
  have hb := successor_covariance_removeSixMode N c
  have hS := selberg_eq_harmonic_sq_add_variance N c
  have hS' := selberg_eq_harmonic_sq_add_variance N (removeSixMode N c)
  rw [hm] at hb hS'
  constructor <;> linarith

private theorem ten_values : Nat.totient 10 = 4 ∧ moebiusReal 10 = 1 := by
  have hcop : Nat.Coprime 2 5 := Nat.coprime_two_left.mpr ⟨2, rfl⟩
  constructor
  · change Nat.totient (2 * 5) = 4
    rw [Nat.totient_mul hcop, Nat.totient_prime Nat.prime_two,
      Nat.totient_prime Nat.prime_five]
  · unfold moebiusReal
    change ((moebius (2 * 5) : ℤ) : ℝ) = 1
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two,
      ArithmeticFunction.moebius_apply_prime Nat.prime_five]
    norm_num

/-- Symbolic extremizers for the next gap, realized by the finite inverse. -/
def successorTenModeWeight (N : ℕ) (t : ℝ) : ℕ → ℝ :=
  pmRamanujanResidueCoeff (fun e => if e = 10 then t else 0) (N + 10)

/-- The divisor-ten family realizes the quarter endpoint at every level at least ten. -/
theorem successorTenModeWeight_moments (N : ℕ) (t : ℝ) :
    finiteHarmonicSum (N + 10) (successorTenModeWeight N t) = 0 ∧
      sieveVariance (N + 10) (successorTenModeWeight N t) = 4 * t^2 ∧
      bezoutCoprimeQuadraticForm (N + 10) (successorTenModeWeight N t) = t^2 ∧
      selbergMultiplesCoord (N + 10) (successorTenModeWeight N t) 6 = 0 := by
  have hsum (w : ℕ → ℝ) :
      (∑ e ∈ Finset.Icc 1 (N + 10), w e * (if e = 10 then t else 0)^2) =
        w 10 * t^2 := by
    calc
      _ = ∑ e ∈ Finset.Icc 1 (N + 10), if e = 10 then w 10 * t^2 else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        by_cases h : e = 10
        · subst e; simp
        · simp [h]
      _ = _ := by simp
  have hH : finiteHarmonicSum (N + 10) (successorTenModeWeight N t) = 0 := by
    rw [← selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    unfold successorTenModeWeight
    rw [selbergMultiplesCoord_ramanujan_inverse]
    simp
  have hS : selbergTotientDiagonalForm (N + 10) (successorTenModeWeight N t) =
      4 * t^2 := by
    unfold successorTenModeWeight
    rw [selbergForm_ramanujan_inverse, hsum, ten_values.1]
    norm_num
  refine ⟨hH, ?_, ?_, ?_⟩
  · have h := selberg_eq_harmonic_sq_add_variance (N + 10) (successorTenModeWeight N t)
    rw [hH, hS] at h
    linarith
  · unfold successorTenModeWeight
    rw [bezoutForm_ramanujan_inverse, hsum, ten_values.2, one_mul]
  · unfold successorTenModeWeight
    rw [selbergMultiplesCoord_ramanujan_inverse]
    simp

/-- The divisor-ten witness remains an extremizer after the canonical projection. -/
theorem successorTenModeWeight_projected_moments (N : ℕ) (t : ℝ) :
    sieveVariance (N + 10) (removeSixMode (N + 10) (successorTenModeWeight N t)) =
        4 * t^2 ∧
      bezoutCoprimeQuadraticForm (N + 10)
          (removeSixMode (N + 10) (successorTenModeWeight N t)) -
        (finiteHarmonicSum (N + 10)
          (removeSixMode (N + 10) (successorTenModeWeight N t)))^2 = t^2 := by
  obtain ⟨hH, hV, hB, h6⟩ := successorTenModeWeight_moments N t
  have hv := sieveVariance_eq_away_add_six (N + 10) (successorTenModeWeight N t)
  have hb := successor_covariance_removeSixMode (N + 10) (successorTenModeWeight N t)
  rw [hV, h6] at hv
  rw [hH, hB, h6] at hb
  constructor
  · rw [sieveVariance_removeSixMode]
    linarith
  · simpa using hb

/-- Complete classification of universal upper constants after deleting the six-mode. -/
theorem universal_removeSixMode_covariance_bound_iff (K : ℝ) :
    (∀ (N : ℕ) (c : ℕ → ℝ),
      bezoutCoprimeQuadraticForm N (removeSixMode N c) -
          (finiteHarmonicSum N (removeSixMode N c))^2 ≤
        K * sieveVariance N (removeSixMode N c)) ↔ (1 : ℝ) / 4 ≤ K := by
  constructor
  · intro h
    have htest := h 10 (successorTenModeWeight 0 1)
    obtain ⟨hv, hc⟩ := successorTenModeWeight_projected_moments 0 1
    change sieveVariance 10 (removeSixMode 10 (successorTenModeWeight 0 1)) = _ at hv
    change bezoutCoprimeQuadraticForm 10 (removeSixMode 10 (successorTenModeWeight 0 1)) -
      (finiteHarmonicSum 10 (removeSixMode 10 (successorTenModeWeight 0 1)))^2 = _ at hc
    rw [hv, hc] at htest
    linarith
  · intro hK N c
    have hv : 0 ≤ sieveVariance N (removeSixMode N c) :=
      Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have h := removeSixMode_quarter_decorrelation N c
    have hmul := mul_le_mul_of_nonneg_right hK hv
    linarith

/-- The stability factor two is optimal among all universal factors. -/
theorem universal_six_mode_stability_factor_iff (K : ℝ) :
    (∀ (N : ℕ) (c : ℕ → ℝ),
      varianceAwayFromSix N c ≤ K * halfDecorrelationDefect N c) ↔ 2 ≤ K := by
  constructor
  · intro h
    have htest := h 10 (successorTenModeWeight 0 1)
    obtain ⟨hH, hV, hB, h6⟩ := successorTenModeWeight_moments 0 1
    have hv := sieveVariance_eq_away_add_six 10 (successorTenModeWeight 0 1)
    change finiteHarmonicSum 10 (successorTenModeWeight 0 1) = 0 at hH
    change sieveVariance 10 (successorTenModeWeight 0 1) = 4 * 1^2 at hV
    change bezoutCoprimeQuadraticForm 10 (successorTenModeWeight 0 1) = 1^2 at hB
    change selbergMultiplesCoord 10 (successorTenModeWeight 0 1) 6 = 0 at h6
    rw [hV, h6] at hv
    unfold halfDecorrelationDefect at htest
    rw [hV, hH, hB] at htest
    nlinarith
  · intro hK N c
    have h := varianceAwayFromSix_le_twice_defect N c
    have hv : 0 ≤ varianceAwayFromSix N c :=
      Finset.sum_nonneg fun e _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hd : 0 ≤ halfDecorrelationDefect N c := by linarith
    exact h.trans (mul_le_mul_of_nonneg_right hK hd)

end
end GaloisForLFunctions.BezoutValuationIncidence
