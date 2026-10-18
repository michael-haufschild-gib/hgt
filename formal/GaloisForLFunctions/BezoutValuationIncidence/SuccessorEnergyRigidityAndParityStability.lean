import GaloisForLFunctions.BezoutValuationIncidence.BezoutSelbergDiagonalCoercivityAndHalfDecorrelation

/-!
# Successor energy rigidity and parity stability

For arbitrary finite sieve weights, the successor Dirichlet energy has exactly the constant
response as its kernel. The opposite spectral endpoint has exactly the constant and parity
responses as its kernel. Both classifications hold at every sieve level, including zero.

Writing `H = finiteHarmonicSum N c`, `V = sieveVariance N c`, `S` for the Selberg form and
`B` for the Bézout successor form, the universal bounds are `-V ≤ B - H² ≤ V / 2` and
`V ≤ 2(S - B) ≤ 4V`. The defect `S + B - 2H²` controls half the variance above parity.
The proof uses the simultaneous totient–Möbius diagonals and descending inversion of the
truncated multiples transform; the latter transfers spectral rigidity to the original weights.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- Vanishing above a cutoff is preserved and reflected by the truncated multiples transform. -/
theorem selbergMultiplesCoord_tail_zero_iff (N r : ℕ) (c : ℕ → ℝ) :
    (∀ e ∈ Finset.Icc (r + 1) N, selbergMultiplesCoord N c e = 0) ↔
      (∀ d ∈ Finset.Icc (r + 1) N, c d = 0) := by
  constructor
  · intro h
    suffices ∀ t d : ℕ, N - d = t → r + 1 ≤ d → d ≤ N → c d = 0 by
      intro d hd
      exact this (N - d) d rfl (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro d htd hdr hdN
      have hdpos : 0 < d := by omega
      have heval : selbergMultiplesCoord N c d = c d / (d : ℝ) := by
        unfold selbergMultiplesCoord
        apply Finset.sum_eq_single d
        · intro b hb hbd
          obtain ⟨hbI, hdb⟩ := Finset.mem_filter.mp hb
          obtain ⟨hbpos, hbN⟩ := Finset.mem_Icc.mp hbI
          have hdb_le : d ≤ b := Nat.le_of_dvd hbpos hdb
          have hcb := ih (N - b) (by omega) b rfl (by omega) hbN
          rw [hcb, zero_div]
        · intro hnot
          exact (hnot (Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hdpos, hdN⟩, dvd_refl d⟩)).elim
      have hz : c d / (d : ℝ) = 0 := by
        rw [← heval]
        exact h d (Finset.mem_Icc.mpr ⟨hdr, hdN⟩)
      exact (div_eq_zero_iff.mp hz).resolve_right (by exact_mod_cast hdpos.ne')
  · intro h e he
    unfold selbergMultiplesCoord
    apply Finset.sum_eq_zero
    intro d hd
    obtain ⟨hdI, hed⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdpos, hdN⟩ := Finset.mem_Icc.mp hdI
    have hed_le : e ≤ d := Nat.le_of_dvd hdpos hed
    rw [h d (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp he).1; omega, hdN⟩), zero_div]

/-- The successor energy has no kernel beyond the constant divisor response. -/
theorem selberg_eq_bezout_iff_weight_tail_zero (N : ℕ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c = bezoutCoprimeQuadraticForm N c ↔
      ∀ d ∈ Finset.Icc 2 N, c d = 0 := by
  rcases N with _ | N
  · simp [selbergTotientDiagonalForm, bezoutCoprimeQuadraticForm]
  · rw [← sub_eq_zero, selbergSubBezoutQuadraticForm_eq_Icc_two (by omega)]
    have hpos : ∀ e ∈ Finset.Icc 2 (N + 1),
        0 < (Nat.totient e : ℝ) - moebiusReal e := by
      intro e he
      have hgap := (two_mul_moebiusReal_le_totient (Finset.mem_Icc.mp he).1).2
      linarith
    have hzero : (∑ e ∈ Finset.Icc 2 (N + 1),
        ((Nat.totient e : ℝ) - moebiusReal e) * (selbergMultiplesCoord (N + 1) c e)^2) = 0 ↔
        ∀ e ∈ Finset.Icc 2 (N + 1), selbergMultiplesCoord (N + 1) c e = 0 := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun e he => mul_nonneg (hpos e he).le (sq_nonneg _))]
      constructor
      · intro h e he
        exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h e he)).resolve_left (hpos e he).ne')
      · intro h e he
        rw [h e he, zero_pow (by omega), mul_zero]
    exact hzero.trans (selbergMultiplesCoord_tail_zero_iff (N + 1) 1 c)

/-- The constant-mode-free Selberg variance. -/
def sieveVariance (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ e ∈ Finset.Icc 2 N, (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e)^2

/-- Separating the harmonic mode gives the exact variance identity, including level zero. -/
theorem selberg_eq_harmonic_sq_add_variance (N : ℕ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c = (finiteHarmonicSum N c)^2 + sieveVariance N c := by
  rcases N with _ | N
  · simp [selbergTotientDiagonalForm, finiteHarmonicSum, sieveVariance]
  · have hI : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    unfold selbergTotientDiagonalForm sieveVariance
    rw [hI, Finset.sum_insert (by simp), Nat.totient_one, Nat.cast_one, one_mul,
      selbergMultiplesCoord_one_eq_finiteHarmonicSum]

/-- The successor covariance has precisely the nonconstant Möbius diagonal. -/
theorem bezout_sub_harmonic_sq_eq (N : ℕ) (c : ℕ → ℝ) :
    bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2 =
      ∑ e ∈ Finset.Icc 2 N, moebiusReal e * (selbergMultiplesCoord N c e)^2 := by
  rcases N with _ | N
  · simp [bezoutCoprimeQuadraticForm, finiteHarmonicSum]
  · have hI : Finset.Icc 1 (N + 1) = insert 1 (Finset.Icc 2 (N + 1)) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [bezoutCoprimeQuadraticForm_eq_moebius_diagonal, hI,
      Finset.sum_insert (by simp), selbergMultiplesCoord_one_eq_finiteHarmonicSum]
    simp [moebiusReal]

/-- The Möbius diagonal never lies below minus one. -/
theorem neg_one_le_moebiusReal (e : ℕ) : -1 ≤ moebiusReal e := by
  have h := (moebiusReal_le_one e).1
  nlinarith [sq_nonneg (moebiusReal e + 1)]

/-- A universal two-sided successor spectral bound, with no harmonic-cancellation premise. -/
theorem successor_covariance_bounds (N : ℕ) (c : ℕ → ℝ) :
    -sieveVariance N c ≤ bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2 ∧
      2 * (bezoutCoprimeQuadraticForm N c - (finiteHarmonicSum N c)^2) ≤
        sieveVariance N c := by
  rw [bezout_sub_harmonic_sq_eq]
  unfold sieveVariance
  constructor
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro e he
    have hep : 0 < e := by have := (Finset.mem_Icc.mp he).1; omega
    have ht : (1 : ℝ) ≤ (Nat.totient e : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hep
    have hm := neg_one_le_moebiusReal e
    have hs := sq_nonneg (selbergMultiplesCoord N c e)
    nlinarith
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have ht := (two_mul_moebiusReal_le_totient (Finset.mem_Icc.mp he).1).1
    have hs := sq_nonneg (selbergMultiplesCoord N c e)
    nlinarith

/-- The Dirichlet energy density is equivalent to variance with universal constants one and four. -/
theorem successor_energy_variance_bounds (N : ℕ) (c : ℕ → ℝ) :
    sieveVariance N c ≤ 2 * (selbergTotientDiagonalForm N c - bezoutCoprimeQuadraticForm N c) ∧
      2 * (selbergTotientDiagonalForm N c - bezoutCoprimeQuadraticForm N c) ≤
        4 * sieveVariance N c := by
  have h := successor_covariance_bounds N c
  rw [selberg_eq_harmonic_sq_add_variance]
  constructor <;> linarith

/-- All modes above parity have a positive plus-diagonal, bounded below by half their variance. -/
theorem half_totient_le_totient_add_moebiusReal {e : ℕ} (he : 3 ≤ e) :
    (Nat.totient e : ℝ) ≤ 2 * ((Nat.totient e : ℝ) + moebiusReal e) ∧
      1 ≤ (Nat.totient e : ℝ) + moebiusReal e := by
  have hp : 0 < Nat.totient e := Nat.totient_pos.mpr (by omega)
  have heven : 2 ∣ Nat.totient e := even_iff_two_dvd.mp (Nat.totient_even he)
  have ht : (2 : ℝ) ≤ (Nat.totient e : ℝ) := by
    exact_mod_cast Nat.le_of_dvd hp heven
  have hm := neg_one_le_moebiusReal e
  constructor <;> linarith

/-- The negative-endpoint defect removes both the constant and parity modes exactly. -/
theorem selberg_add_bezout_sub_two_harmonic_sq_eq (N : ℕ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c + bezoutCoprimeQuadraticForm N c -
        2 * (finiteHarmonicSum N c)^2 =
      ∑ e ∈ Finset.Icc 3 N,
        ((Nat.totient e : ℝ) + moebiusReal e) * (selbergMultiplesCoord N c e)^2 := by
  have hm2 : moebiusReal 2 = -1 := by
    simp [moebiusReal, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hsum : selbergTotientDiagonalForm N c + bezoutCoprimeQuadraticForm N c -
      2 * (finiteHarmonicSum N c)^2 =
      ∑ e ∈ Finset.Icc 2 N,
        ((Nat.totient e : ℝ) + moebiusReal e) * (selbergMultiplesCoord N c e)^2 := by
    rw [selberg_eq_harmonic_sq_add_variance]
    have hb := bezout_sub_harmonic_sq_eq N c
    unfold sieveVariance
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    linarith
  rw [hsum]
  symm
  apply Finset.sum_subset
  · intro e he
    obtain ⟨hel, heu⟩ := Finset.mem_Icc.mp he
    exact Finset.mem_Icc.mpr ⟨by omega, heu⟩
  · intro e he hnot
    have he2 : e = 2 := by
      simp only [Finset.mem_Icc] at he hnot
      omega
    subst e
    rw [Nat.totient_two, Nat.cast_one, hm2]
    ring

/-- Maximal negative covariance forces all weights above the parity divisor to vanish. -/
theorem successor_anticorrelation_iff_weight_tail_zero (N : ℕ) (c : ℕ → ℝ) :
    selbergTotientDiagonalForm N c + bezoutCoprimeQuadraticForm N c =
        2 * (finiteHarmonicSum N c)^2 ↔
      ∀ d ∈ Finset.Icc 3 N, c d = 0 := by
  rw [← sub_eq_zero, selberg_add_bezout_sub_two_harmonic_sq_eq]
  have hpos : ∀ e ∈ Finset.Icc 3 N, 0 < (Nat.totient e : ℝ) + moebiusReal e := by
    intro e he
    have h := (half_totient_le_totient_add_moebiusReal (Finset.mem_Icc.mp he).1).2
    linarith
  have hzero : (∑ e ∈ Finset.Icc 3 N,
      ((Nat.totient e : ℝ) + moebiusReal e) * (selbergMultiplesCoord N c e)^2) = 0 ↔
      ∀ e ∈ Finset.Icc 3 N, selbergMultiplesCoord N c e = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun e he => mul_nonneg (hpos e he).le (sq_nonneg _))]
    constructor
    · intro h e he
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h e he)).resolve_left (hpos e he).ne')
    · intro h e he
      rw [h e he, zero_pow (by omega), mul_zero]
  exact hzero.trans (selbergMultiplesCoord_tail_zero_iff N 2 c)

/-- Near maximal anticorrelation quantitatively forces concentration on the parity mode. -/
theorem variance_above_parity_le_anticorrelation_defect (N : ℕ) (c : ℕ → ℝ) :
    (∑ e ∈ Finset.Icc 3 N, (Nat.totient e : ℝ) * (selbergMultiplesCoord N c e)^2) ≤
      2 * (selbergTotientDiagonalForm N c + bezoutCoprimeQuadraticForm N c -
        2 * (finiteHarmonicSum N c)^2) := by
  rw [selberg_add_bezout_sub_two_harmonic_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e he
  have h := (half_totient_le_totient_add_moebiusReal (Finset.mem_Icc.mp he).1).1
  have hs := sq_nonneg (selbergMultiplesCoord N c e)
  nlinarith

end
end GaloisForLFunctions.BezoutValuationIncidence
