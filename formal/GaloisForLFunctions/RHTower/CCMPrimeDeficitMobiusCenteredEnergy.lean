import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationUniformBound
import GaloisForLFunctions.RHTower.CCMPrimeDeficitDilationInversion

/-!
# The actual Möbius reconstruction with its bounded centered diagonal

The uniformly bounded elementary remainder is reconstructed with the
literal Möbius signs. The exponential and logarithmic main terms remain
in one explicit work. The centered diagonal is uniformly bounded at the
critical normalization; every cross term, including work against the
explicit main terms, remains in the signed remainder.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitMobiusExplicitWork (T : ℝ) : ℝ :=
  (Real.eulerMascheroniConstant + 1) *
    (Real.exp T * (∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, moebiusCoeff n / n) -
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, moebiusCoeff n) -
    Real.log (2 * Real.pi) / 2 *
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, moebiusCoeff n * (T - Real.log n)

def ccmPrimeDeficitMobiusCenteredWork (T : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
    moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)

def ccmPrimeDeficitMobiusCenteredDiagonal (T : ℝ) : ℝ :=
  Real.exp (-T) * ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
    (moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)) ^ 2

def ccmPrimeDeficitMobiusSignedCross (T : ℝ) : ℝ :=
  Real.exp (-T) *
    (ccmPrimeDeficitMobiusExplicitWork T ^ 2 +
      2 * ccmPrimeDeficitMobiusExplicitWork T * ccmPrimeDeficitMobiusCenteredWork T +
      (ccmPrimeDeficitMobiusCenteredWork T ^ 2 -
        ∑ n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
          (moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)) ^ 2))

/-- The exact signed inverse retains both explicit main channels together
with the complete bounded-remainder reconstruction. -/
theorem ccmLogChebyshevDeficitPrimitive_eq_moebius_centered_work {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      ccmPrimeDeficitMobiusExplicitWork T + ccmPrimeDeficitMobiusCenteredWork T := by
  rw [ccmLogChebyshevDeficitPrimitive_eq_moebius_dilation hT,
    ccmPrimeDeficitMobiusExplicitWork, ccmPrimeDeficitMobiusCenteredWork]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  rw [ccmPrimeDeficitDilationRemainder, Real.exp_sub, Real.exp_log hnpos]
  unfold moebiusCoeff
  ring

theorem ccmPrimeDeficitMobiusCenteredDiagonal_nonneg (T : ℝ) :
    0 ≤ ccmPrimeDeficitMobiusCenteredDiagonal T := by
  unfold ccmPrimeDeficitMobiusCenteredDiagonal
  positivity

/-- The complete diagonal of the critically normalized centered inverse
has a constant budget, at every real time and every terminal cutoff. -/
theorem ccmPrimeDeficitMobiusCenteredDiagonal_le (T : ℝ) :
    ccmPrimeDeficitMobiusCenteredDiagonal T ≤ 49 / 4 := by
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊Real.exp T⌋₊) :
      (moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)) ^ 2 ≤ 49 / 4 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hlog : Real.log n ≤ T := (Real.log_le_iff_le_exp hnpos).mpr
      ((Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Icc.mp hn).2)
    have hab : |moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)| ≤ 7 / 2 := by
      rw [abs_mul]
      have h := mul_le_mul (abs_moebiusCoeff_le_one n)
        (abs_ccmPrimeDeficitDilationRemainder_le_uniform (sub_nonneg.mpr hlog))
          (abs_nonneg _) zero_le_one
      simpa only [one_mul] using h
    calc
      _ = |moebiusCoeff n * ccmPrimeDeficitDilationRemainder (T - Real.log n)| ^ 2 := (sq_abs _).symm
      _ ≤ (7 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hab 2
      _ = _ := by ring
  have hs := Finset.sum_le_sum hterm
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hs
  have hc : Real.exp (-T) * Real.exp T = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  unfold ccmPrimeDeficitMobiusCenteredDiagonal
  calc
    _ ≤ Real.exp (-T) * ((⌊Real.exp T⌋₊ : ℝ) * (49 / 4)) :=
      mul_le_mul_of_nonneg_left hs (Real.exp_pos (-T)).le
    _ ≤ Real.exp (-T) * (Real.exp T * (49 / 4)) := by
      gcongr
      exact Nat.floor_le (Real.exp_pos T).le
    _ = _ := by rw [← mul_assoc, hc, one_mul]

/-- Exact full critical energy. The constant diagonal bound has not
discarded any signed cross interaction or either explicit main term. -/
theorem ccmPrimeDeficitCriticalEnergy_eq_moebius_diagonal_add_signed_cross {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCriticalEnergy T =
      ccmPrimeDeficitMobiusCenteredDiagonal T + ccmPrimeDeficitMobiusSignedCross T := by
  rw [ccmPrimeDeficitCriticalEnergy,
    ccmLogChebyshevDeficitPrimitive_eq_moebius_centered_work hT,
    ccmPrimeDeficitMobiusCenteredDiagonal, ccmPrimeDeficitMobiusSignedCross]
  ring

end RHTower
