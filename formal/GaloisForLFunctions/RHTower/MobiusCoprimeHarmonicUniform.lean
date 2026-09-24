import GaloisForLFunctions.RHTower.MobiusFirstPrimeDilationCancellation
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeColumnCancellation
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Uniform moving-modulus Möbius harmonic cancellation

The coprime Möbius floor column is an exact count of integers supported on
the modulus's prime factors. Splitting `N/d` into quotient and remainder
bounds its reciprocal Möbius sum uniformly in *both* modulus and cutoff.
This is a signed arithmetic estimate, not an RH premise.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace RHTower

noncomputable def coprimeMobiusHarmonic (r N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (if r.Coprime d then ((μ d : ℤ) : ℝ) else 0) / (d : ℝ)

private noncomputable def coprimeMobiusRemainder (r N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (if r.Coprime d then ((μ d : ℤ) : ℝ) else 0) *
      ((N % d : ℕ) : ℝ) / (d : ℝ)

/-- Exact quotient--remainder splitting of the coprime Möbius harmonic sum. -/
private theorem coprimeMobiusHarmonic_floor_split (r N : ℕ) :
    (N : ℝ) * coprimeMobiusHarmonic r N =
      ((Sieve.primeSupportedIcc r N).card : ℝ) +
        coprimeMobiusRemainder r N := by
  rw [coprimeMobiusHarmonic, coprimeMobiusRemainder, Finset.mul_sum,
    ← DeletionCoprimeColumn.complete_floor_column r N, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hkey : (d:ℝ) * (((N/d:ℕ):ℝ)) + (((N%d:ℕ):ℝ)) = (N:ℝ) := by
    exact_mod_cast Nat.div_add_mod N d
  calc
    (N:ℝ) * ((if r.Coprime d then ((μ d:ℤ):ℝ) else 0)/(d:ℝ)) =
      (if r.Coprime d then ((μ d:ℤ):ℝ) else 0) * ((N:ℝ)/(d:ℝ)) := by ring
    _ = (if r.Coprime d then ((μ d:ℤ):ℝ) else 0) *
      ((((N/d:ℕ):ℝ)) + (((N%d:ℕ):ℝ))/(d:ℝ)) := by
        congr 1
        rw [← hkey, add_div, mul_div_cancel_left₀ _ hd0.ne']
    _ = (if r.Coprime d then ((μ d:ℤ):ℝ) else 0) * ((N/d:ℕ):ℝ) +
      (if r.Coprime d then ((μ d:ℤ):ℝ) else 0) * ((N%d:ℕ):ℝ)/(d:ℝ) := by ring

/-- The quotient remainder costs at most one copy of the cutoff. -/
private theorem coprimeMobiusRemainder_abs_le (r N : ℕ) :
    |coprimeMobiusRemainder r N| ≤ (N:ℝ) := by
  unfold coprimeMobiusRemainder
  calc
    |∑ d ∈ Finset.Icc 1 N,
       (if r.Coprime d then ((μ d:ℤ):ℝ) else 0) * ((N%d:ℕ):ℝ)/(d:ℝ)| ≤
      ∑ d ∈ Finset.Icc 1 N,
       |(if r.Coprime d then ((μ d:ℤ):ℝ) else 0) * ((N%d:ℕ):ℝ)/(d:ℝ)| :=
         Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 N, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hcop : r.Coprime d
      · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hd).1
        have hμ : |((μ d:ℤ):ℝ)| ≤ 1 := by
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d)
        have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
        have hratio : ((N%d:ℕ):ℝ)/(d:ℝ) ≤ 1 :=
          (div_le_one hdR).2 (by exact_mod_cast (Nat.mod_lt N hdpos).le)
        have hratio0 : 0 ≤ ((N%d:ℕ):ℝ)/(d:ℝ) := by positivity
        rw [if_pos hcop]
        calc
          |((μ d:ℤ):ℝ) * ((N%d:ℕ):ℝ)/(d:ℝ)| =
            |((μ d:ℤ):ℝ)| * (((N%d:ℕ):ℝ)/(d:ℝ)) := by
              simp only [abs_div, abs_mul,
                abs_of_nonneg (show (0:ℝ) ≤ ((N%d:ℕ):ℝ) from Nat.cast_nonneg _),
                abs_of_pos hdR]
              ring
          _ ≤ 1*1 := mul_le_mul hμ hratio hratio0 (by norm_num)
          _ = 1 := by ring
      · simp [hcop]
    _ = (N:ℝ) := by simp

/-- The signed reciprocal Möbius sum remains bounded even when the coprimality
modulus moves arbitrarily with the cutoff. -/
theorem abs_coprimeMobiusHarmonic_le_two (r N : ℕ) (hN : 1 ≤ N) :
    |coprimeMobiusHarmonic r N| ≤ 2 := by
  classical
  have hS : ((Sieve.primeSupportedIcc r N).card : ℝ) ≤ (N:ℝ) := by
    have hsub : Sieve.primeSupportedIcc r N ⊆ Finset.Icc 1 N := by
      unfold Sieve.primeSupportedIcc
      exact Finset.filter_subset _ _
    have hcard := Finset.card_le_card hsub
    exact_mod_cast (by simpa [Sieve.primeSupportedIcc] using hcard)
  have hR := coprimeMobiusRemainder_abs_le r N
  have hsplit := coprimeMobiusHarmonic_floor_split r N
  have hNpos : (0:ℝ)<(N:ℝ) := by exact_mod_cast hN
  have hbound : (N:ℝ)*|coprimeMobiusHarmonic r N| ≤ (N:ℝ)*2 := by
    calc
      (N:ℝ)*|coprimeMobiusHarmonic r N| =
        |(N:ℝ)*coprimeMobiusHarmonic r N| := by
          rw [abs_mul, abs_of_pos hNpos]
      _ = |((Sieve.primeSupportedIcc r N).card:ℝ)+coprimeMobiusRemainder r N| := by
          rw [hsplit]
      _ ≤
        |((Sieve.primeSupportedIcc r N).card:ℝ)|+|coprimeMobiusRemainder r N| :=
          abs_add_le _ _
      _ ≤ (N:ℝ)*2 := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]
        linarith
  by_contra h
  have hh : 0 < |coprimeMobiusHarmonic r N|-2 := by linarith
  nlinarith [mul_pos hNpos hh]

noncomputable def coprimeMobiusShiftedHarmonic (r N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (if r.Coprime d then ((μ d : ℤ) : ℝ) else 0) / ((d : ℝ) + 1)

private noncomputable def coprimeMobiusShiftCorrection (r N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N,
    (if r.Coprime d then ((μ d : ℤ) : ℝ) else 0) /
      ((d : ℝ) * ((d : ℝ) + 1))

private theorem sum_reciprocal_adjacent (N : ℕ) :
    (∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1))) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
      have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hN' : (0 : ℝ) < (N : ℝ) + 2 := by positivity
      push_cast
      field_simp
      ring

private theorem coprimeMobiusShiftCorrection_abs_le_one (r N : ℕ) :
    |coprimeMobiusShiftCorrection r N| ≤ 1 := by
  unfold coprimeMobiusShiftCorrection
  calc
    |∑ d ∈ Finset.Icc 1 N,
      (if r.Coprime d then ((μ d : ℤ) : ℝ) else 0) /
        ((d : ℝ) * ((d : ℝ) + 1))| ≤
      ∑ d ∈ Finset.Icc 1 N,
        |(if r.Coprime d then ((μ d : ℤ) : ℝ) else 0) /
          ((d : ℝ) * ((d : ℝ) + 1))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N,
        (1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : (0 : ℝ) < (d : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hd).1
      have hden : (0 : ℝ) < (d : ℝ) * ((d : ℝ) + 1) := by positivity
      have hμ : |(if r.Coprime d then ((μ d : ℤ) : ℝ) else 0)| ≤ 1 := by
        split_ifs
        · rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        · norm_num
      rw [abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right hμ hden.le
    _ ≤ 1 := by
      rw [sum_reciprocal_adjacent]
      have : (0 : ℝ) ≤ 1 / ((N : ℝ) + 1) := by positivity
      linarith

private theorem coprimeMobiusShiftedHarmonic_eq (r N : ℕ) :
    coprimeMobiusShiftedHarmonic r N =
      coprimeMobiusHarmonic r N - coprimeMobiusShiftCorrection r N := by
  unfold coprimeMobiusShiftedHarmonic coprimeMobiusHarmonic
    coprimeMobiusShiftCorrection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hdpos' : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  field_simp
  ring

/-- The ratio kernel `1/(d+1)` has a signed Möbius bound uniform in both
cutoff and coprimality modulus. -/
theorem abs_coprimeMobiusShiftedHarmonic_le_three (r N : ℕ) :
    |coprimeMobiusShiftedHarmonic r N| ≤ 3 := by
  by_cases hN : 1 ≤ N
  · rw [coprimeMobiusShiftedHarmonic_eq]
    have hH := abs_coprimeMobiusHarmonic_le_two r N hN
    have hC := coprimeMobiusShiftCorrection_abs_le_one r N
    linarith [abs_sub (coprimeMobiusHarmonic r N)
      (coprimeMobiusShiftCorrection r N)]
  · have : N = 0 := by omega
    subst N
    simp [coprimeMobiusShiftedHarmonic]

/-- One oriented integer-dilation ray in the boundary Gamma--Hankel matrix;
`q=1` is retained here as a single diagonal entry. -/
noncomputable def fixedCofactorGammaRay (d N : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 N,
    2 * mobiusRealCoefficient d * mobiusRealCoefficient (d * q) /
      (((q : ℝ) + 1) * (d : ℝ))

theorem fixedCofactorGammaRay_eq_matrixSubsum (d N : ℕ) (hd : 1 ≤ d) :
    fixedCofactorGammaRay d N =
      ∑ q ∈ Finset.Icc 1 N,
        2 * shiftedMobiusRealCoefficient (d - 1) *
          shiftedMobiusRealCoefficient (d * q - 1) /
          (((d - 1) + (d * q - 1) + 2 : ℕ) : ℝ) := by
  unfold fixedCofactorGammaRay
  apply Finset.sum_congr rfl
  intro q hq
  have hq1 := (Finset.mem_Icc.mp hq).1
  simpa only [Nat.mul_comm q d] using (gamma_prime_pair_atom q d hq1 hd).symm

/-- The complete ratio ray, unlike its prime-only subfamily, has bounded
signed coefficient for every squarefree cofactor and moving cutoff. -/
theorem fixedCofactorGammaRay_eq (d N : ℕ) (hd : 1 ≤ d)
    (hsf : Squarefree d) :
    fixedCofactorGammaRay d N =
      (2 / (d : ℝ)) * coprimeMobiusShiftedHarmonic d N := by
  unfold fixedCofactorGammaRay coprimeMobiusShiftedHarmonic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hqpos : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  by_cases hcop : d.Coprime q
  · have hmul := Sieve.moebius_mul_of_coprime hcop
    have hsq : mobiusRealCoefficient d ^ 2 = 1 := by
      have hne : moebius d ≠ 0 := moebius_ne_zero_iff_squarefree.mpr hsf
      rcases moebius_ne_zero_iff_eq_or.mp hne with hm | hm <;>
        simp [mobiusRealCoefficient, hm]
    have hprod : mobiusRealCoefficient d * mobiusRealCoefficient (d * q) =
        mobiusRealCoefficient q := by
      unfold mobiusRealCoefficient at *
      rw [hmul]
      push_cast
      calc
        ((moebius d : ℤ) : ℝ) *
            (((moebius d : ℤ) : ℝ) * ((moebius q : ℤ) : ℝ)) =
          (((moebius d : ℤ) : ℝ) ^ 2) * ((moebius q : ℤ) : ℝ) := by ring
        _ = ((moebius q : ℤ) : ℝ) := by rw [hsq]; ring
    rw [if_pos hcop]
    change 2 * mobiusRealCoefficient d * mobiusRealCoefficient (d * q) /
        (((q : ℝ) + 1) * (d : ℝ)) =
      2 / (d : ℝ) * (mobiusRealCoefficient q / ((q : ℝ) + 1))
    calc
      2 * mobiusRealCoefficient d * mobiusRealCoefficient (d * q) /
          (((q : ℝ) + 1) * (d : ℝ)) =
        2 * (mobiusRealCoefficient d * mobiusRealCoefficient (d * q)) /
          (((q : ℝ) + 1) * (d : ℝ)) := by ring
      _ = 2 * mobiusRealCoefficient q / (((q : ℝ) + 1) * (d : ℝ)) := by
        rw [hprod]
      _ = 2 / (d : ℝ) * (mobiusRealCoefficient q / ((q : ℝ) + 1)) := by
        field_simp
  · have hzero := Sieve.moebius_mul_eq_zero_of_not_coprime hcop
    simp [hcop, mobiusRealCoefficient, hzero]

theorem abs_fixedCofactorGammaRay_le (d N : ℕ) (hd : 1 ≤ d)
    (hsf : Squarefree d) :
    |fixedCofactorGammaRay d N| ≤ 6 / (d : ℝ) := by
  rw [fixedCofactorGammaRay_eq d N hd hsf]
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hshift := abs_coprimeMobiusShiftedHarmonic_le_three d N
  calc
    |(2 / (d : ℝ)) * coprimeMobiusShiftedHarmonic d N| =
      (2 / (d : ℝ)) * |coprimeMobiusShiftedHarmonic d N| := by
        rw [abs_mul, abs_of_pos (div_pos (by norm_num) hdpos)]
    _ ≤ (2 / (d : ℝ)) * 3 := by
      exact mul_le_mul_of_nonneg_left hshift (by positivity)
    _ = 6 / (d : ℝ) := by ring

/-- All entries whose larger index is an integer multiple of the smaller
index, with diagonal counted once and off-diagonal entries twice. -/
noncomputable def integerDilationGammaSection (X : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 X, fixedCofactorGammaRay d (X / d)

/-- Complete integer-ratio subenergy has only logarithmic boundary growth.
The noninteger primitive-ratio pairs remain outside this estimate. -/
theorem abs_integerDilationGammaSection_le (X : ℕ) :
    |integerDilationGammaSection X| ≤ 6 * (1 + Real.log X) := by
  unfold integerDilationGammaSection
  calc
    |∑ d ∈ Finset.Icc 1 X, fixedCofactorGammaRay d (X / d)| ≤
      ∑ d ∈ Finset.Icc 1 X, |fixedCofactorGammaRay d (X / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 X, 6 / (d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd1 := (Finset.mem_Icc.mp hd).1
      by_cases hsf : Squarefree d
      · exact abs_fixedCofactorGammaRay_le d (X / d) hd1 hsf
      · have hzero : moebius d = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
        have hray : fixedCofactorGammaRay d (X / d) = 0 := by
          simp [fixedCofactorGammaRay, mobiusRealCoefficient, hzero]
        rw [hray, abs_zero]
        positivity
    _ = 6 * (∑ d ∈ Finset.Icc 1 X, 1 / (d : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ 6 * (1 + Real.log X) := by
      exact mul_le_mul_of_nonneg_left
        (Sieve.sum_Icc_one_div_le_one_add_log X) (by norm_num)

end RHTower
