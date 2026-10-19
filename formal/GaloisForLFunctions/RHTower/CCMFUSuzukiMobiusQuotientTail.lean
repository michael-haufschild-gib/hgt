import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusClippedKernelBound
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate

/-!
# Quotient tails of the signed Möbius--divisor Abel action

The actual zero abscissa controls the discarded quotient range. The remaining head
retains every Möbius sign and both complete and clipped dilation blocks.
-/

noncomputable section

namespace RHTower

open Finset

private theorem mertensPartialSum_re (N : ℕ) :
    (mobiusMertensPartialSum N).re =
      ∑ k ∈ Icc 1 N, ((ArithmeticFunction.moebius k : ℤ) : ℝ) := by
  rw [mobiusMertensPartialSum, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [mobiusComplexCoefficient, ArithmeticFunction.map_zero, Int.cast_zero, zero_add]
  rw [show Ico 1 (N + 1) = Icc 1 N by ext k; simp]
  simp

/-- Littlewood's unconditional estimate controls the finite Mertens envelope. -/
theorem mobiusDilationMertensEnvelope_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℕ,
      mobiusDilationMertensEnvelope D ≤
        C * ((D : ℝ) + 1) ^ (zetaZeroAbscissa + ε) := by
  obtain ⟨C, hC, hbound⟩ := mobiusMertens_subpower_zetaZeroAbscissa ε hε
  refine ⟨C, hC, fun D => ?_⟩
  apply (Finset.sup'_le_iff _ _).mpr
  intro d hd
  calc
    _ = |(mobiusMertensPartialSum d).re| := by rw [mertensPartialSum_re]
    _ ≤ ‖mobiusMertensPartialSum d‖ := Complex.abs_re_le_norm _
    _ ≤ C * ((d : ℝ) + 1) ^ (zetaZeroAbscissa + ε) := hbound d
    _ ≤ C * ((D : ℝ) + 1) ^ (zetaZeroAbscissa + ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (mem_Icc.mp hd).2 1)
        (by linarith [half_le_zetaZeroAbscissa])) hC

/-- Uniform kernel bound at the true zero abscissa, with no zero-free-strip premise. -/
theorem abs_mobiusClippedAbelKernel_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M q : ℕ, 1 ≤ q →
      |mobiusClippedAbelKernel M q| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
          (q : ℝ) ^ (-(zetaZeroAbscissa + ε) - 1) := by
  obtain ⟨C, hC, hbound⟩ := mobiusDilationMertensEnvelope_subpower ε hε
  let β := zetaZeroAbscissa + ε
  have hβ : 0 ≤ β := by dsimp [β]; linarith [half_le_zetaZeroAbscissa]
  refine ⟨2 * C * (2 : ℝ) ^ β, by positivity, fun M q hq => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  by_cases hqM : q ≤ M
  · have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    let D := (M - 1) / q
    have hDq : D * q ≤ M :=
      (Nat.div_mul_le_self (M - 1) q).trans (Nat.sub_le M 1)
    have hD : (D : ℝ) + 1 ≤ 2 * M / q := by
      apply (le_div_iff₀ hq0).2
      have hd : (D : ℝ) * q ≤ M := by exact_mod_cast hDq
      have hqm : (q : ℝ) ≤ M := by exact_mod_cast hqM
      nlinarith
    change |mobiusClippedAbelKernel M q| ≤
      (2 * C * (2 : ℝ) ^ β) * (M : ℝ) ^ (β + 1 / 2) * (q : ℝ) ^ (-β - 1)
    calc
      _ ≤ 2 * mobiusDilationMertensEnvelope D * Real.sqrt M / q :=
        abs_mobiusClippedAbelKernel_le_envelope M q hq
      _ ≤ 2 * (C * ((D : ℝ) + 1) ^ β) * Real.sqrt M / q := by
        gcongr
        exact hbound D
      _ ≤ 2 * (C * (2 * M / q) ^ β) * Real.sqrt M / q := by
        gcongr
      _ = _ := by
        rw [Real.div_rpow (by positivity) hq0.le,
          Real.mul_rpow (by positivity) hM0.le,
          show -β - 1 = -(β + 1) by ring,
          Real.rpow_neg hq0.le, Real.rpow_add hq0 β 1, Real.rpow_one,
          Real.rpow_add hM0 β (1 / 2), ← Real.sqrt_eq_rpow]
        ring
  · have hD : (M - 1) / q = 0 := Nat.div_eq_of_lt (by omega)
    rw [mobiusClippedAbelKernel, hD]
    simp only [Icc_eq_empty_of_lt (by omega : 0 < (1 : ℕ)), sum_empty, abs_zero]
    positivity

/-- Retained signed quotient head, with the cutoff clipped to physical support. -/
def mobiusDivisorQuotientHead (M Q : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 (min Q (M - 1)),
    primeFreeDivisorDefect q * mobiusClippedAbelKernel M q

/-- The discarded quotient range of the same arithmetic source. -/
def mobiusDivisorQuotientTail (M Q : ℕ) : ℝ :=
  ∑ q ∈ Icc (Q + 1) (M - 1),
    primeFreeDivisorDefect q * mobiusClippedAbelKernel M q

theorem mobiusDivisorSquareRootAbelMoment_eq_head_add_tail (M Q : ℕ) :
    mobiusDivisorSquareRootAbelMoment M =
      mobiusDivisorQuotientHead M Q + mobiusDivisorQuotientTail M Q := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_divisorDefect_kernel]
  have hh : (Icc 1 (M - 1)).filter (fun q => q ≤ Q) = Icc 1 (min Q (M - 1)) := by
    ext q
    simp only [mem_filter, mem_Icc, le_min_iff]
    omega
  have ht : (Icc 1 (M - 1)).filter (fun q => ¬q ≤ Q) = Icc (Q + 1) (M - 1) := by
    ext q
    simp only [mem_filter, mem_Icc]
    omega
  have h := sum_filter_add_sum_filter_not (Icc 1 (M - 1)) (fun q => q ≤ Q)
    (fun q => primeFreeDivisorDefect q * mobiusClippedAbelKernel M q)
  rw [hh, ht] at h
  exact h.symm

private theorem quotient_power_tail_le (β : ℝ) (hβ : 1 / 2 < β)
    (Q R : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Icc (Q + 1) R, (q : ℝ) ^ (-(β + 1 / 2))) ≤
      (Q : ℝ) ^ (1 / 2 - β) / (β - 1 / 2) := by
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  have h := sum_range_add_rpow_neg_le (c := β + 1 / 2) (by linarith) hQ
    (R + 1 - (Q + 1))
  simpa only [Nat.add_comm, show 1 - (β + 1 / 2) = 1 / 2 - β by ring,
    show β + 1 / 2 - 1 = β - 1 / 2 by ring] using h

/-- Uniform quotient-tail estimate with the actual zero abscissa in its exponents. -/
theorem abs_mobiusDivisorQuotientTail_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M Q : ℕ, 1 ≤ Q →
      |mobiusDivisorQuotientTail M Q| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
          (Q : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε) := by
  obtain ⟨C, hC, hbound⟩ := abs_mobiusClippedAbelKernel_subpower ε hε
  let β := zetaZeroAbscissa + ε
  have hβ : 1 / 2 < β := by dsimp [β]; linarith [half_le_zetaZeroAbscissa]
  refine ⟨24 * C / (β - 1 / 2), by positivity, fun M Q hQ => ?_⟩
  have hterm (q : ℕ) (hq : 1 ≤ q) :
      |primeFreeDivisorDefect q * mobiusClippedAbelKernel M q| ≤
        (24 * C * (M : ℝ) ^ (β + 1 / 2)) * (q : ℝ) ^ (-(β + 1 / 2)) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    calc
      _ = |primeFreeDivisorDefect q| * |mobiusClippedAbelKernel M q| := abs_mul _ _
      _ ≤ (24 * Real.sqrt q) *
          (C * (M : ℝ) ^ (β + 1 / 2) * (q : ℝ) ^ (-β - 1)) :=
        mul_le_mul (abs_primeFreeDivisorDefect_le hq) (hbound M q hq)
          (abs_nonneg _) (by positivity)
      _ = (24 * C * (M : ℝ) ^ (β + 1 / 2)) *
          (Real.sqrt q * (q : ℝ) ^ (-β - 1)) := by ring
      _ = _ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq0]
        congr 2
        ring
  have hsum : |mobiusDivisorQuotientTail M Q| ≤
      (24 * C * (M : ℝ) ^ (β + 1 / 2)) *
        ((Q : ℝ) ^ (1 / 2 - β) / (β - 1 / 2)) := by
    calc
      _ ≤ ∑ q ∈ Icc (Q + 1) (M - 1),
          |primeFreeDivisorDefect q * mobiusClippedAbelKernel M q| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Icc (Q + 1) (M - 1),
          (24 * C * (M : ℝ) ^ (β + 1 / 2)) * (q : ℝ) ^ (-(β + 1 / 2)) :=
        sum_le_sum fun q hq => hterm q (by have := (mem_Icc.mp hq).1; omega)
      _ = (24 * C * (M : ℝ) ^ (β + 1 / 2)) *
          ∑ q ∈ Icc (Q + 1) (M - 1), (q : ℝ) ^ (-(β + 1 / 2)) :=
        (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (quotient_power_tail_le β hβ Q (M - 1) hQ)
        (by positivity)
  calc
    _ ≤ _ := hsum
    _ = _ := by
      change (24 * C * (M : ℝ) ^ (β + 1 / 2)) *
          ((Q : ℝ) ^ (1 / 2 - β) / (β - 1 / 2)) =
        (24 * C / (β - 1 / 2)) * (M : ℝ) ^ (β + 1 / 2) *
          (Q : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε)
      rw [show 1 / 2 - zetaZeroAbscissa - ε = 1 / 2 - β by dsimp [β]; ring]
      ring

/-- The head approximates the full signed Abel action with a quantified uniform remainder. -/
theorem mobiusDivisorQuotientHead_error_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M Q : ℕ, 1 ≤ Q →
      |mobiusDivisorSquareRootAbelMoment M - mobiusDivisorQuotientHead M Q| ≤
        C * (M : ℝ) ^ (zetaZeroAbscissa + ε + 1 / 2) *
          (Q : ℝ) ^ (1 / 2 - zetaZeroAbscissa - ε) := by
  obtain ⟨C, hC, hbound⟩ := abs_mobiusDivisorQuotientTail_subpower ε hε
  refine ⟨C, hC, fun M Q hQ => ?_⟩
  rw [mobiusDivisorSquareRootAbelMoment_eq_head_add_tail M Q, add_sub_cancel_left]
  exact hbound M Q hQ

end RHTower
