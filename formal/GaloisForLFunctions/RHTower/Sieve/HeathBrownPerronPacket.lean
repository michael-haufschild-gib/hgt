import GaloisForLFunctions.RHTower.Sieve.HeathBrownFinitePacket
import GaloisForLFunctions.RHTower.Sieve.PerronPrimeSumBound

/-!
# Perron-ready finite Heath--Brown packets

This file closes the exact interface between the finite Heath--Brown identity and finite Perron
analysis.  Each signed term has explicit multiplicative support, its finite Dirichlet sum is the
product of its Möbius/zeta/logarithm factors, and every weighted von Mangoldt prefix below the
Heath--Brown threshold is the sum of these `k` finite term prefixes.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex
open scoped zeta Moebius

/-- An arithmetic function is supported in the positive interval `[1, M]`. -/
def UpperSupported (F : ArithmeticFunction ℝ) (M : ℕ) : Prop :=
  ∀ n, F n ≠ 0 → n ∈ Finset.Icc 1 M

theorem upperSupported_zero (M : ℕ) :
    UpperSupported (0 : ArithmeticFunction ℝ) M := by
  intro n hn
  exact (hn rfl).elim

theorem upperSupported_one :
    UpperSupported (1 : ArithmeticFunction ℝ) 1 := by
  intro n hn
  have hn1 : n = 1 := by
    by_contra h
    exact hn (ArithmeticFunction.one_apply_ne h)
  subst n
  simp

theorem UpperSupported.neg {F : ArithmeticFunction ℝ} {M : ℕ}
    (hF : UpperSupported F M) : UpperSupported (-F) M := by
  intro n hn
  apply hF n
  intro hzero
  apply hn
  simp [hzero]

theorem UpperSupported.add {F G : ArithmeticFunction ℝ} {M : ℕ}
    (hF : UpperSupported F M) (hG : UpperSupported G M) :
    UpperSupported (F + G) M := by
  intro n hn
  by_contra hmem
  have hFzero : F n = 0 := by
    by_contra hne
    exact hmem (hF n hne)
  have hGzero : G n = 0 := by
    by_contra hne
    exact hmem (hG n hne)
  exact hn (by simp [hFzero, hGzero])

/-- Multiplicative support multiplies under Dirichlet convolution. -/
theorem UpperSupported.mul {F G : ArithmeticFunction ℝ} {M N : ℕ}
    (hF : UpperSupported F M) (hG : UpperSupported G N) :
    UpperSupported (F * G) (M * N) := by
  intro n hn
  have hc : complexCoeff (F * G) n ≠ 0 := by
    exact Complex.ofReal_injective.ne hn
  rw [complexCoeff_mul] at hc
  refine convolution_mem_Icc_of_support_mul
    (a := complexCoeff F) (b := complexCoeff G) ?_ ?_ hc
  · intro q hq
    apply hF q
    intro hzero
    apply hq
    rw [complexCoeff_apply, hzero, Complex.ofReal_zero]
  · intro q hq
    apply hG q
    intro hzero
    apply hq
    rw [complexCoeff_apply, hzero, Complex.ofReal_zero]

theorem UpperSupported.pow {F : ArithmeticFunction ℝ} {M : ℕ}
    (hF : UpperSupported F M) (j : ℕ) : UpperSupported (F ^ j) (M ^ j) := by
  induction j with
  | zero => simpa using upperSupported_one
  | succ j ih => simpa [pow_succ] using ih.mul hF

theorem upperSupported_natCast (a : ℕ) :
    UpperSupported (a : ArithmeticFunction ℝ) 1 := by
  induction a with
  | zero => simpa using upperSupported_zero 1
  | succ a ih =>
      rw [Nat.cast_succ]
      exact ih.add upperSupported_one

theorem upperSupported_negOne :
    UpperSupported (-1 : ArithmeticFunction ℝ) 1 := by
  simpa using upperSupported_one.neg

theorem upperSupported_coeffTrunc (F : ArithmeticFunction ℝ) (X : ℕ) :
    UpperSupported (coeffTrunc F X) X := by
  intro n hn
  exact coeffTrunc_support_Icc F hn

theorem upperSupported_truncatedMoebius (L : ℕ) :
    UpperSupported (truncatedMoebius L) L := by
  rw [truncatedMoebius_eq_coeffTrunc]
  exact upperSupported_coeffTrunc _ L

/-- The degree-`j` core has product support `L^j X^j` when `j` is positive. -/
theorem upperSupported_heathBrownFiniteCore
    (L X j : ℕ) (hj : 1 ≤ j) :
    UpperSupported (heathBrownFiniteCore L X j) (L ^ j * X ^ j) := by
  have hM := (upperSupported_truncatedMoebius L).pow j
  have hZ := (upperSupported_coeffTrunc (zeta : ArithmeticFunction ℝ) X).pow (j - 1)
  have hlog := upperSupported_coeffTrunc ArithmeticFunction.log X
  have hraw := (hM.mul hZ).mul hlog
  have hbound : (L ^ j * X ^ (j - 1)) * X = L ^ j * X ^ j := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hj]
  simpa only [heathBrownFiniteCore, hbound] using hraw

/-- A complete signed term has the same support as its positive-degree core. -/
theorem upperSupported_heathBrownFiniteTerm
    (L X k m : ℕ) (hm : m < k) :
    UpperSupported (heathBrownFiniteTerm L X k m)
      (L ^ (k - m) * X ^ (k - m)) := by
  have hj : 1 ≤ k - m := Nat.sub_pos_of_lt hm
  have hsign := upperSupported_negOne.pow (m + k + 1)
  have hchoose := upperSupported_natCast (k.choose m)
  have hcore := upperSupported_heathBrownFiniteCore L X (k - m) hj
  simpa [heathBrownFiniteTerm] using (hsign.mul hchoose).mul hcore

/-- **Perron-ready product identity for one finite signed term.** -/
theorem sum_Icc_heathBrownFiniteTerm_cpow_neg
    (L X k m : ℕ) (hm : m < k) (w : ℂ) :
    (∑ n ∈ Finset.Icc 1 (L ^ (k - m) * X ^ (k - m)),
        complexCoeff (heathBrownFiniteTerm L X k m) n * (n : ℂ) ^ (-w)) =
      (-1 : ℂ) ^ (m + k + 1) * (k.choose m : ℂ) *
        (LSeries (complexCoeff (truncatedMoebius L)) w ^ (k - m) *
          LSeries (complexCoeff (coeffTrunc (zeta : ArithmeticFunction ℝ) X)) w ^
            (k - m - 1) *
          LSeries (complexCoeff (coeffTrunc ArithmeticFunction.log X)) w) := by
  have hsupp := upperSupported_heathBrownFiniteTerm L X k m hm
  change ∀ n, heathBrownFiniteTerm L X k m n ≠ 0 →
    n ∈ Finset.Icc 1 (L ^ (k - m) * X ^ (k - m)) at hsupp
  rw [sum_mul_cpow_neg_eq_LSeries
    (a := complexCoeff (heathBrownFiniteTerm L X k m))
    (s := Finset.Icc 1 (L ^ (k - m) * X ^ (k - m)))
    (by simp) (fun n hn => hsupp n (Complex.ofReal_injective.ne_iff.mp hn)) w]
  exact LSeries_heathBrownFiniteTerm L X k m w

/-- Below the algebraic cutoff, a weighted von Mangoldt prefix is exactly the sum of the `k`
finite signed term prefixes. -/
theorem sum_Icc_vonMangoldt_eq_sum_heathBrownFiniteTerm
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) (w : ℂ) :
    (∑ n ∈ Finset.Icc 1 X, (vonMangoldt n : ℂ) * (n : ℂ) ^ (-w)) =
      ∑ m ∈ Finset.range k, ∑ n ∈ Finset.Icc 1 X,
        complexCoeff (heathBrownFiniteTerm L X k m) n * (n : ℂ) ^ (-w) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
  have hncut : n < (L + 1) ^ k := hnX.trans_lt hXL
  have hLambda := heathBrown_finite_compressed_identity L X k n hnX hncut
  have hterms := congrArg (fun F : ArithmeticFunction ℝ => F n)
    (heathBrownFiniteCompressedPacket_eq_sum_terms L X k)
  have hreal : vonMangoldt n = ∑ m ∈ Finset.range k,
      heathBrownFiniteTerm L X k m n := by
    rw [hLambda, hterms]
    induction Finset.range k using Finset.induction_on with
    | empty => simp
    | @insert a u ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ArithmeticFunction.add_apply, ih]
  rw [hreal]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rfl

end RHTower.Sieve
