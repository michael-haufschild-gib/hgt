import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIIEstimate
import GaloisForLFunctions.RHTower.Sieve.VaughanBlockDecomposition
import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicMain

/-!
# Exact prime-only Vaughan source for the joint Gaussian cubic

Squarefree restriction of the corpus Vaughan identity removes proper prime powers
pointwise. Its Type-II long factor is an actual prime; the short coefficient
retains its sign, squarefree restriction, and coprimality condition. Below the
square of the long cutoff, that coprimality condition follows from the support.

The final identity applies to the entire noncontracting Gaussian cubic, with
all shared moduli and coupled weights inside one signed row. Both Type-I
squarefree masks remain. No cancellation estimate or asymptotic is asserted.
-/

noncomputable section

open Finset ArithmeticFunction

namespace RHTower.Sieve

/-- Squarefree restriction, used exactly rather than as a prime-power error. -/
def vaughanSquarefreePart (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then f n else 0

/-- The actual signed short coefficient after prime-only restriction. -/
def vaughanPrimeShort (V n : ℕ) : ℝ :=
  vaughanSquarefreePart (typeIIShort V) n

/-- The prime-only Type-II coefficient, retaining the exact coprime factorization. -/
def vaughanPrimeTypeII (U V n : ℕ) : ℝ :=
  ∑ dm ∈ n.divisorsAntidiagonal,
    if dm.1.Prime ∧ U < dm.1 ∧ dm.1.Coprime dm.2 then
      Real.log dm.1 * vaughanPrimeShort V dm.2 else 0

/-- Complete signed prime-only Vaughan source. Both Type-I squarefree masks remain. -/
def vaughanPrimeCoefficient (U V n : ℕ) : ℝ :=
  (if n ≤ U then (if n.Prime then Real.log n else 0) else 0) -
    vaughanSquarefreePart
      (((zeta : ArithmeticFunction ℝ) * truncAF vonMangoldt U *
        truncAF (moebius : ArithmeticFunction ℝ) V) : ArithmeticFunction ℝ) n +
    vaughanSquarefreePart
      ((ArithmeticFunction.log * truncAF (moebius : ArithmeticFunction ℝ) V) : ArithmeticFunction ℝ) n +
    vaughanPrimeTypeII U V n

/-- Squarefree restriction removes all proper prime powers pointwise. -/
theorem vaughanSquarefreePart_vonMangoldt (n : ℕ) :
    vaughanSquarefreePart vonMangoldt n = if n.Prime then Real.log n else 0 := by
  by_cases hp : n.Prime
  · simp [vaughanSquarefreePart, hp.squarefree, hp, vonMangoldt_apply_prime hp]
  · by_cases hs : Squarefree n
    · have hz : vonMangoldt n = 0 := vonMangoldt_eq_zero_iff.mpr
        (fun h => hp (Nat.squarefree_and_prime_pow_iff_prime.mp ⟨hs, h⟩))
      simp [vaughanSquarefreePart, hs, hp, hz]
    · simp [vaughanSquarefreePart, hs, hp]

private theorem squarefree_typeIILong (U d : ℕ) :
    vaughanSquarefreePart (typeIILong U) d =
      if d.Prime ∧ U < d then Real.log d else 0 := by
  have hval : typeIILong U d = vonMangoldt d-truncAF vonMangoldt U d := rfl
  by_cases hd : d ≤ U
  · simp only [vaughanSquarefreePart, hval, truncAF_apply, if_pos hd, sub_self,
      ite_self, not_lt.mpr hd, and_false, if_false]
  · have hUd : U < d := by omega
    have he : vaughanSquarefreePart (typeIILong U) d =
        vaughanSquarefreePart vonMangoldt d := by
      simp only [vaughanSquarefreePart, hval, truncAF_apply, if_neg hd, sub_zero]
    rw [he, vaughanSquarefreePart_vonMangoldt]
    simp only [hUd, and_true]

private theorem squarefree_typeII_term (U V d m : ℕ) :
    (if Squarefree (d * m) then typeIILong U d * typeIIShort V m else 0) =
      if d.Prime ∧ U < d ∧ d.Coprime m then Real.log d * vaughanPrimeShort V m else 0 := by
  by_cases hc : d.Coprime m
  · by_cases hm : Squarefree m
    · calc
        _ = vaughanSquarefreePart (typeIILong U) d * typeIIShort V m := by
          by_cases hd : Squarefree d <;> simp [Nat.squarefree_mul hc, hd, hm, vaughanSquarefreePart]
        _ = _ := by
          rw [squarefree_typeIILong]
          by_cases hd : d.Prime ∧ U < d
          · rw [if_pos hd, if_pos ⟨hd.1, hd.2, hc⟩]
            simp only [vaughanPrimeShort, vaughanSquarefreePart, if_pos hm]
          · have hh : ¬(d.Prime ∧ U < d ∧ d.Coprime m) := fun h => hd ⟨h.1, h.2.1⟩
            rw [if_neg hd, if_neg hh, zero_mul]
    · simp [Nat.squarefree_mul hc, hm, vaughanPrimeShort, vaughanSquarefreePart]
  · have hs : ¬ Squarefree (d * m) := fun h => hc (Nat.coprime_of_squarefree_mul h)
    simp [hs, hc]

/-- The full Type-II source equals a signed prime-only divisor sum exactly. -/
theorem vaughanPrimeTypeII_eq (U V n : ℕ) :
    vaughanPrimeTypeII U V n =
      vaughanSquarefreePart ((typeIILong U * typeIIShort V) : ArithmeticFunction ℝ) n := by
  unfold vaughanSquarefreePart
  rw [ArithmeticFunction.mul_apply]
  symm
  calc
    _ = ∑ dm ∈ n.divisorsAntidiagonal,
        if Squarefree n then typeIILong U dm.1 * typeIIShort V dm.2 else 0 := by
      by_cases hs : Squarefree n <;> simp [hs]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro dm hdm
      have hprod := (Nat.mem_divisorsAntidiagonal.mp hdm).1
      rw [← hprod]
      exact squarefree_typeII_term U V dm.1 dm.2

/-- No correction or estimate: the constructed Vaughan coefficient is the actual prime logarithm. -/
theorem vaughanPrimeCoefficient_eq (U V n : ℕ) :
    vaughanPrimeCoefficient U V n = if n.Prime then Real.log n else 0 := by
  have htr : (if n ≤ U then (if n.Prime then Real.log n else 0) else 0) =
      vaughanSquarefreePart (truncAF vonMangoldt U) n := by
    by_cases hn : n ≤ U
    · simpa only [vaughanSquarefreePart, truncAF_apply, if_pos hn] using
        (vaughanSquarefreePart_vonMangoldt n).symm
    · simp [vaughanSquarefreePart, truncAF_apply, hn]
  rw [vaughanPrimeCoefficient, htr, vaughanPrimeTypeII_eq,
    ← vaughanSquarefreePart_vonMangoldt]
  have hv := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_identity U V)
  change vonMangoldt n = truncAF vonMangoldt U n -
    ((zeta : ArithmeticFunction ℝ)*truncAF vonMangoldt U*truncAF (moebius : ArithmeticFunction ℝ) V) n +
    (ArithmeticFunction.log*truncAF (moebius : ArithmeticFunction ℝ) V) n +
    (typeIILong U*typeIIShort V) n at hv
  by_cases hs : Squarefree n
  · simpa only [vaughanSquarefreePart, if_pos hs] using hv.symm
  · simp only [vaughanSquarefreePart, if_neg hs, sub_zero, add_zero]

private theorem prime_long_coprime_of_product_le_sq {U d m : ℕ}
    (hd : d.Prime) (hUd : U < d) (hm : 0 < m) (hprod : d * m ≤ U ^ 2) :
    d.Coprime m := by
  have hmd : m < d := by
    by_contra hh
    have hdm : d ≤ m := by omega
    have hsq := Nat.mul_le_mul_left d hdm
    nlinarith only [hprod, hsq, hUd]
  exact hd.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd hm h).not_gt hmd)

/-- Throughout the square-root-cutoff branch, coprimality is automatic: the
long factor is prime and larger than its positive cofactor. The short signed
coefficient becomes independent of that prime, without a discarded term. -/
theorem vaughanPrimeTypeII_eq_of_le_sq {U V n : ℕ} (hn : n ≤ U ^ 2) :
    vaughanPrimeTypeII U V n =
      ∑ dm ∈ n.divisorsAntidiagonal,
        if dm.1.Prime ∧ U < dm.1 then Real.log dm.1 * vaughanPrimeShort V dm.2 else 0 := by
  unfold vaughanPrimeTypeII
  apply Finset.sum_congr rfl
  intro dm hdm
  obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hdm
  by_cases hd : dm.1.Prime ∧ U < dm.1
  · have hm : 0 < dm.2 := by
      by_contra h
      have hz : dm.2 = 0 := by omega
      simp [hz] at hprod
      exact hn0 hprod.symm
    have hc := prime_long_coprime_of_product_le_sq hd.1 hd.2 hm (hprod ▸ hn)
    rw [if_pos ⟨hd.1, hd.2, hc⟩, if_pos hd]
  · have hh : ¬(dm.1.Prime ∧ U < dm.1 ∧ dm.1.Coprime dm.2) := fun h => hd ⟨h.1, h.2.1⟩
    rw [if_neg hh, if_neg hd]

/-- Exact prime-only weighted sum: any joint signed complex weight is retained.
The division by log is only cancelled on actual primes, where it is nonzero. -/
theorem sum_primes_eq_vaughanPrimeCoefficient (I : Finset ℕ) (U V : ℕ) (w : ℕ → ℂ) :
    (∑ p ∈ I.filter Nat.Prime,w p) =
      ∑ n ∈ I,(vaughanPrimeCoefficient U V n : ℂ)/(Real.log n : ℂ)*w n := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  rw [vaughanPrimeCoefficient_eq]
  by_cases hp : n.Prime
  · have hl : (Real.log n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    simp only [if_pos hp, div_self hl, one_mul]
  · simp only [if_neg hp, Complex.ofReal_zero, zero_div, zero_mul]

end RHTower.Sieve

namespace RHTower

open Sieve

/-- The entire shared q,r aggregate of the actual Gaussian noncontracting cubic. -/
def primeGaussianCubicJointRow (N : ℝ) (n : ℕ) : ℂ :=
  ∑ r ∈ primeProfileBand N,∑ q ∈ primeProfileBand N,
    if n = r ∨ q = r then 0 else primeGaussianCubicMainEntry N n q r

/-- The actual complete noncontracting Gaussian cubic has an exact prime-only
Vaughan expansion. All common prime moduli, Gaussian/window weights and masks
stay inside one signed weight. No prime-power correction or analytic premise remains. -/
theorem primeGaussianCubicOffDiagonal_eq_primeOnlyVaughan (N : ℝ) (U V : ℕ) :
    primeGaussianCubicOffDiagonal N =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        (vaughanPrimeCoefficient U V n : ℂ)/(Real.log n : ℂ)*primeGaussianCubicJointRow N n := by
  have he : primeGaussianCubicOffDiagonal N =
      ∑ p ∈ primeProfileBand N,primeGaussianCubicJointRow N p := by
    unfold primeGaussianCubicOffDiagonal primeGaussianCubicJointRow
    exact Finset.sum_comm
  rw [he]
  change (∑ p ∈ (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter Nat.Prime,primeGaussianCubicJointRow N p) = _
  exact sum_primes_eq_vaughanPrimeCoefficient _ U V _

end RHTower
