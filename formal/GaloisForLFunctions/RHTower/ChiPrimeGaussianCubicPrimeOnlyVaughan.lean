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

/-- On the whole first short-factor band, the actual signed coefficient is Möbius. -/
theorem vaughanPrimeShort_eq_moebius_seam {V n : ℕ}
    (hVn : V < n) (hnV : n ≤ 2*V) :
    vaughanPrimeShort V n = (moebius n : ℝ) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hdV {d : ℕ} (hd : d ∈ n.divisors) (hdn : d ≠ n) : d ≤ V := by
    obtain ⟨k,hk⟩ := (Nat.mem_divisors.mp hd).1
    have hd0 : d ≠ 0 := by intro h; simp only [h,zero_mul] at hk; omega
    have hk1 : 2 ≤ k := by
      by_contra h
      have : k=0 ∨ k=1 := by omega
      rcases this with h | h <;> simp_all
    have hmul : 2*d≤n := by nlinarith
    omega
  have he (d : ℕ) (hd : d ∈ n.divisors) :
      truncAF (moebius : ArithmeticFunction ℝ) V d =
      (moebius d : ℝ) - if d=n then (moebius n : ℝ) else 0 := by
    by_cases hdn : d=n
    · simp [hdn,truncAF_apply,not_le.mpr hVn]
    · simp [truncAF_apply,hdV hd hdn,hdn]
  have hs : ((zeta : ArithmeticFunction ℝ)*truncAF (moebius : ArithmeticFunction ℝ) V) n =
      -(moebius n : ℝ) := by
    rw [coe_zeta_mul_apply]
    simp_rw [Finset.sum_congr rfl (fun d hd => he d hd)]
    rw [Finset.sum_sub_distrib]
    have hz : (∑ d ∈ n.divisors, (moebius d : ℝ))=0 := by
      have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
        (coe_zeta_mul_coe_moebius (R := ℝ))
      simpa only [coe_zeta_mul_apply,intCoe_apply,one_apply,if_neg hn1] using h
    simp [hz,Nat.mem_divisors,hn0]
  have ht : typeIIShort V n=(moebius n : ℝ) := by
    change (1 : ArithmeticFunction ℝ) n-_= _
    rw [one_apply,if_neg hn1,hs,zero_sub,neg_neg]
  unfold vaughanPrimeShort vaughanSquarefreePart
  rw [ht]
  by_cases hn : Squarefree n
  · simp [hn]
  · simp [hn,moebius_eq_zero_of_not_squarefree hn]

/-- Every term of the complete Type-II source has its signed Möbius coefficient at the seam. -/
theorem vaughanPrimeTypeII_eq_moebius_seam {U V n : ℕ}
    (hU : 1 ≤ U) (hn : n ≤ 2*U*V) :
    vaughanPrimeTypeII U V n = ∑ dm ∈ n.divisorsAntidiagonal,
      if dm.1.Prime ∧ U < dm.1 ∧ dm.1.Coprime dm.2 ∧ V < dm.2 then
        Real.log dm.1*(moebius dm.2 : ℝ) else 0 := by
  classical
  unfold vaughanPrimeTypeII
  apply Finset.sum_congr rfl
  intro dm hdm
  have hmul := (Nat.mem_divisorsAntidiagonal.mp hdm).1
  have hn0 := (Nat.mem_divisorsAntidiagonal.mp hdm).2
  have hm0 : 1 ≤ dm.2 := by
    by_contra h
    have : dm.2=0 := by omega
    simp_all
  by_cases hd : dm.1.Prime ∧ U < dm.1 ∧ dm.1.Coprime dm.2
  · rw [if_pos hd]
    have hmV : dm.2≤2*V := by
      have hlu : U*dm.2≤dm.1*dm.2 := Nat.mul_le_mul_right _ hd.2.1.le
      have hprod : U*dm.2≤U*(2*V) := by nlinarith only [hlu,hmul,hn]
      exact Nat.le_of_mul_le_mul_left hprod (by omega)
    by_cases hVm : V < dm.2
    · rw [if_pos ⟨hd.1,hd.2.1,hd.2.2,hVm⟩,
        vaughanPrimeShort_eq_moebius_seam hVm hmV]
    · have hs : vaughanPrimeShort V dm.2=0 := by
        unfold vaughanPrimeShort vaughanSquarefreePart
        have ht : typeIIShort V dm.2=0 :=
          one_sub_zeta_mul_truncAF_moebius_apply_eq_zero hm0 (by omega)
        simp only [ht,ite_self]
      rw [if_neg (fun h => hVm h.2.2.2),hs,mul_zero]
  · rw [if_neg hd,if_neg (fun h => hd ⟨h.1,h.2.1,h.2.2.1⟩)]

/-- The full short source has positive terms at arbitrarily large prime cutoffs. -/
theorem vaughanPrimeShort_twice_prime {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    vaughanPrimeShort p (2*p)=1 := by
  rw [vaughanPrimeShort_eq_moebius_seam (by omega) le_rfl]
  have hc : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  rw [isMultiplicative_moebius.map_mul_of_coprime hc,
    moebius_apply_prime Nat.prime_two,moebius_apply_prime hp]
  simp

/-- The entire signed short source cannot be nonpositive above any cutoff. -/
theorem exists_vaughanPrimeShort_positive_after (K : ℕ) :
    ∃ V n : ℕ, K<V ∧ V<n ∧ n≤2*V ∧ V.Prime ∧ vaughanPrimeShort V n=1 := by
  obtain ⟨p,hpK,hp⟩ := Nat.exists_infinite_primes (max (K+1) 3)
  have hp2 : 2<p := by omega
  exact ⟨p,2*p,by omega,by omega,le_rfl,hp,vaughanPrimeShort_twice_prime hp hp2⟩

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
