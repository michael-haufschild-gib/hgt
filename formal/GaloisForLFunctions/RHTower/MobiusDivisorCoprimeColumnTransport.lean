import GaloisForLFunctions.RHTower.RetainedPrimeTopHomothety
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeColumnCancellation
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.MobiusDivisorAbelGcdCross

/-!
# Complete coprime-column transport for the literal divisor Abel source

Finite hyperbola inversion replaces a complete coprime Möbius floor-summatory
column by the original source at every prime-supported quotient. Applied to
the actual prime-free divisor defect, that source is the signed Chebyshev
defect. The exact square-root Abel weights and terminal cutoff are retained.

The primitive cross contribution is the resulting complete coprime-head
pairing minus its unique diagonal term. These are unconditional identities;
the signed outer pairing still needs a quantitative bound.
-/

noncomputable section
open Finset
namespace RHTower

/-- Complete coprime inversion of a floor-summatory source leaves precisely its supported quotients. -/
theorem coprime_moebius_floor_summatory (r N : ℕ) (F : ℕ → ℝ) :
    (∑ d ∈ Icc 1 N, (if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) *
      ∑ m ∈ Icc 1 (N/d), F (N/d/m)) =
    ∑ n ∈ Sieve.primeSupportedIcc r N, F (N/n) := by
  classical
  have hpoint (d : ℕ) :
      (if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) *
        (∑ m ∈ Icc 1 (N/d), F (N/d/m)) =
      ∑ m ∈ Icc 1 (N/d),
        (if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)*F (N/(d*m)) := by
    rw [mul_sum]
    simp only [Nat.div_div_eq_div_mul]
  simp_rw [hpoint]
  rw [← Sieve.sum_Icc_divisorsAntidiagonal_swap]
  have hinner (n : ℕ) (hn : n ∈ Icc 1 N) :
      (∑ x ∈ n.divisorsAntidiagonal,
        (if r.Coprime x.1 then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)*F (N/(x.1*x.2))) =
      if Sieve.primeSupportedOn r n then F (N/n) else 0 := by
    have he : (∑ x ∈ n.divisorsAntidiagonal,
        (if r.Coprime x.1 then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)*F (N/(x.1*x.2))) =
      (∑ x ∈ n.divisorsAntidiagonal,
        if r.Coprime x.1 then ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) else 0)*F (N/n) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro x hx
      rw [(Nat.mem_divisorsAntidiagonal.mp hx).1]
    rw [he, Nat.sum_divisorsAntidiagonal (fun d _ =>
      if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)]
    have hs : (∑ d ∈ n.divisors,
        if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) =
        if Sieve.primeSupportedOn r n then (1:ℝ) else 0 := by
      exact_mod_cast DeletionCoprimeColumn.sum_coprime_moebius_divisors r (mem_Icc.mp hn).1
    rw [hs]
    split_ifs <;> ring
  rw [sum_congr rfl hinner]
  simp [Sieve.primeSupportedIcc, sum_filter]

/-- The actual coprime divisor column retains the complete signed Chebyshev defect at every supported quotient. -/
theorem coprime_moebius_primeFreeDivisorDefect (r N : ℕ) :
    (∑ d ∈ Icc 1 N, if r.Coprime d then
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)*primeFreeDivisorDefect (N/d) else 0) =
      ∑ n ∈ Sieve.primeSupportedIcc r N, psiDefect (N/n) := by
  have h := coprime_moebius_floor_summatory r N psiDefect
  have he (d : ℕ) :
      (if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) *
        (∑ m ∈ Icc 1 (N/d), psiDefect (N/d/m)) =
      if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ)*primeFreeDivisorDefect (N/d) else 0 := by
    change (if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)*floorSummatory psiDefect (N/d)=_
    rw [floorSummatory_psiDefect_eq_primeFreeDivisorDefect]
    split_ifs <;> ring
  simpa only [he] using h

/-- The complete coprime Abel head preserves the original time weights and all supported signed defect values. -/
theorem mobiusDivisorCoprimeHead_eq_supported_abel (r M : ℕ) :
    mobiusDivisorCoprimeHead r M =
      ∑ k ∈ range M, (Real.sqrt (k+1 : ℕ)-Real.sqrt k)*
        ∑ n ∈ Sieve.primeSupportedIcc r k, psiDefect (k/n) := by
  have hD0 : primeFreeDivisorDefect 0=0 := by simp [primeFreeDivisorDefect]
  have hentry (d : ℕ) :
      (if r.Coprime d then mobiusDivisorDilationChannel M d else 0) =
      ∑ k ∈ range M, (Real.sqrt (k+1 : ℕ)-Real.sqrt k)*
        (if r.Coprime d then ((ArithmeticFunction.moebius d : ℤ) : ℝ)*primeFreeDivisorDefect (k/d) else 0) := by
    by_cases hc : r.Coprime d
    · simp only [if_pos hc]
      rw [mobiusDivisorDilationChannel_eq_moebius_unsigned, divisorUnsignedDilationChannel_eq_range, mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    · simp [hc]
  unfold mobiusDivisorCoprimeHead
  simp_rw [hentry]
  rw [sum_comm]
  apply sum_congr rfl
  intro k hk
  rw [← mul_sum]
  congr 1
  rw [← coprime_moebius_primeFreeDivisorDefect]
  symm
  apply sum_subset (Icc_subset_Icc le_rfl (mem_range.mp hk).le)
  intro d hd hn
  have hkd : k<d := by
    have hd1 := (mem_Icc.mp hd).1
    by_contra h
    exact hn (mem_Icc.mpr ⟨hd1,by omega⟩)
  simp [Nat.div_eq_of_lt hkd,hD0]

/-- The next coprime Abel increment is the full supported Chebyshev-defect column, with its exact square-root step. -/
theorem mobiusDivisorCoprimeHead_succ_sub (r M : ℕ) :
    mobiusDivisorCoprimeHead r (M+1)-mobiusDivisorCoprimeHead r M =
      (Real.sqrt (M+1 : ℕ)-Real.sqrt M)*
        ∑ n ∈ Sieve.primeSupportedIcc r M, psiDefect (M/n) := by
  rw [mobiusDivisorCoprimeHead_eq_supported_abel,mobiusDivisorCoprimeHead_eq_supported_abel,
    Finset.sum_range_succ]
  ring

/-- The primitive cross contribution is the complete coprime-column pairing minus its only diagonal term. -/
theorem mobiusDivisorGcdCross_one_eq_coprimeHeads (M : ℕ) :
    mobiusDivisorGcdCross M 1 =
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d*mobiusDivisorCoprimeHead d M)-
        mobiusDivisorDilationChannel M 1^2 := by
  by_cases hM : M=0
  · subst M
    simp [mobiusDivisorGcdCross,mobiusDivisorDilationChannel]
  have h1 : 1 ∈ Icc 1 M := mem_Icc.mpr ⟨le_rfl,by omega⟩
  have hpoint (d e : ℕ) :
      mobiusDivisorDilationChannel M d*
        (if d.Coprime e then mobiusDivisorDilationChannel M e else 0) =
      (if Nat.gcd d e=1 ∧ d≠e then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0)+
        (if d=1 ∧ e=1 then mobiusDivisorDilationChannel M 1^2 else 0) := by
    by_cases hde : d=e
    · subst e
      by_cases hd : d=1
      · simp [hd,pow_two]
      · simp [Nat.coprime_self,hd]
    · have hn : ¬(d=1 ∧ e=1) := by rintro ⟨rfl,rfl⟩; exact hde rfl
      by_cases hc : d.Coprime e
      · simp [hc,hde,hn]
      · simp [hc,hn]
  have heq : (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d*mobiusDivisorCoprimeHead d M) =
      mobiusDivisorGcdCross M 1+mobiusDivisorDilationChannel M 1^2 := by
    simp only [mobiusDivisorCoprimeHead,mul_sum,hpoint,sum_add_distrib]
    have hd : (∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d=1 ∧ e=1 then mobiusDivisorDilationChannel M 1^2 else 0) =
        mobiusDivisorDilationChannel M 1^2 := by
      simp [ite_and,h1]
    rw [hd]
    rfl
  linarith only [heq]

end RHTower
