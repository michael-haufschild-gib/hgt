import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationMasks

/-!
# Finite local differences of the source square convolution

The point mass at a prime acts by arithmetic dilation. Two local differences
remove the two constant-sequence factors, without an Euler product for the
unknown source.
-/

open Complex
noncomputable section
namespace RHTower.WeilSingularArithmetic

def dirichletPoint (q n : ℕ) : ℂ := if n = q then 1 else 0

theorem convolution_assoc_all (f g h : ℕ → ℂ) :
    LSeries.convolution (LSeries.convolution f g) h =
      LSeries.convolution f (LSeries.convolution g h) := by
  simp [LSeries.convolution, mul_assoc]

theorem convolution_comm_all (f g : ℕ → ℂ) :
    LSeries.convolution f g = LSeries.convolution g f := by
  simp [LSeries.convolution, mul_comm]

theorem convolution_dirichletPoint {q : ℕ} (hq : q ≠ 0) (f : ℕ → ℂ) (n : ℕ) :
    LSeries.convolution (dirichletPoint q) f n =
      if n = 0 then 0 else if q ∣ n then f (n / q) else 0 := by
  by_cases hn : n = 0
  · simp [hn, LSeries.convolution_map_zero]
  rw [if_neg hn, LSeries.convolution_def]
  by_cases hd : q ∣ n
  · rw [if_pos hd]
    change (∑ ab ∈ n.divisorsAntidiagonal, dirichletPoint q ab.1 * f ab.2) = f (n / q)
    have hmem : (q, n / q) ∈ n.divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hd, hn⟩
    rw [Finset.sum_eq_single (q, n / q)]
    · simp [dirichletPoint]
    · intro ab hab hne
      have ha : ab.1 ≠ q := by
        intro ha
        apply hne
        apply Prod.ext ha
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq)
        exact (ha ▸ (Nat.mem_divisorsAntidiagonal.mp hab).1).trans
          (Nat.mul_div_cancel' hd).symm
      simp [dirichletPoint, ha]
    · exact fun h => False.elim (h hmem)
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro ab hab
    have ha : ab.1 ≠ q := by
      intro ha
      apply hd
      exact ⟨ab.2, (ha ▸ (Nat.mem_divisorsAntidiagonal.mp hab).1).symm⟩
    simp [dirichletPoint, ha]

theorem valuationPart_convolution_dirichletPoint_succ {p : ℕ} (hp : p ≠ 0)
    (k : ℕ) (f : ℕ → ℂ) :
    valuationPart p (k + 1) (LSeries.convolution (dirichletPoint p) f) =
      LSeries.convolution (dirichletPoint p) (valuationPart p k f) := by
  funext n
  simp only [valuationPart, LSeries.convolution_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  by_cases ha : ab.1 = p
  · have hn : n = p * ab.2 := (ha ▸ (Nat.mem_divisorsAntidiagonal.mp hab).1).symm
    have hm : valuationMask p (k + 1) n = valuationMask p k ab.2 := by
      rw [hn]
      have hk : p ^ (k + 1) ∣ p * ab.2 ↔ p ^ k ∣ ab.2 := by
        rw [pow_succ', Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hp)]
      have hk1 : p ^ (k + 1 + 1) ∣ p * ab.2 ↔ p ^ (k + 1) ∣ ab.2 := by
        rw [pow_succ', Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hp)]
      simp only [valuationMask, hk, hk1]
    rw [hm]
    ring
  · simp [dirichletPoint, ha]

theorem valuationPart_convolution_dirichletPoint_zero (p : ℕ) (f : ℕ → ℂ) :
    valuationPart p 0 (LSeries.convolution (dirichletPoint p) f) = 0 := by
  funext n
  simp only [valuationPart, LSeries.convolution_def, Finset.mul_sum, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  by_cases ha : ab.1 = p
  · have hd : p ∣ n := ⟨ab.2, (ha ▸ (Nat.mem_divisorsAntidiagonal.mp hab).1).symm⟩
    simp [valuationMask, hd]
  · simp [dirichletPoint, ha]

theorem summable_dirichletPoint (q : ℕ) (s : ℂ) :
    LSeriesSummable (dirichletPoint q) s := by
  unfold LSeriesSummable
  refine summable_of_ne_finset_zero (s := {q}) fun n hn => ?_
  simp only [Finset.mem_singleton] at hn
  simp [LSeries.term, dirichletPoint, hn]

theorem LSeries_dirichletPoint {q : ℕ} (hq : q ≠ 0) (s : ℂ) :
    LSeries (dirichletPoint q) s = (q : ℂ) ^ (-s) := by
  unfold LSeries
  rw [tsum_eq_single q fun n hn => by simp [LSeries.term, dirichletPoint, hn]]
  simp [LSeries.term, dirichletPoint, hq, Complex.cpow_neg]

def primeDifference (p : ℕ) (f : ℕ → ℂ) : ℕ → ℂ :=
  f - LSeries.convolution (dirichletPoint p) f

theorem valuationPart_primeDifference_zero (p : ℕ) (f : ℕ → ℂ) :
    valuationPart p 0 (primeDifference p f) = valuationPart p 0 f := by
  rw [primeDifference, valuationPart_sub, valuationPart_convolution_dirichletPoint_zero,
    sub_zero]

theorem valuationPart_primeDifference_succ {p : ℕ} (hp : p ≠ 0) (k : ℕ) (f : ℕ → ℂ) :
    valuationPart p (k + 1) (primeDifference p f) = valuationPart p (k + 1) f -
      LSeries.convolution (dirichletPoint p) (valuationPart p k f) := by
  rw [primeDifference, valuationPart_sub, valuationPart_convolution_dirichletPoint_succ hp]

private theorem toArithmeticFunction_sub (f g : ℕ → ℂ) :
    toArithmeticFunction (f - g) = toArithmeticFunction f - toArithmeticFunction g := by
  ext n
  change (if n = 0 then 0 else f n - g n) =
    (if n = 0 then 0 else f n) - (if n = 0 then 0 else g n)
  by_cases hn : n = 0 <;> simp [hn]

private theorem toArithmeticFunction_primeDifference (p : ℕ) (f : ℕ → ℂ) :
    toArithmeticFunction (primeDifference p f) =
      (1 - toArithmeticFunction (dirichletPoint p)) * toArithmeticFunction f := by
  rw [primeDifference, toArithmeticFunction_sub]
  simp [LSeries.convolution, sub_mul]

private theorem primeDifferenceKernel_mul_one {p : ℕ} (hp : p.Prime) :
    (1 - toArithmeticFunction (dirichletPoint p)) * toArithmeticFunction (1 : ℕ → ℂ) =
      toArithmeticFunction (coprimePart p 1) := by
  rw [sub_mul, one_mul]
  ext n
  change toArithmeticFunction (1 : ℕ → ℂ) n -
    LSeries.convolution (dirichletPoint p) 1 n = toArithmeticFunction (coprimePart p 1) n
  rw [convolution_dirichletPoint hp.ne_zero]
  have hc : n.Coprime p ↔ ¬p ∣ n := Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  by_cases hn : n = 0
  · simp [toArithmeticFunction, hn]
  · by_cases hd : p ∣ n <;>
      simp [toArithmeticFunction, hn, coprimePart, coprimeMask, hc, hd]

/-- Two finite local differences remove the two zeta coefficient factors. -/
theorem primeDifference_twice_square {p : ℕ} (hp : p.Prime) (f : ℕ → ℂ) :
    primeDifference p (primeDifference p (LSeries.convolution (LSeries.convolution f 1) 1)) =
      LSeries.convolution (LSeries.convolution f (coprimePart p 1)) (coprimePart p 1) := by
  have hA : toArithmeticFunction
      (primeDifference p (primeDifference p (LSeries.convolution (LSeries.convolution f 1) 1))) =
      toArithmeticFunction
        (LSeries.convolution (LSeries.convolution f (coprimePart p 1)) (coprimePart p 1)) := by
    simp only [toArithmeticFunction_primeDifference, LSeries.convolution,
      ArithmeticFunction.toArithmeticFunction_eq_self]
    rw [← primeDifferenceKernel_mul_one hp]
    ring
  funext n
  by_cases hn : n = 0
  · simp [hn, primeDifference, LSeries.convolution_map_zero]
  · have h := congrArg (fun a : ArithmeticFunction ℂ => a n) hA
    change (if n = 0 then 0 else _) = (if n = 0 then 0 else _) at h
    simpa only [hn, if_false] using h

end RHTower.WeilSingularArithmetic
