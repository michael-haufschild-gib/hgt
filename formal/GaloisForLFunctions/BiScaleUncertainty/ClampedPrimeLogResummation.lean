import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarFactorialAtomicPacket
import GaloisForLFunctions.RHTower.Sieve.BivariateConvolutionSummatorySwap

/-! Exact divisor resummation of the actual factorial ramp's prime field.
The collar support kills every product beyond the factorial cutoff; the
remaining divisor fibre has total von Mangoldt weight `log k`. -/

open MeasureTheory Set
open scoped BigOperators CompactlySupported
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open _root_.RHTower ArithmeticFunction
noncomputable section
set_option autoImplicit false

private theorem log_weight_sum (w : ℕ → ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, Real.log k*w k) =
      ∑ m ∈ Finset.Icc 1 K, vonMangoldt m*∑ j ∈ Finset.Icc 1 (K/m), w (j*m) := by
  have hs := Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun m j => vonMangoldt m*w (j*m)) K
  calc
    _ = ∑ k ∈ Finset.Icc 1 K,
        ∑ p ∈ k.divisorsAntidiagonal, vonMangoldt p.1*w (p.2*p.1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      calc
        _ = (∑ p ∈ k.divisorsAntidiagonal, vonMangoldt p.1)*w k := by
          rw [Nat.sum_divisorsAntidiagonal (fun m _ => vonMangoldt m), vonMangoldt_sum]
        _ = _ := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [mul_comm p.2 p.1, (Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = _ := hs
    _ = _ := by simp_rw [Finset.mul_sum]

/-- A finitely supported multiplicative rectangle collapses exactly to logarithms. -/
theorem weighted_prime_rectangle_eq_log (w : ℕ → ℝ) {K M : ℕ} (hKM : K ≤ M)
    (hw : ∀ k, K < k → w k = 0) :
    (∑ m ∈ Finset.Icc 1 M, vonMangoldt m*∑ j ∈ Finset.Icc 1 K, w (j*m)) =
      ∑ k ∈ Finset.Icc 1 K, Real.log k*w k := by
  have ho : (∑ m ∈ Finset.Icc 1 M, vonMangoldt m*∑ j ∈ Finset.Icc 1 K, w (j*m)) =
      ∑ m ∈ Finset.Icc 1 K, vonMangoldt m*∑ j ∈ Finset.Icc 1 K, w (j*m) := by
    symm
    apply Finset.sum_subset
    · intro m hm
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hKM⟩
    · intro m hm hmk
      have hKm : K < m := by
        have hm1 := (Finset.mem_Icc.mp hm).1
        by_contra h
        exact hmk (Finset.mem_Icc.mpr ⟨hm1, by omega⟩)
      have hz : (∑ j ∈ Finset.Icc 1 K, w (j*m)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => hw _ ?_
        exact hKm.trans_le (Nat.le_mul_of_pos_left m (by have := (Finset.mem_Icc.mp hj).1; omega))
      rw [hz, mul_zero]
  rw [ho, log_weight_sum]
  refine Finset.sum_congr rfl fun m hm => congrArg (fun t : ℝ => vonMangoldt m*t) ?_
  symm
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
      (Finset.mem_Icc.mp hj).2.trans (Nat.div_le_self K m)⟩
  · intro j hj hjm
    apply hw
    have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
    have hn : ¬j ≤ K/m := fun h => hjm (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1, h⟩)
    have hn' : ¬j*m ≤ K := by rwa [← Nat.le_div_iff_mul_le hm0]
    omega

/-- The exact prime sum is a log-weighted clamp sum, including the collar endpoint. -/
theorem clampedPrimeFactorialSum_eq_log {ε v : ℝ} {K M : ℕ}
    (hε : 0 < ε) (hv : 0 < v) (hKM : K ≤ M) (hcap : (1+ε)*v ≤ (K : ℝ)+1) :
    clampedPrimeFactorialSum ε K M v =
      ∑ k ∈ Finset.Icc 1 K, Real.log k*clampedRamp ε ((k : ℝ)/v) := by
  have h := weighted_prime_rectangle_eq_log (fun k => clampedRamp ε ((k : ℝ)/v)) hKM
    (fun k hk => clampedRamp_eq_zero hε ((le_div_iff₀ hv).2
      (hcap.trans (by exact_mod_cast (show K+1 ≤ k by omega)))))
  simpa only [clampedPrimeFactorialSum, Nat.cast_mul] using h

/-- The factorial lift with its exact logarithmic divisor weight. -/
def logWeightedFactorialLift (ε : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  Real.exp (x/2)*∑ j ∈ Finset.Icc 1 K,
    Real.log j*clampedRamp ε ((j : ℝ)*Real.exp x/K)

theorem continuous_logWeightedFactorialLift (ε : ℝ) (K : ℕ) :
    Continuous (logWeightedFactorialLift ε K) := by
  unfold logWeightedFactorialLift
  have he : Continuous (fun x : ℝ => Real.exp (x/2)) := by fun_prop
  exact he.mul (continuous_finsetSum _ fun _ _ =>
    continuous_const.mul ((continuous_clampedRamp ε).comp (by fun_prop)))

theorem atomic_smoothFactorialLift_eq_log {ε u : ℝ} {K M : ℕ}
    (hε : 0 < ε) (hu : 0 ≤ u) (hK : 1 ≤ K) (hKM : K ≤ M) (hbudget : ε*(K : ℝ) ≤ 1) :
    (∑ m ∈ Finset.Icc 1 M, primeWeight m*smoothFactorialLift ε K (u+Real.log m)) =
      logWeightedFactorialLift ε K u := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hcap : (1+ε)*((K : ℝ)*Real.exp (-u)) ≤ (K : ℝ)+1 := by
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ (1+ε)*(K : ℝ) by positivity)
    nlinarith
  rw [atomic_smoothFactorialLift_eq hK, clampedPrimeFactorialSum_eq_log hε (by positivity) hKM hcap]
  unfold logWeightedFactorialLift
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [Real.exp_neg]
  field_simp

/-- Explicit logarithmic field replacing the prime packet on the ramp support. -/
def factorialRampLogField (n : ℕ) (u : ℝ) : ℝ :=
  (logWeightedFactorialLift (sourceFactorialCollar (n+1)) (4*(n+1)) u-
    4*logWeightedFactorialLift (sourceFactorialCollar (n+1)) (2*(n+1)) u+
    4*logWeightedFactorialLift (sourceFactorialCollar (n+1)) (n+1) u)/Real.sqrt (n+1 : ℕ)

theorem continuous_factorialRampLogField (n : ℕ) : Continuous (factorialRampLogField n) := by
  unfold factorialRampLogField
  exact (((continuous_logWeightedFactorialLift _ _).sub
    ((continuous_logWeightedFactorialLift _ _).const_mul 4)).add
    ((continuous_logWeightedFactorialLift _ _).const_mul 4)).div_const _

/-- No arithmetic premise remains: the actual collar and cutoff discharge every tail. -/
theorem atomicSource_factorialRamp_eq_log (n : ℕ) {u : ℝ} (hu : 0 ≤ u)
    {K : ℕ} (hK : 4*(n+1) ≤ K+2) :
    atomicSource (factorialRampSource n) K u = factorialRampLogField n u := by
  have hN : 1 ≤ n+1 := by omega
  have hε := sourceFactorialCollar_pos hN
  have hadd (a b c : ℝ) : a*(b+c) = a*b+a*c := mul_add a b c
  change (∑ m ∈ Finset.Icc 1 (K+2), primeWeight m*sourceFactorialRamp (n+1) (u+Real.log m)) = _
  simp only [sourceFactorialRamp, rampBiNull, ← mul_div_assoc, hadd, mul_sub,
    ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have he (a b : ℝ) : a*(4*b) = 4*(a*b) := by ring
  simp only [he, ← Finset.mul_sum]
  rw [atomic_smoothFactorialLift_eq_log hε hu (by omega : 1 ≤ 4*(n+1)) hK
      (sourceFactorialCollar_small_budget hN (by omega)),
    atomic_smoothFactorialLift_eq_log hε hu (by omega : 1 ≤ 2*(n+1)) (by omega)
      (sourceFactorialCollar_small_budget hN (by omega)),
    atomic_smoothFactorialLift_eq_log hε hu hN (by omega)
      (sourceFactorialCollar_small_budget hN (by omega))]
  rfl

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
