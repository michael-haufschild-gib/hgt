import GaloisForLFunctions.RHTower.BaezDuarteMobiusPrefixApproximation
import GaloisForLFunctions.RHTower.Sieve.DivisorSwap
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusHarmonicZero

/-!
# The harmonic mean of a convolution with Möbius

An absolutely harmonic coefficient can be convolved with Möbius before
taking its ordered harmonic mean. Each column contains a bounded Möbius
harmonic prefix tending to zero.
-/

noncomputable section
open Filter Topology Finset ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

/-- The coefficients of an arithmetic product in ordinary divisor notation. -/
theorem arithmetic_product_at (a b : ArithmeticFunction ℝ) (n : ℕ) :
    (a*b) n=∑ d ∈ n.divisors, a d*b (n/d) := by
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun d k => a d*b k)

/-- The harmonic prefix of a convolution with Möbius groups by the first
factor, leaving the Möbius harmonic prefix at the complementary cutoff. -/
theorem harmonic_moebius_product_prefix (a : ArithmeticFunction ℝ) (N : ℕ) :
    (∑ n ∈ range (N+1), (a*(moebius : ArithmeticFunction ℝ)) n/(n:ℝ)) =
      ∑' d : ℕ, a d/(d:ℝ)*deningerHarmonicPartial (N/d) := by
  let μ := (moebius : ArithmeticFunction ℝ)
  let u := fun d k : ℕ => (a d/(d:ℝ))*(μ k/(k:ℝ))
  have hfib (n : ℕ) : (a*μ) n/(n:ℝ)=∑ d ∈ n.divisors, u d (n/d) := by
    rw [arithmetic_product_at,Finset.sum_div]
    refine sum_congr rfl fun d hd => ?_
    have h := congrArg (fun k : ℕ => (k:ℝ)) (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd))
    rw [Nat.cast_mul] at h
    change a d*μ (n/d)/(n:ℝ)=(a d/(d:ℝ))*(μ (n/d)/(↑(n/d:ℕ):ℝ))
    rw [div_mul_div_comm, h]
  have hN : (∑ n ∈ range (N+1), (a*μ) n/(n:ℝ))=∑ n ∈ Icc 1 N, (a*μ) n/(n:ℝ) := by
    rw [sum_range_succ']
    simp only [Nat.cast_zero,div_zero,add_zero]
    exact _root_.RHTower.sum_range_succ_eq_sum_Icc _ _
  rw [show (a*(moebius : ArithmeticFunction ℝ))=a*μ from rfl,hN]
  simp_rw [hfib]
  rw [Sieve.sum_divisors_swap]
  rw [tsum_eq_sum (s := Icc 1 N) (fun d hd => ?_)]
  · refine sum_congr rfl fun d _ => ?_
    dsimp only [u]
    rw [← mul_sum,deningerHarmonicPartial_eq_sum_Icc] <;> rfl
  · rcases Nat.eq_zero_or_pos d with rfl | hp
    · simp
    have hlt := lt_of_not_ge fun hh => hd (mem_Icc.2 ⟨hp,hh⟩)
    rw [Nat.div_eq_of_lt hlt]; simp [deningerHarmonicPartial]

/-- Absolute summability at the harmonic weight forces the ordered
Möbius-product harmonic mean to vanish. -/
theorem tendsto_harmonic_moebius_product_zero (a : ArithmeticFunction ℝ)
    (ha : Summable fun d : ℕ => a d/(d:ℝ)) :
    Tendsto (fun N : ℕ => ∑ n ∈ range (N+1), (a*(moebius : ArithmeticFunction ℝ)) n/(n:ℝ))
      atTop (𝓝 0) := by
  let f := fun N d : ℕ => a d/(d:ℝ)*deningerHarmonicPartial (N/d)
  have hm := deningerHarmonicPartial_tendsto
  rw [deningerHarmonicLimit_eq_zero] at hm
  obtain ⟨B,hB⟩ := deningerHarmonicPartial_bounded
  have hlim (d : ℕ) : Tendsto (fun N => f N d) atTop (𝓝 0) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [f]
    have hdiv : Tendsto (fun N : ℕ => N/d) atTop atTop := tendsto_atTop.2 fun k =>
      (eventually_ge_atTop (k*d)).mono fun _ h => (Nat.le_div_iff_mul_le hd).2 h
    simpa only [f,mul_zero] using (hm.comp hdiv).const_mul (a d/(d:ℝ))
  have hdom : ∀ N d : ℕ, ‖f N d‖ ≤ |a d/(d:ℝ)| * B := fun N d => by
    dsimp only [f]
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (hB (N/d)) (abs_nonneg _)
  have h := tendsto_tsum_of_dominated_convergence (f := f) (g := fun _ => (0:ℝ))
    (ha.abs.mul_right B) hlim (Eventually.of_forall hdom)
  simpa only [harmonic_moebius_product_prefix,f,tsum_zero] using h

#print axioms tendsto_harmonic_moebius_product_zero
end GaloisForLFunctions.ExclusionOfTheCriticalState
