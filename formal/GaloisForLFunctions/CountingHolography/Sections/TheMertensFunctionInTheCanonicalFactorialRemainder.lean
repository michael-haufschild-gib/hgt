import GaloisForLFunctions.CountingHolography.Sections.TheSquareRootContractionInTheStirlingRemainder
import GaloisForLFunctions.CountingHolography.Sections.MobiusInterpolationByIntegerFactorialDegrees
import GaloisForLFunctions.CountingHolography.Sections.EntropyAndValueOfBalancedFactorials
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.FareyCountMertensIdentity
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood

/-! # Möbius cancellation in the canonical factorial remainder

The Möbius presentation of a prefix has factorial log value ψ and balance
one. After subtracting its Stirling entropy, adding the balance leaves
the floor transform of the actual Mertens function. Its kernel is an
invertible perturbation of the identity at square-root precision.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction _root_.RHTower ArithmeticOfSquareRootPrecision

private theorem icc_eq_ioc (n : ℕ) : Icc 1 n=Ioc 0 n := by
  ext k
  simp only [mem_Icc,mem_Ioc,Nat.lt_iff_add_one_le,zero_add]

private def μR (d : ℕ) : ℝ := ((moebius d:ℤ):ℝ)
private def main (j : ℕ) : ℝ := (j:ℝ)*Real.log j

private theorem step_sum (n : ℕ) : ∑ j ∈ Icc 1 n, factorialStirlingStep j =
    Real.log (n.factorial:ℝ)-main n+n := by
  induction n with
  | zero => simp [main]
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega),ih,Nat.factorial_succ,Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    simp only [factorialStirlingStep,main,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    ring

/-- The logarithm of the least common multiple is the value of the
canonical factorial presentation of an entire prefix. -/
theorem factorialLogValue_prefixFactorials (n : ℕ) :
    factorialLogValue (prefixFactorialCoeffs ℤ n)=Chebyshev.psi n := by
  rw [psi_eq_sum_moebius_log_factorial,← icc_eq_ioc]
  simp only [factorialLogValue,prefixFactorialCoeffs,map_sum,Finsupp.linearCombination_single,
    Int.cast_id,zsmul_eq_mul]

private theorem prefix_entropy (n : ℕ) :
    factorialEntropy (prefixFactorialCoeffs ℤ n)=floorTransform μR main n := by
  simp only [factorialEntropy,prefixFactorialCoeffs,map_sum,Finsupp.linearCombination_single,
    Int.cast_id,zsmul_eq_mul,floorTransform,μR,main]

private theorem unit_value {n : ℕ} (hn : 0<n) :
    (∑ d ∈ Icc 1 n, μR d*((n/d:ℕ):ℝ))=1 := by
  have h := factorialFloorReading_prefix ℝ n (k := 1) Nat.one_pos
  simpa only [factorialFloorReading,prefixFactorialCoeffs,map_sum,Finsupp.linearCombination_single,
    smul_eq_mul,Nat.div_one,if_pos hn,μR] using h

/-- The exact Stirling remainder, including the linear balance, is a
positive weighted floor sum of the ordinary Mertens function. -/
theorem mertens_floorTransform_eq_factorial_remainder {n : ℕ} (hn : 0<n) :
    floorTransform factorialStirlingStep (fun k => (mertensIoc k:ℝ)) n =
      1+Chebyshev.psi n-factorialEntropy (prefixFactorialCoeffs ℤ n) := by
  have hM (j : ℕ) : (mertensIoc j:ℝ)=∑ d ∈ Icc 1 j, μR d := by
    simp only [mertensIoc,icc_eq_ioc,Int.cast_sum,μR]
  have hswap := sum_hyperbola_swap_real n (fun d j => μR d*factorialStirlingStep j)
  calc _ = ∑ j ∈ Icc 1 n, ∑ d ∈ Icc 1 (n/j), μR d*factorialStirlingStep j := by
              simp only [floorTransform,hM,sum_mul,mul_sum]
              exact sum_congr rfl fun j _ => sum_congr rfl fun d _ => mul_comm _ _
    _ = ∑ d ∈ Icc 1 n, μR d*(∑ j ∈ Icc 1 (n/d), factorialStirlingStep j) := by
              simpa only [mul_sum] using hswap.symm
    _ = ((∑ d ∈ Icc 1 n, μR d*Real.log ((n/d).factorial:ℝ))-floorTransform μR main n)+
          ∑ d ∈ Icc 1 n, μR d*((n/d:ℕ):ℝ) := by
      simp only [step_sum,floorTransform,mul_add,mul_sub,sum_add_distrib,sum_sub_distrib]
    _ = _ := by
      rw [unit_value hn,prefix_entropy,psi_eq_sum_moebius_log_factorial,← icc_eq_ioc]
      dsimp only [μR]
      ring

/-- Exact endpoint and every larger power agree for the factorial
remainder and the Mertens function. -/
theorem canonicalFactorialRemainder_power_iff_mertens {s : ℝ} (hs : 1/2≤s) :
    (∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n →
      |1+Chebyshev.psi n-factorialEntropy (prefixFactorialCoeffs ℤ n)| ≤ C*(n:ℝ)^s) ↔
    (∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n → |(mertensIoc n:ℝ)| ≤ C*(n:ℝ)^s) := by
  rw [← factorialStirlingStep_power_bound_iff (fun n => (mertensIoc n:ℝ)) hs]
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C,hC,fun n hn => ?_⟩ <;>
    simpa only [mertens_floorTransform_eq_factorial_remainder hn] using h n hn

#print axioms mertens_floorTransform_eq_factorial_remainder
#print axioms canonicalFactorialRemainder_power_iff_mertens

/-- The entropy of the canonical factorial prefix approximates its
logarithmic value to every strict half power exactly under RH. -/
theorem riemannHypothesis_iff_canonicalFactorialRemainder :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0<δ → ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 0<n →
      |1+Chebyshev.psi n-factorialEntropy (prefixFactorialCoeffs ℤ n)|≤C*(n:ℝ)^(1/2+δ) := by
  have hnorm (n : ℕ) : ‖mobiusMertensPartialSum n‖=|(mertensIoc n:ℝ)| := by
    rw [mobiusMertensPartialSum_eq_mertensIoc,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [← mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis]
  constructor
  · intro h δ hδ
    let s := 1/2+δ
    have hs : 0≤s := by dsimp only [s]; linarith
    apply (canonicalFactorialRemainder_power_iff_mertens (s := s) (by dsimp only [s]; linarith)).mpr
    obtain ⟨C,hC,h⟩ := h δ hδ
    refine ⟨C*2^s,by positivity,fun n hn => ?_⟩
    have hn' : (1:ℝ)≤n := by exact_mod_cast hn
    have hb := Real.rpow_le_rpow (by positivity : 0≤(n:ℝ)+1)
      (by linarith only [hn'] : (n:ℝ)+1≤2*n) hs
    rw [Real.mul_rpow two_pos.le (Nat.cast_nonneg _)] at hb
    rw [← hnorm]
    exact (h n).trans ((mul_le_mul_of_nonneg_left hb hC).trans_eq (mul_assoc _ _ _).symm)
  · intro h δ hδ
    obtain ⟨C,hC,hb⟩ := (canonicalFactorialRemainder_power_iff_mertens (s := 1/2+δ) (by linarith)).mp (h δ hδ)
    refine ⟨C,hC,fun n => ?_⟩
    rw [hnorm]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa [mertensIoc] using hC
    · exact (hb n hn).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by linarith : (n:ℝ)≤n+1) (by linarith : (0:ℝ)≤1/2+δ)) hC)

#print axioms riemannHypothesis_iff_canonicalFactorialRemainder

end GaloisForLFunctions.CountingHolography.Sections
