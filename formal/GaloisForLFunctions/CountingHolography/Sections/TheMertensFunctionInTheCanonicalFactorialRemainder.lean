import GaloisForLFunctions.CountingHolography.Sections.TheSquareRootContractionInTheStirlingRemainder
import GaloisForLFunctions.CountingHolography.Sections.MobiusInterpolationByIntegerFactorialDegrees
import GaloisForLFunctions.CountingHolography.Sections.EntropyAndValueOfBalancedFactorials
import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.WherePrecisionIsLost
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.FareyCountMertensIdentity
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTangentPrincipleOfTheTateFamily

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

private theorem unit_value {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ Icc 1 n, μR d*((n/d:ℕ):ℝ))=1 := by
  have h := factorialFloorReading_prefix ℝ n (k := 1) Nat.one_pos
  simpa only [factorialFloorReading,prefixFactorialCoeffs,map_sum,Finsupp.linearCombination_single,
    smul_eq_mul,Nat.div_one,if_pos hn,μR] using h

/-- The exact Stirling remainder, including the linear balance, is a
positive weighted floor sum of the ordinary Mertens function. -/
theorem mertens_floorTransform_eq_factorial_remainder {n : ℕ} (hn : 0 < n) :
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
theorem canonicalFactorialRemainder_power_iff_mertens {s : ℝ} (hs : 1/2 ≤ s) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      |1+Chebyshev.psi n-factorialEntropy (prefixFactorialCoeffs ℤ n)| ≤ C*(n:ℝ)^s) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → |(mertensIoc n:ℝ)| ≤ C*(n:ℝ)^s) := by
  rw [← factorialStirlingStep_power_bound_iff (fun n => (mertensIoc n:ℝ)) hs]
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C,hC,fun n hn => ?_⟩ <;>
    simpa only [mertens_floorTransform_eq_factorial_remainder hn] using h n hn

/-- The entropy of the canonical factorial prefix approximates its
logarithmic value to every strict half power exactly under RH. -/
theorem riemannHypothesis_iff_canonicalFactorialRemainder :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n →
      |1+Chebyshev.psi n-factorialEntropy (prefixFactorialCoeffs ℤ n)| ≤ C*(n:ℝ)^(1/2+δ) := by
  have hnorm (n : ℕ) : ‖mobiusMertensPartialSum n‖=|(mertensIoc n:ℝ)| := by
    rw [mobiusMertensPartialSum_eq_mertensIoc,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [← mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis]
  constructor
  · intro h δ hδ
    let s := 1/2+δ
    have hs : 0 ≤ s := by dsimp only [s]; linarith
    apply (canonicalFactorialRemainder_power_iff_mertens (s := s) (by dsimp only [s]; linarith)).mpr
    obtain ⟨C,hC,h⟩ := h δ hδ
    refine ⟨C*2^s,by positivity,fun n hn => ?_⟩
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hb := Real.rpow_le_rpow (by positivity : 0 ≤ (n:ℝ)+1)
      (by linarith only [hn'] : (n:ℝ)+1 ≤ 2*n) hs
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
        (by linarith : (n:ℝ) ≤ n+1) (by linarith : (0:ℝ) ≤ 1/2+δ)) hC)

open ArithmeticDegenerationTheory WindowTowerOfSpecZ

/-- Entropy of the factorial presentation which is one at the integer sample
m and zero at every other positive degree. -/
def factorialSampleEntropy (m : ℕ) : ℝ :=
  factorialEntropy (prefixFactorialCoeffs ℤ m - prefixFactorialCoeffs ℤ (m-1))

private theorem stirling_prefix {m : ℕ} (hm : 0 < m) :
    ∑ d ∈ Icc 1 m, dirichletConv factorialStirlingStep μR d =
      1+Chebyshev.psi m-factorialEntropy (prefixFactorialCoeffs ℤ m) := by
  have hM (n : ℕ) : floorTransform μR (fun _ => 1) n = (mertensIoc n:ℝ) := by
    simp only [floorTransform,mul_one,μR,icc_eq_ioc,mertensIoc,Int.cast_sum]
  have he := floorTransform_comp factorialStirlingStep μR (fun _ => 1) m
  simp_rw [hM] at he
  exact (by simpa only [floorTransform,mul_one] using he.symm :
    (∑ d ∈ Icc 1 m, dirichletConv factorialStirlingStep μR d) = _).trans
      (mertens_floorTransform_eq_factorial_remainder hm)

private theorem sample_difference {m : ℕ} (hm : 1 < m) :
    factorialSampleEntropy m - vonMangoldt m = -dirichletConv factorialStirlingStep μR m := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h := stirling_prefix (m := n+1) (by omega)
  rw [sum_Icc_succ_top (by omega),stirling_prefix (by omega : 0 < n)] at h
  have hpsi : Chebyshev.psi (n+1:ℕ)=Chebyshev.psi n+vonMangoldt (n+1) := by
    rw [← partialSum_vonMangoldt,← partialSum_vonMangoldt]
    simp only [partialSum,Nat.floor_natCast,sum_Ioc_succ_top (Nat.zero_le n),vonMangoldtWeight]
  rw [hpsi] at h
  simp only [factorialSampleEntropy,Nat.add_sub_cancel,map_sub]
  linarith only [h]

private def localWeight (m k p : ℕ) : ℝ :=
  ((p:ℝ) ^ ((m.factorization p-1)*(k+1):ℕ))⁻¹ * (1-((p:ℝ)⁻¹)^(k+1))

/-- At negative integral dimension the sign of the Jordan totient is the
parity of the number of prime divisors. Each absolute local factor is positive. -/
private theorem negative_jordan_product {m : ℕ} (hm : m ≠ 0) (k : ℕ) :
    jordanTotient (-((k+1:ℕ):ℝ)) m =
      (-1:ℝ)^m.primeFactors.card * ∏ p ∈ m.primeFactors, localWeight m k p := by
  have h := (isMultiplicative_jordanFun (-((k+1:ℕ):ℝ))).multiplicative_factorization
    (jordanFun (-((k+1:ℕ):ℝ))) hm
  simp only [jordanFun_apply,Finsupp.prod,Nat.support_factorization] at h
  rw [h,← prod_const,← prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpow := hprime.factorization_pos_of_dvd hm (Nat.dvd_of_mem_primeFactors hp)
  rw [jordanTotient_prime_pow hprime _ hpow,neg_mul,
    show ((k+1:ℕ):ℝ)*((m.factorization p-1:ℕ):ℝ)=(((m.factorization p-1)*(k+1):ℕ):ℝ) by push_cast; ring,
    Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_natCast,Real.rpow_natCast]
  simp only [localWeight,inv_pow]; ring

private theorem positive_localWeight {m k p : ℕ} (hp : p.Prime) : 0 < localWeight m k p := by
  have hp' : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have h := inv_lt_one_of_one_lt₀ hp'
  exact mul_pos (inv_pos.mpr (pow_pos (zero_lt_one.trans hp') _))
    (sub_pos.mpr (pow_lt_one₀ (inv_nonneg.mpr (Nat.cast_nonneg _)) h (Nat.succ_ne_zero k)))

/-- Exact signed magnitude of the entropy error at a single integer degree.
The product uses all distinct primes and retains the multiplicity in each local factor. -/
theorem factorialSampleEntropy_vonMangoldt_series {m : ℕ} (hm : 1 < m) :
    HasSum (fun k : ℕ => (∏ p ∈ m.primeFactors, localWeight m k p)/(((k:ℝ)+1)*((k:ℝ)+2)))
      ((-1:ℝ)^(m.primeFactors.card+1)*(factorialSampleEntropy m-vonMangoldt m)) := by
  let r := fun k : ℕ => ((k:ℝ)+1)*((k:ℝ)+2)
  let s := (-1:ℝ)^m.primeFactors.card
  have h : HasSum (fun k : ℕ => ∑ d ∈ m.divisors,
      μR (m/d)*(((d:ℝ)⁻¹)^(k+1)/r k))
      (∑ d ∈ m.divisors, μR (m/d)*factorialStirlingStep d) :=
    hasSum_sum fun d hd => (hasSum_factorialStirlingStep (Nat.pos_of_mem_divisors hd)).mul_left _
  have hval : (∑ d ∈ m.divisors, μR (m/d)*factorialStirlingStep d)=
      dirichletConv factorialStirlingStep μR m :=
    sum_congr rfl fun d _ => mul_comm _ _
  rw [hval] at h
  have hs : s*s=1 := by rw [← mul_pow]; norm_num
  have hstep (k : ℕ) : s*(∑ d ∈ m.divisors, μR (m/d)*(((d:ℝ)⁻¹)^(k+1)/r k)) =
      (∏ p ∈ m.primeFactors, localWeight m k p)/r k := by
    have hj : (∑ d ∈ m.divisors, μR (m/d)*((d:ℝ)⁻¹)^(k+1))=
        jordanTotient (-((k+1:ℕ):ℝ)) m := by
      simp only [jordanTotient,μR,Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_natCast,inv_pow]
    simp_rw [← mul_div_assoc]
    rw [← sum_div,hj,negative_jordan_product (by omega : m ≠ 0),← mul_div_assoc]
    change s*(s*_) / _ = _
    rw [← mul_assoc,hs,one_mul]
  have hv : s*dirichletConv factorialStirlingStep μR m =
      (-1:ℝ)^(m.primeFactors.card+1)*(factorialSampleEntropy m-vonMangoldt m) := by
    rw [pow_succ,sample_difference hm]; dsimp only [s]; ring
  rw [← hv]
  exact (h.mul_left s).congr_fun hstep

/-- The sample error has strict sign (−1)^(ω(m)+1), including prime powers. -/
theorem factorialSampleEntropy_vonMangoldt_sign {m : ℕ} (hm : 1 < m) :
    0 < (-1:ℝ)^(m.primeFactors.card+1)*(factorialSampleEntropy m-vonMangoldt m) := by
  let v := fun k : ℕ => (∏ p ∈ m.primeFactors, localWeight m k p)/(((k:ℝ)+1)*((k:ℝ)+2))
  have hv (k : ℕ) : 0 < v k := div_pos
    (prod_pos fun p hp => positive_localWeight (Nat.prime_of_mem_primeFactors hp)) (by positivity)
  have h := factorialSampleEntropy_vonMangoldt_series hm
  rw [← h.tsum_eq]
  exact (hv 0).trans_le (h.summable.le_tsum 0 (fun k _ => (hv k).le))

end GaloisForLFunctions.CountingHolography.Sections
