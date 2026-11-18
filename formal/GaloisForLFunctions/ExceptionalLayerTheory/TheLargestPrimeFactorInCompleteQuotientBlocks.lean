import GaloisForLFunctions.ExceptionalLayerTheory.CumulativeDeepQuotientBlocksHaveThePrimeErrorExponent
import GaloisForLFunctions.RHTower.ComplexFugacityLeeYangTree
import GaloisForLFunctions.PrimeExponentialSums.PrimeSumsByParts
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHorizonLimitCommutesWithTheReceiverExactlyFromHalfDamping
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.GammaInvGrowth
import GaloisForLFunctions.RHTower.ZetaLittlewoodDeficit
import Mathlib.NumberTheory.ZetaValues

/-!
# The largest prime factor in complete quotient blocks

Among distinct prime divisors of an integer at most one exceeds its square
root. Dropping all smaller prime divisors and all proper prime powers
therefore costs at most a square-root prime mass per base cutoff.
-/

noncomputable section

open Finset ArithmeticFunction
open _root_.RHTower.LeeYangChain

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Sum of the largest prime factor times its logarithm. -/
def largestPrimeLogMass (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, largestPrimeFactor n * Real.log (largestPrimeFactor n)

/-- The complete integer divisor baseline at the base cutoff. -/
def divisorSizeMass (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d:ℝ)

private abbrev primeDivisorSizeMass (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d:ℝ)*vonMangoldt d

private theorem smaller_prime_square_le {n p : ℕ} (hn : 1<n) (hp : p.Prime) (hd : p∣n)
    (hne : p≠largestPrimeFactor n) : p*p ≤ n := by
  let P := largestPrimeFactor n
  have hP := largestPrimeFactor_prime hn
  have hpd : p≤P := by
    change p≤largestPrimeFactor n
    rw [largestPrimeFactor,dif_pos hn]
    exact le_max' _ _ (Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩)
  have hcop := (Nat.coprime_primes hp hP).mpr hne
  exact (Nat.mul_le_mul_left p hpd).trans (Nat.le_of_dvd (by omega)
    (hcop.mul_dvd_of_dvd_of_dvd hd (largestPrimeFactor_dvd hn)))

private def smallLevel (N d : ℕ) : ℝ :=
  (if d.Prime then 0 else vonMangoldt d) + (if d≤N.sqrt then vonMangoldt d else 0)

private theorem smallLevel_nonneg (N d : ℕ) : 0 ≤ smallLevel N d := by
  unfold smallLevel
  split <;> split <;> positivity

private theorem primeDivisorSizeMass_bounds (N : ℕ) :
    largestPrimeLogMass N ≤ primeDivisorSizeMass N ∧
    primeDivisorSizeMass N ≤ largestPrimeLogMass N +
      ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d:ℝ)*smallLevel N d := by
  have hl (n : ℕ) (hn : n ∈ Icc 1 N) :
      largestPrimeFactor n*Real.log (largestPrimeFactor n) ≤
        ∑ d ∈ n.divisors, (d:ℝ)*vonMangoldt d := by
    rcases (mem_Icc.mp hn).1.lt_or_eq with h | h
    · have hfactor := vonMangoldt_apply_prime (largestPrimeFactor_prime h)
      rw [← hfactor]
      exact single_le_sum (f := fun d : ℕ => (d:ℝ)*vonMangoldt d) (fun d _ => mul_nonneg (Nat.cast_nonneg d) vonMangoldt_nonneg)
        (Nat.mem_divisors.mpr ⟨largestPrimeFactor_dvd h,by omega⟩)
    · subst n
      simp [largestPrimeFactor]
  constructor
  · exact sum_le_sum hl
  rw [largestPrimeLogMass,← sum_add_distrib]
  refine sum_le_sum fun n hn => ?_
  rcases (mem_Icc.mp hn).1.lt_or_eq with h | h
  · let P := largestPrimeFactor n
    let w := fun d : ℕ => (d:ℝ)*vonMangoldt d
    have hP : P ∈ n.divisors := Nat.mem_divisors.mpr ⟨largestPrimeFactor_dvd h,by omega⟩
    have hsingle : (∑ d ∈ n.divisors, if d=P then w d else 0) = P*Real.log P := by
      rw [sum_ite_eq' _ _ _,if_pos hP]
      exact congrArg ((P:ℝ)*·) (vonMangoldt_apply_prime (largestPrimeFactor_prime h))
    change (∑ d ∈ n.divisors, w d) ≤ P*Real.log P+_
    rw [← hsingle,← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    by_cases he : d=P
    · rw [if_pos he]; exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (smallLevel_nonneg ..))
    rw [if_neg he,zero_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    by_cases hp : d.Prime
    · have hs : d≤N.sqrt := Nat.le_sqrt.mpr ((smaller_prime_square_le h hp (Nat.dvd_of_mem_divisors hd) he).trans
        (mem_Icc.mp hn).2)
      simp only [smallLevel,if_pos hp,if_pos hs,zero_add,le_refl]
    · rw [smallLevel,if_neg hp]
      apply le_add_of_nonneg_right
      split <;> positivity
  · subst n
    simp [largestPrimeFactor,smallLevel]

private theorem smallLevel_sum (N : ℕ) :
    ∑ d ∈ Icc 1 N, smallLevel N d = (Chebyshev.psi N-Chebyshev.theta N)+Chebyshev.psi N.sqrt := by
  simp only [smallLevel,sum_add_distrib]
  congr 1
  · calc
      _ = ∑ d ∈ Icc 1 N, (if ¬d.Prime then vonMangoldt d else 0) :=
        sum_congr rfl fun d _ => by by_cases hp : d.Prime <;> simp [hp]
      _ = _ := by rw [← sum_filter]; exact PrimeExponentialSums.sum_vonMangoldt_not_prime_eq N
  · rw [← sum_filter]
    have he : (Icc 1 N).filter (· ≤ N.sqrt) = Icc 1 N.sqrt := by
      ext d
      simp only [mem_filter,mem_Icc]
      have := Nat.sqrt_le_self N
      omega
    rw [he,Chebyshev.psi,Nat.floor_natCast]
    rfl

/-- The proper powers and the non-largest prime divisors account for the entire
difference, with an explicit ordinary Chebyshev bound. -/
theorem primeDivisorSizeMass_sub_largestPrimeLogMass (N : ℕ) :
    0 ≤ (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d:ℝ)*vonMangoldt d)-largestPrimeLogMass N ∧
    (∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (d:ℝ)*vonMangoldt d)-largestPrimeLogMass N ≤
      N*((Chebyshev.psi N-Chebyshev.theta N)+Chebyshev.psi N.sqrt) := by
  obtain ⟨hl,hu⟩ := primeDivisorSizeMass_bounds N
  refine ⟨sub_nonneg.mpr hl,(sub_le_iff_le_add'.mpr hu).trans ?_⟩
  rw [TransHorizonIncidenceMechanics.sum_Icc_sum_divisors_eq_floor,← smallLevel_sum,mul_sum]
  apply sum_le_sum
  intro d _
  have h : (d:ℝ)*((N/d:ℕ):ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N d
  calc
    _ = ((d:ℝ)*(N/d:ℕ))*smallLevel N d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (smallLevel_nonneg ..)

private theorem primeDivisorSizeMass_excess {q N : ℕ} (hq : N<q) :
    deepBlockPrimeExcess q N = primeDivisorSizeMass N-divisorSizeMass N := by
  rw [deepBlockPrimeExcess,divisorSizeMass,← sum_sub_distrib]
  refine sum_congr rfl fun n hn => ?_
  rw [sum_quotientClassMassOf_deep_block _ (mem_Icc.mp hn).1 ((mem_Icc.mp hn).2.trans_lt hq),
    ← sum_sub_distrib]
  exact sum_congr rfl fun d _ => by ring

private theorem deep_excess_distance {b : ℝ} (hb : 1/2≤b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ,
      |deepBlockPrimeExcess (N+1) N-(largestPrimeLogMass N-divisorSizeMass N)| ≤ C*(N:ℝ)^(b+1) := by
  obtain ⟨T,hT⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C := |T| + (Real.log 4+4)
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hC : 0≤C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun N => ?_⟩
  rw [primeDivisorSizeMass_excess (Nat.lt_succ_self N),sub_sub_sub_cancel_right]
  obtain ⟨hl,hu⟩ := primeDivisorSizeMass_sub_largestPrimeLogMass N
  rw [abs_of_nonneg hl]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact hu.trans (by simp [Real.zero_rpow (show b+1 ≠ 0 by linarith only [hb])])
  have hN0 : 0<(N:ℝ) := by exact_mod_cast hN
  have hN1 : 1≤(N:ℝ) := by exact_mod_cast hN
  have hsqrt : (N.sqrt:ℝ) ≤ Real.sqrt N :=
    (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr (by
      exact_mod_cast (by simpa only [pow_two] using Nat.sqrt_le N))
  have hsm := (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N.sqrt)).trans
      (mul_le_mul_of_nonneg_left hsqrt (by linarith only [hlog]))
  have hpp := (hT N).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
  have he : (Chebyshev.psi N-Chebyshev.theta N)+Chebyshev.psi N.sqrt ≤ C*Real.sqrt N := by
    dsimp only [C]; rw [add_mul]; exact add_le_add hpp hsm
  have hpow : Real.sqrt N ≤ (N:ℝ)^b := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hN1 hb
  calc
    _ ≤ (N:ℝ)*(C*Real.sqrt N) := hu.trans (mul_le_mul_of_nonneg_left he hN0.le)
    _ ≤ (N:ℝ)*(C*(N:ℝ)^b) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC) hN0.le
    _ = _ := by rw [Real.rpow_add_one hN0.ne']; ring

/-- Keeping only the largest prime factor preserves each ordinary prime-error
exponent down to and including one half, after centering by the divisor sum. -/
theorem largestPrimeLogMass_power_iff {b : ℝ} (hb : 1/2≤b) (hb1 : b<1) :
    (∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |largestPrimeLogMass N-divisorSizeMass N| ≤ C*(N:ℝ)^(b+1)) ↔
      ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |Chebyshev.psi N-N| ≤ C*(N:ℝ)^b := by
  rw [← deepBlockPrimeExcess_power_iff (fun N => N+1) Nat.lt_succ_self
    (by linarith only [hb] : 0<b) hb1]
  obtain ⟨T,hT,ht⟩ := deep_excess_distance hb
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨T+C,add_nonneg hT hC,fun N => ?_⟩
    have he := abs_sub_le (deepBlockPrimeExcess (N+1) N) (largestPrimeLogMass N-divisorSizeMass N) 0
    simp only [sub_zero] at he
    simpa only [add_mul] using he.trans (add_le_add (ht N) (h N))
  · rintro ⟨C,hC,h⟩
    refine ⟨T+C,add_nonneg hT hC,fun N => ?_⟩
    have he := abs_sub_le (largestPrimeLogMass N-divisorSizeMass N) (deepBlockPrimeExcess (N+1) N) 0
    rw [abs_sub_comm (largestPrimeLogMass N-divisorSizeMass N) (deepBlockPrimeExcess (N+1) N)] at he
    simp only [sub_zero] at he
    simpa only [add_mul] using he.trans (add_le_add (ht N) (h N))

private theorem twice_sum_integers (n : ℕ) :
    2*(∑ d ∈ Icc 1 n, (d:ℝ)) = (n:ℝ)*(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Icc_succ_top (by omega : 1≤n+1),mul_add,ih,Nat.cast_succ]
    ring

private theorem triangle_rounding (N d : ℕ) (hd : 0 < d) :
    |2*(∑ k ∈ Icc 1 (N/d), (k:ℝ)) - (N:ℝ)^2*(1/(d:ℝ)^2)| ≤ (N:ℝ)/d := by
  rw [twice_sum_integers]
  let x := (N:ℝ)/d
  let u : ℝ := (N/d:ℕ)
  have hx : 0≤x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hu : 0≤u := Nat.cast_nonneg _
  have h₁ : u≤x := Nat.cast_div_le
  have hd0 : 0<(d:ℝ) := by exact_mod_cast hd
  have h₂ : x≤u+1 := (div_le_iff₀ hd0).mpr (by
    dsimp only [u]
    exact_mod_cast ((Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (N/d))).le)
  have hl := (mul_le_mul_of_nonneg_left (show x-1≤u by linarith only [h₂]) hx).trans
    (mul_le_mul_of_nonneg_right h₂ hu)
  have hh := mul_le_mul h₁ (add_le_add_right h₁ 1) (by linarith only [hu]) hx
  rw [show (N:ℝ)^2*(1/(d:ℝ)^2)=x^2 by dsimp only [x]; ring]
  change |u*(u+1)-x^2|≤x
  rw [abs_le]
  constructor <;> linarith only [hl,hh]

private theorem basel_prefix_error {N : ℕ} (hN : 1≤N) :
    |(∑ d ∈ Icc 1 N, 1/(d:ℝ)^2)-Real.pi^2/6| ≤ 1/(N:ℝ) := by
  have he := ((hasSum_nat_add_iff' (N+1)).mpr hasSum_zeta_two).tsum_eq
  rw [sum_range_eq_add_Ico _ (by omega : 0<N+1),Ico_add_one_right_eq_Icc] at he
  simp only [Nat.cast_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,
    div_zero,zero_add] at he
  rw [abs_sub_comm,← he,abs_of_nonneg (tsum_nonneg fun _ => by positivity)]
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_comm (N:ℝ)] using
    (HilbertSchmidt.tsum_reciprocal_square_tail_le hN)

/-- The integer divisor baseline has quadratic coefficient π²/12, with an
explicit logarithmic remainder from rounding the triangular rows. -/
theorem divisorSizeMass_quadratic_error (N : ℕ) :
    |divisorSizeMass N - Real.pi^2/12*(N:ℝ)^2| ≤ (N:ℝ)*(2+Real.log N)/2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [divisorSizeMass]
  have hp : 0<(N:ℝ) := by exact_mod_cast hN
  let S := ∑ d ∈ Icc 1 N, 1/(d:ℝ)^2
  have hround : |2*divisorSizeMass N-(N:ℝ)^2*S| ≤ (N:ℝ)*(1+Real.log N) := by
    rw [divisorSizeMass,TransHorizonIncidenceMechanics.sum_Icc_sum_divisors_eq_floor,
      TransHorizonIncidenceMechanics.sum_mul_div_eq_sum_partial]
    dsimp only [S]
    rw [mul_sum,mul_sum,← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ d ∈ Icc 1 N, (N:ℝ)/d := sum_le_sum fun d hd => triangle_rounding N d (mem_Icc.mp hd).1
      _ ≤ _ := by
        simpa only [mul_sum,mul_one_div] using mul_le_mul_of_nonneg_left
          (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) hp.le
  have htail : |(N:ℝ)^2*S-(N:ℝ)^2*(Real.pi^2/6)| ≤ (N:ℝ) := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (basel_prefix_error hN) (sq_nonneg _)).trans_eq (by field_simp)
  have he := (abs_sub_le (2*divisorSizeMass N) ((N:ℝ)^2*S) ((N:ℝ)^2*(Real.pi^2/6))).trans
    (add_le_add hround htail)
  rw [show 2*divisorSizeMass N-(N:ℝ)^2*(Real.pi^2/6) = 2*(divisorSizeMass N-Real.pi^2/12*(N:ℝ)^2)
    by ring,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at he
  linarith only [he]

/-- After centering by π²N²/12 the largest prime factors alone recover every
prime-error exponent from one half up to one. -/
theorem largestPrimeLogMass_quadratic_power_iff {b : ℝ} (hb : 1/2≤b) (hb1 : b<1) :
    (∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |largestPrimeLogMass N-Real.pi^2/12*(N:ℝ)^2| ≤ C*(N:ℝ)^(b+1)) ↔
      ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, |Chebyshev.psi N-N| ≤ C*(N:ℝ)^b := by
  rw [← largestPrimeLogMass_power_iff hb hb1]
  have hbase (N : ℕ) : |divisorSizeMass N-Real.pi^2/12*(N:ℝ)^2| ≤ 2*(N:ℝ)^(b+1) := by
    apply (divisorSizeMass_quadratic_error N).trans
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [Real.zero_rpow (show b+1≠0 by linarith only [hb])]
    have h1 : 1≤(N:ℝ) := by exact_mod_cast hN
    have h0 := zero_lt_one.trans_le h1
    have hr := Real.one_le_sqrt.mpr h1
    have hl := _root_.RHTower.log_le_sqrt h0
    have hpow : Real.sqrt N ≤ (N:ℝ)^b := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le h1 hb
    rw [Real.rpow_add_one h0.ne']
    have hh := mul_le_mul_of_nonneg_right (show 2+Real.log N≤4*(N:ℝ)^b by
      linarith only [hr,hl,hpow]) h0.le
    linarith only [hh]
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨C+2,by positivity,fun N => ?_⟩
  · have ht := abs_sub_le (largestPrimeLogMass N) (Real.pi^2/12*(N:ℝ)^2) (divisorSizeMass N)
    rw [abs_sub_comm (Real.pi^2/12*(N:ℝ)^2)] at ht
    exact (ht.trans (add_le_add (h N) (hbase N))).trans_eq (add_mul ..).symm
  · exact ((abs_sub_le _ (divisorSizeMass N) _).trans (add_le_add (h N) (hbase N))).trans_eq (add_mul ..).symm

#print axioms primeDivisorSizeMass_sub_largestPrimeLogMass
#print axioms largestPrimeLogMass_power_iff
#print axioms divisorSizeMass_quadratic_error
#print axioms largestPrimeLogMass_quadratic_power_iff

end GaloisForLFunctions.ExceptionalLayerTheory
