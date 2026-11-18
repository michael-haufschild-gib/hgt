import GaloisForLFunctions.ExceptionalLayerTheory.TheFactorialParitySumHasTheMertensErrorExponent
import GaloisForLFunctions.ArithmeticElectrostatics.QuantizationTurnsWindowsIntoPoints
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import GaloisForLFunctions.RHTower.RieszFunctionMellinCriterion

/-!
# The absolute factorial weight in an ordinary prime count

Removing the parity signs replaces the alternating local exponential by the
positive one. Its quotient by zeta starts at degree two at each prime.
Summing the resulting floor errors gives every strict half-power bound.
-/

noncomputable section

open Finset ArithmeticFunction Filter Topology
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.Omega
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

open GaloisForLFunctions.TransHorizonIncidenceMechanics

private abbrev L : ArithmeticFunction ℝ := (liouville:ArithmeticFunction ℝ)

private theorem twist_weight : factorialParityWeight.pmul L=reciprocalFactorial := by
  have hw : factorialParityWeight.IsMultiplicative := localEuler_isMultiplicative _
  have hv : reciprocalFactorial.IsMultiplicative := localEuler_isMultiplicative _
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hw.pmul isMultiplicative_liouville.intCast) _ hv).mpr
    fun p k hp => ?_
  rw [pmul_apply,factorialParityWeight_pow hp,reciprocalFactorial_pow hp]
  simp only [L,intCoe_apply,liouville_apply (pow_ne_zero _ hp.ne_zero),cardFactors_apply_prime_pow hp,
    Int.cast_pow,Int.cast_neg,Int.cast_one]
  rw [div_mul_eq_mul_div,← mul_pow]
  norm_num

/-- Removing the sign gives exactly the reciprocal factorial coefficient. -/
theorem abs_factorialParityWeight (n : ℕ) : |factorialParityWeight n|=reciprocalFactorial n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := congrArg (fun a : ArithmeticFunction ℝ => |a n|) twist_weight
  have hv : 0≤reciprocalFactorial n := by
    change 0≤if n=0 then (0:ℝ) else ∏ p ∈ n.primeFactors, 1/((n.factorization p).factorial:ℝ)
    rw [if_neg hn.ne']
    exact prod_nonneg fun _ _ => by positivity
  simpa only [pmul_apply,abs_mul,L,intCoe_apply,liouville_apply hn.ne',Int.cast_pow,Int.cast_neg,
    Int.cast_one,abs_pow,abs_neg,abs_one,one_pow,mul_one,abs_of_nonneg hv] using h

private def dividedPositive : ArithmeticFunction ℝ :=
  ⟨fun n => |dividedFactorialParityWeight n|,by simp⟩

private theorem twist_divided : dividedFactorialParityWeight.pmul L=dividedPositive := by
  ext n
  have h := congrArg (fun a : ArithmeticFunction ℝ => a n) twist_weight
  change factorialParityWeight n*L n=reciprocalFactorial n at h
  change (factorialParityWeight n/((Ω n:ℝ)+1))*L n=|factorialParityWeight n/((Ω n:ℝ)+1)|
  rw [div_mul_eq_mul_div,h,abs_div,abs_factorialParityWeight,abs_of_nonneg (by positivity : 0≤(Ω n:ℝ)+1)]

private theorem prime_mul_dividedPositive :
    lastClassOrdinaryPrimeIndicator*dividedPositive=reciprocalFactorial-1 := by
  have hl (m n : ℕ) : L (m*n)=L m*L n := by
    simp only [L,intCoe_apply,liouville_apply_mul,Int.cast_mul]
  have hp : lastClassOrdinaryPrimeIndicator.pmul L = -lastClassOrdinaryPrimeIndicator := by
    ext n
    change lastClassOrdinaryPrimeIndicator n*L n = -lastClassOrdinaryPrimeIndicator n
    by_cases hn : n.Prime
    · simp only [show lastClassOrdinaryPrimeIndicator n=1 from if_pos hn,L,intCoe_apply,
        liouville_apply hn.ne_zero,cardFactors_apply_prime hn,pow_one,Int.cast_neg,Int.cast_one,one_mul]
    · rw [show lastClassOrdinaryPrimeIndicator n=0 from if_neg hn,zero_mul,neg_zero]
  have ho : (1:ArithmeticFunction ℝ).pmul L=1 := by
    ext n
    rcases eq_or_ne n 1 with rfl | hn
    · simp [L,pmul_apply,intCoe_apply,liouville_apply_one]
    · simp [pmul_apply,ArithmeticFunction.one_apply_ne hn]
  have h := GaloisForLFunctions.ArithmeticElectrostatics.pmul_mul_pmul
    (f := lastClassOrdinaryPrimeIndicator) (g := dividedFactorialParityWeight) hl
  rw [hp,twist_divided,neg_mul,ordinaryPrimeIndicator_mul_dividedFactorialParityWeight] at h
  have he : (1-factorialParityWeight).pmul L = (1:ArithmeticFunction ℝ).pmul L-factorialParityWeight.pmul L := by
    ext n
    change (_-_)*L n = _*L n - _*L n
    ring
  rw [he,ho,twist_weight] at h
  exact neg_injective (by simpa only [neg_sub] using h)

/-- The ordinary prime sum of the absolute divided coefficients counts the
positive factorial weight exactly, except for the unit. -/
theorem prime_sum_absolute_divided_weight {N : ℕ} (hn : 1≤N) :
    (∑ p ∈ Nat.primesLE N, ∑ m ∈ Icc 1 (N/p), |dividedFactorialParityWeight m|) =
    (∑ n ∈ Icc 1 N, reciprocalFactorial n)-1 := by
  have he : (∑ n ∈ Icc 1 N, (lastClassOrdinaryPrimeIndicator*dividedPositive) n) =
      ∑ p ∈ Nat.primesLE N, ∑ m ∈ Icc 1 (N/p), |dividedFactorialParityWeight m| := by
    rw [_root_.RHTower.sum_Icc_mul_apply,Nat.primesLE_eq_filter_Icc_one,sum_filter]
    refine sum_congr rfl fun p _ => ?_
    change (if p.Prime then (1:ℝ) else 0)*_=(if p.Prime then _ else 0)
    split <;> simp [dividedPositive]
  rw [← he,prime_mul_dividedPositive]
  change (∑ n ∈ Icc 1 N, (reciprocalFactorial n-(1:ArithmeticFunction ℝ) n)) = _
  rw [sum_sub_distrib,sum_eq_single_of_mem (f := fun n => (1:ArithmeticFunction ℝ) n) 1 (mem_Icc.mpr ⟨le_rfl,hn⟩)]
  · simp
  · exact fun n _ h => ArithmeticFunction.one_apply_ne h

/-- Density of the positive factorial weight. -/
def reciprocalFactorialDensity : ℝ := ∑' d : ℕ, (reciprocalFactorial*(μ:ArithmeticFunction ℝ)) d/d

private theorem floor_error_at_power (N d : ℕ) {b : ℝ} (hb : 0≤b) (hb1 : b≤1) :
    |((N/d:ℕ):ℝ)-(N:ℝ)/d|≤(N:ℝ)^b*(d:ℝ)^(-b) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [Nat.div_zero,Nat.cast_zero,div_zero,sub_self,abs_zero]
    positivity
  have hdr : 0<(d:ℝ) := by exact_mod_cast hd
  let x := (N:ℝ)/d
  have hx : 0≤x := div_nonneg (Nat.cast_nonneg _) hdr.le
  have hf : ⌊x⌋₊=N/d := by rw [show x=(N:ℝ)/d from rfl,Nat.floor_div_natCast,Nat.floor_natCast]
  have hle : ((N/d:ℕ):ℝ)≤x := hf ▸ Nat.floor_le hx
  have hlt : x<((N/d:ℕ):ℝ)+1 := hf ▸ Nat.lt_floor_add_one x
  change |((N/d:ℕ):ℝ)-x|≤_
  rw [abs_of_nonpos (sub_nonpos.mpr hle),Real.rpow_neg hdr.le,← div_eq_mul_inv,← Real.div_rpow (Nat.cast_nonneg _) hdr.le]
  change _≤x^b
  by_cases hx1 : 1≤x
  · exact (show -(((N/d:ℕ):ℝ)-x)≤1 by linarith only [hlt]).trans (Real.one_le_rpow hx1 hb)
  · have hp : x≤x^b := by
      rcases hx.eq_or_lt with hzero | hpos
      · rw [← hzero]; exact Real.rpow_nonneg (by norm_num) _
      · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hpos (le_of_not_ge hx1) hb1
    exact (show -(((N/d:ℕ):ℝ)-x)≤x by linarith only [Nat.cast_nonneg (α := ℝ) (N/d)]).trans hp

private theorem correction_at_one_summable :
    Summable (fun d : ℕ => |(reciprocalFactorial*(μ:ArithmeticFunction ℝ)) d / (d:ℝ)|) := by
  simpa only [abs_div,abs_of_nonneg (Nat.cast_nonneg _),div_eq_mul_inv,Real.rpow_neg_one] using
    reciprocalFactorial_correction_summable (b := 1) (by norm_num)

private theorem reciprocal_pole_factor {p : ℕ} (hp : p.Prime) :
    poleLocalFactor reciprocalFactorial p = Real.exp (p:ℝ)⁻¹ := by
  rw [poleLocalFactor,← _root_.RHTower.tsum_pow_div_factorial_eq_exp]
  exact tsum_congr fun k => by rw [reciprocalFactorial_pow hp]; ring

/-- The density is the positive product of the local factorial densities. -/
theorem reciprocalFactorialDensity_product :
    reciprocalFactorialDensity = ∏' p : Nat.Primes,
      (1-((p:ℕ):ℝ)⁻¹)*Real.exp ((p:ℕ):ℝ)⁻¹ := by
  let h := reciprocalFactorial*(μ:ArithmeticFunction ℝ)
  have hv : reciprocalFactorial.IsMultiplicative := localEuler_isMultiplicative _
  have hg : h.IsMultiplicative := hv.mul isMultiplicative_moebius.intCast
  have hB (n : ℕ) : |reciprocalFactorial n|≤1 := by
    rw [← abs_factorialParityWeight,abs_abs]; exact abs_factorialParityWeight_le_one n
  have hs : Summable fun n : ℕ => ‖h n/n‖ := by
    simpa only [Real.norm_eq_abs] using correction_at_one_summable
  have he := EulerProduct.eulerProduct_tprod (f := fun n : ℕ => h n/n)
    (by simp [hg.map_one]) (fun {m n} hmn => by
      rw [hg.map_mul_of_coprime hmn,Nat.cast_mul,mul_div_mul_comm]) hs (by simp)
  rw [reciprocalFactorialDensity,← he]
  refine tprod_congr fun p => ?_
  rw [← reciprocal_pole_factor p.prop,← tsum_mul_moebius_localFactor hv hB p.prop]
  exact tsum_congr fun k => by simp only [h,Nat.cast_pow,div_eq_mul_inv,inv_pow]

theorem reciprocalFactorialDensity_pos : 0<reciprocalFactorialDensity := by
  have hv : reciprocalFactorial.IsMultiplicative := localEuler_isMultiplicative _
  have hp (p : ℕ) (h : p.Prime) : reciprocalFactorial p=1 := by
    simpa using reciprocalFactorial_pow h 1
  have hB (n : ℕ) : |reciprocalFactorial n|≤1 := by
    rw [← abs_factorialParityWeight,abs_abs]; exact abs_factorialParityWeight_le_one n
  have hn : reciprocalFactorialDensity≠0 :=
    tsum_mul_moebius_div_ne_zero hv hp hB (ε := 1/2) (by norm_num) le_rfl
      (fun p h => by rw [reciprocal_pole_factor h]; exact (Real.exp_pos _).ne')
  refine lt_of_le_of_ne ?_ hn.symm
  rw [reciprocalFactorialDensity_product]
  exact tprod_nonneg fun p => mul_nonneg
    (sub_nonneg.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast p.prop.one_lt)).le) (Real.exp_pos _).le

/-- The entire discrepancy is the absolutely convergent sum of the signed
floor errors, including the divisors above the cutoff. -/
theorem hasSum_reciprocalFactorial_rounding (N : ℕ) :
    HasSum (fun d : ℕ => (reciprocalFactorial*(μ:ArithmeticFunction ℝ)) d*
      (((N/d:ℕ):ℝ)-(N:ℝ)/d))
    ((∑ n ∈ Icc 1 N, reciprocalFactorial n)-(N:ℝ)*reciprocalFactorialDensity) := by
  let h := reciprocalFactorial*(μ:ArithmeticFunction ℝ)
  have hh : h*(ζ:ArithmeticFunction ℝ)=reciprocalFactorial := by
    dsimp only [h]
    rw [mul_assoc,coe_moebius_mul_coe_zeta,mul_one]
  have hprefix : (∑ n ∈ Icc 1 N, reciprocalFactorial n) = ∑' d : ℕ, h d*((N/d:ℕ):ℝ) := by
    rw [← hh,_root_.RHTower.sum_Icc_mul_apply,tsum_eq_sum (s := Icc 1 N)]
    · refine sum_congr rfl fun d _ => congrArg (h d*·) ?_
      have he (i : ℕ) (hi : i∈Icc 1 (N/d)) : (ζ:ArithmeticFunction ℝ) i=1 := by
        simp only [natCoe_apply,zeta_apply_ne (Nat.ne_of_gt (mem_Icc.mp hi).1),Nat.cast_one]
      rw [sum_congr rfl he,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
    · intro d hd
      rcases Nat.eq_zero_or_pos d with rfl | hdr
      · simp
      · rw [Nat.div_eq_of_lt (by have := mt mem_Icc.mpr hd; omega),Nat.cast_zero,mul_zero]
  have hdensity : Summable (fun d : ℕ => h d/d) := correction_at_one_summable.of_abs
  have hf : Summable (fun d : ℕ => h d*((N/d:ℕ):ℝ)) := by
    apply summable_of_ne_finset_zero (s := Icc 1 N)
    intro d hd
    rcases Nat.eq_zero_or_pos d with rfl | hdr
    · simp
    · rw [Nat.div_eq_of_lt (by have := mt mem_Icc.mpr hd; omega),Nat.cast_zero,mul_zero]
  rw [hprefix]
  have hd : HasSum (fun d : ℕ => h d/d) reciprocalFactorialDensity := hdensity.hasSum
  apply (hf.hasSum.sub (hd.mul_left (N:ℝ))).congr_fun
  intro d
  dsimp only [Pi.sub_apply]
  ring

/-- Summing fractional-part errors after removing zeta gives an explicit
constant at each exponent above one half. -/
theorem reciprocalFactorial_sum_error {b : ℝ} (hb : 1/2<b) (hb1 : b≤1) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, reciprocalFactorial n) - N*reciprocalFactorialDensity| ≤
      (N:ℝ)^b*(∑' d : ℕ, |(reciprocalFactorial*(μ:ArithmeticFunction ℝ)) d| * (d:ℝ)^(-b)) := by
  let h := reciprocalFactorial*(μ:ArithmeticFunction ℝ)
  have he := hasSum_reciprocalFactorial_rounding N
  have hs : Summable (fun d : ℕ => |h d| * (d:ℝ)^(-b)) := reciprocalFactorial_correction_summable hb
  rw [← he.tsum_eq,← Real.norm_eq_abs,← tsum_mul_left]
  apply (norm_tsum_le_tsum_norm he.summable.norm).trans
  refine he.summable.norm.tsum_le_tsum (fun d => ?_) (hs.mul_left _)
  rw [Real.norm_eq_abs,abs_mul]
  exact (mul_le_mul_of_nonneg_left (floor_error_at_power N d (by linarith only [hb]) hb1)
    (abs_nonneg (h d))).trans_eq (by ring)

/-- Ordinary primes counting the absolute divided coefficients have a linear main
term with an explicit error at each strict half-power exponent up to one. -/
theorem prime_sum_absolute_divided_weight_error {b : ℝ} (hb : 1/2<b) (hb1 : b≤1)
    {N : ℕ} (hN : 1≤N) :
    |(∑ p ∈ Nat.primesLE N, ∑ m ∈ Icc 1 (N/p), |dividedFactorialParityWeight m|) -
      ((N:ℝ)*reciprocalFactorialDensity-1)| ≤
      (N:ℝ)^b*(∑' d : ℕ, |(reciprocalFactorial*(μ:ArithmeticFunction ℝ)) d| * (d:ℝ)^(-b)) := by
  rw [prime_sum_absolute_divided_weight hN,sub_sub_sub_cancel_right]
  exact reciprocalFactorial_sum_error hb hb1 N

#print axioms reciprocalFactorialDensity_pos
#print axioms prime_sum_absolute_divided_weight_error
#print axioms reciprocalFactorial_sum_error

end GaloisForLFunctions.ExceptionalLayerTheory
