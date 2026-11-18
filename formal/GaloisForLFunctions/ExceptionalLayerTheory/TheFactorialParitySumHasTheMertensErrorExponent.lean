import GaloisForLFunctions.ExceptionalLayerTheory.TheFactorialWeightAtTheOrdinaryPrimeGrowthBoundary
import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiplicativeWeightsPretendingToOneArePaidOnlyByAVanishingLocalFactor
import GaloisForLFunctions.RHTower.DampedMobiusSumsZeroFree
import GaloisForLFunctions.BezoutValuationIncidence.TheBalancedStatisticIsTheQuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.PowerGrowthUnderArithmeticConvolution
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization

/-!
# The Möbius error exponent of the factorial parity sum

The local quotient between the factorial-weighted parity function and
Möbius has zero linear term at every prime. The inverse quotient has the
same property. Both absolute Euler products converge to the right of one half.
-/

noncomputable section

open ArithmeticFunction Finset Filter
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

open GaloisForLFunctions.TransHorizonIncidenceMechanics

private theorem summable_of_damped_wiener {g : ArithmeticFunction ℝ} {b : ℝ}
    (h : CriticalWiener (dampedSignWeight ⇑g (b-1/2))) :
    Summable (fun n : ℕ => |g n| * (n:ℝ)^(-b)) := by
  apply h.congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [dampedSignWeight]
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  rw [dampedSignWeight,abs_mul,abs_of_nonneg (Real.rpow_nonneg hnR.le _),mul_assoc,
    ← Real.rpow_add hnR,show -(b-1/2)+-(1/2:ℝ)=-b by ring]

/-- The positive multiplicative weight with local coefficients 1/k!. -/
def reciprocalFactorial : ArithmeticFunction ℝ :=
  localEuler (fun _ k => (1:ℝ)/(k.factorial:ℝ))

/-- The reciprocal factorial weight on a prime power. -/
theorem reciprocalFactorial_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    reciprocalFactorial (p^k)=1/(k.factorial:ℝ) := by
  rw [reciprocalFactorial,localEuler_prime_pow _ (⟨p,hp⟩:Nat.Primes) k]
  split_ifs with h
  · simp [h]
  · rfl

/-- The alternating and positive factorial weights are convolution inverses. -/
theorem parity_mul_reciprocalFactorial : factorialParityWeight*reciprocalFactorial=1 := by
  have hw : factorialParityWeight.IsMultiplicative := localEuler_isMultiplicative _
  have hv : reciprocalFactorial.IsMultiplicative := localEuler_isMultiplicative _
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hw.mul hv) _ isMultiplicative_one).mpr
    fun p k hp => ?_
  rw [_root_.RHTower.DampedMobius.mul_apply_prime_pow _ _ hp]
  simp only [factorialParityWeight_pow hp,reciprocalFactorial_pow hp]
  calc
    _ = ((-1:ℝ)+1)^k/(k.factorial:ℝ) := by
      rw [add_pow,Finset.sum_div]
      refine sum_congr rfl fun j hj => ?_
      rw [one_pow,mul_one,Nat.cast_choose ℝ (Nat.le_of_lt_succ (mem_range.mp hj))]
      field_simp
    _ = _ := by
      rcases k with _ | k
      · simp
      · rw [neg_add_cancel,zero_pow (Nat.succ_ne_zero _),zero_div,
          ArithmeticFunction.one_apply_ne (ne_of_gt (Nat.one_lt_pow (Nat.succ_ne_zero _) hp.one_lt))]

/-- Removing zeta from the positive factorial weight leaves an absolutely
summable factor at every real exponent above one half. -/
theorem reciprocalFactorial_correction_summable {b : ℝ} (hb : 1/2<b) :
    Summable (fun n : ℕ => |(reciprocalFactorial*(μ:ArithmeticFunction ℝ)) n| * (n:ℝ)^(-b)) := by
  let h := reciprocalFactorial*(μ:ArithmeticFunction ℝ)
  have hv : reciprocalFactorial.IsMultiplicative := localEuler_isMultiplicative _
  have he : 0<b-1/2 := sub_pos.mpr hb
  have hprime (p : ℕ) (hp : p.Prime) : h p=0 := by
    simpa only [h,zero_add,pow_one,pow_zero] using (mul_moebius_apply_prime_pow reciprocalFactorial hp 0).trans (by
      rw [reciprocalFactorial_pow hp,reciprocalFactorial_pow hp]; norm_num)
  refine summable_of_damped_wiener (criticalWiener_of_multiplicative
    (hv.mul isMultiplicative_moebius.intCast) hprime (B := 1) zero_le_one (fun p hp k hk => ?_) he)
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega)
  change |(reciprocalFactorial*(μ:ArithmeticFunction ℝ)) (p^(j+1))| ≤ _
  rw [mul_moebius_apply_prime_pow _ hp,reciprocalFactorial_pow hp,reciprocalFactorial_pow hp]
  have hi (i : ℕ) : 0≤(1:ℝ)/(i.factorial:ℝ) ∧ (1:ℝ)/(i.factorial:ℝ)≤1 :=
    ⟨by positivity,(div_le_one (by positivity)).mpr (by exact_mod_cast Nat.factorial_pos _)⟩
  rw [one_mul,abs_le]
  have htwo : (2:ℝ)≤(j.succ:ℝ) := by exact_mod_cast hk
  constructor <;> linarith only [(hi j).1,(hi j).2,(hi (j+1)).1,(hi (j+1)).2,htwo]

private theorem prime_power_correction_pair {b : ℝ} (hb : 1/2<b) :
    ∃ g h : ArithmeticFunction ℝ, g*(μ:ArithmeticFunction ℝ)=factorialParityWeight ∧
      h*factorialParityWeight=(μ:ArithmeticFunction ℝ) ∧
      Summable (fun n : ℕ => |g n| * (n:ℝ)^(-b)) ∧
      Summable (fun n : ℕ => |h n| * (n:ℝ)^(-b)) := by
  let g := factorialParityWeight*(ζ:ArithmeticFunction ℝ)
  let h := reciprocalFactorial*(μ:ArithmeticFunction ℝ)
  have hw : factorialParityWeight.IsMultiplicative := localEuler_isMultiplicative _
  have hpw (p : ℕ) (hp : p.Prime) : factorialParityWeight p = -1 := by
    simpa using factorialParityWeight_pow hp 1
  have he : 0<b-1/2 := sub_pos.mpr hb
  refine ⟨g,h,by dsimp only [g]; rw [mul_assoc,coe_zeta_mul_coe_moebius,mul_one],?_,
    summable_of_damped_wiener (criticalWiener_mul_zeta hw hpw abs_factorialParityWeight_le_one he),?_⟩
  · dsimp only [h]
    rw [mul_comm _ factorialParityWeight,← mul_assoc,parity_mul_reciprocalFactorial,one_mul]
  · exact reciprocalFactorial_correction_summable hb

/-- A summable factor transfers a partial-sum estimate at the given exponent. -/
private theorem convolution_at_exponent {a g : ArithmeticFunction ℝ} {b : ℝ} (hb : 0≤b)
    (hg : Summable (fun n : ℕ => |g n| * (n:ℝ)^(-b)))
    (ha : ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → |∑ n ∈ Icc 1 N, a n|≤C*(N:ℝ)^b) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → |∑ n ∈ Icc 1 N, (g*a) n|≤C*(N:ℝ)^b := by
  obtain ⟨C,hC,h⟩ := ha
  let D := ∑' n : ℕ, |g n| * (n:ℝ)^(-b)
  have hterm (n : ℕ) : 0≤|g n| * (n:ℝ)^(-b) := mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hD : 0≤D := tsum_nonneg hterm
  refine ⟨C*D,mul_nonneg hC hD,fun N _ => ?_⟩
  rw [_root_.RHTower.sum_Icc_mul_apply]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, |g d * ∑ m ∈ Icc 1 (N/d), a m| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, (C*(N:ℝ)^b)*(|g d| * (d:ℝ)^(-b)) := by
      refine sum_le_sum fun d hd => ?_
      obtain ⟨hd,hdN⟩ := mem_Icc.mp hd
      have hdr : 0<(d:ℝ) := by exact_mod_cast hd
      have hdv : ((N/d:ℕ):ℝ)≤(N:ℝ)/d := (le_div_iff₀ hdr).mpr (by exact_mod_cast Nat.div_mul_le_self N d)
      have hpow := Real.rpow_le_rpow (Nat.cast_nonneg _) hdv hb
      rw [Real.div_rpow (Nat.cast_nonneg _) hdr.le,div_eq_mul_inv,← Real.rpow_neg hdr.le] at hpow
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left ((h _ ((Nat.one_le_div_iff hd).mpr hdN)).trans
        (mul_le_mul_of_nonneg_left hpow hC)) (abs_nonneg _)).trans_eq (by ring)
    _ = (C*(N:ℝ)^b)*∑ d ∈ Icc 1 N, |g d| * (d:ℝ)^(-b) := (mul_sum _ _ _).symm
    _ ≤ (C*(N:ℝ)^b)*D := mul_le_mul_of_nonneg_left (hg.sum_le_tsum _ fun d _ => hterm d) (by positivity)
    _ = _ := by ring

/-- Above one half the factorial parity sum has exactly the ordinary Mertens
power bounds, at the same exponent in both directions. -/
theorem factorialParityWeight_power_iff_mertens {b : ℝ} (hb : 1/2<b) :
    (∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → |∑ n ∈ Icc 1 N, factorialParityWeight n|≤C*(N:ℝ)^b) ↔
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → |mertensM N|≤C*(N:ℝ)^b := by
  have hμ (N : ℕ) : ∑ n ∈ Icc 1 N, (μ:ArithmeticFunction ℝ) n=mertensM N :=
    GaloisForLFunctions.BezoutValuationIncidence.sum_Icc_moebiusReal_eq_mertensM N
  simp_rw [← hμ]
  obtain ⟨g,h,hg,hh,sg,sh⟩ := prime_power_correction_pair hb
  have hb0 : 0≤b := by linarith only [hb]
  constructor
  · intro hw
    simpa only [hh] using convolution_at_exponent hb0 sh hw
  · intro hm
    simpa only [hg] using convolution_at_exponent hb0 sg hm

#print axioms factorialParityWeight_power_iff_mertens

end GaloisForLFunctions.ExceptionalLayerTheory
