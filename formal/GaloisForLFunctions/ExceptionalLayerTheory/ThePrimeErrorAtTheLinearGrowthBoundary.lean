import GaloisForLFunctions.ExceptionalLayerTheory.TheFactorialParitySumHasTheMertensErrorExponent
import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimesSeparateSignedQuotientProfiles
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheOneFifthRateUnderTheRiemannHypothesis
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis

/-!
# A linear profile with a power-saving ordinary prime count

Dividing the factorial parity weight by one plus the total number of prime
factors gives a nonzero profile at the sharp boundary for signed prime counts.
Its unweighted prime sum has precisely the Mertens power bounds above one half.
-/

noncomputable section

open Finset ArithmeticFunction
open _root_.RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Partial sums of the divided factorial coefficients. -/
def factorialParityProfile (N : ℕ) : ℝ := ∑ m ∈ Icc 1 N, dividedFactorialParityWeight m

theorem factorialParityProfile_one : factorialParityProfile 1=1 := by
  simp [factorialParityProfile,dividedFactorialParityWeight,factorialParityWeight]

theorem abs_factorialParityProfile_le (N : ℕ) : |factorialParityProfile N|≤N := by
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum
    (fun m (_ : m∈Icc 1 N) => abs_dividedFactorialParityWeight_le_one m)).trans_eq (by simp))

/-- Every exponent above one half is preserved by taking the prime sum of this profile. -/
theorem prime_sum_factorialParityProfile_power_iff {b : ℝ} (hb : 1/2<b) :
    (∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → |∑ p ∈ Nat.primesLE N, factorialParityProfile (N/p)|≤C*(N:ℝ)^b) ↔
      ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → |mertensM N|≤C*(N:ℝ)^b := by
  rw [← factorialParityWeight_power_iff_mertens hb]
  have hbound (N : ℕ) (hn : 1≤N) : (1:ℝ)≤(N:ℝ)^b :=
    Real.one_le_rpow (by exact_mod_cast hn) (by linarith only [hb])
  have htri (a c : ℝ) (he : a+c=1) : |a|≤1+|c| := by
    rw [show a=1-c by linarith only [he]]
    simpa only [abs_one] using abs_sub (1:ℝ) c
  have he (N : ℕ) (hn : 1≤N) : (∑ p ∈ Nat.primesLE N, factorialParityProfile (N/p)) +
      (∑ n ∈ Icc 1 N, factorialParityWeight n) = 1 := by
    simpa only [factorialParityProfile] using (eq_sub_iff_add_eq.mp (prime_sum_dividedFactorialParityWeight hn))
  constructor <;> rintro ⟨C,hC,h⟩ <;> refine ⟨1+C,by linarith only [hC],fun N hn => ?_⟩
  · have ht := htri _ _ ((add_comm ..).trans (he N hn))
    rw [add_mul,one_mul]
    exact ht.trans (add_le_add (hbound N hn) (h N hn))
  · rw [add_mul,one_mul]
    exact (htri _ _ (he N hn)).trans (add_le_add (hbound N hn) (h N hn))

/-- The ordinary prime sum has every power saving supplied by the seven-eighths strip. -/
theorem prime_sum_factorialParityProfile_of_seven_eighths {b : ℝ} (hb : 7/8<b) (hb1 : b<1) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N →
      |∑ p ∈ Nat.primesLE N, factorialParityProfile (N/p)|≤C*(N:ℝ)^b := by
  apply (prime_sum_factorialParityProfile_power_iff (by linarith only [hb])).2
  have h := GaloisForLFunctions.ArithmeticAuxiliaryDynamics.exists_mertens_power_of_zeroFree
    (Θ := 7/8) (σ := 1-b) (by norm_num) (by norm_num)
    (fun _ hs => GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_seven_eighths_lt_re hs)
    (sub_pos.mpr hb1) (by linarith only [hb])
  simpa only [sub_sub_cancel] using h

/-- One explicit sublinear exponent for the nonzero linear-growth profile. -/
theorem prime_sum_factorialParityProfile_power_saving :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N →
      |∑ p ∈ Nat.primesLE N, factorialParityProfile (N/p)|≤C*(N:ℝ)^(15/16:ℝ) :=
  prime_sum_factorialParityProfile_of_seven_eighths (by norm_num) (by norm_num)

/-- The profile itself fails every strictly sublinear power bound. -/
theorem factorialParityProfile_has_no_sublinear_power {a : ℝ} (ha : 0≤a) (ha1 : a<1) :
    ¬∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → |factorialParityProfile N|≤C*(N:ℝ)^a := by
  intro hf
  obtain ⟨C,_,h⟩ := prime_sum_factorialParityProfile_power_saving
  have hz := (sublinear_prime_quotient_count_iff_zero factorialParityProfile ha ha1
    (b := 15/16) (by norm_num) (by norm_num) hf).1 ⟨C,h⟩ 1 le_rfl
  rw [factorialParityProfile_one] at hz
  exact one_ne_zero hz

/-- Testing the single explicit profile at all strict half-power exponents is equivalent to RH. -/
theorem riemannHypothesis_iff_prime_sum_factorialParityProfile :
    RiemannHypothesis ↔ ∀ b : ℝ, 1/2<b → ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N →
      |∑ p ∈ Nat.primesLE N, factorialParityProfile (N/p)|≤C*(N:ℝ)^b := by
  rw [← _root_.RHTower.mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis]
  constructor
  · intro hm b hb
    apply (prime_sum_factorialParityProfile_power_iff hb).2
    obtain ⟨C,hC,h⟩ := hm (b-1/2) (sub_pos.mpr hb)
    have hb0 : 0≤b := by linarith only [hb]
    refine ⟨C*(2:ℝ)^b,by positivity,fun N hn => ?_⟩
    have hN := h N
    rw [_root_.RHTower.mobiusMertensPartialSum_eq_sieveMertensM,Complex.norm_real,Real.norm_eq_abs,
      show 1/2+(b-1/2)=b by ring] at hN
    have hnR : 1≤(N:ℝ) := by exact_mod_cast hn
    have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤N+1)
      (show (N:ℝ)+1≤2*N by linarith only [hnR]) hb0
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)] at hp
    exact (hN.trans (mul_le_mul_of_nonneg_left hp hC)).trans_eq (mul_assoc ..).symm
  · intro h ε hε
    have hb : (1:ℝ)/2<1/2+ε := lt_add_of_pos_right _ hε
    obtain ⟨C,hC,hm⟩ := (prime_sum_factorialParityProfile_power_iff hb).1 (h _ hb)
    refine ⟨C,hC,fun N => ?_⟩
    rw [_root_.RHTower.mobiusMertensPartialSum_eq_sieveMertensM,Complex.norm_real,Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simpa [mertensM] using hC
    · exact (hm N hn).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (le_add_of_nonneg_right zero_le_one) (by linarith only [hε])) hC)

#print axioms riemannHypothesis_iff_prime_sum_factorialParityProfile
#print axioms prime_sum_factorialParityProfile_power_saving
#print axioms factorialParityProfile_has_no_sublinear_power

end GaloisForLFunctions.ExceptionalLayerTheory
