import GaloisForLFunctions.BiScaleUncertainty.OddPrimeSieveFamilies
import GaloisForLFunctions.BiScaleUncertainty.FiniteCoprimeMomentCalculus

/-!
# Literal translated moments of finite odd-prime sieve families

The odd residue period is an exact antiperiod of the actual sieve response, so
all odd translated moments vanish. Even observations are exact CRT averages;
centered independent rows make every translated moment through degree five
insensitive to independent coefficient signs, including all zero cases.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- The parity character appearing in every twice-odd-prime sieve atom. -/
def parityFactor (n : ℕ) : ℝ := if 2 ∣ n then 1 else -1

/-- Integer translation multiplies the parity character. -/
theorem parityFactor_add (n h : ℕ) : parityFactor (n+h) = parityFactor n * parityFactor h := by
  have hn := Nat.mod_lt n (show 0 < 2 by decide)
  have hh := Nat.mod_lt h (show 0 < 2 by decide)
  have hs := Nat.add_mod n h 2
  simp only [parityFactor,Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> norm_num at * <;> omega

private theorem parityFactor_even_pow (n m : ℕ) : parityFactor n ^ (2*m) = 1 := by
  have hs : parityFactor n ^ 2 = 1 := by unfold parityFactor; split_ifs <;> norm_num
  rw [pow_mul,hs,one_pow]

private theorem parityFactor_odd {Q : ℕ} (hQ : Odd Q) : parityFactor Q = -1 := by
  have hn : ¬2 ∣ Q := by obtain ⟨k,hk⟩ := hQ; rintro ⟨j,hj⟩; omega
  simp [parityFactor,hn]

/-- The odd residue period of the full prime sector at a cutoff. -/
def primeFamilyPeriod (N : ℕ) : ℕ := ∏ p : oddPrimeModes N, (p : ℕ)

private theorem primeModes_coprime (N : ℕ) :
    Pairwise (fun p q : oddPrimeModes N => Nat.Coprime (p : ℕ) (q : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes (mem_oddPrimeModes.mp p.property).1
    (mem_oddPrimeModes.mp q.property).1).mpr
  intro h
  exact hpq (Subtype.ext h)

/-- The independent residue period divides the literal factorial sieve period. -/
theorem primeFamilyPeriod_dvd_factorial (N : ℕ) : primeFamilyPeriod N ∣ N.factorial := by
  apply coprime_prod_dvd _ (primeModes_coprime N)
  intro p
  have hp := mem_oddPrimeModes.mp p.property
  exact Nat.dvd_factorial (by have := hp.1.two_le; omega) (by omega)

/-- The residue period is odd, including the empty prime sector. -/
theorem primeFamilyPeriod_odd (N : ℕ) : Odd (primeFamilyPeriod N) := by
  exact odd_period_product _ (fun p => (mem_oddPrimeModes.mp p.property).2.1)

private theorem primeFamily_antiperiod (N : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    sieveSeq N (primeFamilyWeight N a) (n+primeFamilyPeriod N) =
      -sieveSeq N (primeFamilyWeight N a) n := by
  rw [sieveSeq_primeFamilyWeight,sieveSeq_primeFamilyWeight]
  change parityFactor (n+primeFamilyPeriod N) * _ = - (parityFactor n * _)
  rw [parityFactor_add,parityFactor_odd (primeFamilyPeriod_odd N)]
  have hr (p : oddPrimeModes N) :
      (((n+primeFamilyPeriod N : ℕ) : ZMod (p : ℕ))) = (n : ZMod (p : ℕ)) := by
    have hp : (p : ℕ) ∣ primeFamilyPeriod N := Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
    rw [Nat.cast_add,(ZMod.natCast_eq_zero_iff _ _).mpr hp,add_zero]
  simp_rw [hr]
  ring

/-- Every odd translated moment vanishes for the entire finite-prime family. -/
theorem primeFamily_odd_zero (N : ℕ) (a : ℕ → ℝ) (m : ℕ) (h : Fin (2*m+1) → ℕ) :
    translatedMoment N (primeFamilyWeight N a) h = 0 := by
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq,Complex.ofReal_zero]
  apply translationMoment_of_antiperiodic _ (primeFamilyPeriod N : ZMod N.factorial)
  intro n
  have hn : n+(primeFamilyPeriod N : ZMod N.factorial) =
      ((n.val+primeFamilyPeriod N : ℕ) : ZMod N.factorial) := by simp
  rw [hn,residueSignal_sieveSeq,primeFamily_antiperiod]
  have hr := residueSignal_sieveSeq N (primeFamilyWeight N a) n.val
  rw [ZMod.natCast_zmod_val] at hr
  rw [hr]
  simp

/-- Every even translated observation is an exact finite product-residue average. -/
theorem primeFamily_even_crt (N : ℕ) (a : ℕ → ℝ) (m : ℕ) (h : Fin (2*m) → ℕ) :
    translatedMoment N (primeFamilyWeight N a) h =
      (∏ i, parityFactor (h i)) *
        ((∑ x : ∀ p : oddPrimeModes N, ZMod (p : ℕ),
          ∏ i, ∑ p : oddPrimeModes N, a p * residueRow p (x p+(h i : ZMod (p : ℕ)))) /
          (primeFamilyPeriod N : ℝ)) := by
  have hprod (n : ℕ) : (∏ i, sieveSeq N (primeFamilyWeight N a) (n+h i)) =
      (∏ i, parityFactor (h i)) *
        ∏ i, ∑ p : oddPrimeModes N, a p * residueRow p ((n : ZMod (p : ℕ))+(h i : ZMod (p : ℕ))) := by
    simp only [sieveSeq_primeFamilyWeight,Nat.cast_add]
    change (∏ i : Fin (2*m), parityFactor (n+h i) *
      ∑ p : oddPrimeModes N, a p * residueRow p ((n : ZMod (p : ℕ))+(h i : ZMod (p : ℕ)))) = _
    simp only [parityFactor_add,Finset.prod_mul_distrib,Finset.prod_const,
      Finset.card_univ,Fintype.card_fin,parityFactor_even_pow,one_mul]
  unfold translatedMoment
  simp_rw [hprod]
  rw [← Finset.mul_sum,mul_div_assoc]
  congr 1
  exact period_average_crt (fun p : oddPrimeModes N => (p : ℕ)) (primeModes_coprime N)
    N.factorial (Nat.factorial_pos N) (primeFamilyPeriod_dvd_factorial N)
    (fun x : ∀ p : oddPrimeModes N, ZMod (p : ℕ) =>
      ∏ i : Fin (2*m), ∑ p : oddPrimeModes N, a p * residueRow p (x p+(h i : ZMod (p : ℕ))))

/-- All quartic lag observations depend only on the coefficient squares. -/
theorem primeFamily_quartic_eq_of_sq_eq (N : ℕ) (a b : ℕ → ℝ)
    (hsq : ∀ p : oddPrimeModes N, (a p)^2 = (b p)^2) (h : Fin 4 → ℕ) :
    translatedMoment N (primeFamilyWeight N a) h = translatedMoment N (primeFamilyWeight N b) h := by
  have heq := independent_quartic_eq_of_sq_eq
    (fun p : oddPrimeModes N => a p) (fun p : oddPrimeModes N => b p)
    (fun (i : Fin 4) (p : oddPrimeModes N) (x : ZMod (p : ℕ)) =>
      residueRow p (x+(h i : ZMod (p : ℕ)))) hsq
    (fun i p => sum_residueRow_shift (p : ℕ) (h i : ZMod (p : ℕ)))
  rw [primeFamily_even_crt N a 2 h,primeFamily_even_crt N b 2 h,heq]

/-- All quadratic lag observations have the same square-only dependence. -/
theorem primeFamily_quadratic_eq_of_sq_eq (N : ℕ) (a b : ℕ → ℝ)
    (hsq : ∀ p : oddPrimeModes N, (a p)^2 = (b p)^2) (h : Fin 2 → ℕ) :
    translatedMoment N (primeFamilyWeight N a) h = translatedMoment N (primeFamilyWeight N b) h := by
  have heq := independent_quadratic_eq_of_sq_eq
    (fun p : oddPrimeModes N => a p) (fun p : oddPrimeModes N => b p)
    (fun (i : Fin 2) (p : oddPrimeModes N) (x : ZMod (p : ℕ)) =>
      residueRow p (x+(h i : ZMod (p : ℕ)))) hsq
    (fun i p => sum_residueRow_shift (p : ℕ) (h i : ZMod (p : ℕ)))
  rw [primeFamily_even_crt N a 1 h,primeFamily_even_crt N b 1 h,heq]

/-- All translated data through degree five are insensitive to independent coefficient signs. -/
theorem primeFamily_through_five_eq_of_sq_eq (N : ℕ) (a b : ℕ → ℝ)
    (hsq : ∀ p : oddPrimeModes N, (a p)^2 = (b p)^2)
    (m : ℕ) (hm : m ≤ 5) (h : Fin m → ℕ) :
    translatedMoment N (primeFamilyWeight N a) h = translatedMoment N (primeFamilyWeight N b) h := by
  interval_cases m
  · simp [translatedMoment]
  · rw [primeFamily_odd_zero N a 0 h,primeFamily_odd_zero N b 0 h]
  · exact primeFamily_quadratic_eq_of_sq_eq N a b hsq h
  · rw [primeFamily_odd_zero N a 1 h,primeFamily_odd_zero N b 1 h]
  · exact primeFamily_quartic_eq_of_sq_eq N a b hsq h
  · rw [primeFamily_odd_zero N a 2 h,primeFamily_odd_zero N b 2 h]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
