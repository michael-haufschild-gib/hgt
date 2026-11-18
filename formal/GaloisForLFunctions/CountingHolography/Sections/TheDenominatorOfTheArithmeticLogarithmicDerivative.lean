import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralTests

/-! # The denominator of the arithmetic logarithmic derivative

For a finitely supported integer vector of prime valuations, summing
the valuation at p divided by p records all entropy congruences in one
rational number. Each failed congruence contributes exactly one factor
of p to the reduced denominator.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset HTGeometry.Arithmetic

/-- The arithmetic derivative divided by the price, in prime coordinates. -/
def primeReciprocalReading (a : Nat.Primes →₀ ℤ) : ℚ :=
  ∑ p ∈ a.support, (a p:ℚ)/(p:ℕ)

private theorem norm_off_prime {p j : Nat.Primes} (h : j ≠ p) (z : ℤ) :
    padicNorm (p:ℕ) ((z:ℚ)/(j:ℕ)) ≤ 1 := by
  letI : Fact (p:ℕ).Prime := ⟨p.property⟩
  have hn : ¬ (p:ℕ) ∣ (j:ℕ) := fun hd =>
    h (Subtype.ext (((Nat.dvd_prime j.property).mp hd).resolve_left p.property.ne_one).symm)
  rw [padicNorm.div,(padicNorm.nat_eq_one_iff (j:ℕ)).mpr hn,div_one]
  exact padicNorm.of_int _

/-- Every failed prime congruence has valuation exactly one in the
denominator, and every satisfied congruence has valuation zero. -/
theorem primeReciprocalReading_den_exponent (a : Nat.Primes →₀ ℤ) (p : Nat.Primes) :
    (primeReciprocalReading a).den.factorization (p:ℕ) = if (p:ℤ) ∣ a p then 0 else 1 := by
  classical
  let x := primeReciprocalReading a
  letI : Fact (p:ℕ).Prime := ⟨p.property⟩
  have hp : 1 < ((p:ℕ):ℚ) := by exact_mod_cast p.property.one_lt
  have hp0 : (0:ℚ)<(p:ℕ) := zero_lt_one.trans hp
  rw [Nat.factorization_def _ p.property]
  by_cases h : (p:ℤ) ∣ a p
  · rw [if_pos h]
    obtain ⟨k,hk⟩ := h
    have hnorm : padicNorm (p:ℕ) x ≤ 1 := by
      apply padicNorm.sum_le' ?_ zero_le_one
      intro j _
      by_cases he : j=p
      · subst j
        rw [hk,Int.cast_mul,Int.cast_natCast,mul_div_cancel_left₀ _ (ne_of_gt hp0)]
        exact padicNorm.of_int _
      · exact norm_off_prime he _
    by_cases hx : x=0
    · change padicValNat (p:ℕ) x.den=0
      simp [hx]
    have hval : 0 ≤ padicValRat (p:ℕ) x := by
      rw [padicNorm.eq_zpow_of_nonzero hx,← zpow_zero ((p:ℕ):ℚ)] at hnorm
      have he := (zpow_le_zpow_iff_right₀ hp).mp hnorm
      omega
    exact padicValNat.eq_zero_of_not_dvd ((nonneg_val_iff_not_dvd_den (p:ℕ) x).mp hval)
  · rw [if_neg h]
    have hmem : p ∈ a.support := Finsupp.mem_support_iff.mpr (fun hz => h (hz ▸ dvd_zero _))
    have hrest : padicNorm (p:ℕ) (∑ j ∈ a.support.erase p, (a j:ℚ)/(j:ℕ)) ≤ 1 :=
      padicNorm.sum_le' (fun j hj => norm_off_prime (mem_erase.mp hj).1 _) zero_le_one
    have hone : padicNorm (p:ℕ) ((a p:ℚ)/(p:ℕ))=(p:ℕ) := by
      rw [padicNorm.div,(padicNorm.int_eq_one_iff (a p)).mpr h,padicNorm.padicNorm_p_of_prime,one_div,inv_inv]
    have hnorm : padicNorm (p:ℕ) x=(p:ℕ) := by
      dsimp only [x,primeReciprocalReading]
      rw [← sum_erase_add _ _ hmem,padicNorm.add_eq_max_of_ne (by rw [hone]; exact (hrest.trans_lt hp).ne),
        hone,max_eq_right (hrest.trans hp.le)]
    have hx : x≠0 := fun hh => hp0.ne' (by rw [← hnorm,hh,padicNorm.zero])
    rw [padicNorm.eq_zpow_of_nonzero hx] at hnorm
    have he := (zpow_right_inj₀ hp0 hp.ne').mp
      (show ((p:ℕ):ℚ)^(-padicValRat (p:ℕ) x)=((p:ℕ):ℚ)^(1:ℤ) by simpa only [zpow_one] using hnorm)
    have hd := den_valuation_eq_negative_part (p:ℕ) x
    change padicValNat (p:ℕ) x.den = 1
    omega

/-- The product over primes at which the congruence fails is already the
reduced denominator. No cancellation between distinct primes can remove it. -/
theorem primeReciprocalReading_den (a : Nat.Primes →₀ ℤ) :
    (primeReciprocalReading a).den = ∏ p ∈ a.support.filter (fun p => ¬ (p:ℤ) ∣ a p), (p:ℕ) := by
  classical
  let S := a.support.filter (fun p => ¬ (p:ℤ) ∣ a p)
  have hpos : 0 < ∏ p ∈ S, (p:ℕ) := prod_pos fun p _ => p.property.pos
  apply Nat.factorization_inj (primeReciprocalReading a).den_nz hpos.ne'
  ext k
  by_cases hp : k.Prime
  · let p : Nat.Primes := ⟨k,hp⟩
    have hs : p ∈ S ↔ ¬ (p:ℤ) ∣ a p := by
      rw [show S=a.support.filter _ from rfl,mem_filter]
      exact ⟨And.right,fun h => ⟨Finsupp.mem_support_iff.mpr (fun hz => h (hz ▸ dvd_zero _)),h⟩⟩
    change (primeReciprocalReading a).den.factorization (p:ℕ)=(∏ j ∈ S,(j:ℕ)).factorization (p:ℕ)
    rw [primeReciprocalReading_den_exponent,Nat.factorization_prod (fun j _ => j.property.ne_zero),
      Finsupp.finsetSum_apply]
    have hj (j : Nat.Primes) : (j:ℕ).factorization (p:ℕ) = if j=p then 1 else 0 := by
      rw [j.property.factorization,Finsupp.single_apply]
      simp only [Subtype.coe_inj]
    simp only [hj]
    by_cases h : (p:ℤ) ∣ a p <;> simp [h,hs]
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The reciprocal reading is an integer exactly when each prime divides
its own coordinate. -/
theorem primeReciprocalReading_den_one_iff (a : Nat.Primes →₀ ℤ) :
    (primeReciprocalReading a).den=1 ↔ ∀ p : Nat.Primes, (p:ℤ) ∣ a p := by
  constructor
  · intro h p
    by_contra hp
    have he := primeReciprocalReading_den_exponent a p
    rw [h,if_neg hp] at he
    simpa using he
  · intro h
    rw [primeReciprocalReading_den]
    simp [h]

#print axioms primeReciprocalReading_den
#print axioms primeReciprocalReading_den_exponent

end GaloisForLFunctions.CountingHolography.Sections
