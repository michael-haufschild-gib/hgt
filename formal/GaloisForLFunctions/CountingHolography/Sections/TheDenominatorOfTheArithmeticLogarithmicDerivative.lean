import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
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
  have hp0 : (0:ℚ) < (p:ℕ) := zero_lt_one.trans hp
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

private def reciprocalLinear := Finsupp.linearCombination ℤ (fun p : Nat.Primes => (1:ℚ)/(p:ℕ))

private theorem reciprocalLinear_apply (a : Nat.Primes →₀ ℤ) :
    reciprocalLinear a=primeReciprocalReading a := by
  simp only [reciprocalLinear,Finsupp.linearCombination_apply,Finsupp.sum,primeReciprocalReading,
    zsmul_eq_mul,div_eq_mul_inv,one_mul]

private theorem prime_product_inverse_in_range (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) :
    1/((∏ p ∈ S, p:ℕ):ℚ) ∈ LinearMap.range reciprocalLinear := by
  have hprime {p : ℕ} (hp : p.Prime) : (1:ℚ)/p ∈ LinearMap.range reciprocalLinear := by
    refine ⟨Finsupp.single (⟨p,hp⟩ : Nat.Primes) (1:ℤ),?_⟩
    simp only [reciprocalLinear,Finsupp.linearCombination_single,one_smul]
  induction S using Finset.induction_on with
  | empty =>
    have h := (LinearMap.range reciprocalLinear).smul_mem (2:ℤ) (hprime Nat.prime_two)
    norm_num [zsmul_eq_mul] at h ⊢
    exact h
  | @insert p S hp ih =>
    have hP := hS p (mem_insert_self _ _)
    have hQ (q : ℕ) (hq : q∈S) := hS q (mem_insert_of_mem hq)
    let D := ∏ q ∈ S, q
    have hc : p.Coprime D := Nat.coprime_prod_right_iff.mpr fun q hq =>
      hP.coprime_iff_not_dvd.mpr fun hd => hp (((hQ q hq).dvd_iff_eq hP.ne_one).mp hd ▸ hq)
    obtain ⟨r,t,hrt⟩ := hc.isCoprime
    have hd : (D:ℚ)≠0 := Nat.cast_ne_zero.mpr (prod_pos fun q hq => (hQ q hq).pos).ne'
    have hq : (p:ℚ)≠0 := Nat.cast_ne_zero.mpr hP.ne_zero
    have h := (LinearMap.range reciprocalLinear).add_mem
      ((LinearMap.range reciprocalLinear).smul_mem r (ih hQ))
      ((LinearMap.range reciprocalLinear).smul_mem t (hprime hP))
    rw [prod_insert hp,Nat.cast_mul]
    change 1/((p:ℚ)*D) ∈ _
    have he : r • ((1:ℚ)/D)+t • ((1:ℚ)/p)=1/((p:ℚ)*D) := by
      have hh : (r:ℚ)*p+(t:ℚ)*D=1 := by exact_mod_cast hrt
      simp only [zsmul_eq_mul]
      field_simp
      linarith only [hh]
    exact he ▸ h

/-- The image consists of exactly the rationals with squarefree reduced
denominator. Bézout joins reciprocals of coprime prime products. -/
theorem range_primeReciprocalReading (q : ℚ) :
    (∃ a : Nat.Primes →₀ ℤ, primeReciprocalReading a=q) ↔ Squarefree q.den := by
  constructor
  · rintro ⟨a,rfl⟩
    apply (Nat.squarefree_iff_factorization_le_one (primeReciprocalReading a).den_nz).mpr
    intro k
    by_cases hp : k.Prime
    · have h := primeReciprocalReading_den_exponent a ⟨k,hp⟩
      change (primeReciprocalReading a).den.factorization k=if (k:ℤ)∣a ⟨k,hp⟩ then 0 else 1 at h
      rw [h]; split <;> decide
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; exact Nat.zero_le _
  · intro h
    have hr := prime_product_inverse_in_range q.den.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp
    rw [Nat.prod_primeFactors_of_squarefree h] at hr
    obtain ⟨a,ha⟩ := (LinearMap.range reciprocalLinear).smul_mem q.num hr
    refine ⟨a,?_⟩
    rw [← reciprocalLinear_apply,ha,zsmul_eq_mul,mul_one_div,q.num_div_den]

/-- Adding any vector satisfying the entropy congruences preserves the
entire reduced denominator of the derivative. -/
theorem primeReciprocalReading_den_add (a b : Nat.Primes →₀ ℤ) (hb : ∀ p : Nat.Primes, (p:ℤ)∣b p) :
    (primeReciprocalReading (a+b)).den=(primeReciprocalReading a).den := by
  apply Nat.factorization_inj (primeReciprocalReading (a+b)).den_nz (primeReciprocalReading a).den_nz
  ext k
  by_cases hp : k.Prime
  · let p : Nat.Primes := ⟨k,hp⟩
    change (primeReciprocalReading (a+b)).den.factorization (p:ℕ)=(primeReciprocalReading a).den.factorization (p:ℕ)
    rw [primeReciprocalReading_den_exponent,primeReciprocalReading_den_exponent,Finsupp.add_apply,
      dvd_add_left (hb p)]
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

end GaloisForLFunctions.CountingHolography.Sections
