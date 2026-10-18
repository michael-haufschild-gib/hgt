import GaloisForLFunctions.BiScaleUncertainty.PrimeFamilyTranslatedMoments
import GaloisForLFunctions.BiScaleUncertainty.SixthValuationPhaseRecovery

/-!
# Complete sixth-order recovery for finite odd-prime sieve families

Explicit sixth Fourier readouts recover all coefficient pair products. Full
sixth lag data alone therefore determine the actual finite-prime family up to
one common sign, including empty support and zero coefficients. Affine data
see only coefficient squares, and all translated data through degree five are
independently sign-blind. Zero extension includes every finite odd-prime support.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

private theorem primeMode_mem_cutoff {N : ℕ} (p : oddPrimeModes N) :
    2^1*(p : ℕ) ∈ Finset.Icc 1 N := by
  have hp := mem_oddPrimeModes.mp p.property
  simp only [pow_one,Finset.mem_Icc]
  exact ⟨by have := hp.1.two_le; omega,hp.2.2⟩

/-- An explicit sixth observation of the actual family reads each signed coefficient product. -/
theorem primeFamily_sixth_readout (N : ℕ) (a : ℕ → ℝ) (p q : oddPrimeModes N) :
    sixthPairReadout N (primeFamilyWeight N a) 1 p q =
      (N.factorial : ℝ)^6 * (a p*a q)^3 := by
  have h := sixthPairReadout_eq (primeFamilyWeight N a)
    (mem_oddPrimeModes.mp p.property).2.1 (mem_oddPrimeModes.mp q.property).2.1
    (primeMode_mem_cutoff p) (primeMode_mem_cutoff q)
  simpa only [pow_one,coordinate_primeFamilyWeight_at] using h

private theorem prime_readout_eq_iff (N : ℕ) (a b : ℕ → ℝ) (p q : oddPrimeModes N) :
    sixthPairReadout N (primeFamilyWeight N a) 1 p q =
      sixthPairReadout N (primeFamilyWeight N b) 1 p q ↔ a p*a q = b p*b q := by
  have h := sixthPairReadout_eq_iff (primeFamilyWeight N a) (primeFamilyWeight N b)
    (mem_oddPrimeModes.mp p.property).2.1 (mem_oddPrimeModes.mp q.property).2.1
    (primeMode_mem_cutoff p) (primeMode_mem_cutoff q)
  simpa only [pow_one,coordinate_primeFamilyWeight_at] using h

/-- Finitely many explicitly constructed Fourier readouts already give the exact common-sign ambiguity. -/
theorem primeFamily_readouts_iff_common_sign (N : ℕ) (a b : ℕ → ℝ) :
    (∀ p q : oddPrimeModes N, sixthPairReadout N (primeFamilyWeight N a) 1 p q =
      sixthPairReadout N (primeFamilyWeight N b) 1 p q) ↔
      (∀ p : oddPrimeModes N, a p = b p) ∨ (∀ p : oddPrimeModes N, a p = -b p) := by
  have h := pair_products_eq_iff_common_sign (Set.univ : Set (oddPrimeModes N))
    (fun p => a p) (fun p => b p)
  simp only [Set.mem_univ,forall_const] at h
  rw [← h]
  constructor <;> intro heq p q
  · exact (prime_readout_eq_iff N a b p q).mp (heq p q)
  · exact (prime_readout_eq_iff N a b p q).mpr (heq p q)

private theorem family_eq_of_coeff_eq (N : ℕ) (a b : ℕ → ℝ)
    (h : ∀ p : oddPrimeModes N, a p = b p) : primeFamilyWeight N a = primeFamilyWeight N b := by
  funext d
  unfold primeFamilyWeight
  apply Finset.sum_congr rfl
  intro p _
  rw [h p]

private theorem family_neg_of_coeff_neg (N : ℕ) (a b : ℕ → ℝ)
    (h : ∀ p : oddPrimeModes N, a p = -b p) :
    primeFamilyWeight N a = fun d => -primeFamilyWeight N b d := by
  funext d
  unfold primeFamilyWeight
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [h p]
  ring

private theorem sixth_neg (N : ℕ) (c : ℕ → ℝ) (h : Fin 6 → ℕ) :
    translatedMoment N (fun d => -c d) h = translatedMoment N c h := by
  simp only [translatedMoment,sieveSeq,Finset.sum_neg_distrib,Finset.prod_neg,
    Finset.card_univ,Fintype.card_fin]
  norm_num

/-- Full sixth translated data alone recover the whole finite-prime family up to one sign. -/
theorem primeFamily_sixth_iff_common_sign (N : ℕ) (a b : ℕ → ℝ) :
    (∀ h : Fin 6 → ℕ, translatedMoment N (primeFamilyWeight N a) h =
      translatedMoment N (primeFamilyWeight N b) h) ↔
      (∀ p : oddPrimeModes N, a p = b p) ∨ (∀ p : oddPrimeModes N, a p = -b p) := by
  constructor
  · intro h
    apply (primeFamily_readouts_iff_common_sign N a b).mp
    intro p q
    unfold sixthPairReadout
    simp_rw [h]
  · rintro (h | h) t
    · rw [family_eq_of_coeff_eq N a b h]
    · rw [family_neg_of_coeff_neg N a b h]
      exact sixth_neg N (primeFamilyWeight N b) t

private theorem family_coordinate_zero (N : ℕ) (a : ℕ → ℝ) (q : ℕ)
    (h : ¬∃ p : oddPrimeModes N, q = 2*(p : ℕ)) :
    selbergMultiplesCoord N (primeFamilyWeight N a) q = 0 := by
  rw [coordinate_primeFamilyWeight]
  apply Finset.sum_eq_zero
  intro p _
  exact if_neg (fun hp => h ⟨p,hp⟩)

/-- Full affine data retain exactly the individual coefficient squares in this sector. -/
theorem primeFamily_affine_iff_sq (N : ℕ) (a b : ℕ → ℝ) :
    (∀ r s, affineMoment N (primeFamilyWeight N a) r s =
      affineMoment N (primeFamilyWeight N b) r s) ↔
      ∀ p : oddPrimeModes N, (a p)^2 = (b p)^2 := by
  rw [affineMoment_eq_iff_comparable]
  constructor
  · intro h p
    have hm := primeMode_mem_cutoff p
    simp only [pow_one] at hm
    have hp0 : 2*(p : ℕ) ≠ 0 := by have := (Finset.mem_Icc.mp hm).1; omega
    have hd : 2*(p : ℕ) ∈ (2*(p : ℕ)).divisors := by simp [Nat.mem_divisors,hp0]
    have hh := h _ hm _ hd
    simpa only [coordinate_primeFamilyWeight_at,pow_two] using hh
  · intro h q _ d hd
    by_cases hq : ∃ p : oddPrimeModes N, q = 2*(p : ℕ)
    · obtain ⟨p,rfl⟩ := hq
      by_cases hd' : ∃ r : oddPrimeModes N, d = 2*(r : ℕ)
      · obtain ⟨r,rfl⟩ := hd'
        have hdiv := (Nat.mem_divisors.mp hd).1
        obtain ⟨t,ht⟩ := hdiv
        have hrp : (r : ℕ) ∣ (p : ℕ) := ⟨t,by nlinarith only [ht]⟩
        have heq : r = p := Subtype.ext ((Nat.prime_dvd_prime_iff_eq
          (mem_oddPrimeModes.mp r.property).1 (mem_oddPrimeModes.mp p.property).1).mp hrp)
        subst r
        simpa only [coordinate_primeFamilyWeight_at,pow_two] using h p
      · rw [family_coordinate_zero N a d hd',family_coordinate_zero N b d hd']
        simp
    · rw [family_coordinate_zero N a q hq,family_coordinate_zero N b q hq]
      simp

/-- Every independent sign flip preserves all affine and all through-five translated observations. -/
theorem primeFamily_independent_sign_blind (N : ℕ) (a : ℕ → ℝ) (ε : ℕ → Bool) :
    (∀ r s, affineMoment N (primeFamilyWeight N a) r s =
      affineMoment N (primeFamilyWeight N (fun p => if ε p then -a p else a p)) r s) ∧
    (∀ m, m ≤ 5 → ∀ h : Fin m → ℕ,
      translatedMoment N (primeFamilyWeight N a) h =
        translatedMoment N (primeFamilyWeight N (fun p => if ε p then -a p else a p)) h) := by
  have hs : ∀ p : oddPrimeModes N, (a p)^2 =
      ((fun p => if ε p then -a p else a p) (p : ℕ))^2 := by
    intro p
    cases hp : ε p <;> simp [hp]
  exact ⟨(primeFamily_affine_iff_sq N _ _).mpr hs,
    fun m hm h => primeFamily_through_five_eq_of_sq_eq N _ _ hs m hm h⟩

/-- Adding affine observations does not reduce the common-sign ambiguity left by full sixth data. -/
theorem primeFamily_affine_sixth_iff_common_sign (N : ℕ) (a b : ℕ → ℝ) :
    ((∀ r s, affineMoment N (primeFamilyWeight N a) r s =
        affineMoment N (primeFamilyWeight N b) r s) ∧
      (∀ h : Fin 6 → ℕ, translatedMoment N (primeFamilyWeight N a) h =
        translatedMoment N (primeFamilyWeight N b) h)) ↔
      (∀ p : oddPrimeModes N, a p = b p) ∨ (∀ p : oddPrimeModes N, a p = -b p) := by
  constructor
  · intro h
    exact (primeFamily_sixth_iff_common_sign N a b).mp h.2
  · intro h
    refine ⟨(primeFamily_affine_iff_sq N a b).mpr ?_,
      (primeFamily_sixth_iff_common_sign N a b).mpr h⟩
    intro p
    rcases h with h | h
    · rw [h p]
    · rw [h p]; ring

/-- Zero extension embeds every prescribed finite odd-prime support into the actual cutoff family. -/
theorem primeFamilyWeight_finite_support (N : ℕ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ Odd p ∧ 2*p ≤ N) (d : ℕ) :
    primeFamilyWeight N (fun p => if p ∈ S then a p else 0) d =
      ∑ p ∈ S, a p*oddPrimeAtom p d := by
  unfold primeFamilyWeight
  rw [Finset.sum_coe_sort (oddPrimeModes N)
    (fun p : ℕ => (if p ∈ S then a p else 0)*oddPrimeAtom p d)]
  simp only [ite_mul,zero_mul]
  rw [← Finset.sum_filter]
  have hs : (oddPrimeModes N).filter (fun p => p ∈ S) = S := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hp
      exact ⟨mem_oddPrimeModes.mpr (hS p hp),hp⟩
  rw [hs]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
