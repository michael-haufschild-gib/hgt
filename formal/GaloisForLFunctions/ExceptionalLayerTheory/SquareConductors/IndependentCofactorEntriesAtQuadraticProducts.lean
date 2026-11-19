import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.DivisorInversionAtTheProductBoundary
import Mathlib.NumberTheory.Bertrand

/-!
# Independent cofactor entries at quadratic products

For a common prime above twice the largest conductor, the product with
cofactor t enters at exactly t. Taking one cap difference gives a diagonal
table. On odd cofactors the original signed divisor weight is minus one.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- With a prime above the whole interval, any competing first factor leaves
that large prime in the cofactor. Only the entry at t remains. -/
theorem productFirstPrimes_large_factor {p t b : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    (ht : 0 < t) (htp : t < p) (hbp : b < p) :
    productFirstPrimes b (p*t) = if t ≤ b then {p} else ∅ := by
  have hprod := Nat.mul_pos hp.pos ht
  have only_p {r : ℕ} (hr : r ∈ productFirstPrimes b (p*t)) : r = p := by
    obtain ⟨hrD,hrp,_,_,hrb⟩ := mem_filter.mp hr
    have hd := (Nat.mem_divisors.mp hrD).1
    have he : r*((p*t)/r) = p*t := by rw [Nat.mul_comm, Nat.div_mul_cancel hd]
    have hpdiv : p ∣ r*((p*t)/r) := by rw [he]; exact dvd_mul_right p t
    rcases hp.dvd_mul.mp hpdiv with hpr | hpc
    · exact ((Nat.prime_dvd_prime_iff_eq hp hrp).mp hpr).symm
    · have hq := Nat.div_pos (Nat.le_of_dvd hprod hd) hrp.pos
      exact (hbp.not_ge ((Nat.le_of_dvd hq hpc).trans hrb)).elim
  have hmem : p ∈ productFirstPrimes b (p*t) ↔ t ≤ b := by
    simp only [productFirstPrimes,mem_filter,Nat.mem_divisors,Nat.mul_div_cancel_left _ hp.pos]
    have hcop := hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ht htp)
    exact ⟨fun h => h.2.2.2.2,fun h => ⟨⟨dvd_mul_right _ _,hprod.ne'⟩,hp,hp4,hcop,h⟩⟩
  ext r
  by_cases h : t ≤ b
  · rw [if_pos h,mem_singleton]
    exact ⟨only_p,fun e => e ▸ hmem.mpr h⟩
  · rw [if_neg h]
    simp only [notMem_empty,iff_false]
    intro hr
    exact h (hmem.mp (only_p hr ▸ hr))

/-- At an odd cofactor above one the unit divisor is the only contributor
to the inner stencil with support at 1, 2 and 4. -/
theorem innerJump_at_odd_cofactor {t : ℕ} (ht : 2 ≤ t) (ho : ¬ 2 ∣ t) :
    innerJump 1 t = -1 := by
  have h4 : ¬ 4 ∣ t := fun h => ho (dvd_trans (by decide : 2 ∣ 4) h)
  have hμ : ((moebius 1 : ℤ) : ℝ) = 1 := by simp
  rw [innerJump_divisor_stencil ht,stencil]
  norm_num only [show (1+1:ℕ)=2 by decide,show (2*2:ℕ)=4 by decide,
    sum_Icc_succ_top (by decide : 1 ≤ 1+1),Icc_self,sum_singleton,one_dvd,if_true,if_neg ho,if_neg h4,
    mul_zero,sub_zero,add_zero,mul_one,neg_inj] <;> exact hμ

/-- Log mass at the newly admitted cofactor, including the signed inner
jump of the actual fixed-product row. -/
def signedCofactorEntry (n q : ℕ) : ℝ := productInnerWeight q *
  ((∑ p ∈ productFirstPrimes n q, vonMangoldt p) -
    ∑ p ∈ productFirstPrimes (n-1) q, vonMangoldt p)

private theorem signedCofactorEntry_eq {p t n : ℕ} (hp : p.Prime) (hp4 : 4 < p)
    (ht : 2 ≤ t) (htp : t < p) (hnp : n < p) :
    signedCofactorEntry n (p*t) = if n=t then innerJump 1 t*Real.log p else 0 := by
  have ht' := (by omega : 0 < t)
  have hcomp : ¬(p*t).Prime := by
    intro hh
    have he := (Nat.prime_dvd_prime_iff_eq hp hh).mp (dvd_mul_right p t)
    have hlt := Nat.mul_lt_mul_of_pos_left (show 1 < t from ht) hp.pos
    rw [Nat.mul_one] at hlt
    exact hlt.ne he
  have hw : productInnerWeight (p*t) = innerJump 1 t := by
    simp only [productInnerWeight,if_neg hcomp,add_zero,innerJump_prime_multiple le_rfl hp hp4 ht',
      if_neg (by omega : t≠1),sub_zero]
  rw [signedCofactorEntry,hw,productFirstPrimes_large_factor hp hp4 ht' htp hnp,
    productFirstPrimes_large_factor hp hp4 ht' htp ((Nat.sub_le n 1).trans_lt hnp)]
  rcases lt_trichotomy n t with h | rfl | h
  · simp only [if_neg h.not_ge,if_neg ((Nat.sub_le n 1).trans_lt h).not_ge,if_neg h.ne,
      sum_empty,sub_zero,mul_zero]
  · simp [show ¬n ≤ n-1 by omega,vonMangoldt_apply_prime hp]
  · simp only [if_pos h.le,if_pos (by omega : t ≤ n-1),if_neg h.ne',sub_self,mul_zero]

/-- A single ordinary prime supplies independent diagonal entries throughout
an octave. All products exceed its largest conductor square and are at most
sixteen times its smallest square. Odd diagonal entries equal minus log p. -/
theorem quadratic_cofactor_diagonal (B : ℕ) (hB : 0 < B) :
    ∃ p : ℕ, p.Prime ∧ 4*B < p ∧ p ≤ 8*B ∧ ∀ t ∈ Ioc B (2*B),
      (2*B)^2 < p*t ∧ p*t ≤ 16*B^2 ∧ ∀ n ∈ Ioc B (2*B),
        signedCofactorEntry n (p*t) = (if n=t then innerJump 1 t*Real.log p else 0) ∧
        (¬2 ∣ t → signedCofactorEntry n (p*t) = (if n=t then -Real.log p else 0)) := by
  obtain ⟨p,hp,hl,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (4*B) (by omega)
  have hp4 : 4 < p := by omega
  have hu' : p ≤ 8*B := by omega
  refine ⟨p,hp,hl,hu',fun t ht => ?_⟩
  obtain ⟨htl,htu⟩ := mem_Ioc.mp ht
  have hlow := Nat.mul_lt_mul_of_pos_right hl (show 0 < t by omega)
  have hhigh := Nat.mul_le_mul hu' htu
  refine ⟨?_,?_,fun n hn => ?_⟩
  · calc (2*B)^2 = (4*B)*B := by ring
         _ ≤ (4*B)*t := Nat.mul_le_mul_left _ htl.le
         _ < p*t := hlow
  · exact hhigh.trans_eq (by ring)
  · have he := signedCofactorEntry_eq hp hp4 (by omega : 2 ≤ t) (by omega : t < p)
        ((mem_Ioc.mp hn).2.trans_lt (by omega : 2*B < p))
    refine ⟨he,fun ho => ?_⟩
    rw [he,innerJump_at_odd_cofactor (by omega) ho,neg_one_mul]

/-- Linear combinations of the actual near-quadratic signed cap differences
give every real function on the odd conductors of an octave. -/
theorem quadratic_cap_realizes_odd_conductor_traces (B : ℕ) (hB : 0 < B) :
    ∃ p : ℕ, p.Prime ∧ 4*B < p ∧ p ≤ 8*B ∧ ∀ f : ℕ → ℝ, ∀ n ∈ Ioc B (2*B), ¬2 ∣ n →
      (∑ t ∈ Ioc B (2*B) with ¬2 ∣ t, (-f t/Real.log p)*signedCofactorEntry n (p*t)) = f n := by
  obtain ⟨p,hp,hl,hu,h⟩ := quadratic_cofactor_diagonal B hB
  have hp₁ : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog := (Real.log_pos hp₁).ne'
  refine ⟨p,hp,hl,hu,fun f n hn hodd => ?_⟩
  rw [sum_eq_single_of_mem n (mem_filter.mpr ⟨hn,hodd⟩) (fun t ht hne => by
    obtain ⟨htr,hto⟩ := mem_filter.mp ht
    rw [((h t htr).2.2 n hn).2 hto,if_neg hne.symm,mul_zero]),
    ((h n hn).2.2 n hn).2 hodd,if_pos rfl]
  field_simp [hlog]

#print axioms productFirstPrimes_large_factor
#print axioms innerJump_at_odd_cofactor
#print axioms quadratic_cofactor_diagonal
#print axioms quadratic_cap_realizes_odd_conductor_traces
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
