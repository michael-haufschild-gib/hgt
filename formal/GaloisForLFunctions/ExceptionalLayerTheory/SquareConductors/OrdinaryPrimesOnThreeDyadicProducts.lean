import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFiniteMeshAtAnOrdinaryFirstPrime
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.FourCofactorCapsAtAZetaZero

/-!
# Ordinary primes on three dyadic products

At an odd product the first-prime coefficient contains a singleton and
a divisor logarithm. Its doubled and quadrupled products recover the
divisor logarithm with complementary cofactor weights.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem odd_cofactor_weights {v : ℕ} (hv : Odd v) :
    innerJump 1 v = (if v=1 then 1 else 0)-1 ∧
    innerJump 1 (2*v) = 1-cofactorDyadicCoefficient ∧
    innerJump 1 (4*v) = 1+cofactorDyadicCoefficient := by
  obtain ⟨k,hk⟩ := hv
  have hvk : v=2*k+1 := by omega
  have h₁ := (innerJump_dyadic_pair k).1
  have h₂ := (innerJump_dyadic_pair (2*k)).2
  have h₄ := (innerJump_dyadic_pair (4*k+1)).2
  rw [←hvk] at h₁
  simp only [show (k=0) ↔ (v=1) by omega] at h₁
  rw [show 2*(2*k)+2=2*v by omega,pow_mul] at h₂
  rw [show 2*(4*k+1)+2=4*v by omega,pow_succ,pow_mul] at h₄
  exact ⟨h₁,by simpa using h₂,by simpa [show (-1:ℝ)^4=1 by norm_num] using h₄⟩

private def oddProductPrimeDivisors (P u : ℕ) := u.divisors.filter (fun p => p.Prime ∧ max 4 P<p)

private theorem small_dilation_divisors (P : ℕ) {a u : ℕ} (ha : 0<a) (ha' : a≤4) (hu : 0<u) :
    oddProductPrimeDivisors P (a*u)=oddProductPrimeDivisors P u := by
  ext p
  simp only [oddProductPrimeDivisors,mem_filter,Nat.mem_divisors,ne_eq,
    (Nat.mul_pos ha hu).ne',hu.ne',not_false_eq_true,and_true]
  constructor
  · rintro ⟨hd,hp,hP⟩
    rcases hp.dvd_mul.mp hd with hpa | hpu
    · have := Nat.le_of_dvd ha hpa
      have := le_max_left 4 P
      omega
    · exact ⟨hpu,hp,hP⟩
  · rintro ⟨hd,hh⟩
    exact ⟨dvd_mul_of_dvd_right hd a,hh⟩

private theorem dilated_cofactor_sum (P : ℕ) {a u : ℕ} (ha : 0<a) (ha' : a≤4) (hu : 0<u) :
    firstPrimeProductCoefficient P (a*u)=
    ∑ p ∈ oddProductPrimeDivisors P u, vonMangoldt p*innerJump 1 (a*(u/p)) := by
  change (∑ p ∈ oddProductPrimeDivisors P (a*u), _) = _
  rw [small_dilation_divisors P ha ha' hu]
  apply sum_congr rfl
  intro p hp
  rw [Nat.mul_div_assoc a (Nat.mem_divisors.mp (mem_filter.mp hp).1).1]

/-- The three signed coefficients separate the singleton prime from the sum
of all its eligible divisor logarithms, even at repeated odd primes. -/
theorem odd_product_prime_coordinates (P : ℕ) {u : ℕ} (hu : Odd u) :
    let L := ∑ p ∈ u.divisors with p.Prime ∧ max 4 P<p, vonMangoldt p
    firstPrimeProductCoefficient P u = (if u.Prime ∧ max 4 P<u then Real.log u else 0)-L ∧
    firstPrimeProductCoefficient P (2*u)=(1-cofactorDyadicCoefficient)*L ∧
    firstPrimeProductCoefficient P (4*u)=(1+cofactorDyadicCoefficient)*L := by
  intro L
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  let S := oddProductPrimeDivisors P u
  have hd {p : ℕ} (hp : p∈S) : p∣u := (Nat.mem_divisors.mp (mem_filter.mp hp).1).1
  have ho {p : ℕ} (hp : p∈S) : Odd (u/p) := by
    have h : Odd ((u/p)*p) := (Nat.div_mul_cancel (hd hp)).symm ▸ hu
    exact (Nat.odd_mul.mp h).1
  have hei {p : ℕ} (hp : p∈S) : (u/p=1) ↔ (p=u) := by
    constructor
    · intro h
      simpa only [h,one_mul] using Nat.div_mul_cancel (hd hp)
    · rintro rfl
      exact Nat.div_self hu0
  have hs : (∑ p ∈ S, if p=u then vonMangoldt p else 0) =
      (if u.Prime ∧ max 4 P<u then Real.log u else 0) := by
    classical
    rw [Finset.sum_ite_eq']
    have huS : u∈S ↔ u.Prime ∧ max 4 P<u := by simp [S,oddProductPrimeDivisors,hu0.ne']
    by_cases h : u.Prime ∧ max 4 P<u
    · rw [if_pos (huS.mpr h),if_pos h,vonMangoldt_apply_prime h.1]
    · rw [if_neg (fun h' => h (huS.mp h')),if_neg h]
  constructor
  · change (∑ p ∈ S, vonMangoldt p * innerJump 1 (u/p)) = _-∑ p ∈ S, vonMangoldt p
    rw [←hs,←sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    simp only [(odd_cofactor_weights (ho hp)).1,hei hp,mul_sub,mul_ite,mul_one,mul_zero]
  · constructor
    · rw [dilated_cofactor_sum P (by decide : 0<2) (by decide) hu0]
      dsimp only [L]; rw [mul_sum]
      exact sum_congr rfl (fun p hp => by rw [(odd_cofactor_weights (ho hp)).2.1,mul_comm])
    · rw [dilated_cofactor_sum P (by decide : 0<4) le_rfl hu0]
      dsimp only [L]; rw [mul_sum]
      exact sum_congr rfl (fun p hp => by rw [(odd_cofactor_weights (ho hp)).2.2,mul_comm])

/-- A finite combination of actual product rows recovers the ordinary
prime measure at its original sharp cutoff, with no restriction on odd composites. -/
theorem ordinary_prime_from_three_products (P : ℕ) {u : ℕ} (hu : Odd u) :
    firstPrimeProductCoefficient P u +
      (firstPrimeProductCoefficient P (2*u)+firstPrimeProductCoefficient P (4*u))/2 =
      if u.Prime ∧ max 4 P<u then Real.log u else 0 := by
  obtain ⟨h₁,h₂,h₄⟩ := odd_product_prime_coordinates P hu
  rw [h₁,h₂,h₄]; ring

/-- Matching the three dyadic product intervals with their original endpoints
recovers every sharp weighted ordinary-prime interval. -/
theorem weighted_prime_interval_from_three_products (P L H : ℕ) (f : ℕ → ℝ) :
    (∑ u ∈ (Ioc L H).filter Odd, f u*(firstPrimeProductCoefficient P u +
      (firstPrimeProductCoefficient P (2*u)+firstPrimeProductCoefficient P (4*u))/2)) =
    ∑ p ∈ (Ioc L H).filter (fun p => p.Prime ∧ max 4 P<p), f p*Real.log p := by
  classical
  rw [sum_congr rfl (fun u hu => congrArg (fun x : ℝ => f u*x)
    (ordinary_prime_from_three_products P (mem_filter.mp hu).2))]
  simp only [mul_ite,mul_zero,←sum_filter]
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter]
  constructor
  · rintro ⟨⟨hp,_⟩,h⟩
    exact ⟨hp,h⟩
  · rintro ⟨hp,hpr,hcut⟩
    have h4 := (le_max_left 4 P).trans_lt hcut
    exact ⟨⟨hp,hpr.odd_of_ne_two (by omega)⟩,hpr,hcut⟩

#print axioms weighted_prime_interval_from_three_products
#print axioms odd_product_prime_coordinates
#print axioms ordinary_prime_from_three_products
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
