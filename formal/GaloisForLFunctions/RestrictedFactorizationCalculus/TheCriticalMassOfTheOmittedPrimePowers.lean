import GaloisForLFunctions.RestrictedFactorizationCalculus.RemovingProperPowersFromTheQuotientReadings
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments
import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The critical mass of the omitted prime powers

At every pair of cutoffs the deleted proper-power kernel at exponent
one half differs from the harmonic prime mass on (y,√X] by a bounded
nonnegative quantity. Consequently its leading coefficient in log X
is at most one half, leaving strict room in logarithmic inversion.
-/

noncomputable section

open Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def primeSquare (d : ℕ) := ∃ p : ℕ,p.Prime ∧ p^2=d
private def higherWeight (d : ℕ) : ℝ := if primeSquare d then 0 else (d:ℝ)^(-(1/2:ℝ))

private theorem weight_nonneg (d : ℕ) : 0 ≤ higherWeight d := by
  unfold higherWeight
  split <;> positivity

private theorem cubic_tail (p : ℕ) (hp : p.Prime) (N : ℕ) :
    (∑ k ∈ Icc 2 N,higherWeight (p^k)) ≤ 4*(p:ℝ)^(-(3/2:ℝ)) := by
  let r := (p:ℝ)^(-(1/2:ℝ))
  have p0 := Nat.cast_nonneg (α := ℝ) p
  have r0 : 0 ≤ r := Real.rpow_nonneg p0 _
  have rle : r ≤ 3/4 := by
    have low : (4:ℝ)/3 ≤ Real.sqrt p := by
      rw [Real.le_sqrt (by norm_num) p0]
      exact (by norm_num : ((4:ℝ)/3)^2 ≤ 2).trans (by exact_mod_cast hp.two_le)
    dsimp only [r]
    rw [Real.rpow_neg p0,←Real.sqrt_eq_rpow,←one_div,div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos))]
    linarith only [low]
  have cube : r^3=(p:ℝ)^(-(3/2:ℝ)) := by
    rw [←Real.rpow_natCast r 3,←Real.rpow_mul p0]; norm_num
  have eq : (∑ k ∈ Icc 3 N,higherWeight (p^k))=∑ k ∈ Icc 2 N,higherWeight (p^k) := by
    apply sum_subset (Icc_subset_Icc_left (by decide))
    intro k hk out
    have two : k=2 := by simp only [mem_Icc] at hk out; omega
    have square : primeSquare (p^2) := ⟨p,hp,rfl⟩
    simp only [two,higherWeight,if_pos square]
  rw [←eq,←cube]
  have per (k : ℕ) (_ : k ∈ Icc 3 N) : higherWeight (p^k) ≤ r^k := by
    unfold higherWeight
    split
    · exact pow_nonneg r0 k
    · rw [Nat.cast_pow,←Real.rpow_natCast (p:ℝ) k,←Real.rpow_mul p0,mul_comm (k:ℝ),
        Real.rpow_mul p0,Real.rpow_natCast]
  apply (sum_le_sum per).trans
  have range : Icc 3 N ⊆ Ico 3 (N+1) := fun k hk =>
    mem_Ico.mpr ⟨(mem_Icc.mp hk).1,Nat.lt_succ_of_le (mem_Icc.mp hk).2⟩
  have upper := (sum_le_sum_of_subset_of_nonneg range (fun k _ _ => pow_nonneg r0 k)).trans
    (geom_sum_Ico_le_of_lt_one r0 (lt_of_le_of_lt rle (by norm_num)))
  apply upper.trans
  apply (div_le_iff₀ (by linarith only [rle] : 0<1-r)).mpr
  have one : 1 ≤ 4*(1-r) := by linarith only [rle]
  linarith only [mul_le_mul_of_nonneg_left one (pow_nonneg r0 3)]

/-- All exponents above two have uniformly bounded critical mass. -/
private theorem higher_power_mass :
    ∃ K : ℝ,0 ≤ K ∧ ∀ X : ℕ,
      (∑ d ∈ (Icc 1 X).filter (fun d => ¬d.Prime),vonMangoldt d*higherWeight d) ≤ K := by
  let f := fun n : ℕ => Real.log n/(n:ℝ)^(3/2:ℝ)
  have pos (n : ℕ) : 0 ≤ f n := by
    rcases Nat.eq_zero_or_pos n with z | h
    · simp [z,f]
    · exact div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr h)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨4*∑' n,f n,mul_nonneg (by norm_num) (tsum_nonneg pos),fun X => ?_⟩
  have bound := RHTower.sum_nonprime_vonMangoldt_le_pairs X higherWeight weight_nonneg
  rw [sum_product] at bound
  apply bound.trans
  let P := (Icc 1 X).filter Nat.Prime
  have price (p : ℕ) (hp : p ∈ P) : (∑ k ∈ Icc 2 X,Real.log p*higherWeight (p^k)) ≤ 4*f p := by
    have pr := (mem_filter.mp hp).2
    rw [←mul_sum]
    have cost := mul_le_mul_of_nonneg_left (cubic_tail p pr X) (Real.log_nonneg (Nat.one_le_cast.mpr pr.pos))
    dsimp only [f]
    rw [Real.rpow_neg (Nat.cast_nonneg _)] at cost
    exact cost.trans_eq (by ring)
  apply (sum_le_sum price).trans
  rw [←mul_sum]
  exact mul_le_mul_of_nonneg_left ((RHTower.Mertens.summable_log_div_rpow (by norm_num : (1:ℝ)<3/2)).sum_le_tsum P
    (fun n _ => pos n)) (by norm_num)

private theorem on_prime_square (y : ℕ) {p : ℕ} (hp : p.Prime) :
    roughProperPowerWeight y (p^2)/Real.sqrt (p^2:ℕ)=if y<p then Real.log p/p else 0 := by
  have free : IsFree (RoughReading.banned y) (p^2) ↔ y<p := by
    rw [pow_two,isFree_mul_iff _ hp.ne_zero hp.ne_zero,isFree_prime,and_self]
    exact not_le
  have p2 : 1<p^2 := one_lt_pow₀ hp.one_lt (by decide)
  have no : ¬(p^2).Prime := Nat.Prime.not_prime_pow' (by decide : 2 ≠ 1)
  by_cases high : y<p
  · have far := high.trans_le (Nat.le_self_pow (by decide : 2 ≠ 0) p)
    simp only [roughProperPowerWeight,p2,far,no,free,high,and_self,if_true,Nat.cast_pow,
      Real.sqrt_sq (Nat.cast_nonneg _),vonMangoldt_apply_pow (by decide : 2 ≠ 0),vonMangoldt_apply_prime hp]
  · simp [roughProperPowerWeight,free,high]

/-- At every prime wall y and observation X, the only unbounded critical
mass is the explicit prime harmonic interval (y,√X]. -/
theorem critical_mass_of_the_rough_proper_powers :
    ∃ K : ℝ,0 ≤ K ∧ ∀ y X : ℕ,
      let V := ∑ p ∈ (Nat.primesLE X.sqrt).filter (y<·),Real.log p/p
      let H := ∑ d ∈ Icc 1 X,roughProperPowerWeight y d/Real.sqrt d
      V ≤ H ∧ H ≤ V+K := by
  obtain ⟨K,hK,tail⟩ := higher_power_mass
  refine ⟨K,hK,fun y X => ?_⟩
  let P := Nat.primesLE X.sqrt
  let B := Icc 1 X
  let S := B.filter primeSquare
  let f := fun d : ℕ => roughProperPowerWeight y d/Real.sqrt d
  have fn (d : ℕ) : 0 ≤ f d := by
    dsimp only [f,roughProperPowerWeight]
    split <;> first | exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _) | simp
  have squares : S=P.image (fun p => p^2) := by
    ext d
    constructor
    · intro h
      obtain ⟨hi,⟨p,pr,rfl⟩⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨p,Nat.mem_primesLE.mpr ⟨Nat.le_sqrt.mpr (by simpa only [pow_two] using (mem_Icc.mp hi).2),pr⟩,rfl⟩
    · intro h
      obtain ⟨p,hp,rfl⟩ := mem_image.mp h
      obtain ⟨lim,pr⟩ := Nat.mem_primesLE.mp hp
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨pow_pos pr.pos _,by simpa only [pow_two] using Nat.le_sqrt.mp lim⟩,p,pr,rfl⟩
  have ss : (∑ d ∈ S,f d)=∑ p ∈ P.filter (y<·),Real.log p/p := by
    rw [squares,sum_image (Nat.pow_left_injective two_ne_zero).injOn,sum_filter]
    exact sum_congr rfl (fun p hp => on_prime_square y (Nat.prime_of_mem_primesLE hp))
  have rest : (∑ d ∈ B.filter (fun d => ¬primeSquare d),f d) ≤ K := by
    apply LE.le.trans _ (tail X)
    rw [sum_filter,sum_filter]
    apply sum_le_sum
    intro d _
    by_cases sq : primeSquare d
    · simp [sq,higherWeight]
    by_cases h : 1<d ∧ y<d ∧ ¬d.Prime ∧ IsFree (RoughReading.banned y) d
    · simp only [f,roughProperPowerWeight,if_pos h,if_pos h.2.2.1,sq,not_false_eq_true,if_true,
        higherWeight,if_false,Real.rpow_neg (Nat.cast_nonneg _),←Real.sqrt_eq_rpow,div_eq_mul_inv,le_refl]
    · simp only [f,roughProperPowerWeight,if_neg h,zero_div,ite_self]
      split <;> first | exact mul_nonneg vonMangoldt_nonneg (weight_nonneg _) | rfl
  have split := sum_filter_add_sum_filter_not B primeSquare f
  change (∑ d ∈ S,f d)+_=∑ d ∈ B,f d at split
  rw [ss] at split
  change _ ≤ (∑ d ∈ B,f d) ∧ (∑ d ∈ B,f d) ≤ _
  exact ⟨by linarith only [split,sum_nonneg (s := B.filter (fun d => ¬primeSquare d)) (fun d _ => fn d)],
    by linarith only [split,rest]⟩

/-- The sharp critical mass between two integer prime walls equals
their logarithmic distance up to a uniform additive constant. -/
theorem sharp_logarithmic_length_of_the_omitted_powers :
    ∃ K : ℝ,0 ≤ K ∧ ∀ y X : ℕ,1 ≤ y → 1 ≤ X →
      |(∑ d ∈ Icc 1 X,roughProperPowerWeight y d/Real.sqrt d)-
        (Real.log X.sqrt-Real.log (min y X.sqrt))| ≤ K := by
  obtain ⟨K,hK,price⟩ := critical_mass_of_the_rough_proper_powers
  have log4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  refine ⟨K+9+Real.log 4,by linarith only [hK,log4],fun y X hy hx => ?_⟩
  let M := X.sqrt
  let m := min y M
  let S := Nat.primesLE M
  let T := Nat.primesLE m
  have mp : 1 ≤ M := Nat.le_sqrt.mpr (by simpa using hx)
  have small : 1 ≤ m := le_min hy mp
  have sub : T ⊆ S := fun p hp => Nat.mem_primesLE.mpr
    ⟨(Nat.mem_primesLE.mp hp).1.trans (min_le_right ..),(Nat.mem_primesLE.mp hp).2⟩
  have eq : S.filter (y<·)=S \ T := by
    ext p
    simp only [S,T,m,mem_filter,mem_sdiff,Nat.mem_primesLE,le_min_iff]
    omega
  have law := price y X
  change (∑ p ∈ S.filter (y<·),Real.log p/p) ≤ _ ∧ _ ≤ (∑ p ∈ S.filter (y<·),Real.log p/p)+K at law
  rw [eq,sum_sdiff_eq_sub sub] at law
  have hiM := RHTower.mertens_first_upper mp
  have loM := RHTower.mertens_first_lower mp
  have him := RHTower.mertens_first_upper small
  have lom := RHTower.mertens_first_lower small
  change (∑ p ∈ S,Real.log p/p) ≤ _ at hiM
  change _ ≤ ∑ p ∈ S,Real.log p/p at loM
  change (∑ p ∈ T,Real.log p/p) ≤ _ at him
  change _ ≤ ∑ p ∈ T,Real.log p/p at lom
  apply abs_le.mpr
  exact ⟨by linarith only [law.1,loM,him,hK],by linarith only [law.2,hiM,lom]⟩

/-- The half-log coefficient is uniform in the frozen prime cutoff. -/
theorem half_logarithmic_price_of_proper_powers :
    ∃ K : ℝ,0 ≤ K ∧ ∀ y X : ℕ,1 ≤ X →
      (∑ d ∈ Icc 1 X,roughProperPowerWeight y d/Real.sqrt d) ≤ Real.log X/2+K := by
  obtain ⟨K,hK,cost⟩ := critical_mass_of_the_rough_proper_powers
  refine ⟨K+Real.log 4,add_nonneg hK (Real.log_nonneg (by norm_num)),fun y X hx => ?_⟩
  have r1 : 1 ≤ X.sqrt := Nat.le_sqrt.mpr (by simpa using hx)
  have prime := RHTower.mertens_first_upper r1
  have sub := sum_le_sum_of_subset_of_nonneg (filter_subset (fun p => y<p) (Nat.primesLE X.sqrt))
    (fun p hp _ => div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primesLE hp).pos))
      (Nat.cast_nonneg (α := ℝ) p))
  have wall : (X.sqrt:ℝ) ≤ Real.sqrt X := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le' X
  have logwall := Real.log_le_log (Nat.cast_pos.mpr r1) wall
  rw [Real.log_sqrt (Nat.cast_nonneg _)] at logwall
  change (∑ p ∈ Nat.primesLE X.sqrt,Real.log p/p) ≤ _ at prime
  linarith only [(cost y X).2,sub,prime,logwall]

#print axioms sharp_logarithmic_length_of_the_omitted_powers
#print axioms critical_mass_of_the_rough_proper_powers
#print axioms half_logarithmic_price_of_proper_powers

end GaloisForLFunctions.RestrictedFactorizationCalculus
