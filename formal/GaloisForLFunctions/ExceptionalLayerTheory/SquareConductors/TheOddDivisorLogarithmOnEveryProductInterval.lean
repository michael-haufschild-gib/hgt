import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OrdinaryPrimesOnThreeDyadicProducts
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMassAtAQuadraticProductDivider

/-!
# The divisor logarithm on every odd product prefix

Ordinary factorization converts the logarithm missed by eligible prime
divisors into positive weights on small primes and proper powers. The
odd multiples of each omitted divisor have a bounded counting error at
every endpoint, with a single reciprocal density through the full horizon.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Divisors omitted by the ordinary first-prime cutoff on odd products. -/
def oddExcludedDivisors (P H : ℕ) := (Ioc 0 H).filter (fun d => Odd d ∧ ¬(d.Prime ∧ max 4 P<d))

/-- The same reciprocal density applies to all endpoints below H. -/
def oddExcludedDivisorDensity (P H : ℕ) : ℝ :=
  ∑ d ∈ oddExcludedDivisors P H, vonMangoldt d/d

/-- Logarithm of the product of eligible distinct prime divisors. -/
def eligibleDivisorLog (P u : ℕ) :=
  ∑ d ∈ u.divisors with d.Prime ∧ max 4 P<d, vonMangoldt d

private theorem odd_multiple_count {d : ℕ} (hd : Odd d) (x : ℕ) :
    |(∑ u ∈ (Ioc 0 x).filter Odd, (if d∣u then (1:ℝ) else 0))-x/(2*(d:ℝ))| ≤ 1 := by
  classical
  have hd0 : 0<d := by obtain ⟨k,hk⟩ := hd; omega
  let m := x/d
  have hs : (∑ u ∈ (Ioc 0 x).filter Odd, (if d∣u then (1:ℝ) else 0)) =
      ∑ t ∈ Ioc 0 m, (if Odd t then 1 else 0) := by
    rw [sum_filter]
    have hswap (u : ℕ) : (if Odd u then (if d∣u then (1:ℝ) else 0) else 0) =
        (if d∣u then (if Odd u then 1 else 0) else 0) := by
      by_cases h : Odd u <;> simp [h]
    simp_rw [hswap]
    rw [←sum_filter,sum_divisible_Ioc hd0,Nat.zero_div]
    exact sum_congr rfl (fun t _ => by simp only [Nat.odd_mul,hd,true_and])
  have he : ∑ t ∈ Ioc 0 m, (if Odd t then (1:ℝ) else 0) = (m:ℝ)-((m/2:ℕ):ℝ) := by
    have hp := sum_filter_add_sum_filter_not (Ioc 0 m) (2 ∣ ·) (fun _ => (1:ℝ))
    rw [sum_divisible_Ioc (by decide : 0<2),Nat.zero_div] at hp
    have hodd : ((Ioc 0 m).filter fun t => ¬(2∣t)) = (Ioc 0 m).filter Odd := by
      ext t; simp only [mem_filter,←even_iff_two_dvd,Nat.not_even_iff_odd]
    rw [hodd] at hp
    simp only [sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc,Nat.sub_zero] at hp
    rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
    linarith only [hp]
  have hg : (m:ℝ)≤(x:ℝ)/d := Nat.cast_div_le
  have hh : (x:ℝ)/d<(m:ℝ)+1 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hd0)).mpr
    exact_mod_cast (show x<(m+1)*d by dsimp only [m]; simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ x hd0)
  have hlo : 2*((m/2:ℕ):ℝ) ≤ m := by exact_mod_cast (show 2*(m/2) ≤ m by omega)
  have hhi : (m:ℝ)≤2*((m/2:ℕ):ℝ)+1 := by exact_mod_cast (show m≤2*(m/2)+1 by omega)
  rw [hs,he,show (x:ℝ)/(2*(d:ℝ))=((x:ℝ)/d)/2 by ring,abs_le]
  constructor <;> linarith only [hg,hh,hlo,hhi]

private theorem omitted_at_odd_product {u H : ℕ} (hu : Odd u) (huH : u≤H) (P : ℕ) :
    Real.log u-eligibleDivisorLog P u =
      ∑ d ∈ oddExcludedDivisors P H, if d∣u then vonMangoldt d else 0 := by
  classical
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  have hset : (oddExcludedDivisors P H).filter (· ∣ u) =
      u.divisors.filter (fun d => ¬(d.Prime ∧ max 4 P<d)) := by
    ext d
    simp only [oddExcludedDivisors,mem_filter,mem_Ioc,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_,_,h⟩,hdu⟩
      exact ⟨⟨hdu,hu0.ne'⟩,h⟩
    · rintro ⟨⟨hdu,_⟩,h⟩
      have ho : Odd ((u/d)*d) := (Nat.div_mul_cancel hdu).symm ▸ hu
      exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdu hu0,(Nat.le_of_dvd hu0 hdu).trans huH⟩,
        (Nat.odd_mul.mp ho).2,h⟩,hdu⟩
  rw [←sum_filter,hset]
  have h := sum_filter_add_sum_filter_not u.divisors (fun d => d.Prime ∧ max 4 P<d) vonMangoldt
  rw [vonMangoldt_sum] at h
  exact sub_eq_of_eq_add (by simpa only [eligibleDivisorLog,add_comm] using h.symm)

private theorem omitted_weight_bound (P H : ℕ) :
    (∑ d ∈ oddExcludedDivisors P H, vonMangoldt d) ≤
      7*(max 4 P:ℕ)+(Chebyshev.psi H-Chebyshev.theta H) := by
  classical
  let T := oddExcludedDivisors P H
  have sp := sum_filter_add_sum_filter_not T Nat.Prime vonMangoldt
  have hsmall : T.filter Nat.Prime ⊆ Icc 1 (max 4 P) := by
    intro d hd
    obtain ⟨ht,hp⟩ := mem_filter.mp hd
    have h := (mem_filter.mp ht).2.2
    exact mem_Icc.mpr ⟨hp.pos,le_of_not_gt (fun h' => h ⟨hp,h'⟩)⟩
  have hpow : T.filter (fun d => ¬d.Prime) ⊆ (Ioc 0 H).filter (fun d => ¬d.Prime) := by
    intro d hd
    obtain ⟨ht,hp⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨(mem_filter.mp ht).1,hp⟩
  change (∑ d ∈ T, vonMangoldt d) ≤ _
  rw [←sp,Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
  exact add_le_add ((sum_le_sum_of_subset_of_nonneg hsmall (fun _ _ _ => vonMangoldt_nonneg)).trans
    (_root_.RHTower.sum_vonMangoldt_Icc_le_seven _))
    (sum_le_sum_of_subset_of_nonneg hpow (fun _ _ _ => vonMangoldt_nonneg))

/-- The full odd divisor logarithm has square-root error, plus the size
of the small-prime cutoff, simultaneously below the chosen horizon. -/
theorem odd_divisor_log_prefix :
    ∃ C : ℝ, 0≤C ∧ ∀ P H x : ℕ, x≤H →
      |(∑ u ∈ (Ioc 0 x).filter Odd, (Real.log u-eligibleDivisorLog P u)) -
        (x:ℝ)/2*oddExcludedDivisorDensity P H| ≤ 7*(max 4 P:ℕ)+C*Real.sqrt H := by
  classical
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨|C|,abs_nonneg _,fun P H x hx => ?_⟩
  let U := (Ioc 0 x).filter Odd
  let T := oddExcludedDivisors P H
  let N (d : ℕ) := ∑ u ∈ U, if d∣u then (1:ℝ) else 0
  have hrows : (∑ u ∈ U, (Real.log u-eligibleDivisorLog P u)) =
      ∑ d ∈ T, vonMangoldt d*N d := by
    have row (u : ℕ) (hu : u∈U) := omitted_at_odd_product (mem_filter.mp hu).2
      ((mem_Ioc.mp (mem_filter.mp hu).1).2.trans hx) P
    rw [sum_congr rfl row,sum_comm]
    apply sum_congr rfl
    intro d _
    simp only [N,mul_sum,mul_ite,mul_one,mul_zero]
  change |(∑ u ∈ U, _) - _| ≤ _
  rw [hrows,oddExcludedDivisorDensity,mul_sum,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc _ ≤ ∑ d ∈ T, vonMangoldt d := by
            apply sum_le_sum
            intro d hd
            rw [show vonMangoldt d*N d-(x:ℝ)/2*(vonMangoldt d/d) =
              vonMangoldt d*(N d-x/(2*(d:ℝ))) by ring,
              abs_mul,abs_of_nonneg vonMangoldt_nonneg]
            exact mul_le_of_le_one_right vonMangoldt_nonneg (odd_multiple_count (mem_filter.mp hd).2.1 x)
       _ ≤ _ := (omitted_weight_bound P H).trans (add_le_add le_rfl
            ((hC H).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))))

/-- On odd composites the signed coefficient is the negative eligible
divisor logarithm. On primes its unit cofactor has zero weight. -/
theorem odd_product_is_negative_composite_mass (P : ℕ) {u : ℕ} (hu : Odd u) :
    firstPrimeProductCoefficient P u =
      if u.Prime then 0 else -(∑ d ∈ u.divisors with d.Prime ∧ max 4 P<d, vonMangoldt d) := by
  classical
  by_cases hp : u.Prime
  · rw [if_pos hp,firstPrimeProductCoefficient]
    apply sum_eq_zero
    intro d hd
    obtain ⟨hdv,hdp,_⟩ := mem_filter.mp hd
    have he := (Nat.dvd_prime hp).mp (Nat.mem_divisors.mp hdv).1
    rcases he with he | rfl
    · exact (hdp.ne_one he).elim
    · rw [Nat.div_self hp.pos,innerJump_small (by decide : 1≤1),mul_zero]
  · rw [if_neg hp,(odd_product_prime_coordinates P hu).1,if_neg (fun h => hp h.1),zero_sub]

/-- After the explicit divisor density is removed, the odd signed product
row agrees with its ordinary prime singleton minus the odd logarithms. -/
theorem odd_signed_product_prefix :
    ∃ C : ℝ, 0≤C ∧ ∀ P H x : ℕ, x≤H →
      |(∑ u ∈ (Ioc 0 x).filter Odd, (firstPrimeProductCoefficient P u -
        (if u.Prime ∧ max 4 P<u then Real.log u else 0) + Real.log u)) -
        (x:ℝ)/2*oddExcludedDivisorDensity P H| ≤ 7*(max 4 P:ℕ)+C*Real.sqrt H := by
  obtain ⟨C,hC,h⟩ := odd_divisor_log_prefix
  refine ⟨C,hC,fun P H x hx => ?_⟩
  have row (u : ℕ) (hu : u∈(Ioc 0 x).filter Odd) :
      firstPrimeProductCoefficient P u - (if u.Prime ∧ max 4 P<u then Real.log u else 0) +
        Real.log u = Real.log u-eligibleDivisorLog P u := by
    have he := (odd_product_prime_coordinates P (mem_filter.mp hu).2).1
    change firstPrimeProductCoefficient P u = _-eligibleDivisorLog P u at he
    rw [he]; ring
  rw [sum_congr rfl row]
  exact h P H x hx

/-- Any finite product test pays its actual variation and its terminal
sample. The reciprocal correction uses one density for the entire test. -/
theorem weighted_odd_signed_product_error :
    ∃ C : ℝ, 0≤C ∧ ∀ (P H : ℕ) (f : ℕ → ℝ),
      |∑ u ∈ Icc 1 H, ((if Odd u then firstPrimeProductCoefficient P u -
        (if u.Prime ∧ max 4 P<u then Real.log u else 0) + Real.log u else 0) -
        oddExcludedDivisorDensity P H/2)*f u| ≤
        (7*(max 4 P:ℕ)+C*Real.sqrt H) *
          ((∑ u ∈ Icc 1 H, |f u-f (u+1)|) + |f (H+1)|) := by
  classical
  obtain ⟨C,hC,h⟩ := odd_signed_product_prefix
  refine ⟨C,hC,fun P H f => ?_⟩
  let B : ℝ := 7*(max 4 P:ℕ)+C*Real.sqrt H
  let A (u : ℕ) := (if Odd u then firstPrimeProductCoefficient P u -
    (if u.Prime ∧ max 4 P<u then Real.log u else 0) + Real.log u else 0) -
    oddExcludedDivisorDensity P H/2
  have hA (j : ℕ) (hj : j≤H) : |∑ u ∈ Icc 1 j, A u|≤B := by
    have hs : Icc 1 j=Ioc 0 j := by ext u; simp only [mem_Icc,mem_Ioc]; omega
    simp only [A,hs,sum_sub_distrib,←sum_filter,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]
    simpa only [div_mul_eq_mul_div,mul_div_assoc] using h P H j hj
  change |∑ u ∈ Icc 1 H, A u*f u| ≤ B*_
  rw [_root_.HTGeometry.sum_mul_eq_partial_mul_diff_ring,mul_add,mul_sum]
  apply (abs_add_le _ _).trans
  apply add_le_add ((abs_sum_le_sum_abs _ _).trans _) _
  · apply sum_le_sum
    intro j hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hA j (mem_Icc.mp hj).2) (abs_nonneg _)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hA H le_rfl) (abs_nonneg _)

#print axioms weighted_odd_signed_product_error
#print axioms odd_product_is_negative_composite_mass
#print axioms odd_divisor_log_prefix
#print axioms odd_signed_product_prefix
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
