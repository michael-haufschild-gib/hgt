import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheEndpointAtQuotientZero
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheLastTwoQuotientCellsOfTheSpline
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OrdinaryPrimesOnThreeDyadicProducts
import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearArithmeticWeightsAndChebyshevCellIncrement

/-!
# Recovering the first positive quotient on odd products

The positive quotient weight is the sum of a unit impulse and four
differences of divisor indicators. Its finite dyadic mean recovers the
unit impulse, with the last sample carrying the entire remaining weight.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Finite geometric sum, with the remaining mass assigned to the last dilation. -/
def quotientDyadicMean (f : ℕ → ℝ) (u : ℕ) : ℕ → ℝ
  | 0 => 2*f u
  | k+1 => f u+quotientDyadicMean f (2*u) k/2

private def divIndicator (a n : ℕ) : ℝ := if a∣n then 1 else 0

private theorem indicator_doubled (a u : ℕ) :
    divIndicator (2*a) (2*u)=divIndicator a u := by
  simp only [divIndicator,Nat.mul_dvd_mul_iff_left (by decide : 0<2)]

private theorem shifted_indicator_mean (a u k : ℕ) :
    quotientDyadicMean (fun n => divIndicator a n-2*divIndicator (2*a) n) u (k+1) =
      (divIndicator a (2^(k+1)*u)-divIndicator a (2^k*u))/(2:ℝ)^k-2*divIndicator (2*a) u := by
  induction k generalizing u with
  | zero =>
    simp only [quotientDyadicMean,pow_zero,one_mul,div_one,indicator_doubled]
    ring
  | succ k ih =>
    rw [quotientDyadicMean,ih,indicator_doubled]
    have hp (i : ℕ) : 2^i*(2*u)=2^(i+1)*u := by rw [pow_succ,mul_assoc]
    rw [hp,hp,pow_succ (2:ℝ)]
    ring

private theorem quotient_mean_add (f g : ℕ → ℝ) (u k : ℕ) :
    quotientDyadicMean (fun n => f n+g n) u k=quotientDyadicMean f u k+quotientDyadicMean g u k := by
  induction k generalizing u with
  | zero => simp only [quotientDyadicMean]; ring
  | succ k ih => simp only [quotientDyadicMean,ih]; ring

private theorem quotient_mean_smul (c : ℝ) (f : ℕ → ℝ) (u k : ℕ) :
    quotientDyadicMean (fun n => c*f n) u k=c*quotientDyadicMean f u k := by
  induction k generalizing u with
  | zero => simp only [quotientDyadicMean]; ring
  | succ k ih => simp only [quotientDyadicMean,ih]; ring

private theorem quotient_mean_congr {f g : ℕ → ℝ} {u : ℕ} (hu : 0<u)
    (h : ∀ n : ℕ,0<n → f n=g n) (k : ℕ) : quotientDyadicMean f u k=quotientDyadicMean g u k := by
  induction k generalizing u with
  | zero => simp only [quotientDyadicMean,h u hu]
  | succ k ih => rw [quotientDyadicMean,quotientDyadicMean,h u hu,ih (Nat.mul_pos (by decide) hu)]

private theorem mean_unit_of_two_le {u : ℕ} (hu : 2≤u) (k : ℕ) :
    quotientDyadicMean (fun n => if n=1 then 1 else 0) u k=0 := by
  induction k generalizing u with
  | zero => simp [quotientDyadicMean,show u≠1 by omega]
  | succ k ih => rw [quotientDyadicMean,if_neg (by omega : u≠1),ih (by omega : 2≤2*u)]; norm_num

private theorem floor_step (a : ℕ) {n : ℕ} (hn : 0<n) :
    ((n/a:ℕ):ℝ)-(((n-1)/a:ℕ):ℝ) = divIndicator a n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  change ↑((m+1)/a) - (↑((m+1-1)/a) : ℝ) = divIndicator a (m+1)
  rw [Nat.add_sub_cancel,_root_.GaloisForLFunctions.BiScaleUncertainty.succ_div_eq_add_ite_dvd]
  by_cases h : a∣m+1 <;> simp [divIndicator,h]

private def parityIncrement (a n : ℕ) : ℝ := divIndicator a n-2*divIndicator (2*a) n

private theorem quotient_correction_step (a : ℕ) {n : ℕ} (hn : 0<n) :
    parityCorrection a n-parityCorrection a (n-1)=parityIncrement a n-64*parityIncrement (64*a) n := by
  rw [parityCorrection_floors,parityCorrection_floors]
  simp only [parityIncrement,←floor_step _ hn]
  ring

private theorem factorial_unit_step : ∃ c : ℝ, ∀ n : ℕ,0<n →
    factorialPrefix 1 n-factorialPrefix 1 (n-1)=c*parityIncrement 1 n := by
  let a := stencil 1 (fun d => if d=1 then 1 else 0)
  let b := stencil 1 (fun d => if d=2 then 1 else 0)
  have basis (f : ℕ → ℝ) : stencil 1 f=a*f 1+b*f 2 := by
    dsimp only [a,b,stencil]
    simp only [Icc_self,sum_singleton,if_true,if_neg (by decide : (1:ℕ)≠2),
      if_neg (by decide : (2:ℕ)≠1),mul_zero,mul_one,zero_add,sub_zero]
    ring
  have h := basis (fun d => 1/d)
  rw [stencil_linear_quotient (by decide : 1≤1) 1] at h
  norm_num only [Nat.cast_one,Nat.cast_ofNat,div_one,mul_one] at h
  have hb : b= -2*a := by linarith only [h]
  refine ⟨a,fun n hn => ?_⟩
  rw [factorialPrefix,factorialPrefix,basis,basis,hb]
  change _ = a*(divIndicator 1 n-2*divIndicator 2 n)
  rw [←floor_step 1 hn,←floor_step 2 hn]; ring

/-- The zeroth quotient is omitted, so the increment at one includes its unit mass. -/
def positiveQuotientIncrement (n : ℕ) : ℝ :=
  (if n=0 then 0 else centeredPrimeWeight 1 n) -
  (if n-1=0 then 0 else centeredPrimeWeight 1 (n-1))

private theorem quotient_increment_rows : ∃ c₁ c₂ c₃ c₄ : ℝ, ∀ n : ℕ,0<n →
    positiveQuotientIncrement n=(if n=1 then 1 else 0)+
      (c₁*parityIncrement 1 n+(c₂*parityIncrement 64 n+
      (c₃*parityIncrement 129 n+c₄*parityIncrement (64*129) n))) := by
  obtain ⟨a,ha⟩ := factorial_unit_step
  let m := momentRatio 1
  let b := (2/63)*primeWeightMean 1
  refine ⟨-a-m,64*m,b,-64*b,fun n hn => ?_⟩
  have hw : positiveQuotientIncrement n=(if n=1 then 1 else 0)+
      (centeredPrimeWeight 1 n-centeredPrimeWeight 1 (n-1)) := by
    rw [positiveQuotientIncrement,if_neg hn.ne']
    by_cases hn1 : n=1
    · subst n; simp [centeredPrimeWeight_at_zero]
    · rw [if_neg (by omega : n-1≠0),if_neg hn1,zero_add]
  rw [hw]
  have hc := quotient_correction_step 1 hn
  have hc' := quotient_correction_step 129 hn
  norm_num only [Nat.mul_one] at hc
  simp only [centeredPrimeWeight,primeWeight,show 128*1^2+1=129 by decide]
  dsimp only [m,b]
  linear_combination -ha n hn - momentRatio 1*hc + ((2/63)*primeWeightMean 1)*hc'

private theorem mean_parity_row {a u : ℕ} (hu : Odd u) (hstable : a∣128*u ↔ a∣64*u) :
    quotientDyadicMean (parityIncrement a) u 7=0 := by
  have hodd : ¬2*a∣u := fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr
    ((dvd_mul_right 2 a).trans h))
  change quotientDyadicMean (fun n => divIndicator a n-2*divIndicator (2*a) n) u (6+1)=0
  rw [shifted_indicator_mean]
  simp only [show (2:ℕ)^(6+1)=128 by decide,show (2:ℕ)^6=64 by decide,divIndicator,hstable,if_neg hodd,
    sub_self,zero_div,mul_zero]

/-- The actual positive quotient stencil recovers the unit impulse at every odd core. -/
theorem positive_quotient_dyadic_recovery {u : ℕ} (hu : Odd u) :
    quotientDyadicMean positiveQuotientIncrement u 7 = if u=1 then 1 else 0 := by
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  have hunit : quotientDyadicMean (fun n => if n=1 then 1 else 0) u 7=if u=1 then 1 else 0 := by
    rw [show (7:ℕ)=6+1 by rfl,quotientDyadicMean,mean_unit_of_two_le (by omega : 2≤2*u),zero_div,add_zero]
  have a₁ := mean_parity_row (a := 1) hu (by simp)
  have a₂ := mean_parity_row (a := 64) hu (by
    constructor <;> intro _ <;> exact dvd_mul_of_dvd_left (by decide) _)
  have ho : Nat.Coprime 129 2 := by decide
  have same (j : ℕ) : 129∣2^j*u ↔ 129∣u := (ho.pow_right j).dvd_mul_left
  have a₃ := mean_parity_row (a := 129) hu ((same 7).trans (same 6).symm)
  have a₄ := mean_parity_row (a := 64*129) hu (by
    rw [show 128*u=64*(2*u) by ring,Nat.mul_dvd_mul_iff_left (by decide : 0<64),
      Nat.mul_dvd_mul_iff_left (by decide : 0<64),ho.dvd_mul_left])
  obtain ⟨c₁,c₂,c₃,c₄,hr⟩ := quotient_increment_rows
  rw [quotient_mean_congr hu0 hr]
  simp only [quotient_mean_add,quotient_mean_smul,hunit,a₁,a₂,a₃,a₄,mul_zero,add_zero]

#print axioms positive_quotient_dyadic_recovery
/-- Ordinary first primes dividing the product and coprime to their cofactors. -/
private def eligibleProductDivisors (P q : ℕ) :=
  q.divisors.filter (fun p => p.Prime ∧ max 4 P<p ∧ ¬p∣q/p)

/-- First-prime coefficient with the actual strict product cut and closed cofactor cap. -/
def clippedPrimeProductCoefficient (P U n q : ℕ) : ℝ :=
  ∑ p ∈ eligibleProductDivisors P q, if U<q ∧ q/p≤n then vonMangoldt p*innerJump 1 (q/p) else 0

/-- Product and outer-quotient dilations remain separate until their common odd part is fixed. -/
def clippedProductQuotientReading (P U n u : ℕ) : ℝ :=
  ∑ r ∈ u.divisors, (clippedPrimeProductCoefficient P U n r+
    (clippedPrimeProductCoefficient P U n (2*r)+clippedPrimeProductCoefficient P U n (4*r))/2)*
    quotientDyadicMean positiveQuotientIncrement (u/r) 7

private theorem clipped_odd_recovery (P U n : ℕ) {u : ℕ} (hu : Odd u) :
    clippedProductQuotientReading P U n u =
      clippedPrimeProductCoefficient P U n u+
      (clippedPrimeProductCoefficient P U n (2*u)+clippedPrimeProductCoefficient P U n (4*u))/2 := by
  let F (r : ℕ) := clippedPrimeProductCoefficient P U n r+
    (clippedPrimeProductCoefficient P U n (2*r)+clippedPrimeProductCoefficient P U n (4*r))/2
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  have row (r : ℕ) (hr : r∈u.divisors) : F r*quotientDyadicMean positiveQuotientIncrement (u/r) 7 =
      if r=u then F u else 0 := by
    have hd := Nat.dvd_of_mem_divisors hr
    have hodd : Odd (u/r) := (Nat.odd_mul.mp (by rwa [Nat.div_mul_cancel hd] : Odd (u/r*r))).1
    rw [positive_quotient_dyadic_recovery hodd]
    by_cases h : r=u
    · subst r; simp [Nat.div_self hu0]
    have hneq : u/r≠1 := fun he => h (by simpa only [he,one_mul] using Nat.div_mul_cancel hd)
    rw [if_neg hneq,if_neg h,mul_zero]
  change (∑ r ∈ u.divisors,F r*quotientDyadicMean positiveQuotientIncrement (u/r) 7)=F u
  rw [sum_congr rfl row,sum_ite_eq',if_pos (Nat.mem_divisors.mpr ⟨dvd_rfl,hu0.ne'⟩)]

private theorem eligible_product_dilation {u a : ℕ} (hu : 0<u) (ha : 0<a) (ha4 : a≤4) (P : ℕ) :
    eligibleProductDivisors P (a*u)=eligibleProductDivisors P u := by
  ext p
  simp only [eligibleProductDivisors,mem_filter,Nat.mem_divisors]
  have hpa (hP : max 4 P<p) : ¬p∣a := fun h => (not_le_of_gt ((le_max_left 4 P).trans_lt hP))
    ((Nat.le_of_dvd ha h).trans ha4)
  constructor
  · rintro ⟨⟨hd,_⟩,hpr,hP,hcop⟩
    have hd' := (hpr.dvd_mul.mp hd).resolve_left (hpa hP)
    rw [Nat.mul_div_assoc a hd'] at hcop
    exact ⟨⟨hd',hu.ne'⟩,hpr,hP,fun h => hcop (dvd_mul_of_dvd_right h a)⟩
  · rintro ⟨⟨hd,_⟩,hpr,hP,hcop⟩
    rw [Nat.mul_div_assoc a hd]
    exact ⟨⟨dvd_mul_of_dvd_right hd a,(Nat.mul_pos ha hu).ne'⟩,hpr,hP,fun h => hcop ((hpr.dvd_mul.mp h).resolve_left (hpa hP))⟩

private def clippedDilation (a U n u v : ℕ) (w : ℝ) : ℝ :=
  if U<a*u ∧ a*v≤n then w else 0

private theorem clipped_row (P U n : ℕ) {u a : ℕ} (hu : 0<u) (ha : 0<a) (ha4 : a≤4) :
    clippedPrimeProductCoefficient P U n (a*u) = ∑ p ∈ eligibleProductDivisors P u,
      vonMangoldt p*clippedDilation a U n u (u/p) (innerJump 1 (a*(u/p))) := by
  rw [clippedPrimeProductCoefficient,eligible_product_dilation hu ha ha4]
  apply sum_congr rfl
  intro p hp
  rw [Nat.mul_div_assoc a (Nat.dvd_of_mem_divisors (mem_filter.mp hp).1)]
  simp only [clippedDilation,mul_ite,mul_zero]

private theorem clipped_row_weights {v : ℕ} (hv : Odd v) :
    innerJump 1 v=(if v=1 then 1 else 0)-1 ∧
    innerJump 1 (2*v)=1-cofactorDyadicCoefficient ∧ innerJump 1 (4*v)=1+cofactorDyadicCoefficient := by
  obtain ⟨k,hk⟩ := hv
  have h : v=2*k+1 := by omega
  obtain ⟨ho,_⟩ := innerJump_dyadic_pair k
  have h₂ := (innerJump_dyadic_pair (2*k)).2
  have h₄ := (innerJump_dyadic_pair (4*k+1)).2
  rw [←h] at ho
  simp only [show (k=0) ↔ v=1 by omega] at ho
  rw [show 2*(2*k)+2=2*v by omega,pow_mul] at h₂
  rw [show 2*(4*k+1)+2=4*v by omega,pow_succ,pow_mul] at h₄
  exact ⟨ho,by simpa using h₂,by simpa [show (-1:ℝ)^4=1 by norm_num] using h₄⟩

private def threeClippedWeights (U n u v : ℕ) : ℝ :=
  clippedDilation 1 U n u v ((if v=1 then 1 else 0)-1)+
    (clippedDilation 2 U n u v (1-cofactorDyadicCoefficient)+
     clippedDilation 4 U n u v (1+cofactorDyadicCoefficient))/2

/-- Three actual product rows after the outer quotient is inverted. -/
theorem clipped_positive_quotient_coefficients (P U n : ℕ) {u : ℕ} (hu : Odd u) :
    clippedProductQuotientReading P U n u = ∑ p ∈ eligibleProductDivisors P u,
      vonMangoldt p*threeClippedWeights U n u (u/p) := by
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  have h₁ := clipped_row P U n hu0 (a := 1) (by decide) (by decide)
  simp only [one_mul] at h₁
  rw [clipped_odd_recovery P U n hu,h₁,clipped_row P U n hu0 (a := 2) (by decide) (by decide),
    clipped_row P U n hu0 (a := 4) (by decide) le_rfl,←sum_add_distrib,sum_div,←sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hd := Nat.dvd_of_mem_divisors (mem_filter.mp hp).1
  have hodd : Odd (u/p) := (Nat.odd_mul.mp (by rwa [Nat.div_mul_cancel hd] : Odd (u/p*p))).1
  obtain ⟨x,y,z⟩ := clipped_row_weights hodd
  rw [x,y,z,threeClippedWeights]
  ring

/-- Above the lower endpoint only two cofactor bands can contribute a
deficit, with fixed weights and the ordinary singleton separated. -/
private theorem two_cap_bands {U n u v : ℕ} (hn : 4≤n) (hu : U<u) :
    threeClippedWeights U n u v =
      (if v=1 then 1 else 0) - (if v≤n ∧ n<2*v then 1 else 0) -
      (if 2*v≤n ∧ n<4*v then (1+cofactorDyadicCoefficient)/2 else 0) := by
  simp only [threeClippedWeights,clippedDilation,one_mul,hu,show U<2*u by omega,show U<4*u by omega,true_and]
  split_ifs <;> first | omega | ring

/-- Total eligible prime logarithms with cofactor in a specified sharp band. -/
def clippedCofactorBand (P u lo hi : ℕ) : ℝ :=
  ∑ p ∈ eligibleProductDivisors P u, if lo<u/p ∧ u/p≤hi then vonMangoldt p else 0

/-- Exact signed secondary terms from the upper cofactor cap after
retaining the original strict product endpoint and taking the quotient mean. -/
theorem above_product_cut_two_cofactor_bands (P : ℕ) {U n u : ℕ} (hn : 4≤n) (hu : Odd u) (hU : U<u) :
    clippedProductQuotientReading P U n u =
      (if u.Prime ∧ max 4 P<u then Real.log u else 0) -
      clippedCofactorBand P u (n/2) n - ((1+cofactorDyadicCoefficient)/2)*clippedCofactorBand P u (n/4) (n/2) := by
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  let S := eligibleProductDivisors P u
  have unit : (∑ p ∈ S, if p=u then vonMangoldt p else 0)=
      (if u.Prime ∧ max 4 P<u then Real.log u else 0) := by
    rw [sum_ite_eq']
    have hh : u∈S ↔ u.Prime ∧ max 4 P<u := by
      simp only [S,eligibleProductDivisors,mem_filter,Nat.mem_divisors,dvd_rfl,true_and,Nat.div_self hu0]
      exact ⟨fun h => ⟨h.2.1,h.2.2.1⟩,fun h => ⟨hu0.ne',h.1,h.2,fun hd => h.1.not_dvd_one hd⟩⟩
    simp only [hh]
    split_ifs with h
    · exact vonMangoldt_apply_prime h.1
    · rfl
  rw [clipped_positive_quotient_coefficients P U n hu,←unit,clippedCofactorBand,clippedCofactorBand,
    mul_sum,←sum_sub_distrib,←sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hdiv := Nat.dvd_of_mem_divisors (mem_filter.mp hp).1
  have hone : (u/p=1) ↔ p=u := ⟨fun h => by simpa only [h,one_mul] using Nat.div_mul_cancel hdiv,
    fun h => by subst p; exact Nat.div_self hu0⟩
  rw [two_cap_bands hn hU]
  have ha : (u/p≤n ∧ n<2*(u/p)) ↔ n/2<u/p ∧ u/p≤n := by omega
  have hb : (2*(u/p)≤n ∧ n<4*(u/p)) ↔ n/4<u/p ∧ u/p≤n/2 := by omega
  simp only [hone,ha,hb]
  split_ifs <;> ring

#print axioms above_product_cut_two_cofactor_bands

/-- At or below the product cut, only the doubled and quadrupled rows survive. -/
theorem below_product_cut_two_cofactor_caps (P n : ℕ) {U u : ℕ} (hu : Odd u) (hU : u≤U) :
    clippedProductQuotientReading P U n u =
      (if U<2*u then (1-cofactorDyadicCoefficient)/2 else 0)*clippedCofactorBand P u 0 (n/2) +
      (if U<4*u then (1+cofactorDyadicCoefficient)/2 else 0)*clippedCofactorBand P u 0 (n/4) := by
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  rw [clipped_positive_quotient_coefficients P U n hu,clippedCofactorBand,clippedCofactorBand,mul_sum,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  have hd := Nat.dvd_of_mem_divisors (mem_filter.mp hp).1
  have hp0 := Nat.pos_of_dvd_of_pos hd hu0
  have hv : 0<u/p := Nat.div_pos (Nat.le_of_dvd hu0 hd) hp0
  simp only [threeClippedWeights,clippedDilation,one_mul,not_lt.mpr hU,false_and,if_false,zero_add,hv,true_and]
  have h₂ : 2*(u/p)≤n ↔ u/p≤n/2 := by omega
  have h₄ : 4*(u/p)≤n ↔ u/p≤n/4 := by omega
  simp only [h₂,h₄,ite_and]
  split_ifs <;> ring

private theorem cofactor_odd_positive : 0<1+cofactorDyadicCoefficient := by
  have ht := cofactor_density_normalization
  have hl := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num : (2:ℝ)≠1)
  by_contra! hn
  have hc : cofactorDyadicCoefficient≤0 := by linarith only [hn]
  have hprod := mul_nonpos_of_nonpos_of_nonneg hc (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  linarith only [ht,hl,hprod]

private theorem band_nonnegative (P u l h : ℕ) : 0≤clippedCofactorBand P u l h :=
  sum_nonneg (fun p _ => by split_ifs <;> first | exact vonMangoldt_nonneg | exact le_rfl)

/-- The sign of the omitted mass changes at the actual strict product cut. -/
theorem clipped_product_quotient_boundary_signs (P U : ℕ) {n u : ℕ} (hn : 4≤n) (hu : Odd u) :
    (u≤U → 0≤clippedProductQuotientReading P U n u) ∧
      (U<u → clippedProductQuotientReading P U n u ≤ (if u.Prime ∧ max 4 P<u then Real.log u else 0)) := by
  constructor
  · intro hU
    rw [below_product_cut_two_cofactor_caps P n hu hU]
    have ha : 0≤(if U<2*u then (1-cofactorDyadicCoefficient)/2 else 0) := by
      split_ifs <;> first | exact (half_pos first_even_cofactor_positive).le | exact le_rfl
    have hb : 0≤(if U<4*u then (1+cofactorDyadicCoefficient)/2 else 0) := by
      split_ifs <;> first | exact (half_pos cofactor_odd_positive).le | exact le_rfl
    exact add_nonneg (mul_nonneg ha (band_nonnegative ..)) (mul_nonneg hb (band_nonnegative ..))
  · intro hU
    rw [above_product_cut_two_cofactor_bands P hn hu hU]
    exact (sub_le_self _ (mul_nonneg (half_pos cofactor_odd_positive).le (band_nonnegative ..))).trans
      (sub_le_self _ (band_nonnegative ..))

#print axioms below_product_cut_two_cofactor_caps
#print axioms clipped_product_quotient_boundary_signs


/-- Beyond a first-prime cutoff covering the lower product endpoint,
the three dilations recover the singleton throughout the sharp upper range. -/
theorem ordinary_prime_above_both_moving_cuts (P U : ℕ) {n u : ℕ} (hn : 4≤n) (hu : Odd u)
    (hP : U≤P) (hscale : 4*u≤n*P) :
    clippedProductQuotientReading P U n u =
      (if u.Prime ∧ max 4 P<u then Real.log u else 0) := by
  have hu0 : 0<u := by obtain ⟨k,hk⟩ := hu; omega
  have hpP {p : ℕ} (hp : p∈eligibleProductDivisors P u) : P<p :=
    (le_max_right 4 P).trans_lt (mem_filter.mp hp).2.2.1
  by_cases hU : U<u
  · have caps (l h : ℕ) (hl : n/4≤l) : clippedCofactorBand P u l h=0 := by
      apply sum_eq_zero
      intro p hp
      have hd := Nat.dvd_of_mem_divisors (mem_filter.mp hp).1
      have hp0 := Nat.pos_of_dvd_of_pos hd hu0
      have hmul : (4*(u/p))*p≤n*p := by
        rw [mul_assoc,Nat.div_mul_cancel hd]
        exact hscale.trans (Nat.mul_le_mul_left n (hpP hp).le)
      have hv : 4*(u/p)≤n := Nat.le_of_mul_le_mul_right hmul hp0
      exact if_neg (fun hj => by omega)
    rw [above_product_cut_two_cofactor_bands P hn hu hU,caps _ _ (by omega),caps _ _ le_rfl,
      mul_zero,sub_zero,sub_zero]
  · have hempty : eligibleProductDivisors P u=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hd := Nat.le_of_dvd hu0 (Nat.dvd_of_mem_divisors (mem_filter.mp hp).1)
      have hh := hpP hp
      omega
    have hlo : ¬max 4 P<u := by have hh := le_max_right 4 P; omega
    rw [clipped_positive_quotient_coefficients P U n hu,hempty,sum_empty,if_neg (fun h => hlo h.2)]

#print axioms ordinary_prime_above_both_moving_cuts

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
