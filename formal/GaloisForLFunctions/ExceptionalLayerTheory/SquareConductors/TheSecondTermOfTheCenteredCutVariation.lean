import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheFineVariationOfTheCenteredPrimeCut
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeAbelCutoff

/-!
# The logarithmic correction to the absolute variation of the centered cutoff

The drift and the prime impulse at a prime p cancel an amount
2λp min(1,log p) in the absolute variation. Its sum gives the full
second term: V(K) = λK² − λK²/log K + o(K²/log K), uniformly while
the cutoff remains below the first spline knot.
-/

noncomputable section
open Finset Filter Topology GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Total variation along every unit step from 0 to K. -/
def centeredCutVariation (N K : ℕ) : ℝ :=
  ∑ k ∈ range K, ‖centeredFixedPrimeTail N (k+1)-centeredFixedPrimeTail N k‖

private def primeMoment (K : ℕ) : ℝ := ∑ p ∈ Nat.primesLE K, (p:ℝ)*Real.log p
private def clippedMoment (K : ℕ) : ℝ := ∑ p ∈ Nat.primesLE K, (p:ℝ)*min 1 (Real.log p)

private theorem prime_support (K : ℕ) : Nat.primesLE K=ordinaryPrimeLags K := by
  ext p
  simp only [Nat.mem_primesLE,ordinaryPrimeLags,mem_filter,mem_Icc]
  exact ⟨fun h => ⟨⟨h.2.two_le,h.1⟩,h.2⟩,fun h => ⟨h.1.2,h.2⟩⟩

/-- Exact loss from taking the absolute value after the prime and
integer terms have been added at each cutoff. -/
theorem centered_cut_variation_decomposition {N K : ℕ} (hn : 0<N)
    (hk : (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2) :
    centeredCutVariation N K=innerPrimeSlope*((K:ℝ)*(K+1)/2+
      (∑ p ∈ Nat.primesLE K, (p:ℝ)*Real.log p)-2*∑ p ∈ Nat.primesLE K, (p:ℝ)*min 1 (Real.log p)) := by
  let f (p : ℕ) : ℝ := (p:ℝ)+(if p.Prime then (p:ℝ)*Real.log p else 0)-
    2*(if p.Prime then (p:ℝ)*min 1 (Real.log p) else 0)
  have atom (p : ℕ) : |innerCutIncrement p|=innerPrimeSlope*f p := by
    rw [innerCutIncrement,abs_mul,abs_of_nonneg (mul_nonneg innerPrimeSlope_pos.le (Nat.cast_nonneg p))]
    dsimp only [f]
    by_cases prime : p.Prime
    · simp only [prime,if_true]
      rcases le_total (Real.log p) 1 with h|h
      · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr h)]
        ring
      · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr h)]
        ring
    · simp [prime]
  have mesh : centeredCutVariation N K=innerPrimeSlope*(∑ p ∈ range (K+1), f p) := by
    rw [centeredCutVariation,sum_range_succ',show f 0=0 by simp [f],add_zero,mul_sum]
    apply sum_congr rfl
    intro k h
    have hi := Nat.succ_le_of_lt (mem_range.mp h)
    rw [centered_fixed_cut_step hn ((Nat.cast_le.mpr hi).trans hk),Complex.norm_real,Real.norm_eq_abs,atom]
  have triangle (k : ℕ) : (∑ p ∈ range (k+1), (p:ℝ))=(k:ℝ)*(k+1)/2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [sum_range_succ,ih]
      push_cast
      ring
  rw [mesh]
  dsimp only [f]
  rw [sum_sub_distrib,sum_add_distrib,←mul_sum,←sum_filter,←sum_filter,triangle] <;> rfl

-- The elementary inequality p log(K/p) ≤ K−p controls the cost of
-- replacing log p by log K inside the clipped prime moment.
private theorem clipped_log_error {K : ℕ} (lg : 1≤Real.log K) :
    0≤Real.log K*clippedMoment K-primeMoment K ∧
    Real.log K*clippedMoment K-primeMoment K≤(K:ℝ)*Nat.primeCounting K := by
  have each {p : ℕ} (hp : p∈Nat.primesLE K) :
      0≤Real.log K*((p:ℝ)*min 1 (Real.log p))-(p:ℝ)*Real.log p ∧
      Real.log K*((p:ℝ)*min 1 (Real.log p))-(p:ℝ)*Real.log p≤K := by
    obtain ⟨le,pr⟩ := Nat.mem_primesLE.mp hp
    have pos : 0<(p:ℝ) := Nat.cast_pos.mpr pr.pos
    have kp : 0<(K:ℝ) := Nat.cast_pos.mpr (pr.pos.trans_le le)
    have pl := Real.log_le_log pos (Nat.cast_le.mpr le)
    have low : Real.log p≤Real.log K*min 1 (Real.log p) := by
      rcases le_total (Real.log p) 1 with h|h
      · rw [min_eq_right h]
        exact le_mul_of_one_le_left (Real.log_natCast_nonneg p) lg
      · simpa only [min_eq_left h,mul_one] using pl
    have raw := Real.log_le_sub_one_of_pos (div_pos kp pos)
    rw [Real.log_div kp.ne' pos.ne'] at raw
    have endpt := mul_le_mul_of_nonneg_right raw pos.le
    rw [sub_mul,div_mul_cancel₀ _ pos.ne',one_mul] at endpt
    have upper := mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Real.log p)) (Real.log_natCast_nonneg K)
    rw [mul_one] at upper
    constructor <;> linarith only [mul_le_mul_of_nonneg_left low pos.le,
      mul_le_mul_of_nonneg_left upper pos.le,endpt,pos]
  unfold clippedMoment primeMoment
  rw [mul_sum,←sum_sub_distrib]
  refine ⟨sum_nonneg (fun _ h => (each h).1),?_⟩
  have high := sum_le_sum (s:=Nat.primesLE K) (fun p h => (each h).2)
  simpa only [sum_const,nsmul_eq_mul,Nat.primesLE_card_eq_primeCounting,mul_comm (Nat.primeCounting K:ℝ)] using high

/-- The second asymptotic coefficient is −λ. The same error bound
holds for every conductor whose first knot covers K. -/
theorem centered_cut_variation_second_term {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ K : ℕ in atTop, ∀ N : ℕ, 0<N → (K:ℝ)≤Real.exp (-8)*(N:ℝ)^2 →
      |(innerPrimeSlope*(K:ℝ)^2-centeredCutVariation N K)*Real.log K/(K:ℝ)^2-innerPrimeSlope|<ε := by
  obtain ⟨C,hC,hP⟩ := first_prime_moment_at_cut
  let l := innerPrimeSlope
  have lp : 0<l := innerPrimeSlope_pos
  have powlim : Tendsto (fun K : ℕ => ((K:ℝ)^(1/18:ℝ))⁻¹) atTop (𝓝 0) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/18)).comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have density := ArithmeticWeightTheory.GaugeDeformations.tendsto_primeCounting_div_nat_zero
  have limit : Tendsto (fun K : ℕ => l*(18*(C+1)*((K:ℝ)^(1/18:ℝ))⁻¹+
      2*((Nat.primeCounting K:ℝ)/K))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (tendsto_const_nhds (x:=l)).mul
      (((tendsto_const_nhds (x:=18*(C+1))).mul powlim).add ((tendsto_const_nhds (x:=(2:ℝ))).mul density))
  have loggrow : Tendsto (fun K : ℕ => Real.log K) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [limit.eventually_lt_const hε,loggrow.eventually_ge_atTop 1,eventually_ge_atTop 1] with K small lg hK
  intro N hn knot
  let x := (K:ℝ)
  let t := x*(x+1)/2
  let u := Real.log x
  let e := primeMoment K-t
  let r := u*clippedMoment K-primeMoment K
  have x1 : 1≤x := Nat.one_le_cast.mpr hK
  have xp := zero_lt_one.trans_le x1
  have err : |e|≤C*x^(17/9:ℝ) := by simpa only [e,t,x,primeMoment,prime_support] using hP K hK
  obtain ⟨r0,rc⟩ := clipped_log_error lg
  change 0≤r at r0
  change r≤x*Nat.primeCounting K at rc
  change 1≤u at lg
  have un : 0≤u := zero_le_one.trans lg
  have scaled : (l*x^2-centeredCutVariation N K)*u-l*x^2=l*((2-u)*e+x*(1-u)+2*r) := by
    rw [centered_cut_variation_decomposition hn knot]
    dsimp [l,e,r,t,primeMoment,clippedMoment,x,u]
    ring
  have a1 : |2-u|≤u := abs_le.mpr (by constructor <;> linarith only [lg])
  have a2 : |1-u|≤u := abs_le.mpr (by constructor <;> linarith only [lg])
  have ab : |(2-u)*e+x*(1-u)+2*r|≤(C*x^(17/9:ℝ)+x)*u+2*(x*Nat.primeCounting K) := by
    apply (abs_add_le ..).trans
    have pair := abs_add_le ((2-u)*e) (x*(1-u))
    rw [abs_mul,abs_mul,abs_of_pos xp] at pair
    rw [abs_of_nonneg (mul_nonneg (by norm_num) r0)]
    linarith only [pair,mul_le_mul a1 err (abs_nonneg e) un,mul_le_mul_of_nonneg_left a2 xp.le,rc]
  have xpow : x≤x^(17/9:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le x1 (by norm_num : (1:ℝ)≤17/9)
  have logcap : u≤18*x^(1/18:ℝ) := by
    linarith only [Real.log_le_rpow_div xp.le (by norm_num : (0:ℝ)<1/18)]
  have prod := mul_le_mul (show C*x^(17/9:ℝ)+x≤(C+1)*x^(17/9:ℝ) by linarith only [xpow]) logcap un
    (mul_nonneg (by linarith only [hC]) (Real.rpow_nonneg xp.le _))
  have recover : x^(17/9:ℝ)*x^(1/18:ℝ)=x^2*(x^(1/18:ℝ))⁻¹ := by
    rw [←Real.rpow_neg xp.le,←Real.rpow_two,←Real.rpow_add xp,←Real.rpow_add xp]
    norm_num
  have paid : |(l*x^2-centeredCutVariation N K)*u-l*x^2|≤
      l*(18*(C+1)*(x^(1/18:ℝ))⁻¹+2*((Nat.primeCounting K:ℝ)/x))*x^2 := by
    rw [scaled,abs_mul,abs_of_pos lp]
    have main := mul_le_mul_of_nonneg_left (ab.trans (add_le_add prod le_rfl)) lp.le
    apply main.trans_eq
    have den : (Nat.primeCounting K:ℝ)/x*x^2=x*Nat.primeCounting K := by field_simp [xp.ne'] <;> ring
    linear_combination 18*l*(C+1)*recover - 2*l*den
  change |(l*x^2-centeredCutVariation N K)*u/x^2-l|<ε
  rw [show (l*x^2-centeredCutVariation N K)*u/x^2-l=
      ((l*x^2-centeredCutVariation N K)*u-l*x^2)/x^2 by field_simp [xp.ne'],
    abs_div,abs_of_pos (sq_pos_of_pos xp)]
  exact ((div_le_iff₀ (sq_pos_of_pos xp)).mpr paid).trans_lt small

/-- The variation at the prescribed seventeen-ninths cutoff has the
same logarithmic correction in its integer cutoff coordinate. -/
theorem seventeen_ninths_cut_variation_second_term :
    Tendsto (fun N : ℕ => let K := ⌊(N:ℝ)^(17/9:ℝ)⌋₊
      (innerPrimeSlope*(K:ℝ)^2-centeredCutVariation N K)*Real.log K/(K:ℝ)^2)
      atTop (𝓝 innerPrimeSlope) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j,hj⟩ := eventually_atTop.mp (centered_cut_variation_second_term hε)
  filter_upwards [seventeen_ninths_inside_first_knot,eventually_ge_atTop (max 1 j)] with N geo late
  rw [Real.dist_eq]
  exact hj _ (((le_max_right 1 j).trans late).trans geo.1) N ((le_max_left 1 j).trans late) geo.2

#print axioms seventeen_ninths_cut_variation_second_term
#print axioms centered_cut_variation_decomposition
#print axioms centered_cut_variation_second_term
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
