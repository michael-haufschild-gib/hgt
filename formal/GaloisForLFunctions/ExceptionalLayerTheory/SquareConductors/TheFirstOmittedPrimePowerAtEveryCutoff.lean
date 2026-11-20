import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SeparatingEveryPurePowerAtTheCompositeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SharpPowerRecoveryFromOrdinaryPrimeMidpoints
import GaloisForLFunctions.RHTower.RobinLcmCriterion

/-!
# The first omitted prime-power scale

After removing the coprime rows up to exponent J, the remainder is
nonnegative. Its maximum over all centers is attained at one and is
asymptotic to (J+1) x^(1/(J+1)). The same leading coefficient holds
for every varying center with log n = o(x^(1/(J+1))).
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Full-log mass of coprime pure powers with exponent greater than J. -/
def remainingProperPowerPrice (n J : ℕ) (x : ℝ) :=
  fullLogProperPrefix n x - ∑ j ∈ Icc 2 J, (j:ℝ)*coprimeTheta n (x^(1/(j:ℝ)))

private theorem theta_at_center_one (x : ℝ) : coprimeTheta 1 x=Chebyshev.theta x := by
  simp [coprimeTheta,Chebyshev.theta]

private theorem residual_rows (n : ℕ) {J H : ℕ} (hJ : 2≤J) (hH : J≤H) {x : ℝ}
    (hx : 0≤x) (h : ⌊Real.log x/Real.log 2⌋₊≤H) :
    remainingProperPowerPrice n J x = ∑ j ∈ Ioc J H, (j:ℝ)*coprimeTheta n (x^(1/(j:ℝ))) := by
  have hs : Icc 2 H = Icc 2 J ∪ Ioc J H := by ext j; simp; omega
  have hd : Disjoint (Icc 2 J) (Ioc J H) :=
    disjoint_left.mpr fun _ hj hk => (mem_Ioc.mp hk).1.not_ge (mem_Icc.mp hj).2
  rw [remainingProperPowerPrice,full_log_proper_power_rows n hx H h,hs,sum_union hd,add_sub_cancel_left]

/-- Every coprimality center deletes a nonnegative part of the
unrestricted remainder. The upper envelope is attained for every x. -/
theorem largest_proper_power_remainder (n : ℕ) {J : ℕ} (hJ : 2≤J) {x : ℝ} (hx : 0≤x) :
    0≤remainingProperPowerPrice n J x ∧ remainingProperPowerPrice n J x≤remainingProperPowerPrice 1 J x := by
  have he (m : ℕ) := residual_rows m hJ (le_max_left J ⌊Real.log x/Real.log 2⌋₊) hx (le_max_right _ _)
  rw [he n,he 1]
  have hc (y : ℝ) : 0≤coprimeTheta n y ∧ coprimeTheta n y≤Chebyshev.theta y := by
    unfold coprimeTheta Chebyshev.theta
    constructor
    · exact sum_nonneg fun p _ => by split <;> first | exact Real.log_natCast_nonneg _ | rfl
    · exact sum_le_sum fun p _ => by split <;> first | rfl | exact Real.log_natCast_nonneg _
  refine ⟨sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hc _).1),sum_le_sum (fun j _ => ?_)⟩
  rw [theta_at_center_one]
  exact mul_le_mul_of_nonneg_left (hc _).2 (Nat.cast_nonneg j)

private theorem next_power_row {J : ℕ} (hJ : 2≤J) (n : ℕ) (x : ℝ) :
    remainingProperPowerPrice n J x =
      (J+1:ℕ)*coprimeTheta n (x^(1/((J:ℝ)+1))) + remainingProperPowerPrice n (J+1) x := by
  have hs : Icc 2 (J+1) = insert (J+1) (Icc 2 J) := by ext j; simp; omega
  have hn : J+1 ∉ Icc 2 J := by simp
  rw [remainingProperPowerPrice,remainingProperPowerPrice,hs,sum_insert hn,Nat.cast_add,Nat.cast_one]
  ring

/-- Uniform power saving after displaying the actual first omitted
coprime prime row. No restriction on the size of the center is needed. -/
theorem first_omitted_coprime_power_row {J : ℕ} (hJ : 2≤J) {b : ℝ}
    (hb : 1/((J:ℝ)+2)<b) :
    ∃ C : ℝ, 0≤C ∧ ∀ (n : ℕ) (x : ℝ), 1≤x →
      0 ≤ remainingProperPowerPrice n J x-(J+1:ℕ)*coprimeTheta n (x^(1/((J:ℝ)+1))) ∧
      remainingProperPowerPrice n J x-(J+1:ℕ)*coprimeTheta n (x^(1/((J:ℝ)+1))) ≤ C*x^b := by
  have hb' : 1/(((J+1:ℕ):ℝ)+1)<b := by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hb
  obtain ⟨C,hC,hh⟩ := uniform_full_log_truncation (J:=J+1) (by omega) hb'
  refine ⟨C,hC,fun n x hx => ?_⟩
  rw [next_power_row hJ n x,add_sub_cancel_left]
  have hm := largest_proper_power_remainder n (J:=J+1) (by omega) (zero_le_one.trans hx)
  have hh' := hh 1 (by decide) x hx
  simp only [Nat.cast_one,Real.log_one,mul_zero,zero_add] at hh'
  refine ⟨hm.1,hm.2.trans ?_⟩
  unfold remainingProperPowerPrice
  simp only [theta_at_center_one]
  exact (le_abs_self _).trans hh'

/-- At the first omitted scale only its coprime prime row survives,
uniformly for arbitrarily large coprimality centers. -/
theorem normalized_omitted_row_error {ι : Type*} {l : Filter ι} {J : ℕ} (hJ : 2≤J)
    (u : ι → ℝ) (hu : Tendsto u l atTop) (n : ι → ℕ) :
    let r := 1/((J:ℝ)+1)
    Tendsto (fun i => (remainingProperPowerPrice (n i) J (u i) -
      ((J:ℝ)+1)*coprimeTheta (n i) ((u i)^r))/(u i)^r) l (𝓝 0) := by
  let r := 1/((J:ℝ)+1)
  have hgap : 1/((J:ℝ)+2)<r :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith only [show (0:ℝ)<1 by norm_num])
  obtain ⟨b,hb,hbr⟩ := exists_between hgap
  obtain ⟨C,hC,h⟩ := first_omitted_coprime_power_row hJ hb
  have hsmall := ((tendsto_rpow_neg_atTop (sub_pos.mpr hbr)).comp hu).const_mul C
  rw [mul_zero] at hsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
  · filter_upwards [hu.eventually_ge_atTop 1] with i hx
    have hh := (h (n i) (u i) hx).1
    push_cast at hh
    exact div_nonneg hh (Real.rpow_nonneg (zero_le_one.trans hx) r)
  · filter_upwards [hu.eventually_ge_atTop 1] with i hx
    have hh := (h (n i) (u i) hx).2
    push_cast at hh
    have hx₀ := zero_lt_one.trans_le hx
    apply (div_le_div_of_nonneg_right hh (Real.rpow_nonneg hx₀.le r)).trans_eq
    change C*(u i)^b/(u i)^r = C*(u i)^(-(r-b))
    rw [mul_div_assoc,←Real.rpow_sub hx₀,neg_sub]

/-- The sharp coefficient of the upper envelope also survives varying
centers whose logarithm is negligible at the first omitted scale. -/
theorem first_omitted_power_coefficient {ι : Type*} {l : Filter ι} {J : ℕ} (hJ : 2≤J)
    (u : ι → ℝ) (hu : Tendsto u l atTop) (n : ι → ℕ) (hn : ∀ᶠ i in l, 0<n i)
    (hsize : Tendsto (fun i => Real.log (n i)/(u i)^(1/((J:ℝ)+1))) l (𝓝 0)) :
    Tendsto (fun i => remainingProperPowerPrice (n i) J (u i)/(u i)^(1/((J:ℝ)+1)))
      l (𝓝 ((J:ℝ)+1)) := by
  let r := 1/((J:ℝ)+1)
  have hr : 0<r := by dsimp only [r]; positivity
  have hθ := _root_.RHTower.tendsto_theta_div_self.comp ((tendsto_rpow_atTop hr).comp hu)
  have hc : Tendsto (fun i => coprimeTheta (n i) ((u i)^r)/(u i)^r) l (𝓝 1) := by
    have hl := hθ.sub hsize
    rw [sub_zero] at hl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hθ
    · filter_upwards [hn,hu.eventually_gt_atTop 0] with i hn' hx
      have hh := (coprime_theta_loss hn' ((u i)^r)).2
      change Chebyshev.theta ((u i)^r)/(u i)^r-Real.log (n i)/(u i)^r≤_
      rw [←sub_div]
      exact div_le_div_of_nonneg_right (by linarith only [hh]) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hn,hu.eventually_gt_atTop 0] with i hn' hx
      exact div_le_div_of_nonneg_right (sub_nonneg.mp (coprime_theta_loss hn' ((u i)^r)).1) (Real.rpow_nonneg hx.le _)
  have ht := (normalized_omitted_row_error hJ u hu n).add (hc.const_mul ((J:ℝ)+1))
  rw [mul_one,zero_add] at ht
  apply ht.congr
  intro i
  simp only [r,sub_div,mul_div_assoc,sub_add_cancel]

/-- At center one the normalized maximum tends to J+1, so the first
omitted exponent and its coefficient are both attained. -/
theorem sharp_maximal_proper_power_remainder {J : ℕ} (hJ : 2≤J) :
    Tendsto (fun x : ℝ => remainingProperPowerPrice 1 J x/x^(1/((J:ℝ)+1)))
      atTop (𝓝 ((J:ℝ)+1)) := by
  apply first_omitted_power_coefficient hJ id tendsto_id (fun _ => 1) (Eventually.of_forall fun _ => by decide)
  simp only [Nat.cast_one,Real.log_one,zero_div]
  exact tendsto_const_nhds

private theorem dilated_coprime_power_remainder {J : ℕ} (hJ : 2≤J) {k : ℝ} (hk : 0<k) :
    Tendsto (fun n : ℕ => remainingProperPowerPrice n J (k*n)/(n:ℝ)^(1/((J:ℝ)+1)))
      atTop (𝓝 (((J:ℝ)+1)*k^(1/((J:ℝ)+1)))) := by
  let r := 1/((J:ℝ)+1)
  have hr : 0<r := by dsimp only [r]; positivity
  have hk' := Real.rpow_pos_of_pos hk r
  have hc := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hl := ((_root_.RHTower.tendsto_log_pow_div_rpow_atTop 1 hr).comp hc).div_const (k^r)
  rw [zero_div] at hl
  have hsize : Tendsto (fun n : ℕ => Real.log n / (k*n)^r) atTop (𝓝 0) := by
    apply hl.congr
    intro n
    simp only [Function.comp_apply,pow_one,Real.mul_rpow hk.le (Nat.cast_nonneg n),div_div,mul_comm]
  have hp := first_omitted_power_coefficient hJ (fun n : ℕ => k*n) (hc.const_mul_atTop hk) id
    (eventually_gt_atTop (0:ℕ)) hsize
  apply (hp.mul_const (k^r)).congr
  intro n
  change remainingProperPowerPrice n J (k*n)/(k*n)^r*k^r = _
  rw [Real.mul_rpow hk.le (Nat.cast_nonneg n),mul_comm (k^r),←div_div,div_mul_cancel₀ _ hk'.ne']

/-- After removing exponents through J, the signed midpoint of the
remaining proper powers has a positive leading term at the next root.
Only the prime number theorem at that root enters the coefficient. -/
theorem signed_first_omitted_power_of_the_midpoint {J : ℕ} (hJ : 2≤J) :
    let r := 1/((J:ℝ)+1)
    Tendsto (fun n : ℕ => (2*remainingProperPowerPrice n J ((3:ℝ)*n) -
      remainingProperPowerPrice n J ((2:ℝ)*n) - remainingProperPowerPrice n J ((4:ℝ)*n))/(n:ℝ)^r)
      atTop (𝓝 (((J:ℝ)+1)*midpointPowerGap r)) := by
  let r := 1/((J:ℝ)+1)
  have ht := (((dilated_coprime_power_remainder hJ (by norm_num : (0:ℝ)<3)).const_mul 2).sub
    (dilated_coprime_power_remainder hJ (by norm_num : (0:ℝ)<2))).sub
    (dilated_coprime_power_remainder hJ (by norm_num : (0:ℝ)<4))
  change Tendsto _ _ (𝓝 (((J:ℝ)+1)*midpointPowerGap r))
  rw [show ((J:ℝ)+1)*midpointPowerGap r =
    2*(((J:ℝ)+1)*(3:ℝ)^r)-((J:ℝ)+1)*(2:ℝ)^r-((J:ℝ)+1)*(4:ℝ)^r by
      unfold midpointPowerGap; ring]
  apply ht.congr
  intro n
  simp only [sub_div,mul_div_assoc]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
