import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion.Finite
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion.Tilt
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Occupation.Sector

/-! # First exclusion correction to the number of upper prime occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion

open Occupation Finset Real Filter Topology
open Set (Ioi)
open BinaryOrientation.LargestPrime.Bands
local instance : LinearOrder Nat.Primes := LinearOrder.lift' Subtype.val Subtype.val_injective

/-- For a count supported on 0,1,2, its expectation is the sum of the two upper-tail probabilities. -/
def meanUpper (c d D k b : ℝ) (h : Ioi (0:ℝ)) :=
  read c d D k b 2 {1,2} h + read c d D k b 2 {2} h

/-- The two tail readings give the Born-weighted expectation of the upper occupation count. -/
theorem meanUpper_eq_average (c d D k b : ℝ) (h : Ioi (0:ℝ)) :
    let t := c/h.val
    let S := added c d h
    let U := sector S (both D k t) 2
    meanUpper c d D k b h =
      (∑ R ∈ U, born b R*
        (upperCount (modes S (high D k t)) R:ℝ))/
        mass (born b) U := by
  let S := added c d h
  let H := modes S (high D k (c/h.val))
  unfold meanUpper Occupation.read countRead share mass
  simp only [sum_filter,← add_div,← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro R _
  change (if upperCount H R ∈ ({1,2}:Finset ℕ) then born b R else 0)+
    (if upperCount H R ∈ ({2}:Finset ℕ) then born b R else 0)=born b R*(upperCount H R:ℝ)
  have hj : upperCount H R ≤ 2 := (card_filter_le _ _).trans_eq R.property
  rcases (show upperCount H R=0 ∨ upperCount H R=1 ∨ upperCount H R=2 by omega) with he | he | he <;>
    simp [he,mul_two]

/-- The exact displacement from the independent mean is the difference between the one-draw
upper shares at b and 2b, weighted by the odds of a repeated label. -/
theorem mean_shift {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    ∀ᶠ h in criticalApproach, let t := c/h.val
      let C := collision c d D k b h
      meanUpper c d D k b h - 2*upper D k b t =
        2*C*(upper D k b t-upper D k (2*b) t)/(1-C) := by
  filter_upwards [mode_coverage hc hcd hD hk,(translation_limit hc).eventually (windows hD hk),
    (collision_vanishes hc hcd hD hk b).eventually_lt_const zero_lt_one] with h cov hw hC
  let t := c/h.val
  let S := added c d h
  let P := both D k t
  let H := high D k t
  let q := draw S P b t
  let C := collision c d D k b h
  have hp : P.Nonempty := hw.1.mono subset_union_left
  have him : (modes S P).image serial=P := cov
  have hu (g : ℝ) : (∑ r ∈ modes S H,draw S P g t r) = upper D k g t :=
    draw_event him (show H ⊆ P from subset_union_right) g t
  have hsq : (∑ r ∈ modes S H,q r^2) = C*upper D k (2*b) t := by
    rw [sum_congr rfl (fun r _ => collision_tilt hp him b t r),← mul_sum,hu]
    rfl
  have eqv := pair_mean q (draw_total hp him b t) (modes S H)
  rw [hsq,show (∑ r ∈ modes S H,q r)=upper D k b t from hu b] at eqv
  change (countRead S P H b 2 {1,2}+countRead S P H b 2 {2})-2*upper D k b t = _
  rw [born_subset P H hp b t,born_subset P H hp b t,eqv]
  change 2*(upper D k b t-C*upper D k (2*b) t)/(1-C)-2*upper D k b t =
    2*C*(upper D k b t-upper D k (2*b) t)/(1-C)
  have hd : 1-C ≠ 0 := (sub_pos.mpr (show C < 1 from hC)).ne'
  apply (eq_div_iff hd).mpr
  rw [sub_mul,div_mul_cancel₀ _ hd]
  ring

/-- Uniform one-draw weights make the mean exactly unchanged by removing repetitions. -/
theorem uniform_pair_mean {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) :
    ∀ᶠ h in criticalApproach, meanUpper c d D k 0 h = 2*upper D k 0 (c/h.val) := by
  filter_upwards [mean_shift hc hcd hD hk 0] with h hh
  dsimp only at hh
  simpa only [mul_zero,sub_self,zero_div,sub_eq_zero] using hh

def bias (D k b : ℝ) := 2*(odds D k b-odds D k (2*b))/(1+odds D k b)^3

private theorem bias_eq {D k : ℝ} (hk : 0 < k) (b : ℝ) :
    2*collisionScale D k b*(upperProbability D k b-upperProbability D k (2*b)) = bias D k b := by
  unfold collisionScale upperProbability bias
  field_simp [(add_pos zero_lt_one (odds_pos D hk b)).ne',(add_pos zero_lt_one (odds_pos D hk (2*b))).ne']
  ring

/-- First-order deviation from the actual finite independent-draw mean, on the birthday scale. -/
theorem bias_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    Tendsto (fun h : Ioi (0:ℝ) => (meanUpper c d D k b h-2*upper D k b (c/h.val))/scale (c/h.val))
      criticalApproach (𝓝 (bias D k b)) := by
  have hu (g : ℝ) : Tendsto (fun h : Ioi (0:ℝ) => upper D k g (c/h.val)) criticalApproach (𝓝 (upperProbability D k g)) :=
    (upper_limit hD hk g).comp (translation_limit hc)
  have hc' := squared_draw_limit hc hcd hD hk b
  have den := (tendsto_const_nhds (x := (1:ℝ))).sub (collision_vanishes hc hcd hD hk b)
  rw [sub_zero] at den
  have lim := (((hc'.const_mul 2).mul ((hu b).sub (hu (2*b)))).div den one_ne_zero)
  rw [div_one,bias_eq hk b] at lim
  apply lim.congr'
  filter_upwards [mean_shift hc hcd hD hk b] with h hh
  dsimp only at hh ⊢
  rw [hh]
  change 2*(collision c d D k b h/scale (c/h.val))*_/_ = 2*collision c d D k b h*_/_/scale (c/h.val)
  ring

/-- The leading correction is strictly positive exactly at positive inverse temperature. -/
theorem bias_pos_iff {D k : ℝ} (hD : 0 < D) (hk : 0 < k) (b : ℝ) : 0 < bias D k b ↔ 0 < b := by
  have hd := pow_pos (add_pos zero_lt_one (odds_pos D hk b)) 3
  rw [bias,div_pos_iff_of_pos_right hd,mul_pos_iff_of_pos_left two_pos,sub_pos,odds,odds,
    mul_lt_mul_iff_right₀ hk,exp_lt_exp,mul_lt_mul_iff_left₀ hD]
  constructor <;> intro h <;> linarith only [h]

theorem bias_zero_iff {D k : ℝ} (hD : 0 < D) (hk : 0 < k) (b : ℝ) : bias D k b = 0 ↔ b = 0 := by
  have hd := pow_pos (add_pos zero_lt_one (odds_pos D hk b)) 3
  rw [bias,div_eq_zero_iff,or_iff_left hd.ne',mul_eq_zero,or_iff_right (two_ne_zero : (2:ℝ)≠0),sub_eq_zero]
  constructor
  · intro he
    have e := exp_injective (mul_left_cancel₀ hk.ne' he)
    change (1-b)*D=(1-2*b)*D at e
    have g := mul_right_cancel₀ hD.ne' e
    linarith only [g]
  · rintro rfl
    rw [mul_zero]

theorem bias_neg_iff {D k : ℝ} (hD : 0 < D) (hk : 0 < k) (b : ℝ) : bias D k b < 0 ↔ b < 0 := by
  have hz : 0 = bias D k b ↔ 0 = b := eq_comm.trans ((bias_zero_iff hD hk b).trans eq_comm)
  have he : 0 ≤ bias D k b ↔ 0 ≤ b := by simp only [le_iff_lt_or_eq,hz,bias_pos_iff hD hk b]
  simpa only [not_le] using not_congr he

/-- At critical damping and equal widths, distinct primes raise the mean above the
finite independent-draw baseline to first order. -/
theorem critical_pair_correction {c d D : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) :
    Tendsto (fun h : Ioi (0:ℝ) => (meanUpper c d D 1 1 h-2*upper D 1 1 (c/h.val))/scale (c/h.val))
      criticalApproach (𝓝 ((1-exp (-D))/4)) ∧ 0 < (1-exp (-D))/4 := by
  have coefficient : bias D 1 1 = (1-exp (-D))/4 := by
    simp only [bias,odds,sub_self,zero_mul,exp_zero,one_mul,mul_one,one_add_one_eq_two]
    rw [show (1-(2:ℝ))*D = -D by ring]
    ring
  rw [← coefficient]
  exact ⟨bias_limit hc hcd hD zero_lt_one 1,(bias_pos_iff hD zero_lt_one 1).mpr zero_lt_one⟩

#print axioms critical_pair_correction
#print axioms meanUpper_eq_average
#print axioms mean_shift
#print axioms uniform_pair_mean
#print axioms bias_limit
#print axioms bias_pos_iff
#print axioms bias_zero_iff
#print axioms bias_neg_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exclusion
