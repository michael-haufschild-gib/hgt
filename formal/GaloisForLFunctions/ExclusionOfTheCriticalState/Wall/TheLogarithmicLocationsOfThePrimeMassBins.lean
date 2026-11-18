import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.DilatingTheOrdinaryPrimeMeasure
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import GaloisForLFunctions.RHTower.ChebyshevErrorExponentLaw
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount

/-!
# Locations of the dilated Chebyshev mass bins

On the axis v = 2 log y, replacing y by the prime at Chebyshev mass y
changes both its logarithmic position and its reciprocal weight by an
exponentially decreasing amount.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower GaloisForLFunctions.RHTower

private theorem theta_power_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
    |Chebyshev.theta x-x| ≤ C*x^(9/10:ℝ) := by
  have hz : zeroReSup ≤ 7/8 := zeroReSup_le_of_forall_re_le fun q =>
    le_of_not_gt fun h =>
      MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_seven_eighths_lt_re h
        (riemannZeta_xiZeroCopy_eq_zero q)
  obtain ⟨C,hC,hψ⟩ := exists_abs_chebyshevPsi_sub_le_rpow
    (show zeroReSup < (9/10:ℝ) by linarith only [hz])
  obtain ⟨B,hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨C+|B|,add_nonneg hC (abs_nonneg _),fun x hx => ?_⟩
  have hd : |Chebyshev.theta x-Chebyshev.psi x| ≤ |B|*x^(9/10:ℝ) := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi _))]
    exact (hB x).trans (mul_le_mul (le_abs_self _) (by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)) (Real.sqrt_nonneg _) (abs_nonneg _))
  calc _ ≤ |Chebyshev.theta x-Chebyshev.psi x|+|Chebyshev.psi x-x| := abs_sub_le ..
    _ ≤ _ := (add_le_add hd (hψ x hx)).trans_eq (by ring)

private theorem bin_power_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y : ℝ in atTop,
    |primeBinReading 1 y-y| ≤ C*y^(9/10:ℝ) := by
  obtain ⟨K,hK,hθ⟩ := theta_power_error
  refine ⟨1+K*2^(9/10:ℝ),by positivity,?_⟩
  filter_upwards [tendsto_primeBinReading_one_div.eventually_gt_const (by norm_num : (1/2:ℝ)<1),
    tendsto_primeBinReading_one_div.eventually_lt_const one_lt_two,eventually_ge_atTop (4:ℝ)] with y hlo hhi hy
  let p := primeBinReading 1 y
  have hy0 : 0 < y := by linarith only [hy]
  have hlo' : 1/2*y < p := (lt_div_iff₀ hy0).mp hlo
  have hhi' : p < 2*y := (div_lt_iff₀ hy0).mp hhi
  have hp : 1 ≤ p-1 := by linarith only [hy,hlo']
  have hp1 : 1 ≤ p := by linarith only [hp]
  obtain ⟨hl,hr⟩ := primeBinReading_one_brackets hy0.le
  have hpow : p^(9/10:ℝ) ≤ 2^(9/10:ℝ)*y^(9/10:ℝ) :=
    (Real.rpow_le_rpow (zero_le_one.trans hp1) hhi'.le (by norm_num)).trans_eq
      (Real.mul_rpow (by norm_num) hy0.le)
  have hm := Real.rpow_le_rpow (zero_le_one.trans hp) (sub_le_self p zero_le_one) (by norm_num : (0:ℝ)≤9/10)
  have hL := (abs_le.mp (hθ (p-1) hp)).1
  have hR := (abs_le.mp (hθ p hp1)).2
  have h1 := Real.one_le_rpow (show 1 ≤ y by linarith only [hy]) (by norm_num : (0:ℝ) ≤ 9/10)
  change Chebyshev.theta (p-1) ≤ y at hl
  change y < Chebyshev.theta p at hr
  change |p-y| ≤ _
  have H := mul_le_mul_of_nonneg_left hpow hK
  have H' := mul_le_mul_of_nonneg_left hm hK
  rw [abs_le]
  constructor <;> linarith only [hL,hR,hl,hr,H,H',h1]

/-- Logarithmic location of the prime square at mass coordinate v. -/
def squareBinLocation (v : ℝ) : ℝ := 2*Real.log (primeBinReading 1 (Real.exp (v/2)))

/-- Relative reciprocal weight of the same prime. -/
def squareBinWeight (v : ℝ) : ℝ := Real.exp (v/2)/primeBinReading 1 (Real.exp (v/2))

theorem monotone_squareBinLocation : Monotone squareBinLocation := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.log_le_log (primeBinReading_one_pos _)
  exact monotone_primeBinReading_one (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hab (by norm_num)))

theorem measurable_squareBinWeight : Measurable squareBinWeight := by
  have he : Measurable (fun v : ℝ => Real.exp (v/2)) := by fun_prop
  exact he.div ((measurable_primeBinReading 1).comp he)

private theorem abs_log_le_twice_sub {u : ℝ} (hu : 1/2 ≤ u) : |Real.log u| ≤ 2*|u-1| := by
  have hp : 0 < u := by linarith only [hu]
  have h := Real.log_le_sub_one_of_pos hp
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hi
  have hdiv : |u⁻¹-1| ≤ 2*|u-1| := by
    rw [show u⁻¹-1= -(u-1)/u by field_simp [hp.ne']; ring,abs_div,abs_neg,abs_of_pos hp,div_le_iff₀ hp]
    nlinarith only [mul_le_mul_of_nonneg_left hu (abs_nonneg (u-1))]
  rw [abs_le]
  constructor <;> linarith only [h,hi,hdiv,le_abs_self (u-1),le_abs_self (u⁻¹-1),abs_nonneg (u-1)]

/-- The prime and its mass coordinate agree exponentially in logarithmic position
and in relative weight, uniformly on the full late ray. -/
theorem exists_squareBin_displacement : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ v : ℝ in atTop,
    |squareBinLocation v-v| ≤ B*Real.exp (-v/20) ∧
    |squareBinWeight v-1| ≤ B*Real.exp (-v/20) := by
  obtain ⟨C,hC,hp⟩ := bin_power_error
  have hY : Tendsto (fun v : ℝ => Real.exp (v/2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [hY hp,hY (tendsto_primeBinReading_one_div.eventually_gt_const
    (by norm_num : (1/2:ℝ)<1))] with v hb hlo
  let y := Real.exp (v/2)
  let p := primeBinReading 1 y
  have hy : 0 < y := Real.exp_pos _
  have hr : 1/2 ≤ p/y := hlo.le
  have hr0 : 0 < p/y := by linarith only [hr]
  have hp0 : 0 < p := (div_pos_iff_of_pos_right hy).mp hr0
  have hrel : |p/y-1| ≤ C*Real.exp (-v/20) := by
    rw [show p/y-1=(p-y)/y by field_simp [hy.ne'],abs_div,abs_of_pos hy]
    apply (div_le_div_of_nonneg_right hb hy.le).trans_eq
    dsimp only [y]
    rw [show (Real.exp (v/2))^(9/10:ℝ) = Real.exp ((v/2)*(9/10)) from
      (Real.exp_mul _ _).symm, mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  have hloc : squareBinLocation v-v=2*Real.log (p/y) := by
    rw [Real.log_div hp0.ne' hy.ne']
    change 2*Real.log p-v = 2*(Real.log p-Real.log (Real.exp (v/2)))
    rw [Real.log_exp]; ring
  have hw : squareBinWeight v-1= -(p/y-1)/(p/y) := by
    change y/p-1=_
    field_simp [hy.ne',hp0.ne']; ring
  rw [hloc,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),hw,abs_div,abs_neg,abs_of_pos hr0]
  constructor
  · linarith only [abs_log_le_twice_sub hr,hrel]
  · rw [div_le_iff₀ hr0]
    nlinarith only [hrel,mul_le_mul_of_nonneg_left hr (mul_nonneg hC (Real.exp_pos (-v/20)).le)]

#print axioms exists_squareBin_displacement
end GaloisForLFunctions.ExclusionOfTheCriticalState
