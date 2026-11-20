import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheProperPowerMassOnADilatedGcdOctave
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Counting and absolute convergence after deleting proper powers

The difference of the two eighth-power readings has its own Weyl law.
Its fourth root has harmonic coefficient (1−1/√2)^(1/4); its Dirichlet
series reaches the line Re s = −3 and diverges absolutely on that line.
-/

noncomputable section
open Filter Set Asymptotics
open scoped Topology
open GaloisForLFunctions.HarmonicSuperlevel
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Part of the signed shortfall contributed by deleting proper prime powers. -/
def eighthProperPowerDifference (n : ℕ) := eighthReading true n-eighthReading false n

private abbrev A : ℝ := 1-1/Real.sqrt 2
private theorem positive_density : 0 < A :=
  sub_pos.mpr ((div_lt_one (Real.sqrt_pos.mpr (by norm_num))).mpr
    ((Real.lt_sqrt zero_le_one).mpr (by norm_num)))

open private reading_order from GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CountingLargeEighthPowerGcdDeficits

private theorem nn (n : ℕ) : 0 ≤ eighthProperPowerDifference n :=
  sub_nonneg.mpr (reading_order n)

private abbrev qroot (x : ℝ) := Real.sqrt (Real.sqrt x)

private theorem fourth_root_fourth {x : ℝ} (hx : 0 ≤ x) : qroot (x^4)=x := by
  rw [show x^4=(x^2)^2 by ring]
  simp [qroot,Real.sqrt_sq (sq_nonneg x),Real.sqrt_sq hx]

/-- Counting proper-power corrections above 1/t⁴ gives an asymptotic
linear count in t with a positive and explicit coefficient. -/
theorem eighth_deleted_power_counting_law :
    Tendsto (fun t : ℝ => (count eighthProperPowerDifference (t^4):ℝ)/t)
      atTop (𝓝 (qroot A)) := by
  let a := eighthProperPowerDifference
  have asymp : Tendsto (fun n : ℕ => (n:ℝ)*qroot (a n)) atTop (𝓝 (qroot A)) := by
    apply eighth_proper_power_fourth_coefficient.sqrt.sqrt.congr
    intro n
    change qroot ((n:ℝ)^4*a n) = _
    rw [show qroot ((n:ℝ)^4*a n) = qroot ((n:ℝ)^4)*qroot (a n) by
      dsimp only [qroot]
      rw [Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)^4),Real.sqrt_mul (Real.sqrt_nonneg _)],
      fourth_root_fourth (Nat.cast_nonneg n)]
  have h := (harmonic_counting_law (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr positive_density)) asymp).2
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  congr 2
  apply congrArg Set.ncard
  ext n
  change 1 < t*qroot (a n) ↔ 1 < t^4*a n
  have fourth : (t*qroot (a n))^4 = t^4*a n := by
    rw [mul_pow,show qroot (a n)^4=(qroot (a n)^2)^2 by ring,
      Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt (nn n)]
  rw [←fourth]
  simpa only [one_pow] using ((pow_lt_pow_iff_left₀ zero_le_one
    (mul_nonneg ht.le (Real.sqrt_nonneg _)) (by decide : (4:ℕ)≠0))).symm

private theorem coefficient_comparison (s : ℂ) :
    (fun n => ‖LSeries.term (fun n => (eighthProperPowerDifference n:ℂ)) s n‖)
      ~[atTop] (fun n : ℕ => A*(n:ℝ)^(-4-s.re)) := by
  apply (isEquivalent_iff_tendsto_one ?_).mpr
  · have h := eighth_proper_power_fourth_coefficient.div_const A
    rw [div_self positive_density.ne'] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have nr := (Nat.cast_pos (α:=ℝ)).mpr hn
    simp only [Pi.div_apply]
    rw [LSeries.norm_term_eq,if_neg (Nat.ne_of_gt hn),Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (nn n),Real.rpow_sub nr,Real.rpow_neg nr.le,
      show (4:ℝ)=((4:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    change (n:ℝ)^4*eighthProperPowerDifference n/A = _
    field_simp [positive_density.ne',Real.rpow_pos_of_pos nr s.re |>.ne']
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    exact mul_ne_zero positive_density.ne' (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne'

/-- The complex Dirichlet series of the deleted proper powers converges
absolutely precisely on Re s > −3, including failure at the boundary. -/
theorem eighth_deleted_power_absolute_convergence (s : ℂ) :
    LSeriesSummable (fun n => (eighthProperPowerDifference n:ℂ)) s ↔ -3 < s.re := by
  rw [LSeriesSummable,←summable_norm_iff,(coefficient_comparison s).summable_iff_nat,
    summable_mul_left_iff positive_density.ne',Real.summable_nat_rpow]
  constructor <;> intro h <;> linarith only [h]

/-- Exact absolute abscissa of the correction to the ordinary-prime reading. -/
theorem eighth_deleted_power_abscissa :
    LSeries.abscissaOfAbsConv (fun n => (eighthProperPowerDifference n:ℂ)) = ((-3:ℝ):EReal) := by
  apply le_antisymm (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    (eighth_deleted_power_absolute_convergence y).mpr hy)
  by_contra! h
  have hh := (eighth_deleted_power_absolute_convergence (-3)).mp
    (LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using h))
  norm_num at hh

#print axioms eighth_deleted_power_counting_law
#print axioms eighth_deleted_power_absolute_convergence
#print axioms eighth_deleted_power_abscissa
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
