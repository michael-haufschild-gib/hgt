import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import GaloisForLFunctions.RHTower.LiClockThetaGammaMixture
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import GaloisForLFunctions.RHTower.CanonicalXiSeamLogEquivalence
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set
open scoped BigOperators
local notation "Lap" => GaloisForLFunctions.HTGeometry.laplace
namespace RHTower
noncomputable section

def liClockThetaLogJumpCoefficient (p : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else
    (-1 : ℝ)^(j-1) * normalizedPrimeArchMoment (j-1) /
      ((2*j : ℝ) * p^(2*j))

def liClockThetaJumpPart (p : ℝ) (positive : Bool) (j : ℕ) : ℝ :=
  if positive then max (liClockThetaLogJumpCoefficient p j) 0
  else max (-liClockThetaLogJumpCoefficient p j) 0

def liClockThetaJumpMass (p : ℝ) (positive : Bool) : ℝ :=
  ∑' j : ℕ, liClockThetaJumpPart p positive j

def liClockThetaDegreeJumpMeasure (p : ℝ) (positive : Bool) : Measure ℝ :=
  Measure.sum (fun j : ℕ => ENNReal.ofReal (liClockThetaJumpPart p positive j) •
    Measure.dirac (j : ℝ))

def liClockThetaGammaJumpDensity (p : ℝ) (positive : Bool) (t : ℝ) : ℝ :=
  ∑' j : ℕ, liClockThetaJumpPart p positive j * liClockThetaGammaRowDensity p j t

def liClockThetaGammaJumpMeasure (p : ℝ) (positive : Bool) : Measure ℝ :=
  Measure.sum (fun j : ℕ => ENNReal.ofReal (liClockThetaJumpPart p positive j) •
    liClockThetaGammaRowLaw p j)

def liClockThetaSignedGammaDensity (p : ℝ) (t : ℝ) : ℝ :=
  ∑' j : ℕ, liClockThetaLogJumpCoefficient p j * liClockThetaGammaRowDensity p j t

def liClockThetaSignedGammaMeasure (p : ℝ) : SignedMeasure ℝ :=
  volume.withDensityᵥ (liClockThetaSignedGammaDensity p)

def liClockThetaSignedGammaTail (p : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  ∑' r : ℕ, liClockThetaLogJumpCoefficient p (J+r) *
    liClockThetaGammaRowDensity p (J+r) t

/-- The wide damping threshold `1/√150`: every admission below holds for `p > 1/√150`. -/
def liClockThetaWideThreshold : ℝ := Real.sqrt (1 / 150)

theorem liClockThetaWideThreshold_pos : 0 < liClockThetaWideThreshold :=
  Real.sqrt_pos.2 (by norm_num)

theorem liClockThetaWideThreshold_sq : liClockThetaWideThreshold ^ 2 = 1 / 150 :=
  Real.sq_sqrt (by norm_num)

theorem one_lt_mul_sq_of_wideThreshold_lt {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    1 < 150 * p ^ 2 := by
  have h := pow_lt_pow_left₀ hp liClockThetaWideThreshold_pos.le two_ne_zero
  rw [liClockThetaWideThreshold_sq] at h
  linarith

theorem wideThreshold_lt_iff {p : ℝ} (hp : 0 < p) :
    liClockThetaWideThreshold < p ↔ 1 < 150 * p ^ 2 := by
  refine ⟨one_lt_mul_sq_of_wideThreshold_lt, fun h => ?_⟩
  have h2 : liClockThetaWideThreshold ^ 2 < p ^ 2 := by rw [liClockThetaWideThreshold_sq]; linarith
  exact (pow_lt_pow_iff_left₀ liClockThetaWideThreshold_pos.le hp.le two_ne_zero).1 h2

theorem liClockThetaWideThreshold_lt_one : liClockThetaWideThreshold < 1 :=
  (wideThreshold_lt_iff one_pos).2 (by norm_num)

end
end RHTower

open Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section



private theorem sgj_first_two {p : ℝ} (hp : 0 < p) :
    liClockThetaLogJumpCoefficient p 1 = normalizedPrimeArchMoment 0 / (2*p^2) ∧
    liClockThetaLogJumpCoefficient p 2 = -normalizedPrimeArchMoment 1 / (4*p^4) ∧
    0 < liClockThetaLogJumpCoefficient p 1 ∧ liClockThetaLogJumpCoefficient p 2 < 0 := by
  have h1 : liClockThetaLogJumpCoefficient p 1 = normalizedPrimeArchMoment 0 / (2*p^2) := by
    norm_num [liClockThetaLogJumpCoefficient]
  have h2 : liClockThetaLogJumpCoefficient p 2 = -normalizedPrimeArchMoment 1 / (4*p^4) := by
    norm_num [liClockThetaLogJumpCoefficient]
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h1]
    exact div_pos normalizedPrimeArchMoment_zero_pos (by positivity)
  · rw [h2]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos normalizedPrimeArchMoment_one_pos)
      (by positivity)

private theorem sgj_abs_succ {p : ℝ} (hp : 0 < p) (n : ℕ) :
    |liClockThetaLogJumpCoefficient p (n+1)| =
      |normalizedPrimeArchMoment n| / ((2*(n+1) : ℝ)*p^(2*(n+1))) := by
  simp [liClockThetaLogJumpCoefficient, abs_div, abs_mul, abs_pow, abs_of_pos hp,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity)]

/-- `|ℓ_{n+1}(p)| ≤ A/(2(n+1)p²) (1/(150p²))^n`. -/
theorem abs_liClockThetaLogJumpCoefficient_succ_le {p : ℝ} (hp : 0 < p) (n : ℕ) :
    |liClockThetaLogJumpCoefficient p (n+1)| ≤
      xiShiftAbsoluteMass 0 / (2*((n+1 : ℕ) : ℝ)*p^2) * (1/(150*p^2))^n := by
  have hM : |normalizedPrimeArchMoment n| ≤ (1/150 : ℝ)^n * xiShiftAbsoluteMass 0 := by
    simpa only [Nat.zero_add] using abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 n
  rw [sgj_abs_succ hp]
  calc
    |normalizedPrimeArchMoment n| / ((2*(n+1) : ℝ)*p^(2*(n+1))) ≤
        ((1/150 : ℝ)^n * xiShiftAbsoluteMass 0) /
          ((2*(n+1) : ℝ)*p^(2*(n+1))) :=
      div_le_div_of_nonneg_right hM (by positivity)
    _ = xiShiftAbsoluteMass 0 / (2*((n+1 : ℕ) : ℝ)*p^2) *
        (1/(150*p^2))^n := by
      rw [show 2*(n+1) = 2*n+2 by omega, pow_add, pow_mul]
      push_cast
      simp only [div_pow, mul_pow, one_pow]
      field_simp

private theorem sgj_geometric_ratio {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    0 ≤ 1/(150*p^2) ∧ 1/(150*p^2) < 1 := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  constructor
  · positivity
  · apply (div_lt_one (by positivity : 0 < 150*p^2)).mpr
    exact one_lt_mul_sq_of_wideThreshold_lt hp

private theorem sgj_tail_majorant {p : ℝ} (hp : liClockThetaWideThreshold < p) {J : ℕ} (hJ : 1 ≤ J)
    (r : ℕ) :
    |liClockThetaLogJumpCoefficient p (J+r)| ≤
      (xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
        (1/(150*p^2))^(J-1)) * (1/(150*p^2))^r := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have he := abs_liClockThetaLogJumpCoefficient_succ_le hp0 (J+r-1)
  rw [show J+r-1+1 = J+r by omega] at he
  have hden : xiShiftAbsoluteMass 0 / (2*((J+r : ℕ) : ℝ)*p^2) ≤
      xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) := by
    apply div_le_div_of_nonneg_left (xiShiftAbsoluteMass_nonneg 0) (by positivity)
    push_cast
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sq_nonneg p)]
  calc
    |liClockThetaLogJumpCoefficient p (J+r)| ≤
        xiShiftAbsoluteMass 0 / (2*((J+r : ℕ) : ℝ)*p^2) *
          (1/(150*p^2))^(J+r-1) := he
    _ ≤ xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
          (1/(150*p^2))^(J+r-1) :=
      mul_le_mul_of_nonneg_right hden (by positivity)
    _ = (xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
          (1/(150*p^2))^(J-1)) * (1/(150*p^2))^r := by
      rw [show J+r-1 = J-1+r by omega, pow_add]
      ring

private theorem sgj_tail_summable {p : ℝ} (hp : liClockThetaWideThreshold < p) {J : ℕ} (hJ : 1 ≤ J) :
    Summable (fun r : ℕ => |liClockThetaLogJumpCoefficient p (J+r)|) := by
  have hq := sgj_geometric_ratio hp
  exact Summable.of_nonneg_of_le (fun r => abs_nonneg _)
    (sgj_tail_majorant hp hJ)
    ((summable_geometric_of_lt_one hq.1 hq.2).mul_left
      (xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) * (1/(150*p^2))^(J-1)))

private theorem sgj_abs_summable {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    Summable (fun j : ℕ => |liClockThetaLogJumpCoefficient p j|) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [Nat.add_comm] using sgj_tail_summable hp (J := 1) (by omega)

private theorem sgj_tail_bound {p : ℝ} (hp : liClockThetaWideThreshold < p) {J : ℕ} (hJ : 1 ≤ J) :
    (∑' r : ℕ, |liClockThetaLogJumpCoefficient p (J+r)|) ≤
      xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
        (1/(150*p^2))^(J-1) / (1-1/(150*p^2)) := by
  have hq := sgj_geometric_ratio hp
  have hsum := (summable_geometric_of_lt_one hq.1 hq.2).mul_left
    (xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) * (1/(150*p^2))^(J-1))
  calc
    (∑' r : ℕ, |liClockThetaLogJumpCoefficient p (J+r)|) ≤
        ∑' r : ℕ, (xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
          (1/(150*p^2))^(J-1)) * (1/(150*p^2))^r :=
      (sgj_tail_summable hp hJ).tsum_le_tsum (sgj_tail_majorant hp hJ) hsum
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq.1 hq.2]
      simp only [div_eq_mul_inv]





/-- The jump parts are nonnegative. -/
theorem liClockThetaJumpPart_nonneg (p : ℝ) (positive : Bool) (j : ℕ) :
    0 ≤ liClockThetaJumpPart p positive j := by
  cases positive <;> simp [liClockThetaJumpPart]

/-- Each jump part is at most the absolute jump coefficient. -/
theorem liClockThetaJumpPart_le_abs (p : ℝ) (positive : Bool) (j : ℕ) :
    liClockThetaJumpPart p positive j ≤ |liClockThetaLogJumpCoefficient p j| := by
  cases positive
  · exact max_le (neg_le_abs _) (abs_nonneg _)
  · exact max_le (le_abs_self _) (abs_nonneg _)

/-- The jump parts split the signed coefficient: `ℓ⁺ - ℓ⁻ = ℓ`. -/
theorem liClockThetaJumpPart_sub (p : ℝ) (j : ℕ) :
    liClockThetaJumpPart p true j - liClockThetaJumpPart p false j = liClockThetaLogJumpCoefficient p j := by
  by_cases h : 0 ≤ liClockThetaLogJumpCoefficient p j
  · simp [liClockThetaJumpPart, max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have hle : liClockThetaLogJumpCoefficient p j ≤ 0 := (lt_of_not_ge h).le
    simp [liClockThetaJumpPart, max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)]

private theorem sgj_part_summable {p : ℝ} (hp : liClockThetaWideThreshold < p) (positive : Bool) :
    Summable (liClockThetaJumpPart p positive) :=
  Summable.of_nonneg_of_le (liClockThetaJumpPart_nonneg p positive) (liClockThetaJumpPart_le_abs p positive)
    (sgj_abs_summable hp)

private theorem sgj_mass_pos {p : ℝ} (hp : liClockThetaWideThreshold < p) (positive : Bool) :
    0 < liClockThetaJumpMass p positive := by
  have hc := sgj_first_two (liClockThetaWideThreshold_pos.trans hp)
  cases positive
  · apply (sgj_part_summable hp false).tsum_pos (liClockThetaJumpPart_nonneg p false) 2
    exact lt_of_lt_of_le (neg_pos.mpr hc.2.2.2) (le_max_left _ _)
  · apply (sgj_part_summable hp true).tsum_pos (liClockThetaJumpPart_nonneg p true) 1
    exact lt_of_lt_of_le hc.2.2.1 (le_max_left _ _)

private theorem sgj_mass_sub {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    liClockThetaJumpMass p true - liClockThetaJumpMass p false = ∑' j : ℕ, liClockThetaLogJumpCoefficient p j := by
  rw [liClockThetaJumpMass, liClockThetaJumpMass, ← (sgj_part_summable hp true).tsum_sub (sgj_part_summable hp false)]
  exact tsum_congr (liClockThetaJumpPart_sub p)

end
end RHTower

namespace RHTower
noncomputable section

private theorem sgj_weighted_pow_summable {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    Summable (fun j : ℕ => |liClockThetaLogJumpCoefficient p j| * (j : ℝ)^n) := by
  let q : ℝ := 1/(150*p^2)
  let C : ℝ := xiShiftAbsoluteMass 0 / (2*p^2)
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hq : 0 < q := by dsimp [q]; positivity
  have hqn : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq]
    exact (sgj_geometric_ratio hp).2
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one n hqn
  have hs1 : Summable (fun j : ℕ => (((j+1 : ℕ) : ℝ)^n)*q^j) := by
    have hs := ((summable_nat_add_iff 1).mpr hs0).div_const q
    apply hs.congr
    intro j
    rw [pow_succ]
    field_simp [hq.ne']
  have he (j : ℕ) : |liClockThetaLogJumpCoefficient p (j+1)| ≤ C*q^j := by
    simpa only [Nat.cast_one, Nat.sub_self, pow_zero, mul_one, Nat.add_comm]
      using sgj_tail_majorant hp (J := 1) (by omega) j
  apply (summable_nat_add_iff 1).mp
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hs1.mul_left C)
  calc
    |liClockThetaLogJumpCoefficient p (j+1)| * (((j+1 : ℕ) : ℝ)^n) ≤
        (C*q^j) * (((j+1 : ℕ) : ℝ)^n) :=
      mul_le_mul_of_nonneg_right (he j) (by positivity)
    _ = C * ((((j+1 : ℕ) : ℝ)^n)*q^j) := by ring

private theorem sgj_weighted_succ_pow_summable {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    Summable (fun j : ℕ => |liClockThetaLogJumpCoefficient p j| * (((j+1 : ℕ) : ℝ)^n)) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((sgj_weighted_pow_summable hp n).mul_left ((2 : ℝ)^n))
  by_cases hj : j=0
  · simp [hj, liClockThetaLogJumpCoefficient]
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
  have hpow : (((j+1 : ℕ) : ℝ)^n) ≤ (2 : ℝ)^n*(j : ℝ)^n := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast
    linarith
  calc
    |liClockThetaLogJumpCoefficient p j| * (((j+1 : ℕ) : ℝ)^n) ≤
        |liClockThetaLogJumpCoefficient p j| * ((2 : ℝ)^n*(j : ℝ)^n) :=
      mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
    _ = (2 : ℝ)^n * (|liClockThetaLogJumpCoefficient p j| * (j : ℝ)^n) := by ring

private theorem sgj_weighted_choose_summable {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    Summable (fun j : ℕ => |liClockThetaLogJumpCoefficient p j| * (Nat.choose (2*j+n-1) n : ℝ)) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((sgj_weighted_succ_pow_summable hp n).mul_left (((n+2 : ℕ) : ℝ)^n))
  have hb : 2*j+n-1 ≤ (n+2)*(j+1) := by
    nlinarith [Nat.sub_le (2*j+n) 1, Nat.zero_le (n*j)]
  have hc : Nat.choose (2*j+n-1) n ≤ ((n+2)*(j+1))^n := by
    apply (Nat.choose_le_pow (2*j+n-1) n).trans
    gcongr
  rw [Nat.mul_pow] at hc
  have hcR : (Nat.choose (2*j+n-1) n : ℝ) ≤
      (((n+2 : ℕ) : ℝ)^n) * (((j+1 : ℕ) : ℝ)^n) := by exact_mod_cast hc
  calc
    |liClockThetaLogJumpCoefficient p j| * (Nat.choose (2*j+n-1) n : ℝ) ≤
        |liClockThetaLogJumpCoefficient p j| * ((((n+2 : ℕ) : ℝ)^n) * (((j+1 : ℕ) : ℝ)^n)) :=
      mul_le_mul_of_nonneg_left hcR (abs_nonneg _)
    _ = (((n+2 : ℕ) : ℝ)^n) * (|liClockThetaLogJumpCoefficient p j| * (((j+1 : ℕ) : ℝ)^n)) := by ring

end
end RHTower


/-! The literal canonical seam coefficients define an analytic logarithm on the strict disk150.
The exponential identity extends the pinned germ, without a global principal-log assertion. -/

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal NNReal
namespace RHTower
noncomputable section

private theorem sgLog_coeff_zero : canonicalXiSeamLogCoeff 0 = 0 := by
  simp [canonicalXiSeamLogCoeff, seamLogCoeff]

private theorem sgLog_coeff_succ (n : ℕ) :
    canonicalXiSeamLogCoeff (n+1) =
      (-1 : ℂ)^n * (normalizedPrimeArchMoment n : ℂ) /
        (2 * ((n+1 : ℕ) : ℂ)) := by
  have h := canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment n
  unfold canonicalXiSeamLogMoment at h
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hs : (-1 : ℂ)^n * (-1 : ℂ)^(n+1) = -1 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  apply (eq_div_iff (mul_ne_zero (by norm_num) hn)).2
  calc
    canonicalXiSeamLogCoeff (n+1) * (2 * ((n+1 : ℕ) : ℂ)) =
        (-1 : ℂ)^n *
          (-2 * ((n+1 : ℕ) : ℂ) * (-1 : ℂ)^(n+1) *
            canonicalXiSeamLogCoeff (n+1)) := by
      calc
        _ = -2 * ((n+1 : ℕ) : ℂ) *
            ((-1 : ℂ)^n * (-1 : ℂ)^(n+1)) *
              canonicalXiSeamLogCoeff (n+1) := by rw [hs]; ring
        _ = _ := by ring
    _ = (-1 : ℂ)^n * (normalizedPrimeArchMoment n : ℂ) := by rw [h]

private def sgLogSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ canonicalXiSeamLogCoeff

private def sgLogSum : ℂ → ℂ := sgLogSeries.sum

private theorem sgLog_coeff_bound (n : ℕ) :
    ‖canonicalXiSeamLogCoeff n‖ * (150 : ℝ)^n ≤ 75 * xiShiftAbsoluteMass 0 := by
  cases n with
  | zero =>
    simp only [sgLog_coeff_zero, norm_zero, zero_mul]
    exact mul_nonneg (by norm_num) (xiShiftAbsoluteMass_nonneg 0)
  | succ n =>
    have hM := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 n
    simp only [zero_add] at hM
    have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have hN : (1 : ℝ) ≤ ((n+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    have hn0 := ne_of_gt hn
    have hp0 : (150 : ℝ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
    have heq : ‖canonicalXiSeamLogCoeff (n+1)‖ =
        |normalizedPrimeArchMoment n| / (2 * ((n+1 : ℕ) : ℝ)) := by
      rw [sgLog_coeff_succ, norm_div, norm_mul, norm_pow, norm_mul, Complex.norm_natCast]
      norm_num [Complex.norm_real, Real.norm_eq_abs]
    rw [heq]
    calc
      |normalizedPrimeArchMoment n| / (2 * ((n+1 : ℕ) : ℝ)) * 150^(n+1) ≤
          ((1/150 : ℝ)^n * xiShiftAbsoluteMass 0) /
            (2 * ((n+1 : ℕ) : ℝ)) * 150^(n+1) := by gcongr
      _ = 75 * xiShiftAbsoluteMass 0 / ((n+1 : ℕ) : ℝ) := by
        rw [one_div_pow, pow_succ]
        field_simp [hn0, hp0]
        ring
      _ ≤ 75 * xiShiftAbsoluteMass 0 := by
        apply (div_le_iff₀ hn).2
        nlinarith [xiShiftAbsoluteMass_nonneg 0]

private theorem sgLog_radius : (150 : ℝ≥0∞) ≤ sgLogSeries.radius := by
  simpa using (sgLogSeries.le_radius_of_bound (75 * xiShiftAbsoluteMass 0)
    (r := (150 : ℝ≥0)) (fun n => by
      simpa [sgLogSeries, FormalMultilinearSeries.ofScalars_norm] using sgLog_coeff_bound n))

private theorem sgLog_sum_eq_tsum (z : ℂ) :
    sgLogSum z = ∑' n : ℕ, canonicalXiSeamLogCoeff n * z^n := by
  unfold sgLogSum sgLogSeries
  change FormalMultilinearSeries.ofScalarsSum canonicalXiSeamLogCoeff z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

private theorem sgLog_analytic : AnalyticOnNhd ℂ sgLogSum (Metric.ball 0 150) := by
  intro z hz
  apply (FormalMultilinearSeries.analyticOnNhd (p := sgLogSeries)) z
  have h150 : z ∈ Metric.eball (0 : ℂ) (150 : ℝ≥0) := by
    rw [Metric.eball_coe]
    exact hz
  change edist z 0 < (150 : ℝ≥0∞) at h150
  exact h150.trans_le sgLog_radius

private theorem sgLog_eventuallyEq : sgLogSum =ᶠ[𝓝 0] canonicalXiSeamLog := by
  obtain ⟨r, hr, ha⟩ := analyticAt_canonicalXiSeamLog.exists_ball_analyticOnNhd
  have hd : DifferentiableOn ℂ canonicalXiSeamLog (Metric.ball 0 r) :=
    fun z hz => (ha z hz).differentiableAt.differentiableWithinAt
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
  rw [sgLog_sum_eq_tsum]
  simpa only [canonicalXiSeamLogCoeff, seamLogCoeff, sub_zero] using
    Complex.taylorSeries_eq_on_ball' (hz := hz) hd

private theorem sgLog_exp_eventuallyEq :
    (fun z : ℂ => Complex.exp (sgLogSum z)) =ᶠ[𝓝 0]
      (fun z => canonicalXiSeamQuotient z / canonicalXiSeamQuotient 0) := by
  have hn := differentiable_canonicalXiSeamQuotient.continuous.continuousAt.eventually_ne
    canonicalXiSeamQuotient_zero_ne
  filter_upwards [sgLog_eventuallyEq, hn] with z hz hnz
  rw [hz, canonicalXiSeamLog]
  exact Complex.exp_log (div_ne_zero hnz canonicalXiSeamQuotient_zero_ne)

private theorem sgLog_exp_eq {z : ℂ} (hz : ‖z‖ < 150) :
    Complex.exp (sgLogSum z) =
      canonicalXiSeamQuotient z / canonicalXiSeamQuotient 0 := by
  have ha : AnalyticOnNhd ℂ (fun z => Complex.exp (sgLogSum z)) (Metric.ball 0 150) :=
    fun z hz => (sgLog_analytic z hz).cexp'
  have hb : AnalyticOnNhd ℂ
      (fun z => canonicalXiSeamQuotient z / canonicalXiSeamQuotient 0)
        (Metric.ball 0 150) :=
    fun z _ => (differentiable_canonicalXiSeamQuotient.analyticAt z).div_const
  apply ha.eqOn_of_preconnected_of_eventuallyEq hb
    (convex_ball (0 : ℂ) (150 : ℝ)).isPreconnected (by simp) sgLog_exp_eventuallyEq
  simpa only [Metric.mem_ball, dist_zero_right] using hz

end
end RHTower

namespace RHTower
noncomputable section

private theorem sge_quotient_sq (w : ℂ) :
    canonicalXiSeamQuotient (w^2) = XiC (-Complex.I*w) := by
  calc
    canonicalXiSeamQuotient (w^2) =
        xiSquaredSeamEntireQuotient ((-Complex.I*w)^2) := by
      unfold canonicalXiSeamQuotient
      congr 1
      rw [mul_pow]
      simp [Complex.I_sq]
    _ = XiC (-Complex.I*w) := xiSquaredSeamEntireQuotient_sq _

private theorem sge_coefficient (p : ℝ) (j : ℕ) :
    canonicalXiSeamLogCoeff j * (((p : ℂ)⁻¹)^2)^j =
      (liClockThetaLogJumpCoefficient p j : ℂ) := by
  cases j with
  | zero => simp [liClockThetaLogJumpCoefficient, sgLog_coeff_zero]
  | succ n =>
    rw [sgLog_coeff_succ]
    simp only [liClockThetaLogJumpCoefficient, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow, ← pow_mul]
    ring

private theorem sge_sum (p : ℝ) :
    sgLogSum (((p : ℂ)⁻¹)^2) = (∑' j : ℕ, liClockThetaLogJumpCoefficient p j : ℝ) := by
  rw [sgLog_sum_eq_tsum, Complex.ofReal_tsum]
  exact tsum_congr (sge_coefficient p)

private theorem sge_exp_source {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    Real.exp (∑' j : ℕ, liClockThetaLogJumpCoefficient p j) =
      (XiC (-Complex.I*(p : ℂ)⁻¹) / XiC 0).re := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have hp2 : 1 < 150 * p ^ 2 := one_lt_mul_sq_of_wideThreshold_lt hp
  have hz : ‖((p : ℂ)⁻¹)^2‖ < 150 := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0,
      inv_pow]
    rw [← one_div]
    apply (div_lt_iff₀ (sq_pos_of_pos hp0)).2
    nlinarith
  have hzero : canonicalXiSeamQuotient 0 = XiC 0 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using sge_quotient_sq 0
  have he := sgLog_exp_eq hz
  rw [sge_sum, sge_quotient_sq, hzero] at he
  simpa only [Complex.exp_ofReal_re] using congrArg Complex.re he

end
end RHTower

namespace RHTower
noncomputable section

private theorem sge_sum_eq_reciprocalLog {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    (∑' j : ℕ, liClockThetaLogJumpCoefficient p j) = liClockThetaReciprocalLog p := by
  have he : Real.exp (∑' j : ℕ, liClockThetaLogJumpCoefficient p j) =
      liClockThetaGammaNormalizer p := sge_exp_source hp
  rw [liClockThetaReciprocalLog, ← he, Real.log_exp]

private theorem sge_hasSum_reciprocalLog {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    HasSum (liClockThetaLogJumpCoefficient p) (liClockThetaReciprocalLog p) := by
  have hs : Summable (liClockThetaLogJumpCoefficient p) := by
    have h := (sgj_part_summable hp true).sub (sgj_part_summable hp false)
    exact h.congr (liClockThetaJumpPart_sub p)
  simpa only [sge_sum_eq_reciprocalLog hp] using hs.hasSum

end
end RHTower


open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace RHTower
noncomputable section

private def sgpTerm (n : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ)^n * normalizedPrimeArchMoment n * t^(2*n+2) /
    ((2*n+2).factorial : ℝ)

private theorem sgp_term_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (sgpTerm n) (liEvenCrossActualClockResponseTerm t n) t := by
  have hd := ((hasDerivAt_pow (2*n+2) t).const_mul
    ((-1 : ℝ)^n * normalizedPrimeArchMoment n)).div_const
      ((2*n+2).factorial : ℝ)
  unfold sgpTerm
  convert hd using 1 <;> try rfl
  unfold liEvenCrossActualClockResponseTerm
  simp only [show 2*n+2-1 = 2*n+1 by omega]
  rw [show (2*n+2).factorial = (2*n+2)*(2*n+1).factorial by
    simpa only [Nat.add_assoc] using Nat.factorial_succ (2*n+1)]
  push_cast
  field_simp

private theorem sgp_integral_term (n : ℕ) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, liEvenCrossActualClockResponseTerm s n) = sgpTerm n t := by
  have hc : Continuous (fun s : ℝ => liEvenCrossActualClockResponseTerm s n) := by
    unfold liEvenCrossActualClockResponseTerm
    fun_prop
  have hz : sgpTerm n 0 = 0 := by simp [sgpTerm]
  simpa only [hz, sub_zero] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => sgp_term_hasDerivAt n s) (hc.intervalIntegrable 0 t)

private theorem sgp_abs_le_of_mem_uIoc {s t : ℝ} (hs : s ∈ uIoc 0 t) :
    |s| ≤ |t| := by
  rcases le_total 0 t with ht | ht
  · rw [uIoc_of_le ht] at hs
    simpa only [abs_of_nonneg hs.1.le, abs_of_nonneg ht] using hs.2
  · rw [uIoc_of_ge ht] at hs
    rw [abs_of_nonpos hs.2, abs_of_nonpos ht]
    linarith [hs.1]

private theorem sgp_primitive_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => (-1 : ℝ)^n * normalizedPrimeArchMoment n *
      t^(2*n+2) / ((2*n+2).factorial : ℝ))
      (liEvenCrossActualClockPrimitive t) := by
  let E : ℕ → ℝ := fun n => xiShiftAbsoluteMass 0 * |t| *
    ((|t|^2/150)^n / ((2*n+1).factorial : ℝ))
  have hE : Summable E :=
    (summable_liEvenCrossActualCurrentClockFactorialEnvelope (|t|^2/150)
      (by positivity)).mul_left (xiShiftAbsoluteMass 0 * |t|)
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ uIoc 0 t) :
      ‖liEvenCrossActualClockResponseTerm s n‖ ≤ E n :=
    norm_liEvenCrossActualClockResponseTerm_le (sgp_abs_le_of_mem_uIoc hs) n
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := 0) (b := t) (μ := volume)
    (F := fun n s => liEvenCrossActualClockResponseTerm s n)
    (f := liEvenCrossActualClockResponse) (fun n _ => E n)
    (fun n => (by unfold liEvenCrossActualClockResponseTerm
                  fun_prop : Continuous (fun s => liEvenCrossActualClockResponseTerm s n)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall (fun s hs => hbound n s hs))
    (Filter.Eventually.of_forall (fun _ _ => hE))
    (by exact intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun s _ => by
      rw [liEvenCrossActualClockResponse_eq_tsum]
      exact (summable_liEvenCrossActualClockResponseTerm s).hasSum))
  simpa only [sgp_integral_term, sgpTerm, liEvenCrossActualClockPrimitive] using hsum

end
end RHTower



open MeasureTheory
namespace RHTower
noncomputable section

private theorem sgt_density_totalVariation {f : ℝ → ℝ}
    (hm : Measurable f) (hf : Integrable f volume) :
    SignedMeasure.totalVariation (volume.withDensityᵥ f) =
      volume.withDensity (fun t => ENNReal.ofReal |f t|) := by
  let J : JordanDecomposition ℝ := {
    posPart := volume.withDensity (fun t => ENNReal.ofReal (f t))
    negPart := volume.withDensity (fun t => ENNReal.ofReal (-f t))
    posPart_finite := isFiniteMeasure_withDensity_ofReal hf.2
    negPart_finite := isFiniteMeasure_withDensity_ofReal hf.neg.2
    mutuallySingular := withDensity_ofReal_mutuallySingular hm
  }
  have hJ : SignedMeasure.toJordanDecomposition (volume.withDensityᵥ f) = J := by
    apply SignedMeasure.toJordanDecomposition_eq
    exact withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf
  rw [SignedMeasure.totalVariation, hJ]
  change volume.withDensity (fun t => ENNReal.ofReal (f t)) +
    volume.withDensity (fun t => ENNReal.ofReal (-f t)) = _
  rw [← withDensity_add_left hm.ennreal_ofReal]
  congr 1
  funext t
  change ENNReal.ofReal (f t) + ENNReal.ofReal (-f t) = ENNReal.ofReal |f t|
  by_cases ht : 0 ≤ f t
  · rw [abs_of_nonneg ht, ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr ht), add_zero]
  · have hle : f t ≤ 0 := (lt_of_not_ge ht).le
    rw [abs_of_nonpos hle, ENNReal.ofReal_eq_zero.mpr hle, zero_add]

end
end RHTower

namespace RHTower
noncomputable section

theorem liClockThetaLogJumpCoefficient_first_two {p : ℝ} (hp : 0 < p) :
  liClockThetaLogJumpCoefficient p 1 = normalizedPrimeArchMoment 0 / (2*p^2) ∧
  liClockThetaLogJumpCoefficient p 2 = -normalizedPrimeArchMoment 1 / (4*p^4) ∧
  0 < liClockThetaLogJumpCoefficient p 1 ∧ liClockThetaLogJumpCoefficient p 2 < 0 :=
  sgj_first_two hp

theorem liClockThetaLogJumpCoefficient_admission_wide {p : ℝ} (hp : liClockThetaWideThreshold < p) :
  Summable (fun j : ℕ => |liClockThetaLogJumpCoefficient p j|) ∧
  HasSum (liClockThetaLogJumpCoefficient p) (liClockThetaReciprocalLog p) ∧
  (∀ J : ℕ, 1 ≤ J →
    (∑' r : ℕ, |liClockThetaLogJumpCoefficient p (J+r)|) ≤
      xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
        (1/(150*p^2))^(J-1) / (1-1/(150*p^2))) :=
  ⟨sgj_abs_summable hp, sge_hasSum_reciprocalLog hp, fun J hJ => sgj_tail_bound hp (J := J) hJ⟩

end
end RHTower

namespace RHTower
noncomputable section

private theorem sgb_weighted_row_succ {p t : ℝ} (hp : 0 < p) (ht : 0 < t) (n : ℕ) :
    liClockThetaLogJumpCoefficient p (n+1) * liClockThetaGammaRowDensity p (n+1) t =
      (Real.exp (-(p*t))/t) *
        ((-1 : ℝ)^n * normalizedPrimeArchMoment n * t^(2*n+2) /
          ((2*n+2).factorial : ℝ)) := by
  simp only [liClockThetaLogJumpCoefficient, liClockThetaGammaRowDensity,
    show n+1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel,
    indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
  have hfact : ((2*n+2).factorial : ℝ) =
      (2*(n+1) : ℝ) * ((2*n+1).factorial : ℝ) := by
    rw [show 2*n+2=(2*n+1)+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [show 2*(n+1)-1=2*n+1 by omega, hfact,
    show 2*n+2=(2*n+1)+1 by omega]
  simp only [pow_succ]
  push_cast
  field_simp [hp.ne', ht.ne']

private theorem sgb_signed_density_hasSum {p : ℝ} (hp : liClockThetaWideThreshold < p) (t : ℝ) :
    HasSum (fun j : ℕ => liClockThetaLogJumpCoefficient p j *
      liClockThetaGammaRowDensity p j t)
      ((Ioi (0 : ℝ)).indicator (fun t =>
        Real.exp (-(p*t)) * liEvenCrossActualClockPrimitive t / t) t) := by
  by_cases ht : 0 < t
  · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have h := (sgp_primitive_hasSum t).mul_left (Real.exp (-(p*t))/t)
    have hh : HasSum (fun n : ℕ => liClockThetaLogJumpCoefficient p (n+1) *
        liClockThetaGammaRowDensity p (n+1) t)
        (Real.exp (-(p*t)) * liEvenCrossActualClockPrimitive t / t) := by
      simpa only [sgb_weighted_row_succ (liClockThetaWideThreshold_pos.trans hp) ht,
        show Real.exp (-(p*t)) * liEvenCrossActualClockPrimitive t / t =
          Real.exp (-(p*t)) / t * liEvenCrossActualClockPrimitive t by ring] using h
    simpa [liClockThetaLogJumpCoefficient] using
      (hasSum_nat_add_iff (f := fun j : ℕ => liClockThetaLogJumpCoefficient p j *
        liClockThetaGammaRowDensity p j t) 1).mp hh
  · simp [liClockThetaGammaRowDensity, ht]

theorem liClockThetaSignedGammaDensity_eq_primitive_wide {p : ℝ} (hp : liClockThetaWideThreshold < p) (t : ℝ) :
  liClockThetaSignedGammaDensity p t =
    (Ioi (0 : ℝ)).indicator (fun t =>
      Real.exp (-(p*t)) * liEvenCrossActualClockPrimitive t / t) t :=
  (sgb_signed_density_hasSum hp t).tsum_eq

end
end RHTower


/-!
Private positive weighted Gamma/degree measure admission. Each complete
countable family retains its degree-zero row with proved zero weight.
Finite mass, strict support and genuine density integrability precede all
real mass identities. No normalized-probability or all-moment assertion.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace RHTower

private theorem sgWeighted_density_measurable (p : ℝ) (j : ℕ) :
    Measurable (liClockThetaGammaRowDensity p j) := by
  unfold liClockThetaGammaRowDensity
  split_ifs
  · fun_prop
  · exact Measurable.indicator (by fun_prop) measurableSet_Ioi

private theorem sgWeighted_density_nonneg {p : ℝ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    0 ≤ liClockThetaGammaRowDensity p j t := by
  by_cases hj : j = 0
  · simp [liClockThetaGammaRowDensity, hj]
  by_cases ht : 0 < t
  · simp only [liClockThetaGammaRowDensity, if_neg hj,
      indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    positivity
  · simp [liClockThetaGammaRowDensity, hj, ht]

private theorem sgWeighted_rowDensity_le {p : ℝ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    liClockThetaGammaRowDensity p j t ≤ p := by
  by_cases hj : j = 0
  · simp [liClockThetaGammaRowDensity, hj, hp.le]
  by_cases ht : 0 < t
  · have he : 2*j = (2*j-1)+1 := by omega
    have hf : ((2*j-1).factorial : ℝ) ≠ 0 := by positivity
    have hid : liClockThetaGammaRowDensity p j t =
        p * ((p*t)^(2*j-1)/((2*j-1).factorial : ℝ)) * Real.exp (-(p*t)) := by
      simp only [liClockThetaGammaRowDensity, if_neg hj,
        indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      have hpPow : p^(2*j) = p^(2*j-1)*p := by
        calc
          _ = p^((2*j-1)+1) := congrArg (fun n : ℕ => p^n) he
          _ = _ := pow_succ _ _
      rw [hpPow, mul_pow]
      field_simp
    rw [hid]
    calc
      _ ≤ p * Real.exp (p*t) * Real.exp (-(p*t)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (Real.pow_div_factorial_le_exp (p*t) (mul_nonneg hp.le ht.le) _) hp.le)
          (Real.exp_pos _).le
      _ = p := by rw [Real.exp_neg]; field_simp
  · simp [liClockThetaGammaRowDensity, hj, ht, hp.le]

private theorem sgWeighted_density_summable {p : ℝ} (hp : 0 < p)
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hs : Summable w) (t : ℝ) :
    Summable (fun j => w j * liClockThetaGammaRowDensity p j t) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (hw j) (sgWeighted_density_nonneg hp j t))
    (fun j => ?_) (hs.mul_left p)
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (sgWeighted_rowDensity_le hp j t) (hw j)

private theorem sgWeighted_probabilityRows_mass {w : ℕ → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hs : Summable w) {ν : ℕ → Measure ℝ}
    (hν : ∀ j, ν j Set.univ = 1) :
    (Measure.sum (fun j => ENNReal.ofReal (w j) • ν j)) Set.univ =
      ENNReal.ofReal (∑' j, w j) := by
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [Measure.smul_apply, hν, smul_eq_mul, mul_one]
  exact (ENNReal.ofReal_tsum_of_nonneg hw hs).symm

private theorem sgWeighted_density_measure_eq {p : ℝ} (hp : 0 < p)
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hs : Summable w) (h0 : w 0 = 0) :
    Measure.sum (fun j => ENNReal.ofReal (w j) • liClockThetaGammaRowLaw p j) =
      volume.withDensity
        (fun t => ENNReal.ofReal (∑' j, w j * liClockThetaGammaRowDensity p j t)) := by
  have he (j : ℕ) : ENNReal.ofReal (w j) • liClockThetaGammaRowLaw p j =
      volume.withDensity (fun t => ENNReal.ofReal
        (w j * liClockThetaGammaRowDensity p j t)) := by
    by_cases hj : j = 0
    · subst j
      simp [h0, liClockThetaGammaRowLaw, liClockThetaGammaRowDensity]
    · have hd := (liClockThetaGammaRowLaw_admission hp j).2.2.2 (by omega : 0 < j)
      rw [hd]
      symm
      calc
        _ = volume.withDensity (ENNReal.ofReal (w j) •
            (fun t : ℝ => ENNReal.ofReal (liClockThetaGammaRowDensity p j t))) := by
          congr 1
          ext t
          exact ENNReal.ofReal_mul (hw j)
        _ = _ := withDensity_smul (μ := volume) (ENNReal.ofReal (w j))
          (sgWeighted_density_measurable p j).ennreal_ofReal
  rw [Measure.sum_congr he, ← withDensity_tsum
    (fun j => ((sgWeighted_density_measurable p j).const_mul (w j)).ennreal_ofReal)]
  congr 1
  ext t
  rw [tsum_apply (Pi.summable.mpr (fun _ => ENNReal.summable)),
    ← ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (hw j) (sgWeighted_density_nonneg hp j t))
      (sgWeighted_density_summable hp hw hs t)]

private theorem sgWeighted_gamma_admission {p : ℝ} (hp : 0 < p)
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hs : Summable w) (h0 : w 0 = 0) :
    let μ := Measure.sum (fun j => ENNReal.ofReal (w j) • liClockThetaGammaRowLaw p j)
    let g := fun t : ℝ => ∑' j, w j * liClockThetaGammaRowDensity p j t
    IsFiniteMeasure μ ∧ μ Set.univ = ENNReal.ofReal (∑' j, w j) ∧
    (∀ᵐ t ∂μ, 0 < t) ∧ μ {0} = 0 ∧
    Measurable g ∧ (∀ t, 0 ≤ g t) ∧ Integrable g ∧
    (∫ t, g t) = ∑' j, w j ∧
    μ = volume.withDensity (fun t => ENNReal.ofReal (g t)) := by
  let μ := Measure.sum (fun j => ENNReal.ofReal (w j) • liClockThetaGammaRowLaw p j)
  let g := fun t : ℝ => ∑' j, w j * liClockThetaGammaRowDensity p j t
  have hm : μ Set.univ = ENNReal.ofReal (∑' j, w j) := by
    apply sgWeighted_probabilityRows_mass hw hs
    intro j
    exact (liClockThetaGammaRowLaw_admission hp j).1.measure_univ
  have hμ : IsFiniteMeasure μ := ⟨by rw [hm]; exact ENNReal.ofReal_lt_top⟩
  have hd : μ = volume.withDensity (fun t => ENNReal.ofReal (g t)) :=
    sgWeighted_density_measure_eq hp hw hs h0
  have hg : Measurable g := Measurable.tsum
    (fun j => (sgWeighted_density_measurable p j).const_mul (w j))
  have hn : ∀ t, 0 ≤ g t := fun t =>
    tsum_nonneg (fun j => mul_nonneg (hw j) (sgWeighted_density_nonneg hp j t))
  have hlin : (∫⁻ t, ENNReal.ofReal (g t)) = ENNReal.ofReal (∑' j, w j) := by
    rw [hd, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hm
    exact hm
  have hi : Integrable g := ⟨hg.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hn)).mpr
      (by rw [hlin]; exact ENNReal.ofReal_lt_top)⟩
  have hint : (∫ t, g t) = ∑' j, w j := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)] at hlin
    have h := congrArg ENNReal.toReal hlin
    simpa only [ENNReal.toReal_ofReal (integral_nonneg hn),
      ENNReal.toReal_ofReal (tsum_nonneg hw)] using h
  have hz (t : ℝ) (ht : ¬ 0 < t) : g t = 0 := by
    dsimp [g]
    have he (j : ℕ) : w j * liClockThetaGammaRowDensity p j t = 0 := by
      simp [liClockThetaGammaRowDensity, ht]
    simp_rw [he]
    simp
  have hsupport : ∀ᵐ t ∂μ, 0 < t := by
    rw [hd]
    apply (ae_withDensity_iff hg.ennreal_ofReal).mpr
    exact ae_of_all _ (fun t ht => by
      by_contra hn
      exact ht (by simp [hz t hn]))
  have hatom : μ {0} = 0 := by rw [hd]; simp
  exact ⟨hμ, hm, hsupport, hatom, hg, hn, hi, hint, hd⟩

private theorem sgWeighted_degree_admission
    {w : ℕ → ℝ} (hw : ∀ j, 0 ≤ w j) (hs : Summable w) (h0 : w 0 = 0) :
    let η := Measure.sum (fun j => ENNReal.ofReal (w j) • Measure.dirac (j : ℝ))
    IsFiniteMeasure η ∧ η Set.univ = ENNReal.ofReal (∑' j, w j) ∧
    (∀ᵐ t ∂η, 0 < t) ∧ η {0} = 0 := by
  let η := Measure.sum (fun j => ENNReal.ofReal (w j) • Measure.dirac (j : ℝ))
  have hm : η Set.univ = ENNReal.ofReal (∑' j, w j) := by
    apply sgWeighted_probabilityRows_mass hw hs
    intro j
    simp
  have hη : IsFiniteMeasure η := ⟨by rw [hm]; exact ENNReal.ofReal_lt_top⟩
  have hsupport : ∀ᵐ t ∂η, 0 < t := by
    apply Measure.ae_sum_iff.mpr
    intro j
    by_cases hj : j = 0
    · subst j
      simp [h0]
    · apply Measure.ae_smul_measure
      apply (ae_dirac_iff measurableSet_Ioi).mpr
      exact_mod_cast (by omega : 0 < j)
  have hatom : η {0} = 0 := by
    change (Measure.sum (fun j => ENNReal.ofReal (w j) • Measure.dirac (j : ℝ))) {0} = 0
    rw [Measure.sum_apply _ (measurableSet_singleton _)]
    have he (j : ℕ) : (ENNReal.ofReal (w j) • Measure.dirac (j : ℝ)) {0} = 0 := by
      by_cases hj : j = 0
      · simp [hj, h0]
      · simp [Measure.smul_apply, hj]
    simp_rw [he]
    simp
  exact ⟨hη, hm, hsupport, hatom⟩

end RHTower

end

namespace RHTower
noncomputable section

private theorem sgb_part_zero (p : ℝ) (positive : Bool) :
    liClockThetaJumpPart p positive 0 = 0 := by
  cases positive <;> simp [liClockThetaJumpPart, liClockThetaLogJumpCoefficient]

theorem liClockThetaJumpMeasure_admission_wide {p : ℝ} (hp : liClockThetaWideThreshold < p) :
  liClockThetaJumpMass p true - liClockThetaJumpMass p false =
    liClockThetaReciprocalLog p ∧
  (∀ positive : Bool,
    0 < liClockThetaJumpMass p positive ∧
    IsFiniteMeasure (liClockThetaDegreeJumpMeasure p positive) ∧
    IsFiniteMeasure (liClockThetaGammaJumpMeasure p positive) ∧
    liClockThetaDegreeJumpMeasure p positive Set.univ =
      ENNReal.ofReal (liClockThetaJumpMass p positive) ∧
    liClockThetaGammaJumpMeasure p positive Set.univ =
      ENNReal.ofReal (liClockThetaJumpMass p positive) ∧
    (∀ᵐ t ∂liClockThetaDegreeJumpMeasure p positive, 0 < t) ∧
    (∀ᵐ t ∂liClockThetaGammaJumpMeasure p positive, 0 < t)) := by
  have hm := sgj_mass_sub hp
  rw [sge_sum_eq_reciprocalLog hp] at hm
  refine ⟨hm, fun positive => ?_⟩
  have hg := sgWeighted_gamma_admission (liClockThetaWideThreshold_pos.trans hp)
    (liClockThetaJumpPart_nonneg p positive) (sgj_part_summable hp positive) (sgb_part_zero p positive)
  have hd := sgWeighted_degree_admission
    (liClockThetaJumpPart_nonneg p positive) (sgj_part_summable hp positive) (sgb_part_zero p positive)
  exact ⟨sgj_mass_pos hp positive, hd.1, hg.1, hd.2.1, hg.2.1,
    hd.2.2.1, hg.2.2.1⟩

end
end RHTower

namespace RHTower
noncomputable section

private theorem sgb_gamma_density_data {p : ℝ} (hp : liClockThetaWideThreshold < p) (positive : Bool) :
    Measurable (liClockThetaGammaJumpDensity p positive) ∧
    (∀ t, 0 ≤ liClockThetaGammaJumpDensity p positive t) ∧
    Integrable (liClockThetaGammaJumpDensity p positive) ∧
    (∫ t, liClockThetaGammaJumpDensity p positive t) = liClockThetaJumpMass p positive ∧
    liClockThetaGammaJumpMeasure p positive = volume.withDensity
      (fun t => ENNReal.ofReal (liClockThetaGammaJumpDensity p positive t)) :=
  (sgWeighted_gamma_admission (liClockThetaWideThreshold_pos.trans hp)
    (liClockThetaJumpPart_nonneg p positive) (sgj_part_summable hp positive)
    (sgb_part_zero p positive)).2.2.2.2

private theorem sgb_signed_density_eq_sub {p : ℝ} (hp : liClockThetaWideThreshold < p) (t : ℝ) :
    liClockThetaSignedGammaDensity p t =
      liClockThetaGammaJumpDensity p true t - liClockThetaGammaJumpDensity p false t := by
  symm
  change (∑' j, liClockThetaJumpPart p true j * liClockThetaGammaRowDensity p j t) -
    (∑' j, liClockThetaJumpPart p false j * liClockThetaGammaRowDensity p j t) =
    ∑' j, liClockThetaLogJumpCoefficient p j * liClockThetaGammaRowDensity p j t
  rw [← Summable.tsum_sub
    (sgWeighted_density_summable (liClockThetaWideThreshold_pos.trans hp)
      (liClockThetaJumpPart_nonneg p true) (sgj_part_summable hp true) t)
    (sgWeighted_density_summable (liClockThetaWideThreshold_pos.trans hp)
      (liClockThetaJumpPart_nonneg p false) (sgj_part_summable hp false) t)]
  apply tsum_congr
  intro j
  rw [← sub_mul, liClockThetaJumpPart_sub]

end
end RHTower


open MeasureTheory Set
open scoped ENNReal
namespace RHTower
noncomputable section

private theorem sgd_positive_density_set {f : ℝ → ℝ}
    (hi : Integrable f) (hn : ∀ t, 0 ≤ f t) {s : Set ℝ} (hs : MeasurableSet s) :
    (volume.withDensity (fun t => ENNReal.ofReal (f t)) s).toReal = ∫ t in s, f t := by
  rw [withDensity_apply _ hs]
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ hn) hi.integrableOn.aestronglyMeasurable).symm

private theorem sgd_positive_density_test {f : ℝ → ℝ}
    (hm : Measurable f) (hi : Integrable f) (hn : ∀ t, 0 ≤ f t)
    {h : ℝ → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ t, |h t| ≤ C) :
    Integrable (fun t => h t * f t) ∧
    Integrable h (volume.withDensity (fun t => ENNReal.ofReal (f t))) ∧
    (∫ t, h t ∂volume.withDensity (fun t => ENNReal.ofReal (f t))) =
      ∫ t, h t * f t := by
  have hprod := hi.bdd_mul hh.aestronglyMeasurable (ae_of_all _ hC)
  have htop : ∀ᵐ t ∂(volume : Measure ℝ), ENNReal.ofReal (f t) < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hfinite : Integrable h (volume.withDensity (fun t => ENNReal.ofReal (f t))) := by
    rw [integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal htop]
    simpa only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_comm] using hprod
  refine ⟨hprod, hfinite, ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal htop]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_comm]

private theorem sgd_signed_density_set {f g : ℝ → ℝ}
    (hfi : Integrable f) (hgi : Integrable g)
    (hfn : ∀ t, 0 ≤ f t) (hgn : ∀ t, 0 ≤ g t)
    {s : Set ℝ} (hs : MeasurableSet s) :
    (volume.withDensityᵥ (fun t => f t - g t)) s =
      (volume.withDensity (fun t => ENNReal.ofReal (f t)) s).toReal -
      (volume.withDensity (fun t => ENNReal.ofReal (g t)) s).toReal := by
  change (volume.withDensityᵥ (f - g)) s = _
  rw [withDensityᵥ_apply (hfi.sub hgi) hs]
  change (∫ t in s, f t - g t) = _
  rw [integral_sub hfi.integrableOn hgi.integrableOn,
    sgd_positive_density_set hfi hfn hs, sgd_positive_density_set hgi hgn hs]

private theorem sgd_signed_density_test {f g : ℝ → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g)
    (hfn : ∀ t, 0 ≤ f t) (hgn : ∀ t, 0 ≤ g t)
    {h : ℝ → ℝ} (hh : Measurable h) {C : ℝ} (hC : ∀ t, |h t| ≤ C) :
    Integrable (fun t => h t * (f t - g t)) ∧
    Integrable h (volume.withDensity (fun t => ENNReal.ofReal (f t))) ∧
    Integrable h (volume.withDensity (fun t => ENNReal.ofReal (g t))) ∧
    (∫ t, h t * (f t - g t)) =
      (∫ t, h t ∂volume.withDensity (fun t => ENNReal.ofReal (f t))) -
      (∫ t, h t ∂volume.withDensity (fun t => ENNReal.ofReal (g t))) := by
  have hf := sgd_positive_density_test hfm hfi hfn hh hC
  have hg := sgd_positive_density_test hgm hgi hgn hh hC
  have hi : Integrable (fun t => h t * (f t - g t)) := by
    simp only [mul_sub]
    exact hf.1.sub hg.1
  refine ⟨hi, hf.2.1, hg.2.1, ?_⟩
  simp only [mul_sub]
  rw [integral_sub hf.1 hg.1, hf.2.2, hg.2.2]

end
end RHTower

namespace RHTower
noncomputable section

theorem liClockThetaSignedGammaMeasure_admission_wide {p : ℝ} (hp : liClockThetaWideThreshold < p) :
  (∀ s : Set ℝ, MeasurableSet s →
    liClockThetaSignedGammaMeasure p s =
      (liClockThetaGammaJumpMeasure p true s).toReal -
        (liClockThetaGammaJumpMeasure p false s).toReal) ∧
  (∀ h : ℝ → ℝ, Measurable h → (∃ C : ℝ, ∀ t, |h t| ≤ C) →
    Integrable (fun t => h t * liClockThetaSignedGammaDensity p t) volume ∧
    Integrable h (liClockThetaGammaJumpMeasure p true) ∧
    Integrable h (liClockThetaGammaJumpMeasure p false) ∧
    (∫ t, h t * liClockThetaSignedGammaDensity p t) =
      (∫ t, h t ∂liClockThetaGammaJumpMeasure p true) -
        (∫ t, h t ∂liClockThetaGammaJumpMeasure p false)) := by
  have hf := sgb_gamma_density_data hp true
  have hg := sgb_gamma_density_data hp false
  have he : liClockThetaSignedGammaDensity p = fun t =>
      liClockThetaGammaJumpDensity p true t - liClockThetaGammaJumpDensity p false t :=
    funext (sgb_signed_density_eq_sub hp)
  constructor
  · intro s hs
    change (volume.withDensityᵥ (liClockThetaSignedGammaDensity p)) s = _
    rw [he, hf.2.2.2.2, hg.2.2.2.2]
    exact sgd_signed_density_set hf.2.2.1 hg.2.2.1 hf.2.1 hg.2.1 hs
  · intro h hh hC
    obtain ⟨C, hC⟩ := hC
    rw [he, hf.2.2.2.2, hg.2.2.2.2]
    exact sgd_signed_density_test hf.1 hg.1 hf.2.2.1 hg.2.2.1 hf.2.1 hg.2.1 hh hC

end
end RHTower


/-!
Private full signed polynomial Gamma-density L1 support. Positive-degree
row moments retain exact shape 2*j and rate p. Zero row remains literal,
and zero-degree weight is retained as hypothesis. Real norm-integral
summability is proved before the complete signed-density L1 assertion.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace RHTower

private theorem sgPolynomialRow_power_integrable {r : ℝ} (hr : 0 < r) (m : ℕ) :
    IntegrableOn (fun t : ℝ => t^m * Real.exp (-(r*t))) (Ioi 0) := by
  have hm : (-1:ℝ)<(m:ℝ) := by
    have hm0 : 0≤(m:ℝ) := by positivity
    linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p:=1) (s:=(m:ℝ))
    (b:=r) hm (by norm_num) hr
  simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h

private theorem sgPolynomialRow_power_integral {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (∫ t in Ioi 0, t^m * Real.exp (-(r*t))) = (m.factorial:ℝ)/r^(m+1) := by
  have hm : (-1:ℝ)<(m:ℝ) := by
    have hm0 : 0≤(m:ℝ) := by positivity
    linarith
  have hc : (m:ℝ)+1=((m+1:ℕ):ℝ) := by norm_num
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p:=1) (q:=(m:ℝ)) (b:=r) (by norm_num) hm hr
  calc
    _ = r^(-((m:ℝ)+1))*Real.Gamma ((m:ℝ)+1) := by
      simpa only [Real.rpow_one,Real.rpow_natCast,div_one,mul_one,neg_mul] using h
    _ = (r^(m+1))⁻¹*(m.factorial:ℝ) := by
      rw [Real.rpow_neg hr.le,Real.Gamma_nat_eq_factorial,hc,Real.rpow_natCast]
    _ = _ := by rw [div_eq_mul_inv]; ring

private theorem sgPolynomialRow_density_measurable (p : ℝ) (j : ℕ) :
    Measurable (liClockThetaGammaRowDensity p j) := by
  unfold liClockThetaGammaRowDensity
  split_ifs
  · fun_prop
  · exact Measurable.indicator (by fun_prop) measurableSet_Ioi

private theorem sgPolynomialRow_density_nonneg {p : ℝ} (hp : 0 < p) (j : ℕ) (t : ℝ) :
    0 ≤ liClockThetaGammaRowDensity p j t := by
  by_cases hj : j=0
  · simp [liClockThetaGammaRowDensity,hj]
  by_cases ht : 0<t
  · simp only [liClockThetaGammaRowDensity, if_neg hj, indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
    positivity
  · simp [liClockThetaGammaRowDensity,hj,ht]

private theorem sgPolynomialRow_polynomial_tilt_eq {p u : ℝ} {j : ℕ} (hj : 0<j) (n : ℕ) :
    (fun t : ℝ => t^n * Real.exp (u*t) * liClockThetaGammaRowDensity p j t) =
    (fun t : ℝ => (p^(2*j)/((2*j-1).factorial:ℝ)) *
      (Ioi (0:ℝ)).indicator (fun t => t^(2*j+n-1)*Real.exp (-((p-u)*t))) t) := by
  funext t
  by_cases ht : 0<t
  · simp only [liClockThetaGammaRowDensity,if_neg (by omega : j≠0),
      indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
    rw [show -((p-u)*t)=-(p*t)+u*t by ring,Real.exp_add]
    have hn : 2*j+n-1 = n+(2*j-1) := by omega
    rw [hn,pow_add]
    ring
  · simp [liClockThetaGammaRowDensity,show j≠0 by omega,ht]

private theorem sgPolynomialRow_polynomial_exponential_moment {p u : ℝ}
    (_hp : 0<p) (hu : u<p) (j n : ℕ) :
    Integrable (fun t : ℝ => t^n * Real.exp (u*t) * liClockThetaGammaRowDensity p j t) ∧
    (∫ t : ℝ, t^n * Real.exp (u*t) * liClockThetaGammaRowDensity p j t) =
      if j=0 then 0 else
        p^(2*j) * ((2*j+n-1).factorial:ℝ) /
          (((2*j-1).factorial:ℝ) * (p-u)^(2*j+n)) := by
  by_cases hj : j=0
  · simp [liClockThetaGammaRowDensity,hj]
  · rw [sgPolynomialRow_polynomial_tilt_eq (by omega : 0<j) n]
    have hr : 0<p-u := sub_pos.mpr hu
    have hi := (integrable_indicator_iff measurableSet_Ioi).mpr
      (sgPolynomialRow_power_integrable hr (2*j+n-1))
    refine ⟨hi.const_mul _,?_⟩
    rw [integral_const_mul,integral_indicator measurableSet_Ioi,
      sgPolynomialRow_power_integral hr,if_neg hj]
    rw [show 2*j+n-1+1=2*j+n by omega]
    ring

private theorem sgPolynomialRow_polynomial_moment_factorial {p : ℝ} (hp : 0<p) (j n : ℕ) :
    Integrable (fun t : ℝ => t^n * liClockThetaGammaRowDensity p j t) ∧
    (∫ t : ℝ, t^n * liClockThetaGammaRowDensity p j t)/(n.factorial:ℝ) =
      if j=0 then 0 else (1/p)^n * ((2*j+n-1).choose n:ℝ) := by
  have h : Integrable (fun t : ℝ => t^n * liClockThetaGammaRowDensity p j t) ∧
      (∫ t : ℝ, t^n * liClockThetaGammaRowDensity p j t) =
        if j=0 then 0 else p^(2*j)*((2*j+n-1).factorial:ℝ) /
          (((2*j-1).factorial:ℝ)*p^(2*j+n)) := by
    simpa only [zero_mul,Real.exp_zero,mul_one,sub_zero] using
      sgPolynomialRow_polynomial_exponential_moment hp (by linarith : (0:ℝ)<p) j n
  refine ⟨h.1,?_⟩
  by_cases hj : j=0
  · rw [h.2,if_pos hj,zero_div,if_pos hj]
  · have hn : (2*j-1)+n=2*j+n-1 := by omega
    have hf := Nat.add_choose_mul_factorial_mul_factorial (2*j-1) n
    rw [hn] at hf
    have hfactor : ((2*j+n-1).factorial:ℝ) =
        ((2*j+n-1).choose n:ℝ) * ((2*j-1).factorial:ℝ) * (n.factorial:ℝ) := by
      exact_mod_cast hf.symm
    have hm : ((2*j-1).factorial:ℝ)≠0 := by positivity
    have hnf : (n.factorial:ℝ)≠0 := by positivity
    rw [h.2,if_neg hj,if_neg hj,hfactor,pow_add,div_pow]
    field_simp [hp.ne',hm,hnf]
    simp


private theorem sgPolynomial_series_integrable (F : ℕ → ℝ → ℝ)
    (hF : ∀ j, Measurable (F j)) (hi : ∀ j, Integrable (F j))
    (hs : Summable (fun j => ∫ t, ‖F j t‖)) :
    Integrable (fun t => ∑' j, F j t) := by
  have hrow (j : ℕ) : (∫⁻ t, ‖F j t‖ₑ) = ‖∫ t, ‖F j t‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hi j).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg (fun t => abs_nonneg (F j t)))]
    simp only [coe_nnnorm]
    rfl
  have hsum : (∑' j, ∫⁻ t, ‖F j t‖ₑ) ≠ ∞ := by
    rw [funext hrow]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  refine ⟨(Measurable.tsum hF).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun j => (hF j).enorm.aemeasurable)]
  exact hsum.lt_top


private theorem sgPolynomial_polynomial_row_nonneg {p : ℝ} (hp : 0 < p)
    (j n : ℕ) (t : ℝ) :
    0 ≤ t^n * liClockThetaGammaRowDensity p j t := by
  by_cases ht : 0 < t
  · exact mul_nonneg (by positivity) (sgPolynomialRow_density_nonneg hp j t)
  · have hz : liClockThetaGammaRowDensity p j t = 0 := by
      simp [liClockThetaGammaRowDensity, ht]
    simp [hz]

private theorem sgPolynomial_row_norm_integral {p : ℝ} (hp : 0 < p)
    {w : ℕ → ℝ} (h0 : w 0 = 0) (j n : ℕ) :
    Integrable (fun t : ℝ => t^n * w j * liClockThetaGammaRowDensity p j t) ∧
    (∫ t : ℝ, |t^n * w j * liClockThetaGammaRowDensity p j t|) =
      |w j| * (n.factorial : ℝ) / p^n * ((2*j+n-1).choose n : ℝ) := by
  have hr := sgPolynomialRow_polynomial_moment_factorial hp j n
  have hi : Integrable (fun t : ℝ => t^n * w j * liClockThetaGammaRowDensity p j t) :=
    (hr.1.mul_const (w j)).congr (ae_of_all _ (fun t => by ring))
  refine ⟨hi, ?_⟩
  by_cases hj : j = 0
  · simp [hj, h0, liClockThetaGammaRowDensity]
  · have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hm : (∫ t : ℝ, t^n * liClockThetaGammaRowDensity p j t) =
        (1/p)^n * ((2*j+n-1).choose n : ℝ) * (n.factorial : ℝ) :=
      (div_eq_iff hn).mp (by simpa only [if_neg hj] using hr.2)
    have he : (fun t : ℝ => |t^n * w j * liClockThetaGammaRowDensity p j t|) =
        fun t => |w j| * (t^n * liClockThetaGammaRowDensity p j t) := by
      funext t
      calc
        _ = |w j * (t^n * liClockThetaGammaRowDensity p j t)| := by congr 1; ring
        _ = |w j| * |t^n * liClockThetaGammaRowDensity p j t| := abs_mul _ _
        _ = _ := by rw [abs_of_nonneg (sgPolynomial_polynomial_row_nonneg hp j n t)]
    rw [he, integral_const_mul, hm]
    simp only [div_pow, one_pow]
    ring

private theorem sgPolynomial_series_admission {p : ℝ} (hp : 0 < p)
    {w : ℕ → ℝ} (h0 : w 0 = 0) (n : ℕ)
    (hs : Summable (fun j => |w j| * ((2*j+n-1).choose n : ℝ))) :
    Summable (fun j => ∫ t : ℝ,
      |t^n * w j * liClockThetaGammaRowDensity p j t|) ∧
    Integrable (fun t : ℝ => t^n *
      ∑' j, w j * liClockThetaGammaRowDensity p j t) := by
  have hsum : Summable (fun j => ∫ t : ℝ,
      |t^n * w j * liClockThetaGammaRowDensity p j t|) :=
    (hs.mul_left ((n.factorial : ℝ)/p^n)).congr (fun j => by
      rw [(sgPolynomial_row_norm_integral hp h0 j n).2]
      ring)
  refine ⟨hsum, ?_⟩
  have hi := sgPolynomial_series_integrable
    (fun (j : ℕ) (t : ℝ) => t^n * w j * liClockThetaGammaRowDensity p j t)
    (fun j => ((measurable_id.pow_const n).mul_const (w j)).mul
      (sgPolynomialRow_density_measurable p j))
    (fun j => (sgPolynomial_row_norm_integral hp h0 j n).1)
    (by simpa only [Real.norm_eq_abs] using hsum)
  simpa only [mul_assoc, tsum_mul_left] using hi

end RHTower

end

namespace RHTower
noncomputable section

theorem liClockThetaGammaJumpDensity_admission_wide {p : ℝ} (hp : liClockThetaWideThreshold < p) :
  (∀ positive : Bool,
    Integrable (liClockThetaGammaJumpDensity p positive) volume ∧
    (∀ t : ℝ, 0 ≤ liClockThetaGammaJumpDensity p positive t) ∧
    (∫ t, liClockThetaGammaJumpDensity p positive t) =
      liClockThetaJumpMass p positive ∧
    liClockThetaGammaJumpMeasure p positive =
      volume.withDensity (fun t => ENNReal.ofReal (liClockThetaGammaJumpDensity p positive t))) ∧
  (∑' j : ℕ, ∫ t, |liClockThetaLogJumpCoefficient p j *
    liClockThetaGammaRowDensity p j t|) =
      ∑' j : ℕ, |liClockThetaLogJumpCoefficient p j| ∧
  (∀ n : ℕ,
    Summable (fun j : ℕ => ∫ t, |t^n * liClockThetaLogJumpCoefficient p j *
      liClockThetaGammaRowDensity p j t|) ∧
    Integrable (fun t => t^n * liClockThetaSignedGammaDensity p t) volume) := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h0 : liClockThetaLogJumpCoefficient p 0 = 0 := by
    simp [liClockThetaLogJumpCoefficient]
  constructor
  · intro positive
    have h := sgb_gamma_density_data hp positive
    exact ⟨h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
  constructor
  · apply tsum_congr
    intro j
    simpa using (sgPolynomial_row_norm_integral hp0 h0 j 0).2
  · intro n
    exact sgPolynomial_series_admission hp0 h0 n (sgj_weighted_choose_summable hp n)

end
end RHTower

namespace RHTower
noncomputable section

private theorem sgb_signed_density_data {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    Measurable (liClockThetaSignedGammaDensity p) ∧
    Integrable (liClockThetaSignedGammaDensity p) ∧
    (∫ t, liClockThetaSignedGammaDensity p t) = liClockThetaReciprocalLog p := by
  have hf := sgb_gamma_density_data hp true
  have hg := sgb_gamma_density_data hp false
  have he : liClockThetaSignedGammaDensity p = fun t =>
      liClockThetaGammaJumpDensity p true t - liClockThetaGammaJumpDensity p false t :=
    funext (sgb_signed_density_eq_sub hp)
  have hm : Measurable (liClockThetaSignedGammaDensity p) := by
    rw [he]
    exact hf.1.sub hg.1
  have hi : Integrable (liClockThetaSignedGammaDensity p) := by
    rw [he]
    exact hf.2.2.1.sub hg.2.2.1
  refine ⟨hm, hi, ?_⟩
  rw [he, integral_sub hf.2.2.1 hg.2.2.1, hf.2.2.2.1, hg.2.2.2.1]
  exact (liClockThetaJumpMeasure_admission_wide hp).1

theorem liClockThetaSignedGammaMeasure_totalVariation_wide {p : ℝ} (hp : liClockThetaWideThreshold < p) :
  (liClockThetaSignedGammaMeasure p).totalVariation =
    volume.withDensity (fun t => ENNReal.ofReal |liClockThetaSignedGammaDensity p t|) ∧
  (∫ t, |liClockThetaSignedGammaDensity p t|) ≤
    liClockThetaJumpMass p true + liClockThetaJumpMass p false := by
  have hd := sgb_signed_density_data hp
  have hf := sgb_gamma_density_data hp true
  have hg := sgb_gamma_density_data hp false
  refine ⟨sgt_density_totalVariation hd.1 hd.2.1, ?_⟩
  have hsum : Integrable (fun t =>
      liClockThetaGammaJumpDensity p true t + liClockThetaGammaJumpDensity p false t) :=
    hf.2.2.1.add hg.2.2.1
  have hbound (t : ℝ) : |liClockThetaSignedGammaDensity p t| ≤
      liClockThetaGammaJumpDensity p true t + liClockThetaGammaJumpDensity p false t := by
    rw [sgb_signed_density_eq_sub hp]
    apply abs_le.mpr
    constructor
    · linarith [hf.2.1 t]
    · linarith [hg.2.1 t]
  have h := integral_mono hd.2.1.abs hsum hbound
  rw [integral_add hf.2.2.1 hg.2.2.1, hf.2.2.2.1, hg.2.2.2.1] at h
  exact h

private theorem sgb_signed_density_laplace_shift {p s : ℝ} (hp : liClockThetaWideThreshold < p) (hs : 0 ≤ s) :
    (fun t => Real.exp (-(s*t)) * liClockThetaSignedGammaDensity p t) =
      liClockThetaSignedGammaDensity (p+s) := by
  have hps : liClockThetaWideThreshold < p+s := by linarith
  funext t
  rw [liClockThetaSignedGammaDensity_eq_primitive_wide hp,
    liClockThetaSignedGammaDensity_eq_primitive_wide hps]
  by_cases ht : 0 < t
  · simp only [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    have he : Real.exp (-(s*t)) * Real.exp (-(p*t)) = Real.exp (-((p+s)*t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← he]
    ring
  · simp [ht]

theorem liClockThetaSignedGammaDensity_laplace_wide {p : ℝ} (hp : liClockThetaWideThreshold < p)
    {s : ℝ} (hs : 0 ≤ s) :
  Integrable (fun t => Real.exp (-(s*t))*liClockThetaSignedGammaDensity p t) volume ∧
  (∫ t, Real.exp (-(s*t))*liClockThetaSignedGammaDensity p t) =
    liClockThetaReciprocalLog (p+s) ∧
  Real.log (Lap (liClockThetaGammaMixture p) s).toReal =
    liClockThetaReciprocalLog (p+s) - liClockThetaReciprocalLog p ∧
  Real.log (Lap (liClockThetaGammaMixture p) s).toReal =
    ∫ t, (Real.exp (-(s*t))-1)*liClockThetaSignedGammaDensity p t := by
  have hps : liClockThetaWideThreshold < p+s := by linarith
  have hd := sgb_signed_density_data hp
  have hds := sgb_signed_density_data hps
  have he := sgb_signed_density_laplace_shift hp hs
  have hi : Integrable (fun t => Real.exp (-(s*t))*liClockThetaSignedGammaDensity p t) := by
    rw [he]
    exact hds.2.1
  have hint : (∫ t, Real.exp (-(s*t))*liClockThetaSignedGammaDensity p t) =
      liClockThetaReciprocalLog (p+s) := by
    rw [he]
    exact hds.2.2
  have hpz : 0 < liClockThetaGammaNormalizer p :=
    lt_trans zero_lt_one (liClockThetaGammaNormalizer_source (liClockThetaWideThreshold_pos.trans hp)).2.2
  have hpsz : 0 < liClockThetaGammaNormalizer (p+s) :=
    lt_trans zero_lt_one (liClockThetaGammaNormalizer_source (by linarith [liClockThetaWideThreshold_pos] : 0 < p+s)).2.2
  have hlog : Real.log (Lap (liClockThetaGammaMixture p) s).toReal =
      liClockThetaReciprocalLog (p+s) - liClockThetaReciprocalLog p := by
    rw [liClockThetaGammaMixture_laplace (liClockThetaWideThreshold_pos.trans hp) hs,
      ENNReal.toReal_ofReal (div_nonneg hpsz.le hpz.le), Real.log_div hpsz.ne' hpz.ne']
    rfl
  refine ⟨hi, hint, hlog, ?_⟩
  rw [hlog]
  symm
  simp only [sub_mul, one_mul]
  rw [integral_sub hi hd.2.1, hint, hd.2.2]

end
end RHTower

namespace RHTower
noncomputable section

theorem liClockThetaSignedGammaTail_bound_wide {p : ℝ} (hp : liClockThetaWideThreshold < p)
    {J : ℕ} (hJ : 1 ≤ J) :
  let E : ℝ := xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
    (1/(150*p^2))^(J-1) / (1-1/(150*p^2))
  Integrable (liClockThetaSignedGammaTail p J) volume ∧
  (∫ t, |liClockThetaSignedGammaTail p J t|) ≤ E ∧
  SignedMeasure.totalVariation (volume.withDensityᵥ (liClockThetaSignedGammaTail p J)) Set.univ ≤
    ENNReal.ofReal E := by
  dsimp only
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h0 : liClockThetaLogJumpCoefficient p 0 = 0 := by
    simp [liClockThetaLogJumpCoefficient]
  let F : ℕ → ℝ → ℝ := fun r t => liClockThetaLogJumpCoefficient p (J+r) *
    liClockThetaGammaRowDensity p (J+r) t
  have hrow (r : ℕ) : Integrable (F r) ∧
      (∫ t, |F r t|) = |liClockThetaLogJumpCoefficient p (J+r)| := by
    simpa [F] using (sgPolynomial_row_norm_integral hp0 h0 (J+r) 0)
  have hm (r : ℕ) : Measurable (F r) :=
    (sgPolynomialRow_density_measurable p (J+r)).const_mul
      (liClockThetaLogJumpCoefficient p (J+r))
  have hev (r : ℕ) : (∫ t, ‖F r t‖) = |liClockThetaLogJumpCoefficient p (J+r)| := by
    simpa only [Real.norm_eq_abs] using (hrow r).2
  have hs : Summable (fun r => ∫ t, ‖F r t‖) := by
    simp_rw [hev]
    exact sgj_tail_summable hp hJ
  have hn (t : ℝ) : Summable (fun r => ‖F r t‖) := by
    apply Summable.of_nonneg_of_le (fun r => norm_nonneg (F r t))
      (fun r => ?_) ((sgj_tail_summable hp (J := J) hJ).mul_left p)
    calc
      ‖F r t‖ = |liClockThetaLogJumpCoefficient p (J+r)| *
          liClockThetaGammaRowDensity p (J+r) t := by
        simp only [F, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (sgWeighted_density_nonneg hp0 (J+r) t)]
      _ ≤ |liClockThetaLogJumpCoefficient p (J+r)| * p :=
        mul_le_mul_of_nonneg_left (sgWeighted_rowDensity_le hp0 (J+r) t) (abs_nonneg _)
      _ = p * |liClockThetaLogJumpCoefficient p (J+r)| := by ring
  have hi := sgPolynomial_series_integrable F hm (fun r => (hrow r).1) hs
  have hma := sgPolynomial_series_integrable (fun r t => ‖F r t‖)
    (fun r => (hm r).norm) (fun r => (hrow r).1.norm)
    (by simpa only [norm_norm] using hs)
  have hmass := hasSum_integral_of_summable_integral_norm
    (fun r => (hrow r).1.norm) (by simpa only [norm_norm] using hs)
  have hcomp := integral_mono hi.norm hma (fun t => norm_tsum_le_tsum_norm (hn t))
  rw [← hmass.tsum_eq] at hcomp
  simp_rw [hev] at hcomp
  change (∫ t, |liClockThetaSignedGammaTail p J t|) ≤
    ∑' r, |liClockThetaLogJumpCoefficient p (J+r)| at hcomp
  have hfinal := le_trans hcomp (sgj_tail_bound hp (J := J) hJ)
  have hti : Integrable (liClockThetaSignedGammaTail p J) := hi
  have htm : Measurable (liClockThetaSignedGammaTail p J) := Measurable.tsum hm
  refine ⟨hti, hfinal, ?_⟩
  rw [sgt_density_totalVariation htm hti, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hti.abs
      (ae_of_all _ (fun t => abs_nonneg (liClockThetaSignedGammaTail p J t)))]
  exact ENNReal.ofReal_le_ofReal hfinal

end
end RHTower

namespace RHTower
noncomputable section

private theorem sgb_signed_row_integral {p : ℝ} (hp : liClockThetaWideThreshold < p) (j n : ℕ) :
    (∫ t : ℝ, t^n * liClockThetaLogJumpCoefficient p j * liClockThetaGammaRowDensity p j t) =
      ((n.factorial : ℝ)/p^n) *
        (liClockThetaLogJumpCoefficient p j * ((2*j+n-1).choose n : ℝ)) := by
  have hr := sgPolynomialRow_polynomial_moment_factorial (liClockThetaWideThreshold_pos.trans hp) j n
  by_cases hj : j = 0
  · simp [hj, liClockThetaLogJumpCoefficient, liClockThetaGammaRowDensity]
  · have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hv : (∫ t : ℝ, t^n * liClockThetaGammaRowDensity p j t) =
        (1/p)^n * ((2*j+n-1).choose n : ℝ) * (n.factorial : ℝ) :=
      (div_eq_iff hn).mp (by simpa only [if_neg hj] using hr.2)
    have he : (fun t : ℝ => t^n * liClockThetaLogJumpCoefficient p j *
        liClockThetaGammaRowDensity p j t) = fun t =>
        liClockThetaLogJumpCoefficient p j * (t^n * liClockThetaGammaRowDensity p j t) := by
      funext t
      ring
    rw [he, integral_const_mul, hv]
    simp only [div_pow, one_pow]
    ring

private theorem sgb_signed_moment_binomial {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    (∫ t, t^n*liClockThetaSignedGammaDensity p t) / (n.factorial : ℝ) =
      (1/p)^n * ∑' j : ℕ, liClockThetaLogJumpCoefficient p j *
        ((2*j+n-1).choose n : ℝ) := by
  have hp0 : 0 < p := liClockThetaWideThreshold_pos.trans hp
  have h0 : liClockThetaLogJumpCoefficient p 0 = 0 := by
    simp [liClockThetaLogJumpCoefficient]
  have hf (j : ℕ) : Integrable (fun t : ℝ => t^n * liClockThetaLogJumpCoefficient p j *
      liClockThetaGammaRowDensity p j t) := (sgPolynomial_row_norm_integral hp0 h0 j n).1
  have hs := ((liClockThetaGammaJumpDensity_admission_wide hp).2.2 n).1
  have hsum := hasSum_integral_of_summable_integral_norm hf
    (by simpa only [Real.norm_eq_abs] using hs)
  have he : (fun t : ℝ => ∑' j, t^n * liClockThetaLogJumpCoefficient p j *
      liClockThetaGammaRowDensity p j t) = fun t => t^n * liClockThetaSignedGammaDensity p t := by
    funext t
    simp only [liClockThetaSignedGammaDensity, mul_assoc, tsum_mul_left]
  have hint : (∫ t, t^n * liClockThetaSignedGammaDensity p t) =
      ((n.factorial : ℝ)/p^n) * ∑' j, liClockThetaLogJumpCoefficient p j *
        ((2*j+n-1).choose n : ℝ) := by
    calc
      _ = ∫ t, ∑' j, t^n * liClockThetaLogJumpCoefficient p j *
          liClockThetaGammaRowDensity p j t := by rw [he]
      _ = ∑' j, ∫ t, t^n * liClockThetaLogJumpCoefficient p j *
          liClockThetaGammaRowDensity p j t := hsum.tsum_eq.symm
      _ = ∑' j, ((n.factorial : ℝ)/p^n) * (liClockThetaLogJumpCoefficient p j *
          ((2*j+n-1).choose n : ℝ)) := tsum_congr (fun j => sgb_signed_row_integral hp j n)
      _ = _ := tsum_mul_left
  rw [hint]
  simp only [div_pow, one_pow]
  field_simp [hp0.ne', show (n.factorial : ℝ) ≠ 0 by positivity]

end
end RHTower


/-! Signed positive-ray Laplace moment jets, with explicit genuine all-rate L1 admission.
No actual source equality or source moment bound is asserted by this private adapter. -/

open MeasureTheory Set Filter
open scoped Topology

namespace RHTower

private theorem sgLaplace_moment_hasDerivAt
    {f : ℝ → ℝ} (hf : Measurable f)
    (hzero : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hL1 : ∀ q : ℝ, liClockThetaWideThreshold < q → ∀ n : ℕ,
      Integrable (fun t : ℝ => t ^ n * Real.exp (-(q * t)) * f t))
    {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    HasDerivAt
      (fun q : ℝ => ∫ t : ℝ, t ^ n * Real.exp (-(q * t)) * f t)
      (-(∫ t : ℝ, t ^ (n + 1) * Real.exp (-(p * t)) * f t)) p := by
  let q0 : ℝ := (p + liClockThetaWideThreshold) / 2
  have hq0 : liClockThetaWideThreshold < q0 := by dsimp [q0]; linarith
  have hq0p : q0 < p := by dsimp [q0]; linarith
  have hmeas : ∀ q : ℝ, ∀ k : ℕ,
      Measurable (fun t : ℝ => t ^ k * Real.exp (-(q * t)) * f t) := by
    intro q k
    exact ((measurable_id.pow_const k).mul
      ((measurable_const.mul measurable_id).neg.exp)).mul hf
  have hFmeas : ∀ᶠ q : ℝ in 𝓝 p,
      AEStronglyMeasurable (fun t : ℝ => t ^ n * Real.exp (-(q * t)) * f t) :=
    Eventually.of_forall fun q => (hmeas q n).aestronglyMeasurable
  have hFderivmeas : AEStronglyMeasurable
      (fun t : ℝ => -(t ^ (n + 1) * Real.exp (-(p * t)) * f t)) :=
    (hmeas p (n + 1)).neg.aestronglyMeasurable
  have hbound : Integrable
      (fun t : ℝ => |t ^ (n + 1) * Real.exp (-(q0 * t)) * f t|) :=
    (hL1 q0 hq0 (n + 1)).abs
  have hdom : ∀ᵐ t : ℝ, ∀ q ∈ Ioi q0,
      ‖-(t ^ (n + 1) * Real.exp (-(q * t)) * f t)‖ ≤
        |t ^ (n + 1) * Real.exp (-(q0 * t)) * f t| := by
    apply Eventually.of_forall
    intro t q hq
    by_cases ht : t ≤ 0
    · simp [hzero t ht]
    · have ht0 : 0 < t := lt_of_not_ge ht
      have hexp : Real.exp (-(q * t)) ≤ Real.exp (-(q0 * t)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [show q0 < q from hq]
      simp only [norm_neg, Real.norm_eq_abs, abs_mul]
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (abs_nonneg _)) (abs_nonneg _)
  have hdiff : ∀ᵐ t : ℝ, ∀ q ∈ Ioi q0,
      HasDerivAt (fun x : ℝ => t ^ n * Real.exp (-(x * t)) * f t)
        (-(t ^ (n + 1) * Real.exp (-(q * t)) * f t)) q := by
    apply Eventually.of_forall
    intro t q _
    have hd := ((((hasDerivAt_id q).mul_const t).neg.exp).const_mul (t ^ n)).mul_const
      (f t)
    refine hd.congr_deriv ?_
    dsimp only [Pi.neg_apply, id_eq]
    rw [pow_succ]
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun q t : ℝ => t ^ n * Real.exp (-(q * t)) * f t)
    (F' := fun q t : ℝ => -(t ^ (n + 1) * Real.exp (-(q * t)) * f t))
    (bound := fun t : ℝ => |t ^ (n + 1) * Real.exp (-(q0 * t)) * f t|)
    (Ioi_mem_nhds hq0p) hFmeas (hL1 p hp n) hFderivmeas hdom hbound hdiff
  simpa only [integral_neg] using hmain.2

private theorem sgLaplace_iteratedDeriv
    {f : ℝ → ℝ} (hf : Measurable f)
    (hzero : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hL1 : ∀ q : ℝ, liClockThetaWideThreshold < q → ∀ n : ℕ,
      Integrable (fun t : ℝ => t ^ n * Real.exp (-(q * t)) * f t))
    {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    iteratedDeriv n (fun q : ℝ => ∫ t : ℝ, Real.exp (-(q * t)) * f t) p =
      (-1 : ℝ) ^ n * (∫ t : ℝ, t ^ n * Real.exp (-(p * t)) * f t) := by
  induction n generalizing p with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ n ih =>
    have hfun : Set.EqOn
        (iteratedDeriv n (fun q : ℝ => ∫ t : ℝ, Real.exp (-(q * t)) * f t))
        (fun q : ℝ => (-1 : ℝ) ^ n *
          (∫ t : ℝ, t ^ n * Real.exp (-(q * t)) * f t)) (Ioi liClockThetaWideThreshold) := by
      intro q hq
      exact ih hq
    have hd := (sgLaplace_moment_hasDerivAt hf hzero hL1 hp n).const_mul
      ((-1 : ℝ) ^ n)
    have hd' := hd.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hp) hfun)
    rw [iteratedDeriv_succ, hd'.deriv, pow_succ]
    ring

private theorem sgLaplace_iteratedDeriv_of_eqOn
    {f H : ℝ → ℝ} (hf : Measurable f)
    (hzero : ∀ t : ℝ, t ≤ 0 → f t = 0)
    (hL1 : ∀ q : ℝ, liClockThetaWideThreshold < q → ∀ n : ℕ,
      Integrable (fun t : ℝ => t ^ n * Real.exp (-(q * t)) * f t))
    (hH : ∀ q : ℝ, liClockThetaWideThreshold < q → H q = ∫ t : ℝ, Real.exp (-(q * t)) * f t)
    {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    iteratedDeriv n H p =
      (-1 : ℝ) ^ n * (∫ t : ℝ, t ^ n * Real.exp (-(p * t)) * f t) := by
  have heq : H =ᶠ[𝓝 p] (fun q : ℝ => ∫ t : ℝ, Real.exp (-(q * t)) * f t) := by
    filter_upwards [Ioi_mem_nhds hp] with q hq
    exact hH q hq
  rw [heq.iteratedDeriv_eq n]
  exact sgLaplace_iteratedDeriv hf hzero hL1 hp n

end RHTower

namespace RHTower
noncomputable section

private def sgbPrimitiveProfile (t : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun t => liEvenCrossActualClockPrimitive t / t) t

private theorem sgb_profile_measurable : Measurable sgbPrimitiveProfile := by
  unfold sgbPrimitiveProfile
  exact Measurable.indicator
    (contDiff_liEvenCrossActualClockPrimitive.continuous.measurable.div measurable_id)
    measurableSet_Ioi

private theorem sgb_exp_profile {p : ℝ} (hp : liClockThetaWideThreshold < p) :
    (fun t => Real.exp (-(p*t)) * sgbPrimitiveProfile t) = liClockThetaSignedGammaDensity p := by
  funext t
  rw [liClockThetaSignedGammaDensity_eq_primitive_wide hp]
  by_cases ht : 0 < t
  · simp only [sgbPrimitiveProfile, indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
    ring
  · simp [sgbPrimitiveProfile, ht]

private theorem sgb_signed_moment_derivative {p : ℝ} (hp : liClockThetaWideThreshold < p) (n : ℕ) :
    (∫ t, t^n * liClockThetaSignedGammaDensity p t) =
      (-1 : ℝ)^n * iteratedDeriv n liClockThetaReciprocalLog p := by
  have hzero : ∀ t : ℝ, t ≤ 0 → sgbPrimitiveProfile t = 0 := by
    intro t ht
    simp [sgbPrimitiveProfile, not_lt.mpr ht]
  have he (q : ℝ) (hq : liClockThetaWideThreshold < q) (k : ℕ) :
      (fun t => t^k * Real.exp (-(q*t)) * sgbPrimitiveProfile t) =
        fun t => t^k * liClockThetaSignedGammaDensity q t := by
    funext t
    rw [mul_assoc]
    exact congrArg (fun x : ℝ => t^k * x) (congrFun (sgb_exp_profile hq) t)
  have hL1 (q : ℝ) (hq : liClockThetaWideThreshold < q) (k : ℕ) :
      Integrable (fun t => t^k * Real.exp (-(q*t)) * sgbPrimitiveProfile t) := by
    rw [he q hq k]
    exact ((liClockThetaGammaJumpDensity_admission_wide hq).2.2 k).2
  have hH (q : ℝ) (hq : liClockThetaWideThreshold < q) : liClockThetaReciprocalLog q =
      ∫ t, Real.exp (-(q*t)) * sgbPrimitiveProfile t := by
    rw [sgb_exp_profile hq]
    exact (sgb_signed_density_data hq).2.2.symm
  have hjet := sgLaplace_iteratedDeriv_of_eqOn sgb_profile_measurable hzero hL1 hH hp n
  rw [he p hp n] at hjet
  rw [hjet, ← mul_assoc, ← mul_pow]
  norm_num

theorem liClockThetaSignedGammaDensity_moment_wide {p : ℝ} (hp : liClockThetaWideThreshold < p)
    {n : ℕ} (hn : 1 ≤ n) :
  Integrable (fun t => t^n*liClockThetaSignedGammaDensity p t) volume ∧
  (∫ t, t^n*liClockThetaSignedGammaDensity p t) / (n.factorial : ℝ) =
    (-1 : ℝ)^n * iteratedDeriv n liClockThetaReciprocalLog p / (n.factorial : ℝ) ∧
  (∫ t, t^n*liClockThetaSignedGammaDensity p t) / (n.factorial : ℝ) =
    (1/p)^n * ∑' j : ℕ, liClockThetaLogJumpCoefficient p j *
      (Nat.choose (2*j+n-1) n : ℝ) := by
  cases n with
  | zero => omega
  | succ n =>
    refine ⟨((liClockThetaGammaJumpDensity_admission_wide hp).2.2 (n+1)).2, ?_,
      sgb_signed_moment_binomial hp (n+1)⟩
    rw [sgb_signed_moment_derivative hp (n+1)]

end
end RHTower

namespace RHTower

/-! ## The original `p > 1` admissions -/

theorem liClockThetaLogJumpCoefficient_admission {p : ℝ} (hp : 1 < p) :
  Summable (fun j : ℕ => |liClockThetaLogJumpCoefficient p j|) ∧
  HasSum (liClockThetaLogJumpCoefficient p) (liClockThetaReciprocalLog p) ∧
  (∀ J : ℕ, 1 ≤ J →
    (∑' r : ℕ, |liClockThetaLogJumpCoefficient p (J+r)|) ≤
      xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
        (1/(150*p^2))^(J-1) / (1-1/(150*p^2))) :=
  liClockThetaLogJumpCoefficient_admission_wide (liClockThetaWideThreshold_lt_one.trans hp)

theorem liClockThetaSignedGammaDensity_eq_primitive {p : ℝ} (hp : 1 < p) (t : ℝ) :
  liClockThetaSignedGammaDensity p t =
    (Ioi (0 : ℝ)).indicator (fun t =>
      Real.exp (-(p*t)) * liEvenCrossActualClockPrimitive t / t) t :=
  liClockThetaSignedGammaDensity_eq_primitive_wide (liClockThetaWideThreshold_lt_one.trans hp) t

theorem liClockThetaJumpMeasure_admission {p : ℝ} (hp : 1 < p) :
  liClockThetaJumpMass p true - liClockThetaJumpMass p false =
    liClockThetaReciprocalLog p ∧
  (∀ positive : Bool,
    0 < liClockThetaJumpMass p positive ∧
    IsFiniteMeasure (liClockThetaDegreeJumpMeasure p positive) ∧
    IsFiniteMeasure (liClockThetaGammaJumpMeasure p positive) ∧
    liClockThetaDegreeJumpMeasure p positive Set.univ =
      ENNReal.ofReal (liClockThetaJumpMass p positive) ∧
    liClockThetaGammaJumpMeasure p positive Set.univ =
      ENNReal.ofReal (liClockThetaJumpMass p positive) ∧
    (∀ᵐ t ∂liClockThetaDegreeJumpMeasure p positive, 0 < t) ∧
    (∀ᵐ t ∂liClockThetaGammaJumpMeasure p positive, 0 < t)) :=
  liClockThetaJumpMeasure_admission_wide (liClockThetaWideThreshold_lt_one.trans hp)

theorem liClockThetaSignedGammaMeasure_admission {p : ℝ} (hp : 1 < p) :
  (∀ s : Set ℝ, MeasurableSet s →
    liClockThetaSignedGammaMeasure p s =
      (liClockThetaGammaJumpMeasure p true s).toReal -
        (liClockThetaGammaJumpMeasure p false s).toReal) ∧
  (∀ h : ℝ → ℝ, Measurable h → (∃ C : ℝ, ∀ t, |h t| ≤ C) →
    Integrable (fun t => h t * liClockThetaSignedGammaDensity p t) volume ∧
    Integrable h (liClockThetaGammaJumpMeasure p true) ∧
    Integrable h (liClockThetaGammaJumpMeasure p false) ∧
    (∫ t, h t * liClockThetaSignedGammaDensity p t) =
      (∫ t, h t ∂liClockThetaGammaJumpMeasure p true) -
        (∫ t, h t ∂liClockThetaGammaJumpMeasure p false)) :=
  liClockThetaSignedGammaMeasure_admission_wide (liClockThetaWideThreshold_lt_one.trans hp)

theorem liClockThetaGammaJumpDensity_admission {p : ℝ} (hp : 1 < p) :
  (∀ positive : Bool,
    Integrable (liClockThetaGammaJumpDensity p positive) volume ∧
    (∀ t : ℝ, 0 ≤ liClockThetaGammaJumpDensity p positive t) ∧
    (∫ t, liClockThetaGammaJumpDensity p positive t) =
      liClockThetaJumpMass p positive ∧
    liClockThetaGammaJumpMeasure p positive =
      volume.withDensity (fun t => ENNReal.ofReal (liClockThetaGammaJumpDensity p positive t))) ∧
  (∑' j : ℕ, ∫ t, |liClockThetaLogJumpCoefficient p j *
    liClockThetaGammaRowDensity p j t|) =
      ∑' j : ℕ, |liClockThetaLogJumpCoefficient p j| ∧
  (∀ n : ℕ,
    Summable (fun j : ℕ => ∫ t, |t^n * liClockThetaLogJumpCoefficient p j *
      liClockThetaGammaRowDensity p j t|) ∧
    Integrable (fun t => t^n * liClockThetaSignedGammaDensity p t) volume) :=
  liClockThetaGammaJumpDensity_admission_wide (liClockThetaWideThreshold_lt_one.trans hp)

theorem liClockThetaSignedGammaMeasure_totalVariation {p : ℝ} (hp : 1 < p) :
  (liClockThetaSignedGammaMeasure p).totalVariation =
    volume.withDensity (fun t => ENNReal.ofReal |liClockThetaSignedGammaDensity p t|) ∧
  (∫ t, |liClockThetaSignedGammaDensity p t|) ≤
    liClockThetaJumpMass p true + liClockThetaJumpMass p false :=
  liClockThetaSignedGammaMeasure_totalVariation_wide (liClockThetaWideThreshold_lt_one.trans hp)

theorem liClockThetaSignedGammaDensity_laplace {p : ℝ} (hp : 1 < p)
    {s : ℝ} (hs : 0 ≤ s) :
  Integrable (fun t => Real.exp (-(s*t))*liClockThetaSignedGammaDensity p t) volume ∧
  (∫ t, Real.exp (-(s*t))*liClockThetaSignedGammaDensity p t) =
    liClockThetaReciprocalLog (p+s) ∧
  Real.log (Lap (liClockThetaGammaMixture p) s).toReal =
    liClockThetaReciprocalLog (p+s) - liClockThetaReciprocalLog p ∧
  Real.log (Lap (liClockThetaGammaMixture p) s).toReal =
    ∫ t, (Real.exp (-(s*t))-1)*liClockThetaSignedGammaDensity p t :=
  liClockThetaSignedGammaDensity_laplace_wide (liClockThetaWideThreshold_lt_one.trans hp) hs

theorem liClockThetaSignedGammaTail_bound {p : ℝ} (hp : 1 < p)
    {J : ℕ} (hJ : 1 ≤ J) :
  let E : ℝ := xiShiftAbsoluteMass 0 / (2*(J : ℝ)*p^2) *
    (1/(150*p^2))^(J-1) / (1-1/(150*p^2))
  Integrable (liClockThetaSignedGammaTail p J) volume ∧
  (∫ t, |liClockThetaSignedGammaTail p J t|) ≤ E ∧
  SignedMeasure.totalVariation (volume.withDensityᵥ (liClockThetaSignedGammaTail p J)) Set.univ ≤
    ENNReal.ofReal E :=
  liClockThetaSignedGammaTail_bound_wide (liClockThetaWideThreshold_lt_one.trans hp) hJ

theorem liClockThetaSignedGammaDensity_moment {p : ℝ} (hp : 1 < p)
    {n : ℕ} (hn : 1 ≤ n) :
  Integrable (fun t => t^n*liClockThetaSignedGammaDensity p t) volume ∧
  (∫ t, t^n*liClockThetaSignedGammaDensity p t) / (n.factorial : ℝ) =
    (-1 : ℝ)^n * iteratedDeriv n liClockThetaReciprocalLog p / (n.factorial : ℝ) ∧
  (∫ t, t^n*liClockThetaSignedGammaDensity p t) / (n.factorial : ℝ) =
    (1/p)^n * ∑' j : ℕ, liClockThetaLogJumpCoefficient p j *
      (Nat.choose (2*j+n-1) n : ℝ) :=
  liClockThetaSignedGammaDensity_moment_wide (liClockThetaWideThreshold_lt_one.trans hp) hn

end RHTower
