import GaloisForLFunctions.CountingHolography.Sections.ThePrimeProfileOfThreeSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity

/-!
# The outer band of the square contact profile

Measuring the lag in units of the largest conductor removes the conductor
from the shape of the last overlap. On this band only its frequency changes.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticWeightTheory ArithmeticCastelnuovoSeveri BiScaleUncertainty.ChebyshevGauge
open ArithmeticOrientationGeometry _root_.RHTower.WeilDeletion

/-- Square root of the largest conductor of the signed triple. -/
def squareUpperRoot (n : ℕ) : ℝ := 2*(n:ℝ)+1

/-- Original unrounded reading of the square divisor at lag k. -/
def successorSquareRawRow (n m k : ℕ) :=
  contactMultiplicity (packet (m • successorSquareTriple n)) (3*windowEnd ((2*n+1)^2+1))
    (resolution (m • successorSquareTriple n)) k

def outerSquareLeft : ℝ := Real.exp 8/2
def outerSquareRight : ℝ := 2*Real.exp 8

/-- Magnitude of the negative contact after scaling the lag by the largest
conductor and removing the factor m²/(2n+1). -/
def outerSquareProfile (x : ℝ) := 2*splineAutoCorr (-Real.log x)/Real.sqrt x

/-- The outer profile crosses a fixed interval of values with uniformly
bounded slope. -/
theorem outerSquareProfile_crosses : 1 ≤ outerSquareLeft ∧ outerSquareLeft ≤ outerSquareRight ∧
    ContinuousOn outerSquareProfile (Set.Icc outerSquareLeft outerSquareRight) ∧
    0 < outerSquareProfile outerSquareLeft ∧ outerSquareProfile outerSquareRight = 0 ∧
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x ∈ Set.Icc outerSquareLeft (outerSquareRight+1),
      ∀ y ∈ Set.Icc outerSquareLeft (outerSquareRight+1), |outerSquareProfile x-outerSquareProfile y| ≤ L*|x-y| := by
  have hE : 9 ≤ Real.exp 8 := by linarith only [Real.add_one_le_exp (8:ℝ)]
  have hu : 1 ≤ outerSquareLeft := by unfold outerSquareLeft; linarith only [hE]
  have huv : outerSquareLeft ≤ outerSquareRight := by unfold outerSquareLeft outerSquareRight; linarith only [hE]
  have hcorr : ContDiff ℝ 2 splineAutoCorr := by
    exact Complex.reCLM.contDiff.comp (Zeta23.EF.weilTest_contDiff (cx_contDiff contDiff_cubicSpline)
      (cx_contDiff contDiff_cubicSpline).continuous (cx_hasCompactSupport hasCompactSupport_cubicSpline))
  have hcorr₁ : ContDiff ℝ 1 splineAutoCorr := hcorr.of_le (by decide)
  have hs : ContDiffOn ℝ 1 outerSquareProfile (Set.Icc outerSquareLeft (outerSquareRight+1)) := by
    intro x hx
    have hx₀ := zero_lt_one.trans_le (hu.trans hx.1)
    have hlog : ContDiffAt ℝ 1 Real.log x := Real.contDiffAt_log.mpr hx₀.ne'
    exact ((contDiffAt_const.mul (hcorr₁.contDiffAt.comp x hlog.neg)).div
      (Real.contDiffAt_sqrt hx₀.ne') (Real.sqrt_pos.mpr hx₀).ne').contDiffWithinAt
  obtain ⟨L,hL⟩ := hs.exists_lipschitzOnWith one_ne_zero (convex_Icc ..) isCompact_Icc
  have h₂ := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have h₂' := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2:ℝ))
  have hlu : Real.log outerSquareLeft = 8-Real.log 2 := by
    rw [outerSquareLeft,Real.log_div (Real.exp_pos _).ne' (by norm_num),Real.log_exp]
  have hlv : Real.log outerSquareRight = Real.log 2+8 := by
    rw [outerSquareRight,Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp]
  refine ⟨hu,huv,hs.continuousOn.mono (Set.Icc_subset_Icc_right (by linarith)),?_,?_,max L 1,le_max_right _ _,?_⟩
  · apply div_pos _ (Real.sqrt_pos.mpr (zero_lt_one.trans_le hu))
    apply mul_pos (by norm_num) (splineAutoCorr_interior ?_)
    rw [hlu,abs_lt]
    constructor <;> linarith only [h₂,h₂']
  · unfold outerSquareProfile
    rw [splineAutoCorr_zero_outside (show 8 < |-(Real.log outerSquareRight)| by
      rw [abs_neg,hlv]; exact (by linarith only [h₂] : 8 < Real.log 2+8).trans_le (le_abs_self _)),
      mul_zero,zero_div]
  · intro x hx y hy
    have hd := hL.dist_le_mul x hx y hy
    simp only [Real.dist_eq] at hd
    exact hd.trans (mul_le_mul_of_nonneg_right (le_max_left (L:ℝ) 1) (abs_nonneg _))

/-- On all lags of the outer band the original row differs from the fixed
profile by at most a constant times m/(2n+1). All these lags lie inside the
original prime horizon. -/
theorem successorSquare_outer_reading : ∃ E : ℝ, 0 ≤ E ∧ ∀ {n m k : ℕ}, 4 ≤ n → 0 < m →
    let R := squareUpperRoot n
    let x := (k:ℝ)/R^2
    outerSquareLeft ≤ x → x ≤ outerSquareRight+1 →
    2 ≤ k ∧ k ≤ 3*windowEnd ((2*n+1)^2+1) ∧
    |successorSquareRawRow n m k + ((m:ℝ)^2/R)*outerSquareProfile x| ≤ E*m/R := by
  obtain ⟨C,hC,hmesh⟩ := contactMultiplicity_uniform_error
  refine ⟨2*C,by positivity,fun {n m k} hn hm => ?_⟩
  let R := squareUpperRoot n
  let b := R^2
  let x := (k:ℝ)/b
  let d := successorSquareTriple n
  let L := 3*windowEnd ((2*n+1)^2+1)
  let r := resolution (m • d)
  change outerSquareLeft ≤ x → x ≤ outerSquareRight+1 → _
  intro hu hv
  have hR : 0 < R := by dsimp only [R,squareUpperRoot]; positivity
  have hb : 0 < b := sq_pos_of_pos hR
  have hroot_id : ((2*n+1:ℕ):ℝ) = R := by simp only [R,squareUpperRoot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hk : outerSquareLeft*b ≤ k := (le_div_iff₀ hb).mp hu
  have hk' : (k:ℝ) ≤ (outerSquareRight+1)*b := (div_le_iff₀ hb).mp hv
  have hx₁ := outerSquareProfile_crosses.1.trans hu
  have hx₀ := zero_lt_one.trans_le hx₁
  have hkpos : 0 < (k:ℝ) := (mul_pos (zero_lt_one.trans_le outerSquareProfile_crosses.1) hb).trans_le hk
  have hn₄ : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0:ℝ) < n := by linarith only [hn₄]
  have hdil : 4*(n:ℝ)^2 ≤ b := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(n:ℝ)) (le_add_of_nonneg_right zero_le_one) 2
    dsimp only [b,R,squareUpperRoot]
    linarith only [hh]
  have hsep : Real.exp 8*(n:ℝ)^2 < k := by
    unfold outerSquareLeft at hk
    linarith only [hk,mul_le_mul_of_nonneg_left hdil (Real.exp_pos 8).le,
      mul_pos (Real.exp_pos 8) (sq_pos_of_pos hn₀)]
  have hlog := Real.log_lt_log (mul_pos (Real.exp_pos _) (sq_pos_of_pos hn₀)) hsep
  rw [Real.log_mul (Real.exp_pos _).ne' (sq_pos_of_pos hn₀).ne',Real.log_exp] at hlog
  have h9 : (9:ℝ) ≤ (n:ℝ)^2 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hn₄ 2
    linarith only [hp]
  have hlong : 8+Real.log 9 < Real.log k := by
    linarith only [hlog,Real.log_le_log (by norm_num : (0:ℝ)<9) h9]
  have htop : (k:ℝ) ≤ 3*(windowEnd ((2*n+1)^2+1):ℝ) := by
    have he := Real.add_one_le_exp (8:ℝ)
    have hw := (successorSquareWindowScale_bounds n).2.2
    simp only [successorSquareWindowScale,hroot_id] at hw
    change (k:ℝ) ≤ (2*Real.exp 8+1)*b at hk'
    change Real.exp 8*b ≤ _ at hw
    linarith only [hk',hw,mul_le_mul_of_nonneg_right he hb.le]
  have hk₂ : (2:ℝ) ≤ k := by
    have he := Real.add_one_le_exp (8:ℝ)
    linarith only [hsep,h9,mul_le_mul_of_nonneg_right he (sq_nonneg (n:ℝ))]
  refine ⟨by exact_mod_cast hk₂,by exact_mod_cast htop,?_⟩
  have hx : x*b = k := div_mul_cancel₀ _ hb.ne'
  have hlogx : Real.log b-Real.log k = -Real.log x := by
    rw [show x=(k:ℝ)/b from rfl,Real.log_div hkpos.ne' hb.ne']; ring
  have hroot : Real.sqrt k = R*Real.sqrt x := by
    calc Real.sqrt k = Real.sqrt (x*b) := congrArg Real.sqrt hx.symm
      _ = _ := by rw [Real.sqrt_mul hx₀.le,show b=R^2 from rfl,Real.sqrt_sq hR.le,mul_comm]
  have hvanish := splineAutoCorr_zero_outside (x := Real.log ((n:ℝ)^2)-Real.log k)
    ((show 8 < -(Real.log ((n:ℝ)^2)-Real.log k) by linarith only [hlog]).trans_le (neg_le_abs _))
  have hcont := successorSquare_long_contact (by omega : 0 < n) hlong
  rw [hvanish,hroot_id] at hcont
  change integratedContact d k = 2/Real.sqrt k*(2*0-splineAutoCorr (Real.log b-Real.log k)) at hcont
  rw [hlogx,hroot] at hcont
  have hmain : (m:ℝ)^2*integratedContact d k = -(((m:ℝ)^2/R)*outerSquareProfile x) := by
    rw [hcont,outerSquareProfile]
    field_simp [hR.ne',(Real.sqrt_pos.mpr hx₀).ne']; ring
  have hr := successorSquare_resolution_ge n m
  have hm₀ : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hr' : (m:ℝ) ≤ r := by exact_mod_cast hr
  have hsample := hmesh _ d (successorSquareTriple_mass n) (hm.trans_le hr) (Nat.cast_pos.mp hkpos)
  have hdiff : |successorSquareRawRow n m k-(m:ℝ)^2*integratedContact d k| ≤ (2*C)*m/R := by
    change |contactMultiplicity (packet (m • d)) L r k-(m:ℝ)^2*integratedContact d k| ≤ _
    rw [packet_smul,contactMultiplicity_scale,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg (m:ℝ))]
    have hrt : R ≤ Real.sqrt k := by
      rw [hroot]
      exact le_mul_of_one_le_right hR.le (by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx₁)
    have herr : (m:ℝ)^2*C/r ≤ C*m := by
      apply (div_le_iff₀ (hm₀.trans_le hr')).mpr
      linarith only [mul_le_mul_of_nonneg_left hr' (mul_nonneg hC hm₀.le)]
    calc _ ≤ (m:ℝ)^2*((2/Real.sqrt k)*(C/r)) := mul_le_mul_of_nonneg_left hsample (sq_nonneg _)
      _ = (2*((m:ℝ)^2*C/r))/Real.sqrt k := by ring
      _ ≤ _ := div_le_div₀ (by positivity) (by linarith only [herr]) hR hrt
  rw [hmain,sub_neg_eq_add] at hdiff
  exact hdiff

#print axioms outerSquareProfile_crosses
#print axioms successorSquare_outer_reading

end GaloisForLFunctions.CountingHolography.Sections
