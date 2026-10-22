import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthTransferKernel
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Exact finite convolution decomposition of the source growth transfer

The likelihood cumulants through order eight are exactly the nonconstant
jets of a finite logarithmic polynomial. Rebase that polynomial around the
actual tail mass to obtain eight alternating full convolution sectors with
positive weights. An exact positive remainder controls every normalized
weight by its logarithmic coefficient. This supplies an unconditional
identity for the complete source transfer functional, not its sign.

The hard remaining comparison is the dominant pair against the stable
single-component tail and odd convolution sectors three, five and seven.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section


def finiteLogWeight (p : ℝ) : ℕ → ℝ
  | 1 => 840*(1+p+p^2+p^3+p^4+p^5+p^6+p^7)
  | 2 => 420+840*p+1260*p^2+1680*p^3+2100*p^4+2520*p^5+2940*p^6
  | 3 => 280+840*p+1680*p^2+2800*p^3+4200*p^4+5880*p^5
  | 4 => 210+840*p+2100*p^2+4200*p^3+7350*p^4
  | 5 => 168+840*p+2520*p^2+5880*p^3
  | 6 => 140+840*p+2940*p^2
  | 7 => 120+840*p
  | 8 => 105
  | _ => 0

def logJetEight (P : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.C 840*P-PowerSeries.C 420*P^2+PowerSeries.C 280*P^3-
    PowerSeries.C 210*P^4+PowerSeries.C 168*P^5-PowerSeries.C 140*P^6+
    PowerSeries.C 120*P^7-PowerSeries.C 105*P^8

theorem logJetEight_rebase (P : PowerSeries ℝ) (p : ℝ) :
    logJetEight (P-PowerSeries.C p) =
      PowerSeries.C (finiteLogWeight p 1)*P-
      PowerSeries.C (finiteLogWeight p 2)*P^2+
      PowerSeries.C (finiteLogWeight p 3)*P^3-
      PowerSeries.C (finiteLogWeight p 4)*P^4+
      PowerSeries.C (finiteLogWeight p 5)*P^5-
      PowerSeries.C (finiteLogWeight p 6)*P^6+
      PowerSeries.C (finiteLogWeight p 7)*P^7-
      PowerSeries.C (finiteLogWeight p 8)*P^8-
      PowerSeries.C (840*p+420*p^2+280*p^3+210*p^4+168*p^5+140*p^6+120*p^7+105*p^8) := by
  simp only [logJetEight,finiteLogWeight,map_add,map_mul,map_pow,map_ofNat,map_one]
  ring

theorem finiteLogWeight_pos {p : ℝ} (hp : 0 ≤ p) {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 8) :
    0 < finiteLogWeight p k := by
  obtain ⟨hk1,hk8⟩ := hk
  interval_cases k <;> norm_num only [finiteLogWeight] <;> positivity

def momentSeries (m : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun j => m j/(j.factorial:ℝ))

def spectralPowerMoment (m : ℕ → ℝ) (k j : ℕ) : ℝ :=
  (j.factorial:ℝ)*PowerSeries.coeff j (momentSeries m ^ k)

def finiteLogMoment (m : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial:ℝ)*PowerSeries.coeff j (logJetEight (momentSeries m-PowerSeries.C (m 0)))

theorem finiteLogMoment_decomposition (m : ℕ → ℝ) {j : ℕ} (hj : j ≠ 0) :
    finiteLogMoment m j =
      finiteLogWeight (m 0) 1*spectralPowerMoment m 1 j-
      finiteLogWeight (m 0) 2*spectralPowerMoment m 2 j+
      finiteLogWeight (m 0) 3*spectralPowerMoment m 3 j-
      finiteLogWeight (m 0) 4*spectralPowerMoment m 4 j+
      finiteLogWeight (m 0) 5*spectralPowerMoment m 5 j-
      finiteLogWeight (m 0) 6*spectralPowerMoment m 6 j+
      finiteLogWeight (m 0) 7*spectralPowerMoment m 7 j-
      finiteLogWeight (m 0) 8*spectralPowerMoment m 8 j := by
  unfold finiteLogMoment spectralPowerMoment
  rw [logJetEight_rebase]
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul,PowerSeries.coeff_C_of_ne_zero hj,pow_one]
  ring

def centeredMomentCoeff (m : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=0 then 0 else m j/(j.factorial:ℝ)

private theorem centered_series_coeff (m : ℕ → ℝ) (j : ℕ) :
    PowerSeries.coeff j (momentSeries m-PowerSeries.C (m 0)) = centeredMomentCoeff m j := by
  simp only [momentSeries,map_sub,PowerSeries.coeff_mk,PowerSeries.coeff_C,centeredMomentCoeff]
  split_ifs with hj
  · subst j; norm_num
  · ring

private theorem coeff_pow_add_two (P : PowerSeries ℝ) (k j : ℕ) :
    PowerSeries.coeff j (P^(k+2)) =
      ∑ i ∈ Finset.range (j+1), PowerSeries.coeff i P * PowerSeries.coeff (j-i) (P^(k+1)) := by
  rw [pow_succ',PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a P*PowerSeries.coeff b (P^(k+1))) j

private def jetPowerCoeff (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 2, 2 => a 1^2
  | 2, 3 => 2*a 1*a 2
  | 2, 4 => 2*a 1*a 3+a 2^2
  | 2, 5 => 2*a 1*a 4+2*a 2*a 3
  | 2, 6 => 2*a 1*a 5+2*a 2*a 4+a 3^2
  | 2, 7 => 2*a 1*a 6+2*a 2*a 5+2*a 3*a 4
  | 2, 8 => 2*a 1*a 7+2*a 2*a 6+2*a 3*a 5+a 4^2
  | 3, 3 => a 1^3
  | 3, 4 => 3*a 1^2*a 2
  | 3, 5 => 3*a 1^2*a 3+3*a 1*a 2^2
  | 3, 6 => 3*a 1^2*a 4+6*a 1*a 2*a 3+a 2^3
  | 3, 7 => 3*a 1^2*a 5+6*a 1*a 2*a 4+3*a 1*a 3^2+3*a 2^2*a 3
  | 3, 8 => 3*a 1^2*a 6+6*a 1*a 2*a 5+6*a 1*a 3*a 4+3*a 2^2*a 4+3*a 2*a 3^2
  | 4, 4 => a 1^4
  | 4, 5 => 4*a 1^3*a 2
  | 4, 6 => 4*a 1^3*a 3+6*a 1^2*a 2^2
  | 4, 7 => 4*a 1^3*a 4+12*a 1^2*a 2*a 3+4*a 1*a 2^3
  | 4, 8 => 4*a 1^3*a 5+12*a 1^2*a 2*a 4+6*a 1^2*a 3^2+
      12*a 1*a 2^2*a 3+a 2^4
  | 5, 5 => a 1^5
  | 5, 6 => 5*a 1^4*a 2
  | 5, 7 => 5*a 1^4*a 3+10*a 1^3*a 2^2
  | 5, 8 => 5*a 1^4*a 4+20*a 1^3*a 2*a 3+10*a 1^2*a 2^3
  | 6, 6 => a 1^6
  | 6, 7 => 6*a 1^5*a 2
  | 6, 8 => 6*a 1^5*a 3+15*a 1^4*a 2^2
  | 7, 7 => a 1^7
  | 7, 8 => 7*a 1^6*a 2
  | 8, 8 => a 1^8
  | _, _ => 0

private theorem coeff_power_two (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {j : ℕ} (hj : j ≤ 8) :
    PowerSeries.coeff j (P^2)=jetPowerCoeff (fun i => PowerSeries.coeff i P) 2 j := by
  rw [show 2=0+2 by rfl,coeff_pow_add_two]
  interval_cases j <;> norm_num [Finset.sum_range_succ,jetPowerCoeff,hP] <;> ring

private theorem coeff_power_three (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {j : ℕ} (hj : j ≤ 8) :
    PowerSeries.coeff j (P^3)=jetPowerCoeff (fun i => PowerSeries.coeff i P) 3 j := by
  rw [show 3=1+2 by rfl,coeff_pow_add_two]
  interval_cases j <;> norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.reduceAdd,Nat.reduceSub,zero_add]
  all_goals simp (disch := omega) only [coeff_power_two P hP]
  all_goals norm_num [jetPowerCoeff,hP]
  all_goals ring

private theorem coeff_power_four (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {j : ℕ} (hj : j ≤ 8) :
    PowerSeries.coeff j (P^4)=jetPowerCoeff (fun i => PowerSeries.coeff i P) 4 j := by
  rw [show 4=2+2 by rfl,coeff_pow_add_two]
  interval_cases j <;> norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.reduceAdd,Nat.reduceSub,zero_add]
  all_goals simp (disch := omega) only [coeff_power_three P hP]
  all_goals norm_num [jetPowerCoeff,hP]
  all_goals ring

private theorem coeff_power_five (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {j : ℕ} (hj : j ≤ 8) :
    PowerSeries.coeff j (P^5)=jetPowerCoeff (fun i => PowerSeries.coeff i P) 5 j := by
  rw [show 5=3+2 by rfl,coeff_pow_add_two]
  interval_cases j <;> norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.reduceAdd,Nat.reduceSub,zero_add]
  all_goals simp (disch := omega) only [coeff_power_four P hP]
  all_goals norm_num [jetPowerCoeff,hP]
  all_goals ring

private theorem coeff_power_six (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {j : ℕ} (hj : j ≤ 8) :
    PowerSeries.coeff j (P^6)=jetPowerCoeff (fun i => PowerSeries.coeff i P) 6 j := by
  rw [show 6=4+2 by rfl,coeff_pow_add_two]
  interval_cases j <;> norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.reduceAdd,Nat.reduceSub,zero_add]
  all_goals simp (disch := omega) only [coeff_power_five P hP]
  all_goals norm_num [jetPowerCoeff,hP]
  all_goals ring

private theorem coeff_power_seven (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {j : ℕ} (hj : j ≤ 8) :
    PowerSeries.coeff j (P^7)=jetPowerCoeff (fun i => PowerSeries.coeff i P) 7 j := by
  rw [show 7=5+2 by rfl,coeff_pow_add_two]
  interval_cases j <;> norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.reduceAdd,Nat.reduceSub,zero_add]
  all_goals simp (disch := omega) only [coeff_power_six P hP]
  all_goals norm_num [jetPowerCoeff,hP]
  all_goals ring

private theorem coeff_power_eight (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {j : ℕ} (hj : j ≤ 8) :
    PowerSeries.coeff j (P^8)=jetPowerCoeff (fun i => PowerSeries.coeff i P) 8 j := by
  rw [show 8=6+2 by rfl,coeff_pow_add_two]
  interval_cases j <;> norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.reduceAdd,Nat.reduceSub,zero_add]
  all_goals simp (disch := omega) only [coeff_power_seven P hP]
  all_goals norm_num [jetPowerCoeff,hP]
  all_goals ring

private theorem coeff_power_small (P : PowerSeries ℝ) (hP : PowerSeries.coeff 0 P=0)
    {k j : ℕ} (hk2 : 2 ≤ k) (hk8 : k ≤ 8) (hj : j ≤ 8) :
    PowerSeries.coeff j (P^k)=jetPowerCoeff (fun i => PowerSeries.coeff i P) k j := by
  interval_cases k
  · exact coeff_power_two P hP hj
  · exact coeff_power_three P hP hj
  · exact coeff_power_four P hP hj
  · exact coeff_power_five P hP hj
  · exact coeff_power_six P hP hj
  · exact coeff_power_seven P hP hj
  · exact coeff_power_eight P hP hj

theorem finiteLogMoment_source_two (q : ℝ) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) 2 =
      840*thetaCuspLikelihoodVariance q := by
  rw [thetaCuspLikelihoodVariance_eq_normalizedMoment_two_sub_mean_sq]
  simp only [← thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold finiteLogMoment logJetEight
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 (momentSeries (thetaCuspLikelihoodNormalizedMoment q)-
      PowerSeries.C (thetaCuspLikelihoodNormalizedMoment q 0))=0 := by
    simp [centered_series_coeff,centeredMomentCoeff]
  simp (disch := omega) only [coeff_power_small _ h0]
  norm_num [jetPowerCoeff,centered_series_coeff,centeredMomentCoeff,momentSeries]
  ring

theorem finiteLogMoment_source_eight (q : ℝ) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) 8 =
      840*thetaCuspLikelihoodEighthCumulant q := by
  unfold thetaCuspLikelihoodEighthCumulant
  simp only [← thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold finiteLogMoment logJetEight
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 (momentSeries (thetaCuspLikelihoodNormalizedMoment q)-
      PowerSeries.C (thetaCuspLikelihoodNormalizedMoment q 0))=0 := by
    simp [centered_series_coeff,centeredMomentCoeff]
  simp (disch := omega) only [coeff_power_small _ h0]
  norm_num [jetPowerCoeff,centered_series_coeff,centeredMomentCoeff,momentSeries]
  ring

def finiteLogRemainder (r : ℝ) : ℕ → ℝ
  | 1 => 1
  | 2 => 1+7*r
  | 3 => 1+6*r+21*r^2
  | 4 => 1+5*r+15*r^2+35*r^3
  | 5 => 1+4*r+10*r^2+20*r^3+35*r^4
  | 6 => 1+3*r+6*r^2+10*r^3+15*r^4+21*r^5
  | 7 => 1+2*r+3*r^2+4*r^3+5*r^4+6*r^5+7*r^6
  | 8 => 1+r+r^2+r^3+r^4+r^5+r^6+r^7
  | _ => 0

theorem finiteLogWeight_remainder_identity (p : ℝ) {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 8) :
    finiteLogWeight p k*(1-p)^k+
      (840/(k:ℝ))*p^(9-k)*finiteLogRemainder (1-p) k=840/(k:ℝ) := by
  obtain ⟨hk1,hk8⟩ := hk
  interval_cases k <;> norm_num [finiteLogWeight,finiteLogRemainder] <;> ring

theorem finiteLogWeight_normalized_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {k : ℕ} (hk : 1 ≤ k ∧ k ≤ 8) :
    finiteLogWeight p k*(1-p)^k ≤ 840/(k:ℝ) := by
  have hrem : 0 ≤ finiteLogRemainder (1-p) k := by
    have hr : 0 ≤ 1-p := sub_nonneg.mpr hp1
    obtain ⟨hk1,hk8⟩ := hk
    interval_cases k <;> norm_num only [finiteLogRemainder] <;> positivity
  have hnonneg : 0 ≤ (840/(k:ℝ))*p^(9-k)*finiteLogRemainder (1-p) k := by positivity
  linarith [finiteLogWeight_remainder_identity p hk]

theorem finiteLogMoment_source_three (q : ℝ) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) 3 =
      840*thetaCuspLikelihoodThirdCumulant q := by
  unfold thetaCuspLikelihoodThirdCumulant
  simp only [← thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold finiteLogMoment logJetEight
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 (momentSeries (thetaCuspLikelihoodNormalizedMoment q)-
      PowerSeries.C (thetaCuspLikelihoodNormalizedMoment q 0))=0 := by
    simp [centered_series_coeff,centeredMomentCoeff]
  simp (disch := omega) only [coeff_power_small _ h0]
  norm_num [jetPowerCoeff,centered_series_coeff,centeredMomentCoeff,momentSeries]
  all_goals unfold thetaCuspLikelihoodNormalizedMoment
  all_goals ring

theorem finiteLogMoment_source_four (q : ℝ) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) 4 =
      840*thetaCuspLikelihoodFourthCumulant q := by
  unfold thetaCuspLikelihoodFourthCumulant
  simp only [← thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold finiteLogMoment logJetEight
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 (momentSeries (thetaCuspLikelihoodNormalizedMoment q)-
      PowerSeries.C (thetaCuspLikelihoodNormalizedMoment q 0))=0 := by
    simp [centered_series_coeff,centeredMomentCoeff]
  simp (disch := omega) only [coeff_power_small _ h0]
  norm_num [jetPowerCoeff,centered_series_coeff,centeredMomentCoeff,momentSeries]
  all_goals unfold thetaCuspLikelihoodNormalizedMoment
  all_goals ring

theorem finiteLogMoment_source_five (q : ℝ) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) 5 =
      840*thetaCuspLikelihoodFifthCumulant q := by
  unfold thetaCuspLikelihoodFifthCumulant
  simp only [← thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold finiteLogMoment logJetEight
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 (momentSeries (thetaCuspLikelihoodNormalizedMoment q)-
      PowerSeries.C (thetaCuspLikelihoodNormalizedMoment q 0))=0 := by
    simp [centered_series_coeff,centeredMomentCoeff]
  simp (disch := omega) only [coeff_power_small _ h0]
  norm_num [jetPowerCoeff,centered_series_coeff,centeredMomentCoeff,momentSeries]
  all_goals unfold thetaCuspLikelihoodNormalizedMoment
  all_goals ring

theorem finiteLogMoment_source_six (q : ℝ) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) 6 =
      840*thetaCuspLikelihoodSixthCumulant q := by
  unfold thetaCuspLikelihoodSixthCumulant
  simp only [← thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold finiteLogMoment logJetEight
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 (momentSeries (thetaCuspLikelihoodNormalizedMoment q)-
      PowerSeries.C (thetaCuspLikelihoodNormalizedMoment q 0))=0 := by
    simp [centered_series_coeff,centeredMomentCoeff]
  simp (disch := omega) only [coeff_power_small _ h0]
  norm_num [jetPowerCoeff,centered_series_coeff,centeredMomentCoeff,momentSeries]
  all_goals unfold thetaCuspLikelihoodNormalizedMoment
  all_goals ring

theorem finiteLogMoment_source_seven (q : ℝ) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) 7 =
      840*thetaCuspLikelihoodSeventhCumulant q := by
  unfold thetaCuspLikelihoodSeventhCumulant
  simp only [← thetaCuspLikelihoodNormalizedMoment_one_eq_mean]
  unfold finiteLogMoment logJetEight
  simp only [map_sub,map_add,PowerSeries.coeff_C_mul]
  have h0 : PowerSeries.coeff 0 (momentSeries (thetaCuspLikelihoodNormalizedMoment q)-
      PowerSeries.C (thetaCuspLikelihoodNormalizedMoment q 0))=0 := by
    simp [centered_series_coeff,centeredMomentCoeff]
  simp (disch := omega) only [coeff_power_small _ h0]
  norm_num [jetPowerCoeff,centered_series_coeff,centeredMomentCoeff,momentSeries]
  all_goals unfold thetaCuspLikelihoodNormalizedMoment
  all_goals ring

def likelihoodCumulantEight (q : ℝ) (j : ℕ) : ℝ :=
  if j=8 then thetaCuspLikelihoodEighthCumulant q else likelihoodCumulantSeven q j

theorem finiteLogMoment_source (q : ℝ) {j : ℕ} (hj2 : 2 ≤ j) (hj8 : j ≤ 8) :
    finiteLogMoment (thetaCuspLikelihoodNormalizedMoment q) j=840*likelihoodCumulantEight q j := by
  interval_cases j
  · simpa [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant] using
      finiteLogMoment_source_two q
  · simpa [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant] using
      finiteLogMoment_source_three q
  · simpa [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant] using
      finiteLogMoment_source_four q
  · simpa [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant] using
      finiteLogMoment_source_five q
  · simpa [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant] using
      finiteLogMoment_source_six q
  · simpa [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant] using
      finiteLogMoment_source_seven q
  · simpa [likelihoodCumulantEight,likelihoodCumulantSeven,likelihoodCumulant] using
      finiteLogMoment_source_eight q

theorem spectralPowerMoment_one (m : ℕ → ℝ) {j : ℕ} (hj : j ≤ 8) :
    spectralPowerMoment m 1 j=m j := by
  interval_cases j <;> norm_num [spectralPowerMoment,momentSeries] <;> ring

theorem spectralPowerMoment_succ (m : ℕ → ℝ) (k : ℕ) {j : ℕ} (hj : j ≤ 8) :
    spectralPowerMoment m (k+1) j=momentConvolution m (spectralPowerMoment m k) j := by
  unfold spectralPowerMoment momentConvolution
  rw [pow_succ',PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  interval_cases j <;>
    norm_num [momentSeries,Finset.sum_range_succ,Nat.choose,Nat.factorial] <;> ring

theorem spectralPowerMoment_two (m : ℕ → ℝ) {j : ℕ} (hj : j ≤ 8) :
    spectralPowerMoment m 2 j=momentConvolution m m j := by
  rw [show 2=1+1 by rfl,spectralPowerMoment_succ m 1 hj]
  unfold momentConvolution
  apply Finset.sum_congr rfl
  intro i hi
  rw [spectralPowerMoment_one m (by omega : j-i ≤ 8)]

def growthTransferFunctional (q : ℝ) (m : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6,
    ((growthCoefficient q (j+2)*slopeNumerator q 3-
      q*growthCoefficientJet q (j+2)*growthNumerator q 3)*m (j+2)+
    q*growthCoefficient q (j+2)*growthNumerator q 3*m (j+3))

theorem growthTransferFunctional_point (q t : ℝ) :
    growthTransferFunctional q (fun j => t^j)=growthTransferKernel q t := by
  unfold growthTransferFunctional growthTransferKernel growthScore growthScoreJet
  simp only [Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show j+3=(j+2)+1 by omega,pow_succ]
  ring

theorem growthTransferFunctional_finite_decomposition (q : ℝ) (m : ℕ → ℝ) :
    growthTransferFunctional q (finiteLogMoment m) =
      finiteLogWeight (m 0) 1*growthTransferFunctional q (spectralPowerMoment m 1)-
      finiteLogWeight (m 0) 2*growthTransferFunctional q (spectralPowerMoment m 2)+
      finiteLogWeight (m 0) 3*growthTransferFunctional q (spectralPowerMoment m 3)-
      finiteLogWeight (m 0) 4*growthTransferFunctional q (spectralPowerMoment m 4)+
      finiteLogWeight (m 0) 5*growthTransferFunctional q (spectralPowerMoment m 5)-
      finiteLogWeight (m 0) 6*growthTransferFunctional q (spectralPowerMoment m 6)+
      finiteLogWeight (m 0) 7*growthTransferFunctional q (spectralPowerMoment m 7)-
      finiteLogWeight (m 0) 8*growthTransferFunctional q (spectralPowerMoment m 8) := by
  unfold growthTransferFunctional
  simp only [Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [finiteLogMoment_decomposition m (by omega : j+2 ≠ 0),
    finiteLogMoment_decomposition m (by omega : j+3 ≠ 0)]
  ring

theorem growthTransferFunctional_source_decomposition (q : ℝ) :
    840*growthTransferFunctional q (likelihoodCumulantEight q) =
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 1*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 1)-
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 2*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 2)+
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 3*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 3)-
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 4*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 4)+
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 5*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 5)-
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 6*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 6)+
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 7*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 7)-
      finiteLogWeight (thetaCuspLikelihoodNormalizedMoment q 0) 8*
        growthTransferFunctional q (spectralPowerMoment (thetaCuspLikelihoodNormalizedMoment q) 8) := by
  rw [← growthTransferFunctional_finite_decomposition]
  unfold growthTransferFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
  rw [finiteLogMoment_source q (by omega : 2 ≤ j+2) (by omega : j+2 ≤ 8),
    finiteLogMoment_source q (by omega : 2 ≤ j+3) (by omega : j+3 ≤ 8)]
  ring

end
end RHTower.ThetaCuspDefect
