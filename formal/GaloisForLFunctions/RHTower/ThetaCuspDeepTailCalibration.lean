import GaloisForLFunctions.RHTower.ThetaCuspC5SharpTailMeasures
import GaloisForLFunctions.RHTower.ThetaCuspEffectiveLikelihoodCooling

/-!
# Explicit calibration of the complete deep theta likelihood tail

The n ≥ 3 sector has support edge eight. Its full mass at tilt 19/20
is bounded by one millionth using one geometric majorant of the infinite
atom series. Support transport retains this calibration at every order.
-/

namespace RHTower
noncomputable section
open MeasureTheory Set
set_option maxHeartbeats 1500000

/-- The complete deep-tail mass is the sum of all atoms starting at n=3. -/
theorem thetaCuspDeepTailMoment_zero_eq_tsum {B : ℝ} (hB : 0 < B) :
    thetaCuspDeepTailMoment B 0 =
      ∑' k : ℕ, thetaCuspAtomLikelihoodSpectralTerm (k+3) B := by
  have hi := integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure 0 hB
  simp only [pow_zero, one_mul] at hi
  rw [thetaCuspDeepTailMoment, thetaCuspDeepTailSpectralMeasure]
  simp only [pow_zero, one_mul]
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro k
  exact integral_exp_neg_mul_thetaCuspAtomLikelihoodSpectralMeasure (by omega) hB

private theorem quartic_geometric (k : ℕ) : ((k+3 : ℕ) : ℝ)^4 ≤ 81*4^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hstep : ((k : ℝ)+4)^4 ≤ 4*((k : ℝ)+3)^4 := by
      have h : 0 ≤ 3*(k : ℝ)^4+32*(k : ℝ)^3+120*(k : ℝ)^2+176*(k : ℝ)+68 := by positivity
      nlinarith only [h]
    push_cast at ih ⊢
    rw [pow_succ (4 : ℝ) k]
    nlinarith only [hstep, ih]

private theorem exp_gap_step_le : Real.exp (-(343/20 : ℝ)) ≤ 1/100 := by
  have he1 : (27/10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he5 : (100 : ℝ) ≤ Real.exp 5 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10) he1 5
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  have he : (100 : ℝ) ≤ Real.exp (343/20) :=
    he5.trans (Real.exp_le_exp.mpr (by norm_num))
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) he

private theorem exp_gap_base_le : Real.exp (-(98/5 : ℝ)) ≤ 1/260000000 := by
  have he1 : (271/100 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he19 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 271/100) he1 19
  rw [← Real.exp_nat_mul] at he19
  norm_num only [Nat.cast_ofNat, mul_one] at he19
  have he3 : (8/5 : ℝ) ≤ Real.exp (3/5) := by linarith [Real.add_one_le_exp (3/5)]
  have hp := mul_le_mul he19 he3 (by norm_num : (0 : ℝ) ≤ 8/5) (Real.exp_pos 19).le
  rw [← Real.exp_add] at hp
  have he : (260000000 : ℝ) ≤ Real.exp (98/5) := by
    norm_num at hp
    linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 260000000) he

private theorem atom_base_bound (k : ℕ) :
    thetaCuspAtomLikelihoodSpectralTerm (k+3) (19/20) ≤
      243*Real.exp (-(98/5 : ℝ))*(1/25)^k := by
  let n : ℝ := k+3
  let g := thetaCuspLikelihoodGap (k+3)
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hn4 : 0 ≤ n^4 := pow_nonneg hn0 4
  have hid : thetaCuspAtomLikelihoodSpectralTerm (k+3) (19/20) =
      Real.exp (-(49/20)*g)*((49/19)*n^4-(30/19)*n^2) := by
    calc
      _ = (Real.exp (-(3/2)*g)*Real.exp (-(19/20)*g))*
          (n^4+(30/19)*n^2*g) := by
        unfold thetaCuspAtomLikelihoodSpectralTerm
        dsimp [n, g]
        push_cast
        ring
      _ = _ := by
        rw [← Real.exp_add]
        dsimp [n, g, thetaCuspLikelihoodGap]
        push_cast
        ring_nf
  have hp : (49/19)*n^4-(30/19)*n^2 ≤ 3*n^4 := by nlinarith [sq_nonneg n]
  have hk2 : (k : ℝ) ≤ (k : ℝ)^2 := by
    exact_mod_cast Nat.le_self_pow (by norm_num : 2 ≠ 0) k
  have hgap : 8+7*(k : ℝ) ≤ g := by
    dsimp [g, thetaCuspLikelihoodGap]
    push_cast
    nlinarith
  have he : Real.exp (-(49/20)*g) ≤
      Real.exp (-(98/5 : ℝ))*(1/100)^k := by
    calc
      _ ≤ Real.exp (-(98/5 : ℝ))*Real.exp (-(343/20)*(k : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp (-(98/5 : ℝ))*Real.exp (-(343/20 : ℝ))^k := by
        rw [← Real.exp_nat_mul]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.exp_pos _).le exp_gap_step_le k) (Real.exp_pos _).le
  have hquartic : n^4 ≤ 81*4^k := by simpa [n] using quartic_geometric k
  rw [hid]
  calc
    _ ≤ Real.exp (-(49/20)*g)*(3*n^4) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ ≤ (Real.exp (-(98/5 : ℝ))*(1/100)^k)*(3*(81*4^k)) :=
      mul_le_mul he (mul_le_mul_of_nonneg_left hquartic (by norm_num))
        (by positivity) (by positivity)
    _ = 243*Real.exp (-(98/5 : ℝ))*(1/25)^k := by
      have hp : (4 : ℝ)^k*(1/100)^k = (1/25 : ℝ)^k := by rw [← mul_pow]; norm_num
      rw [← hp]
      ring

/-- The complete n≥3 likelihood sector has a fixed exact mass ceiling at tilt 19/20. -/
theorem thetaCuspDeepTailMoment_calibration :
    thetaCuspDeepTailMoment (19/20) 0 ≤ (1/1000000 : ℝ) := by
  have hs : Summable (fun k : ℕ => thetaCuspAtomLikelihoodSpectralTerm (k+3) (19/20)) := by
    have h := (summable_nat_add_iff 1).mpr
      (summable_thetaCuspAtomLikelihoodSpectralTerm (by norm_num : (0 : ℝ) < 19/20))
    simpa only [Nat.add_assoc, Nat.reduceAdd] using h
  have hg : Summable (fun k : ℕ => 243*Real.exp (-(98/5 : ℝ))*(1/25)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/25) (by norm_num)).mul_left _
  have hsum := hs.tsum_le_tsum atom_base_bound hg
  rw [← thetaCuspDeepTailMoment_zero_eq_tsum (by norm_num : (0 : ℝ) < 19/20),
    tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/25) (by norm_num)] at hsum
  have he := exp_gap_base_le
  norm_num at hsum
  linarith

/-- Quantitative error scale of the complete deep likelihood tail. -/
def thetaCuspDeepTailErrorScale (x : ℝ) : ℝ :=
  Real.exp (-8*(thetaCuspSingleAtomReflectionScale 1 x-49/20))/1000000

/-- All deep-tail moments retain the exact calibrated support transport. -/
theorem thetaCuspDeepTailMoment_le_errorScale (m : ℕ) {x : ℝ}
    (hm : (m : ℝ)/8 ≤ thetaCuspSingleAtomReflectionScale 1 x-49/20) :
    thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) m ≤
      8^m*thetaCuspDeepTailErrorScale x := by
  have hcoord : thetaCuspLikelihoodCoordinate x-(19/20) =
      thetaCuspSingleAtomReflectionScale 1 x-49/20 := by
    have h := thetaCuspLikelihoodCoordinate_sub_zero x
    have h0 := thetaCuspLikelihoodCoordinate_zero_eq
    linarith
  have hd : (m : ℝ)/8 ≤ thetaCuspLikelihoodCoordinate x-19/20 := by rwa [hcoord]
  have h := thetaCuspDeepTailMoment_le_eight_pow_mul_exp_support_comparison m
    (by norm_num : (0 : ℝ) < 19/20) hd
  rw [hcoord] at h
  have hcal := mul_le_mul_of_nonneg_left thetaCuspDeepTailMoment_calibration
    (show 0 ≤ (8 : ℝ)^m*Real.exp (-(8*(thetaCuspSingleAtomReflectionScale 1 x-49/20))) by positivity)
  unfold thetaCuspDeepTailErrorScale
  simp only [neg_mul] at h hcal ⊢
  nlinarith only [h, hcal]

end
end RHTower
