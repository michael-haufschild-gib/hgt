import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Uniform error in one row of a finite-resolution gap measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open Set MeasureTheory

/-- The right endpoint can lie between mesh points. At most the leftmost weight is lost. -/
private theorem row_sandwich {z R : ℝ} (hR : 0 ≤ R) {f : ℝ → ℝ}
    (hf : AntitoneOn f (Ici z)) (hn : ∀ y, 0 ≤ f y) :
    let S := ∑ i ∈ Finset.range ⌊R⌋₊, f (z + ((i+1:ℕ):ℝ))
    S ≤ (∫ y in z..z+R, f y) ∧ (∫ y in z..z+R, f y) ≤ S+f z := by
  let d := ⌊R⌋₊
  have hlow : (d:ℝ) ≤ R := Nat.floor_le hR
  have hhigh : R ≤ ((d+1:ℕ):ℝ) := by
    rw [Nat.cast_add_one]
    exact (Nat.lt_floor_add_one R).le
  have hi {y : ℝ} (hy : z ≤ y) : IntervalIntegrable f volume z y := by
    apply AntitoneOn.intervalIntegrable
    rw [uIcc_of_le hy]
    exact hf.mono (fun _ h => h.1)
  have hm {b c : ℝ} (hb : z ≤ b) (hc : b ≤ c) :
      (∫ y in z..b, f y) ≤ ∫ y in z..c, f y :=
    intervalIntegral.integral_mono_interval le_rfl hb hc (Filter.Eventually.of_forall hn) (hi (hb.trans hc))
  have hsmall : AntitoneOn f (Icc z (z+d)) := hf.mono (fun _ h => h.1)
  have hlarge : AntitoneOn f (Icc z (z+((d+1:ℕ):ℝ))) := hf.mono (fun _ h => h.1)
  constructor
  · exact hsmall.sum_le_integral.trans (hm (le_add_of_nonneg_right (Nat.cast_nonneg d)) (by linarith only [hlow]))
  · have hu := (hm (le_add_of_nonneg_right hR) (by linarith only [hhigh])).trans hlarge.integral_le_sum
    simpa only [Finset.sum_range_succ',Nat.cast_zero,add_zero] using hu

/-- Unnormalized Gibbs mass in the row n of the band 0 < log(m/n) ≤ t. -/
def positiveGapRow (h t : ℝ) (n : ℕ+) : ℝ :=
  ∑ i ∈ Finset.range ⌊(Real.exp t-1)*(n.val:ℝ)⌋₊,
    Real.exp (-(1+h)*Real.log ((n.val:ℝ)+((i+1:ℕ):ℝ)))

/-- Approximating a whole row by its integral costs at most the diagonal weight, uniformly in the band width. -/
theorem positive_gap_row_estimate {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) (n : ℕ+) :
    let I := (n.val:ℝ)^(-h) * (1-Real.exp (-h*t))/h
    0 ≤ I-positiveGapRow h t n ∧ I-positiveGapRow h t n ≤ Real.exp (-(1+h)*energy n) := by
  let z : ℝ := n.val
  let f := fun y : ℝ => Real.exp (-(1+h)*Real.log y)
  have hz : 0 < z := Nat.cast_pos.mpr n.pos
  have hmono : AntitoneOn f (Ici z) := by
    intro a ha b _ hab
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (Real.log_le_log (hz.trans_le ha) hab) (by linarith)
  have hE := Real.one_le_exp ht
  have hbound : z ≤ Real.exp t*z := le_mul_of_one_le_left hz.le hE
  have he : z+(Real.exp t-1)*z = Real.exp t*z := by ring
  have hs := row_sandwich (mul_nonneg (sub_nonneg.mpr hE) hz.le) hmono (fun y => (Real.exp_pos _).le)
  dsimp only at hs
  rw [he] at hs
  have hzero : (0:ℝ) ∉ uIcc z (Real.exp t*z) := by
    rw [uIcc_of_le hbound]
    exact fun hz0 => hz.not_ge hz0.1
  have hpow : (Real.exp t)^(-h) = Real.exp (-h*t) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,mul_comm]
  have hInt : (∫ y in z..Real.exp t*z, f y) = z^(-h)*(1-Real.exp (-h*t))/h := by
    calc
      _ = ∫ y in z..Real.exp t*z, y^(-(1+h)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hbound] at hy
        change Real.exp (-(1+h)*Real.log y) = y^(-(1+h))
        rw [Real.rpow_def_of_pos (hz.trans_le hy.1)]
        exact congrArg Real.exp (mul_comm _ _)
      _ = _ := by
        rw [integral_rpow (Or.inr ⟨by linarith,hzero⟩),
          show -(1+h)+1 = -h by ring,Real.mul_rpow (Real.exp_pos _).le hz.le,hpow]
        ring
  rw [hInt] at hs
  change 0 ≤ z^(-h)*(1-Real.exp (-h*t))/h - positiveGapRow h t n ∧
    z^(-h)*(1-Real.exp (-h*t))/h - positiveGapRow h t n ≤ f z
  change positiveGapRow h t n ≤ _ ∧ _ ≤ positiveGapRow h t n + f z at hs
  exact ⟨sub_nonneg.mpr hs.1,by linarith only [hs.2]⟩

#print axioms positive_gap_row_estimate

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
