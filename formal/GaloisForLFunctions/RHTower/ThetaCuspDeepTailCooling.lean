import GaloisForLFunctions.RHTower.ThetaCuspDeepTailCalibration
import GaloisForLFunctions.RHTower.ThetaCuspSharpFiniteCooling

/-!
# Actual derivatives and sharp signed bounds for the complete deep tail

The fixed n≥3 measure retains every atom. Its support edge eight and the
exact scalar cooling scores give (16q)^n times the calibrated error scale
for every n≤10 throughout q≥37/10.
-/

open MeasureTheory Filter Topology Set
namespace RHTower
noncomputable section
set_option maxHeartbeats 1200000

/-- The compact comparison threshold lies strictly above the modular center. -/
theorem thetaCusp_pos_of_thirtySevenTenths_le {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) : 0 < x := by
  by_contra hn
  have hx : x ≤ 0 := le_of_not_gt hn
  have he : Real.exp (2*x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hp := mul_le_mul_of_nonneg_left he Real.pi_pos.le
  simp only [thetaCuspSingleAtomReflectionScale, Nat.cast_one, one_pow, mul_one] at hq
  nlinarith [Real.pi_lt_d2]

/-- The literal likelihood remainder after retaining both first source atoms. -/
def thetaCuspDeepLikelihoodRemainder (x : ℝ) : ℝ :=
  thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) 0

/-- A scale-weighted moment of the literal higher-likelihood measure. -/
def thetaCuspDeepCoolingMoment (m : ℕ) (x : ℝ) : ℝ :=
  thetaCuspSingleAtomReflectionScale 1 x^m *
    thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) m

/-- Finite triangular derivative recurrence for the scale-weighted moments. -/
def thetaCuspDeepCoolingJet : ℕ → ℕ → ℝ → ℝ
  | 0, m, x => thetaCuspDeepCoolingMoment m x
  | n+1, m, x => 2*(m : ℝ)*thetaCuspDeepCoolingJet n m x - 2*thetaCuspDeepCoolingJet n (m+1) x

/-- Logarithmic source differentiation closes on adjacent weighted moments. -/
theorem hasDerivAt_thetaCuspDeepCoolingMoment (m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspDeepCoolingMoment m)
      (2*(m : ℝ)*thetaCuspDeepCoolingMoment m x - 2*thetaCuspDeepCoolingMoment (m+1) x) x := by
  have hq := hasDerivAt_thetaCuspSingleAtomReflectionScale_one x
  have hM := (hasDerivAt_thetaCuspDeepTailMoment m
    (thetaCuspLikelihoodCoordinate_pos hx.le)).comp x (hasDerivAt_thetaCuspLikelihoodCoordinate x)
  have h := (hq.pow m).mul hM
  apply h.congr_deriv
  cases m with
  | zero => simp [thetaCuspDeepCoolingMoment]; ring
  | succ m =>
    simp only [thetaCuspDeepCoolingMoment, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, Pi.pow_apply, Function.comp_apply, pow_succ]
    ring

/-- Every finite cooling jet differentiates to its successor. -/
theorem hasDerivAt_thetaCuspDeepCoolingJet (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspDeepCoolingJet n m) (thetaCuspDeepCoolingJet (n+1) m x) x := by
  induction n generalizing m with
  | zero => exact hasDerivAt_thetaCuspDeepCoolingMoment m hx
  | succ n ih =>
    exact ((ih m).const_mul (2*(m : ℝ))).sub ((ih (m+1)).const_mul 2)

/-- The finite recurrence is the actual all-order source derivative. -/
theorem iteratedDeriv_thetaCuspDeepCoolingMoment (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (thetaCuspDeepCoolingMoment m) x = thetaCuspDeepCoolingJet n m x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have he : iteratedDeriv n (thetaCuspDeepCoolingMoment m) =ᶠ[𝓝 x] thetaCuspDeepCoolingJet n m := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (hasDerivAt_thetaCuspDeepCoolingJet n m hx).deriv

/-- Every derivative of the complete deep likelihood is its exact cooling recurrence. -/
theorem iteratedDeriv_thetaCuspDeepLikelihoodRemainder (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n thetaCuspDeepLikelihoodRemainder x = thetaCuspDeepCoolingJet n 0 x := by
  have he : thetaCuspDeepLikelihoodRemainder = thetaCuspDeepCoolingMoment 0 := by
    funext y
    simp only [thetaCuspDeepLikelihoodRemainder, thetaCuspDeepCoolingMoment, pow_zero, one_mul]
  rw [he, iteratedDeriv_thetaCuspDeepCoolingMoment n 0 hx]

/-- Every finite scalar cooling score is integrable against the complete tilted deep-tail measure. -/
theorem integrable_laplaceCoolingJet_mul_exp_deep (n m : ℕ) {x : ℝ}
    (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    Integrable (fun t : ℝ => HTGeometry.laplaceCoolingJet n m
      (thetaCuspSingleAtomReflectionScale 1 x*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
      thetaCuspDeepTailSpectralMeasure := by
  induction n generalizing m with
  | zero =>
    have h := (integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure m hB).const_mul
      (thetaCuspSingleAtomReflectionScale 1 x^m)
    apply h.congr
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet, mul_pow]
    ring
  | succ n ih =>
    apply (((ih m).const_mul (2*(m : ℝ))).sub ((ih (m+1)).const_mul 2)).congr
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet, Pi.sub_apply]
    ring

/-- The actual derivative recurrence is the integral of the exact scalar score. -/
theorem thetaCuspDeepCoolingJet_eq_integral_score (n m : ℕ) {x : ℝ}
    (hB : 0 < thetaCuspLikelihoodCoordinate x) :
    thetaCuspDeepCoolingJet n m x =
      ∫ t : ℝ, HTGeometry.laplaceCoolingJet n m
        (thetaCuspSingleAtomReflectionScale 1 x*t)*Real.exp (-thetaCuspLikelihoodCoordinate x*t)
        ∂thetaCuspDeepTailSpectralMeasure := by
  induction n generalizing m with
  | zero =>
    rw [thetaCuspDeepCoolingJet, thetaCuspDeepCoolingMoment,
      thetaCuspDeepTailMoment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet, mul_pow]
    ring
  | succ n ih =>
    rw [thetaCuspDeepCoolingJet, ih m, ih (m+1), ← integral_const_mul, ← integral_const_mul,
      ← integral_sub ((integrable_laplaceCoolingJet_mul_exp_deep n m hB).const_mul _)
        ((integrable_laplaceCoolingJet_mul_exp_deep n (m+1) hB).const_mul _)]
    apply integral_congr_ae
    filter_upwards with t
    simp only [HTGeometry.laplaceCoolingJet]
    ring

/-- Signed finite cooling preserves positivity and is bounded by the leading spectral moment. -/
theorem thetaCuspDeepCoolingJet_signed_le_leadingMoment {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*thetaCuspDeepCoolingJet n 0 x ∧
    (-1 : ℝ)^n*thetaCuspDeepCoolingJet n 0 x ≤
      (2*thetaCuspSingleAtomReflectionScale 1 x)^n *
        thetaCuspDeepTailMoment (thetaCuspLikelihoodCoordinate x) n := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le hq
  have hB := thetaCuspLikelihoodCoordinate_pos hx.le
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hs := integrable_laplaceCoolingJet_mul_exp_deep n 0 hB
  rw [thetaCuspDeepCoolingJet_eq_integral_score n 0 hB, ← integral_const_mul]
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    have hqt : 18 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds hn hqt).1
    have hm := mul_nonneg hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change 0 ≤ (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    nlinarith only [hm]
  · rw [thetaCuspDeepTailMoment, ← integral_const_mul]
    apply integral_mono_ae (hs.const_mul _)
      ((integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure n hB).const_mul _)
    filter_upwards [ae_eight_le_thetaCuspDeepTailSpectralMeasure] with t ht
    have hqt : 18 ≤ q*t := by nlinarith
    have hb := (HTGeometry.laplaceCoolingJet_signed_bounds hn hqt).2
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-thetaCuspLikelihoodCoordinate x*t)).le
    change (-1 : ℝ)^n*(HTGeometry.laplaceCoolingJet n 0 (q*t)*
      Real.exp (-thetaCuspLikelihoodCoordinate x*t)) ≤
      (2*q)^n*(t^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t))
    calc
      _ ≤ (2*(q*t))^n*Real.exp (-thetaCuspLikelihoodCoordinate x*t) := by nlinarith only [hm]
      _ = _ := by simp only [mul_pow]; ring

/-- Sharp signed bounds for every required derivative of the complete deep likelihood. -/
theorem thetaCuspDeepLikelihoodRemainder_signed_bounds {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 ≤ (-1 : ℝ)^n*iteratedDeriv n thetaCuspDeepLikelihoodRemainder x ∧
    (-1 : ℝ)^n*iteratedDeriv n thetaCuspDeepLikelihoodRemainder x ≤
      (16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  rw [iteratedDeriv_thetaCuspDeepLikelihoodRemainder n (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  have h := thetaCuspDeepCoolingJet_signed_le_leadingMoment hn hq
  refine ⟨h.1, h.2.trans ?_⟩
  have hnr : (n : ℝ) ≤ 10 := by exact_mod_cast hn
  have hd : (n : ℝ)/8 ≤ thetaCuspSingleAtomReflectionScale 1 x-49/20 := by linarith
  have hb := thetaCuspDeepTailMoment_le_errorScale n hd
  have hp := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n by
      apply pow_nonneg
      have : 0 ≤ thetaCuspSingleAtomReflectionScale 1 x := by linarith
      positivity)
  calc
    _ ≤ (2*thetaCuspSingleAtomReflectionScale 1 x)^n*(8^n*thetaCuspDeepTailErrorScale x) := hp
    _ = _ := by rw [← mul_assoc, ← mul_pow]; congr 2; ring

/-- Absolute errors retain the full calibrated n≥3 tail, uniformly through derivative ten. -/
theorem abs_iteratedDeriv_thetaCuspDeepLikelihoodRemainder_le {n : ℕ} (hn : n ≤ 10) {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| ≤
      (16*thetaCuspSingleAtomReflectionScale 1 x)^n*thetaCuspDeepTailErrorScale x := by
  have h := thetaCuspDeepLikelihoodRemainder_signed_bounds hn hq
  have he : |iteratedDeriv n thetaCuspDeepLikelihoodRemainder x| =
      (-1 : ℝ)^n*iteratedDeriv n thetaCuspDeepLikelihoodRemainder x := by
    rw [← abs_of_nonneg h.1, abs_mul, abs_pow]
    norm_num
  rw [he]
  exact h.2

end
end RHTower
