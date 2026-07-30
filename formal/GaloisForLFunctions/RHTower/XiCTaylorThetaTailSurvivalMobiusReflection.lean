import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSurvivalMixedCurrent
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMobiusConstraint

open Complex Real MeasureTheory Set Filter Topology Polynomial ArithmeticFunction Nat
open scoped BigOperators

namespace RHTower

noncomputable section

theorem thetaCuspTailSurvival_neg (x : ℝ) :
    thetaCuspTailSurvival (-x) =
      -thetaCuspTailSurvival x + Real.exp (x / 2) + Real.exp (-x / 2) := by
  have hreflection : (fun y : ℝ => thetaCuspTailDerivative 0 (-y)) =
      fun y => thetaCuspTailDerivative 0 y + thetaCuspReflectionMode y := by
    funext y
    simpa [thetaCuspReflectionMode] using thetaCuspTailDerivative_zero_neg y
  have hl := (hasDerivAt_thetaCuspTailDerivative 0 (-x)).comp x (hasDerivAt_neg x)
  have hr := (hasDerivAt_thetaCuspTailDerivative 0 x).add
    (hasDerivAt_thetaCuspReflectionMode x)
  have hl' : HasDerivAt (fun y : ℝ => thetaCuspTailDerivative 0 (-y))
      (-thetaCuspTailDerivative 1 (-x)) x := by
    simpa [Function.comp_def] using hl
  have hr' : HasDerivAt
      (fun y : ℝ => thetaCuspTailDerivative 0 y + thetaCuspReflectionMode y)
      (thetaCuspTailDerivative 1 x + thetaCuspReflectionModeDeriv x) x := by
    simpa using! hr
  rw [hreflection] at hl'
  have h := hl'.unique hr'
  unfold thetaCuspTailSurvival
  unfold thetaCuspReflectionModeDeriv at h
  linarith

theorem exp_neg_half_log_mul_thetaCuspTailSurvival_reflectionModes
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    Real.exp (-(Real.log n) / 2) *
        (Real.exp ((x - Real.log n) / 2) +
          Real.exp (-(x - Real.log n) / 2)) =
      Real.exp (x / 2) / (n : ℝ) + Real.exp (-x / 2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfirst :
      Real.exp (-(Real.log n) / 2) *
          Real.exp ((x - Real.log n) / 2) =
        Real.exp (x / 2) / (n : ℝ) := by
    rw [← Real.exp_add]
    rw [show -(Real.log n) / 2 + (x - Real.log n) / 2 =
        x / 2 - Real.log n by ring]
    rw [Real.exp_sub, Real.exp_log hnR]
  have hsecond :
      Real.exp (-(Real.log n) / 2) *
          Real.exp (-(x - Real.log n) / 2) =
        Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_add, hfirst, hsecond]

theorem coeff_mul_exp_neg_half_log_mul_thetaCuspTailSurvival_neg_add_log
    {n : ℕ} (hn : 0 < n) (c x : ℝ) :
    c * Real.exp (-(Real.log n) / 2) *
        thetaCuspTailSurvival (-x + Real.log n) =
      -(c * Real.exp (-(Real.log n) / 2) *
          thetaCuspTailSurvival (x - Real.log n)) +
        c * Real.exp (x / 2) / (n : ℝ) +
        c * Real.exp (-x / 2) := by
  rw [show -x + Real.log n = -(x - Real.log n) by ring,
    thetaCuspTailSurvival_neg]
  have hmodes :=
    exp_neg_half_log_mul_thetaCuspTailSurvival_reflectionModes hn x
  calc
    c * Real.exp (-(Real.log n) / 2) *
        (-thetaCuspTailSurvival (x - Real.log n) +
          Real.exp ((x - Real.log n) / 2) +
          Real.exp (-(x - Real.log n) / 2)) =
      -(c * Real.exp (-(Real.log n) / 2) *
          thetaCuspTailSurvival (x - Real.log n)) +
        c * (Real.exp (-(Real.log n) / 2) *
          (Real.exp ((x - Real.log n) / 2) +
            Real.exp (-(x - Real.log n) / 2))) := by ring
    _ = _ := by rw [hmodes]; ring

def thetaCuspTailSurvivalBalancedMobiusTranslate
    (N : ℕ) (x : ℝ) : ℝ :=
  finiteMoebiusBalancedCoefficientMoment N (fun n =>
    Real.exp (-(Real.log n) / 2) *
      thetaCuspTailSurvival (x + Real.log n))

def thetaCuspTailSurvivalBalancedMobiusLeftShift
    (N : ℕ) (x : ℝ) : ℝ :=
  finiteMoebiusBalancedCoefficientMoment N (fun n =>
    Real.exp (-(Real.log n) / 2) *
      thetaCuspTailSurvival (x - Real.log n))

theorem thetaCuspTailSurvivalBalancedMobiusTranslate_neg
    (N : ℕ) (x : ℝ) :
    thetaCuspTailSurvivalBalancedMobiusTranslate N (-x) =
      -thetaCuspTailSurvivalBalancedMobiusLeftShift N x := by
  unfold thetaCuspTailSurvivalBalancedMobiusTranslate
    thetaCuspTailSurvivalBalancedMobiusLeftShift
    finiteMoebiusBalancedCoefficientMoment
  have hterm (n : ℕ) (hn : 0 < n) (c : ℝ) :
      c * (Real.exp (-(Real.log n) / 2) *
        thetaCuspTailSurvival (-x + Real.log n)) =
        -(c * (Real.exp (-(Real.log n) / 2) *
          thetaCuspTailSurvival (x - Real.log n))) +
          c * Real.exp (x / 2) / (n : ℝ) +
          c * Real.exp (-x / 2) := by
    simpa only [mul_assoc] using
      coeff_mul_exp_neg_half_log_mul_thetaCuspTailSurvival_neg_add_log hn c x
  rw [show (∑ n ∈ Finset.Icc 1 N,
      moebiusCoeff n *
        (Real.exp (-(Real.log n) / 2) *
          thetaCuspTailSurvival (-x + Real.log n))) =
      ∑ n ∈ Finset.Icc 1 N,
        (-(moebiusCoeff n *
          (Real.exp (-(Real.log n) / 2) *
            thetaCuspTailSurvival (x - Real.log n))) +
          moebiusCoeff n * Real.exp (x / 2) / (n : ℝ) +
          moebiusCoeff n * Real.exp (-x / 2)) by
    apply Finset.sum_congr rfl
    intro n hnmem
    apply hterm n
    exact (Finset.mem_Icc.mp hnmem).1
  ]
  rw [hterm (N + 1) (by omega), hterm (N + 2) (by omega)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have hzeroOne := finiteMoebiusBalancedCoefficientMoment_one N
  have hzeroInv := finiteMoebiusBalancedCoefficientMoment_inv N
  unfold finiteMoebiusBalancedCoefficientMoment at hzeroOne hzeroInv
  simp only [mul_one] at hzeroOne
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    div_eq_mul_inv] at hzeroInv ⊢
  have hhalf : x * (2 : ℝ)⁻¹ = x / 2 := by ring
  have hneghalf : -x * (2 : ℝ)⁻¹ = -x / 2 := by ring
  rw [hhalf, hneghalf]
  have hsumInv :
      (∑ n ∈ Finset.Icc 1 N,
        moebiusCoeff n * Real.exp (x / 2) * (n : ℝ)⁻¹) =
        Real.exp (x / 2) *
          ∑ n ∈ Finset.Icc 1 N, moebiusCoeff n * (n : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  have hsumOne :
      (∑ n ∈ Finset.Icc 1 N,
        moebiusCoeff n * Real.exp (-x / 2)) =
        Real.exp (-x / 2) *
          ∑ n ∈ Finset.Icc 1 N, moebiusCoeff n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    ring
  rw [hsumInv, hsumOne]
  linear_combination Real.exp (x / 2) * hzeroInv +
    Real.exp (-x / 2) * hzeroOne

theorem thetaCuspTailSecondSectionSourceDerivative_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSectionSourceDerivative d z (-x) =
      -thetaCuspTailSecondSectionSourceDerivative d z x := by
  unfold thetaCuspTailSecondSectionSourceDerivative
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  push_cast
  have hpow : (-((x : ℂ))) ^ (2 * k + 1) =
      -((x : ℂ) ^ (2 * k + 1)) := by
    rw [pow_add, pow_mul, pow_add, pow_mul]
    ring
  rw [hpow]
  ring

theorem thetaCuspTailSecondSectionSourceSpectralDerivative_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondSectionSourceSpectralDerivative d z (-x) =
      -thetaCuspTailSecondSectionSourceSpectralDerivative d z x := by
  unfold thetaCuspTailSecondSectionSourceSpectralDerivative
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  push_cast
  have hpow : (-((x : ℂ))) ^ (2 * k + 1) =
      -((x : ℂ) ^ (2 * k + 1)) := by
    rw [pow_add, pow_mul, pow_add, pow_mul]
    ring
  rw [hpow]
  ring

theorem thetaCuspTailSecondCoreAtomSourceDerivative_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondCoreAtomSourceDerivative d z (-x) =
      -thetaCuspTailSecondCoreAtomSourceDerivative d z x := by
  unfold thetaCuspTailSecondCoreAtomSourceDerivative
  rw [thetaCuspTailSecondSectionSourceDerivative_neg]
  ring

theorem thetaCuspTailSecondCoreAtomSourceSpectralDerivative_neg
    (d : ℕ) (z : ℂ) (x : ℝ) :
    thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z (-x) =
      -thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x := by
  unfold thetaCuspTailSecondCoreAtomSourceSpectralDerivative
  rw [thetaCuspTailSecondSectionSourceDerivative_neg,
    thetaCuspTailSecondSectionSourceSpectralDerivative_neg]
  ring

theorem integral_Ioi_balancedMobiusSurvivalLeft_mul_coreAtomSourceDerivative_eq_integral_Iic_right
    (N d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSurvivalBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceDerivative d z x) =
      ∫ x : ℝ in Iic 0,
        (thetaCuspTailSurvivalBalancedMobiusTranslate N x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceDerivative d z x := by
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSurvivalBalancedMobiusTranslate N x : ℂ) *
      thetaCuspTailSecondCoreAtomSourceDerivative d z x
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSurvivalBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceDerivative d z x) =
        ∫ x : ℝ in Ioi 0, f (-x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [f]
          rw [thetaCuspTailSurvivalBalancedMobiusTranslate_neg,
            thetaCuspTailSecondCoreAtomSourceDerivative_neg]
          push_cast
          ring
    _ = ∫ x : ℝ in Iic 0, f x := by
      simpa only [neg_zero] using integral_comp_neg_Ioi 0 f
    _ = _ := rfl

theorem integral_Ioi_balancedMobiusSurvivalLeft_mul_coreAtomSourceSpectralDerivative_eq_integral_Iic_right
    (N d : ℕ) (z : ℂ) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSurvivalBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x) =
      ∫ x : ℝ in Iic 0,
        (thetaCuspTailSurvivalBalancedMobiusTranslate N x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x := by
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSurvivalBalancedMobiusTranslate N x : ℂ) *
      thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x
  calc
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSurvivalBalancedMobiusLeftShift N x : ℂ) *
          thetaCuspTailSecondCoreAtomSourceSpectralDerivative d z x) =
        ∫ x : ℝ in Ioi 0, f (-x) := by
          apply integral_congr_ae
          filter_upwards with x
          dsimp [f]
          rw [thetaCuspTailSurvivalBalancedMobiusTranslate_neg,
            thetaCuspTailSecondCoreAtomSourceSpectralDerivative_neg]
          push_cast
          ring
    _ = ∫ x : ℝ in Iic 0, f x := by
      simpa only [neg_zero] using integral_comp_neg_Ioi 0 f
    _ = _ := rfl

end

end RHTower
