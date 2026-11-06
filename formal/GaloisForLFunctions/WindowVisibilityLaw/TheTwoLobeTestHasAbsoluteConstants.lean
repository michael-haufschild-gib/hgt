import GaloisForLFunctions.WindowVisibilityLaw.TheUniversalVisibilityThreshold
import GaloisForLFunctions.WindowVisibilityLaw.TheSineLocalizerOfATest
import GaloisForLFunctions.VerifiedHeightRungs.TheNormalizedSmoothingKeepsThePoles
import GaloisForLFunctions.RHTower.LowHeightHodgeExclusion

/-!
# The two-lobe test has absolute constants

In a configuration with `N(t,t+1] ≤ A₀ log(|t|+3)`, take a coherent cluster of depth at least `δ` in
a sea of depth at most `σ ≤ δ`. Window positivity at `a` forces

`M_S e^{2(δ−σ)a} ≤ 12000 A₀ log(|γ₀| + 4·10⁸ A₀ log(|γ₀|+3) + 6)`,

with no dependence on `a` or `δ` on the right. The earlier bound carried `2²⁶ δ (2a+2π) e^{2π}` and a
logarithm of size `a`.

The test is the odd pair of narrow bumps `s(u) = w(u−c) − w(u+c)`, `w = (b²−v²)₊^{5/2}`, `b = 1/(2δ)`,
`c = a−b`. Three identities make it sharp:

* its pairing with `sinh(δu)` is `2 sinh(δc) ∫ w(v) cosh(δv) dv`;
* its transform is `2i sin(cz) ŵ(z)`, so sampling it costs only the support length `2b` of `w`;
* its second derivative is a difference of translates, so `testNorm s ≤ 2 testNorm w` carries no
  exponential factor, and the far tail is paid at bounded distance.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower.CCMParityQuartet

/-- The odd pair of bumps at `±c`. -/
def twoLobeTest (b c u : ℝ) : ℝ := sinhTestWeight b (u - c) - sinhTestWeight b (u + c)

theorem twoLobeTest_contDiff (b c : ℝ) : ContDiff ℝ 2 (twoLobeTest b c) := by
  unfold twoLobeTest
  exact ((sinhTestWeight_contDiff b).comp (contDiff_id.sub contDiff_const)).sub
    ((sinhTestWeight_contDiff b).comp (contDiff_id.add contDiff_const))

theorem twoLobeTest_odd (b c u : ℝ) : twoLobeTest b c (-u) = -twoLobeTest b c u := by
  unfold twoLobeTest
  rw [show -u - c = -(u + c) by ring, show -u + c = -(u - c) by ring, sinhTestWeight_even,
    sinhTestWeight_even]
  ring

theorem twoLobeTest_supp {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∀ u, twoLobeTest b c u ≠ 0 → |u| ≤ b + c := by
  intro u hu
  by_contra hn
  rw [not_le] at hn
  apply hu
  have h1 : b < |u - c| := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases abs_cases (u - c) with ⟨h', _⟩ | ⟨h', _⟩ <;>
      linarith only [h, h', hn, hb, hc]
  have h2 : b < |u + c| := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩ <;> rcases abs_cases (u + c) with ⟨h', _⟩ | ⟨h', _⟩ <;>
      linarith only [h, h', hn, hb, hc]
  unfold twoLobeTest
  rw [sinhTestWeight_eq_zero hb h1, sinhTestWeight_eq_zero hb h2, sub_zero]

theorem twoLobeTest_nonneg {b c u : ℝ} (hb : 0 ≤ b) (hbc : b < c) (hu : 0 ≤ u) :
    0 ≤ twoLobeTest b c u := by
  have h2 : b < |u + c| := by
    rw [abs_of_nonneg (by linarith only [hu, hb, hbc])]
    linarith only [hu, hbc]
  unfold twoLobeTest
  rw [sinhTestWeight_eq_zero hb h2, sub_zero]
  exact sinhTestWeight_nonneg _ _

private theorem hasCompactSupport_weight {b : ℝ} (hb : 0 ≤ b) :
    HasCompactSupport (sinhTestWeight b) :=
  hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp hb)

/-- **The pairing with `sinh`.** -/
theorem integral_twoLobeTest_mul_sinh {b : ℝ} (hb : 0 ≤ b) (c δ : ℝ) :
    ∫ u, twoLobeTest b c u * Real.sinh (δ * u) =
      2 * Real.sinh (δ * c) * ∫ v, sinhTestWeight b v * Real.cosh (δ * v) := by
  have hcs := hasCompactSupport_weight hb
  have hcw := (sinhTestWeight_contDiff b).continuous
  have hI : ∀ t : ℝ, Integrable fun v => sinhTestWeight b v * Real.sinh (δ * (v + t)) := fun t =>
    (hcw.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have h1 : ∫ u, sinhTestWeight b (u - c) * Real.sinh (δ * u) =
      ∫ v, sinhTestWeight b v * Real.sinh (δ * (v + c)) := by
    rw [← integral_sub_right_eq_self (fun v => sinhTestWeight b v * Real.sinh (δ * (v + c))) c]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [sub_add_cancel]
  have h2 : ∫ u, sinhTestWeight b (u + c) * Real.sinh (δ * u) =
      ∫ v, sinhTestWeight b v * Real.sinh (δ * (v + -c)) := by
    rw [← integral_add_right_eq_self (fun v => sinhTestWeight b v * Real.sinh (δ * (v + -c))) c]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [add_neg_cancel_right]
  have hsplit : ∫ u, twoLobeTest b c u * Real.sinh (δ * u) =
      (∫ u, sinhTestWeight b (u - c) * Real.sinh (δ * u)) -
        ∫ u, sinhTestWeight b (u + c) * Real.sinh (δ * u) := by
    rw [← integral_sub]
    · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [twoLobeTest]
      ring
    · have := (hI c).comp_sub_right c
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [sub_add_cancel]
    · have := (hI (-c)).comp_add_right c
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [add_neg_cancel_right]
  rw [hsplit, h1, h2, ← integral_sub (hI c) (hI (-c)), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  have e1 : δ * (v + c) = δ * v + δ * c := by ring
  have e2 : δ * (v + -c) = δ * v - δ * c := by ring
  rw [e1, e2, Real.sinh_add, Real.sinh_sub]
  ring

/-- **Translates do not change the test norm.** -/
theorem testNorm_twoLobeTest_le {b : ℝ} (hb : 0 ≤ b) (c : ℝ) :
    testNorm (twoLobeTest b c) ≤ 2 * testNorm (sinhTestWeight b) := by
  let F₁ : ℝ → ℂ := fun v => (sinhTestWeight b v : ℂ)
  have hF₁c : ContDiff ℝ 2 F₁ := Complex.ofRealCLM.contDiff.comp (sinhTestWeight_contDiff b)
  have hd1 : ContDiff ℝ 1 (deriv F₁) := ((contDiff_succ_iff_deriv (n := 1)).mp hF₁c).2.2
  have hF₂c : Continuous (deriv (deriv F₁)) := hd1.continuous_deriv le_rfl
  have hF₂eq : deriv (deriv F₁) = fun v => ((sinhTestWeightDeriv2 b v : ℝ) : ℂ) :=
    deriv_deriv_ofReal_sinhTestWeight b
  have hF₁int : Integrable fun v => ‖F₁ v‖ :=
    hF₁c.continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b)) fun v hv => by
        have : b < |v| := by
          by_contra h
          rw [not_lt] at h
          exact hv (abs_le.mp h)
        simp [F₁, sinhTestWeight_eq_zero hb this])
  have hF₂int : Integrable fun v => ‖deriv (deriv F₁) v‖ :=
    hF₂c.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b)) fun v hv => by
        have : b < |v| := by
          by_contra h
          rw [not_lt] at h
          exact hv (abs_le.mp h)
        rw [hF₂eq]
        simp [sinhTestWeightDeriv2_eq_zero hb this])
  have hshift : ∀ {G : ℝ → ℂ}, Integrable (fun v => ‖G v‖) →
      ∫ u, ‖G (u - c) - G (u + c)‖ ≤ 2 * ∫ v, ‖G v‖ := by
    intro G hG
    have h1 : Integrable fun u => ‖G (u - c)‖ := hG.comp_sub_right c
    have h2 : Integrable fun u => ‖G (u + c)‖ := hG.comp_add_right c
    calc ∫ u, ‖G (u - c) - G (u + c)‖
        ≤ ∫ u, (‖G (u - c)‖ + ‖G (u + c)‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (h1.add h2)
            (Eventually.of_forall fun u => norm_sub_le _ _)
      _ = 2 * ∫ v, ‖G v‖ := by
          rw [integral_add h1 h2, integral_sub_right_eq_self (fun v => ‖G v‖) c,
            integral_add_right_eq_self (fun v => ‖G v‖) c]
          ring
  have hval : (fun u => ((twoLobeTest b c u : ℝ) : ℂ)) = fun u => F₁ (u - c) - F₁ (u + c) := by
    funext u
    simp [twoLobeTest, F₁]
  have hderiv1 : deriv (fun u => F₁ (u - c) - F₁ (u + c)) =
      fun u => deriv F₁ (u - c) - deriv F₁ (u + c) := by
    funext u
    have hd : Differentiable ℝ F₁ := hF₁c.differentiable (by norm_num)
    have h1 : HasDerivAt (fun u => F₁ (u - c)) (deriv F₁ (u - c)) u :=
      (hd (u - c)).hasDerivAt.comp_sub_const u c
    have h2 : HasDerivAt (fun u => F₁ (u + c)) (deriv F₁ (u + c)) u :=
      (hd (u + c)).hasDerivAt.comp_add_const u c
    exact (h1.sub h2).deriv
  have hderiv2 : deriv (fun u => deriv F₁ (u - c) - deriv F₁ (u + c)) =
      fun u => deriv (deriv F₁) (u - c) - deriv (deriv F₁) (u + c) := by
    funext u
    have hd : Differentiable ℝ (deriv F₁) := hd1.differentiable le_rfl
    have h1 : HasDerivAt (fun u => deriv F₁ (u - c)) (deriv (deriv F₁) (u - c)) u :=
      (hd (u - c)).hasDerivAt.comp_sub_const u c
    have h2 : HasDerivAt (fun u => deriv F₁ (u + c)) (deriv (deriv F₁) (u + c)) u :=
      (hd (u + c)).hasDerivAt.comp_add_const u c
    exact (h1.sub h2).deriv
  have htw : testNorm (sinhTestWeight b) =
      (∫ v, ‖F₁ v‖) + ∫ v, ‖deriv (deriv F₁) v‖ := rfl
  rw [htw]
  unfold testNorm
  rw [hval, hderiv1, hderiv2]
  have h1 := hshift hF₁int
  have h2 := hshift hF₂int
  linarith only [h1, h2]

private theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖cexp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    simp
  have h2 : ‖cexp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    simp
  have hle1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hle2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [norm_div, norm_mul, Complex.norm_I, mul_one]
  have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2']
  have := norm_sub_le (cexp (-z * I)) (cexp (z * I))
  rw [h1, h2] at this
  linarith only [this, hle1, hle2]

/-- **The transform of the two-lobe test.** `ŝ(z) = 2i sin(cz) ŵ(z)`. -/
theorem paperFT_twoLobeTest {b : ℝ} (hb : 0 ≤ b) (c : ℝ) (z : ℂ) :
    paperFT (fun u => ((twoLobeTest b c u : ℝ) : ℂ)) z =
      2 * I * (Complex.sin (c * z) * paperFT (fun v => ((sinhTestWeight b v : ℝ) : ℂ)) z) := by
  have hcw : Continuous fun v => ((sinhTestWeight b v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (sinhTestWeight_contDiff b).continuous
  have hcs : HasCompactSupport fun v => ((sinhTestWeight b v : ℝ) : ℂ) :=
    (hasCompactSupport_weight hb).comp_left (g := Complex.ofReal) (by simp)
  rw [← paperFT_sineLift c hcw hcs z]
  simp only [paperFT, sineLift]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [twoLobeTest]
  push_cast
  field_simp

end GaloisForLFunctions.WindowVisibilityLaw
