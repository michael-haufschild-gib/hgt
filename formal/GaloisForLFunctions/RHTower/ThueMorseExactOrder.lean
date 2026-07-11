import GaloisForLFunctions.RHTower.ThueMorseFlankEnergyDischarge
import GaloisForLFunctions.RHTower.GammaInvGrowth
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Quadratic growth of the Thue--Morse Mellin carrier

The positive radial lower bound from `ThueMorseMellinFlatness` becomes a sharp quadratic lower
bound on the negative real axis after the logarithmic Mellin change of variables.  This module
formalizes that transport.  It is the lower-growth half of the exact order-two theorem; no
Hadamard-order wrapper or asymptotic Prop is assumed.
-/

noncomputable section

namespace RHTower

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal Topology

/-- The positive logarithmic source defining the Mellin carrier on the negative real axis is
integrable at every real Laplace parameter. -/
theorem thueMorseLogSource_integrable (r : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp (r * y) * thueMorseKernel (Real.exp (-y))) := by
  have hconv : MellinConvergent thueMorseMellinKernel ((-r : ℝ) : ℂ) :=
    thueMorseMellinKernel_isMellinFlatKernel.mellinConvergent ((-r : ℝ) : ℂ)
  have hc := integrable_logMellinPullback_of_mellinConvergent
    thueMorseMellinKernel (-r) hconv
  have hr := hc.re
  apply hr.congr
  filter_upwards with y
  simp only [neg_neg, thueMorseMellinKernel, Complex.real_smul]
  norm_cast

theorem thueMorseLogSource_nonneg (r y : ℝ) :
    0 ≤ Real.exp (r * y) * thueMorseKernel (Real.exp (-y)) :=
  mul_nonneg (Real.exp_pos _).le (thueMorseKernel_nonneg _)

private theorem quadratic_laplace_window_lower {r y : ℝ}
    (hy : y ∈ Icc (Real.log 2 * (r - 3 / 2))
      (Real.log 2 * (r - 3 / 2) + 1)) :
    Real.log 2 / 2 * (r - 3 / 2) ^ 2 - 1 / (2 * Real.log 2) ≤
      -y ^ 2 / (2 * Real.log 2) + (r - 3 / 2) * y := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let y0 := Real.log 2 * (r - 3 / 2)
  have hy0 : y0 ≤ y := hy.1
  have hy1 : y ≤ y0 + 1 := hy.2
  have hsq : (y - y0) ^ 2 ≤ 1 := by nlinarith
  have hden : 0 < 2 * Real.log 2 := by positivity
  have hleft : Real.log 2 / 2 * (r - 3 / 2) ^ 2 - 1 / (2 * Real.log 2) =
      ((Real.log 2) ^ 2 * (r - 3 / 2) ^ 2 - 1) / (2 * Real.log 2) := by
    field_simp
  have hright : -y ^ 2 / (2 * Real.log 2) + (r - 3 / 2) * y =
      (-y ^ 2 + 2 * Real.log 2 * (r - 3 / 2) * y) / (2 * Real.log 2) := by
    field_simp
  rw [hleft, hright]
  apply (div_le_div_iff_of_pos_right hden).2
  dsimp [y0] at hsq
  nlinarith

private theorem thueMorseLogSource_window_lower {r y : ℝ}
    (hr : 3 / 2 ≤ r)
    (hy : y ∈ Icc (Real.log 2 * (r - 3 / 2))
      (Real.log 2 * (r - 3 / 2) + 1)) :
    thueMorseRadialLowerConstant *
        Real.exp (Real.log 2 / 2 * (r - 3 / 2) ^ 2 -
          1 / (2 * Real.log 2)) ≤
      Real.exp (r * y) * thueMorseKernel (Real.exp (-y)) := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 ≤ y := by
    have : 0 ≤ Real.log 2 * (r - 3 / 2) := mul_nonneg hL.le (by linarith)
    linarith [hy.1]
  have hradial := thueMorseKernel_radial_quadratic_lower hy0
  have hquad := quadratic_laplace_window_lower hy
  calc
    thueMorseRadialLowerConstant *
        Real.exp (Real.log 2 / 2 * (r - 3 / 2) ^ 2 -
          1 / (2 * Real.log 2)) ≤
      thueMorseRadialLowerConstant *
        Real.exp (-y ^ 2 / (2 * Real.log 2) + (r - 3 / 2) * y) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hquad)
            thueMorseRadialLowerConstant_pos.le
    _ = Real.exp (r * y) *
        (thueMorseRadialLowerConstant *
          Real.exp (-y ^ 2 / (2 * Real.log 2) - 3 * y / 2)) := by
            have harg : -y ^ 2 / (2 * Real.log 2) + (r - 3 / 2) * y =
                r * y + (-y ^ 2 / (2 * Real.log 2) - 3 * y / 2) := by ring
            rw [harg, Real.exp_add]
            ring
    _ ≤ Real.exp (r * y) * thueMorseKernel (Real.exp (-y)) :=
      mul_le_mul_of_nonneg_left hradial (Real.exp_pos _).le

/-- **Sharp quadratic lower growth of the Mellin carrier.**  A unit interval around the Laplace
saddle point gives the explicit lower bound on the negative real axis. -/
theorem thueMorseMellin_neg_real_lower {r : ℝ} (hr : 3 / 2 ≤ r) :
    thueMorseRadialLowerConstant *
        Real.exp (Real.log 2 / 2 * (r - 3 / 2) ^ 2 -
          1 / (2 * Real.log 2)) ≤
      (mellin thueMorseMellinKernel ((-r : ℝ) : ℂ)).re := by
  let f : ℝ → ℝ := fun y => Real.exp (r * y) * thueMorseKernel (Real.exp (-y))
  let c : ℝ := thueMorseRadialLowerConstant *
    Real.exp (Real.log 2 / 2 * (r - 3 / 2) ^ 2 - 1 / (2 * Real.log 2))
  let S : Set ℝ := Icc (Real.log 2 * (r - 3 / 2))
    (Real.log 2 * (r - 3 / 2) + 1)
  have hf : Integrable f := thueMorseLogSource_integrable r
  have hnonneg : ∀ y, 0 ≤ f y := thueMorseLogSource_nonneg r
  have hset : c ≤ ∫ y in S, f y := by
    have hSfinite : volume S ≠ ∞ := by simp [S]
    have hcint : IntegrableOn (fun _ : ℝ => c) S := integrableOn_const hSfinite
    have hfint : IntegrableOn f S := hf.integrableOn
    have hmono : (∫ y in S, c) ≤ ∫ y in S, f y := by
      apply setIntegral_mono_on hcint hfint measurableSet_Icc
      intro y hy
      exact thueMorseLogSource_window_lower hr hy
    have hvol : volume S = 1 := by
      simp [S, Real.volume_Icc]
    have hconst : (∫ y in S, c) = c := by
      rw [setIntegral_const]
      simp [Measure.real, hvol]
    rw [hconst] at hmono
    exact hmono
  have hfull : (∫ y in S, f y) ≤ ∫ y, f y :=
    setIntegral_le_integral hf (Eventually.of_forall hnonneg)
  rw [mellin_thueMorse_neg_real_eq_realIntegral]
  norm_num
  simpa [c, f] using hset.trans hfull

theorem thueMorseMellin_neg_real_norm_lower {r : ℝ} (hr : 3 / 2 ≤ r) :
    thueMorseRadialLowerConstant *
        Real.exp (Real.log 2 / 2 * (r - 3 / 2) ^ 2 -
          1 / (2 * Real.log 2)) ≤
      ‖mellin thueMorseMellinKernel ((-r : ℝ) : ℂ)‖ :=
  (thueMorseMellin_neg_real_lower hr).trans (Complex.re_le_norm _)

/-! ## The entire Dirichlet continuation and its half-integer lower sequence -/

/-- The actual entire continuation of the shifted signed Thue--Morse Dirichlet series. -/
def thueMorseEntireDirichlet (s : ℂ) : ℂ :=
  (Complex.Gamma s)⁻¹ * mellin thueMorseMellinKernel s

theorem thueMorseEntireDirichlet_differentiable :
    Differentiable ℂ thueMorseEntireDirichlet :=
  Complex.differentiable_one_div_Gamma.mul
    thueMorseMellinKernel_isMellinFlatKernel.mellin_differentiable

/-- On the half-plane of absolute convergence the entire continuation is the original `LSeries`. -/
theorem thueMorseEntireDirichlet_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    thueMorseEntireDirichlet s = LSeries thueMorseDirichletCoeff s := by
  rw [thueMorseEntireDirichlet,
    mellin_thueMorseMellinKernel_eq_gamma_mul_LSeries hs]
  field_simp [Complex.Gamma_ne_zero_of_re_pos (by linarith)]

/-- Fixed positive reciprocal-Gamma norm at the first negative half-integer. -/
def gammaHalfInvConstant : ℝ :=
  ‖(Complex.Gamma ((-(1 / 2 : ℝ) : ℝ) : ℂ))⁻¹‖

theorem gammaHalfInvConstant_pos : 0 < gammaHalfInvConstant := by
  rw [gammaHalfInvConstant, norm_pos_iff]
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  norm_num at hre
  have htwo : (2 : ℝ) * (m : ℝ) = 1 := by linarith
  have htwoNat : 2 * m = 1 := by exact_mod_cast htwo
  omega

/-- Reciprocal Gamma does not erode the negative-half-integer lower sequence: its norm is bounded
below by the fixed first value. -/
theorem gamma_neg_half_inv_norm_lower (n : ℕ) :
    gammaHalfInvConstant ≤
      ‖(Complex.Gamma ((-((n : ℝ) + 1 / 2) : ℝ) : ℂ))⁻¹‖ := by
  induction n with
  | zero => norm_num [gammaHalfInvConstant]
  | succ n ih =>
      let z : ℂ := ((-(((n + 1 : ℕ) : ℝ) + 1 / 2) : ℝ) : ℂ)
      have hz : z ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp [z] at hre
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      have hrec := Complex.Gamma_add_one z hz
      have hzinv : (Complex.Gamma z)⁻¹ =
          z * (Complex.Gamma (z + 1))⁻¹ := by
        calc
          (Complex.Gamma z)⁻¹ = z * (z * Complex.Gamma z)⁻¹ := by
            field_simp [hz]
          _ = z * (Complex.Gamma (z + 1))⁻¹ := by rw [hrec]
      have hzNorm : 1 ≤ ‖z‖ := by
        dsimp [z]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by
          have hn0 : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by positivity
          linarith : -(((n + 1 : ℕ) : ℝ) + 1 / 2) ≤ 0)]
        have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        linarith
      have hmono :
          ‖(Complex.Gamma ((-((n : ℝ) + 1 / 2) : ℝ) : ℂ))⁻¹‖ ≤
            ‖(Complex.Gamma z)⁻¹‖ := by
        rw [hzinv, norm_mul]
        have hshift : z + 1 = ((-((n : ℝ) + 1 / 2) : ℝ) : ℂ) := by
          dsimp [z]
          push_cast
          ring
        rw [hshift]
        nlinarith [norm_nonneg
          ((Complex.Gamma ((-((n : ℝ) + 1 / 2) : ℝ) : ℂ))⁻¹)]
      exact ih.trans hmono

/-- **Quadratic lower sequence for the entire Dirichlet continuation.**  At every negative
half-integer past the first, reciprocal Gamma retains a fixed positive fraction of the Mellin
carrier's sharp quadratic lower bound. -/
theorem thueMorseEntireDirichlet_neg_half_norm_lower {n : ℕ} (hn : 1 ≤ n) :
    gammaHalfInvConstant * thueMorseRadialLowerConstant *
        Real.exp (Real.log 2 / 2 * (((n : ℝ) + 1 / 2) - 3 / 2) ^ 2 -
          1 / (2 * Real.log 2)) ≤
      ‖thueMorseEntireDirichlet (((-((n : ℝ) + 1 / 2) : ℝ) : ℂ))‖ := by
  let r : ℝ := (n : ℝ) + 1 / 2
  have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : 3 / 2 ≤ r := by dsimp [r]; linarith
  have hG := gamma_neg_half_inv_norm_lower n
  have hH := thueMorseMellin_neg_real_norm_lower hr
  have hnonneg : 0 ≤ thueMorseRadialLowerConstant *
      Real.exp (Real.log 2 / 2 * (r - 3 / 2) ^ 2 -
        1 / (2 * Real.log 2)) :=
    mul_nonneg thueMorseRadialLowerConstant_pos.le (Real.exp_pos _).le
  have hmul := mul_le_mul hG hH hnonneg (norm_nonneg _)
  simpa [thueMorseEntireDirichlet, r, norm_mul, mul_assoc] using hmul

/-! ## Sharp whole-plane upper bound for the Mellin carrier -/

/-- Natural binary-prefix depth adapted to a complex Mellin parameter. -/
def thueMorseGrowthIndex (s : ℂ) : ℕ := ⌈‖s‖⌉₊ + 1

/-- The adapted binary-prefix depth is at least one unit beyond the Mellin radius. -/
theorem growthIndex_ge_norm (s : ℂ) :
    ‖s‖ + 1 ≤ (thueMorseGrowthIndex s : ℝ) := by
  dsimp [thueMorseGrowthIndex]
  push_cast
  simpa [add_comm] using add_le_add_right (Nat.le_ceil ‖s‖) 1

/-- The adapted binary-prefix depth costs less than two units beyond the Mellin radius. -/
theorem growthIndex_lt_norm_add_two (s : ℂ) :
    (thueMorseGrowthIndex s : ℝ) < ‖s‖ + 2 := by
  dsimp [thueMorseGrowthIndex]
  push_cast
  linarith [Nat.ceil_lt_add_one (norm_nonneg s)]

private theorem thueMorse_mellin_integrand_le_flat {s : ℂ} {x : ℝ}
    (hx : x ∈ Ioc (0 : ℝ) 1) :
    ‖(x : ℂ) ^ (s - 1) • thueMorseMellinKernel x‖ ≤
      thueMorseFlatConstant (thueMorseGrowthIndex s) := by
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2
  let m := thueMorseGrowthIndex s
  have hm : ‖s‖ + 1 ≤ (m : ℝ) := growthIndex_ge_norm s
  have hsre : -‖s‖ ≤ s.re := (abs_le.mp (Complex.abs_re_le_norm s)).1
  have hexp : 0 ≤ s.re - 1 + (m : ℝ) := by linarith
  have hK : ‖thueMorseMellinKernel x‖ ≤ thueMorseFlatConstant m * x ^ m :=
    (thueMorseMellinKernel_bound m x hx0 hx1).trans
      (thueMorseFiniteKernel_flat_bound m hx0.le)
  have hpow : x ^ (s.re - 1) * x ^ m ≤ 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0]
    exact Real.rpow_le_one hx0.le hx1 hexp
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re,
    Complex.one_re]
  calc
    x ^ (s.re - 1) * ‖thueMorseMellinKernel x‖
        ≤ x ^ (s.re - 1) * (thueMorseFlatConstant m * x ^ m) :=
          mul_le_mul_of_nonneg_left hK (Real.rpow_nonneg hx0.le _)
    _ = thueMorseFlatConstant m * (x ^ (s.re - 1) * x ^ m) := by ring
    _ ≤ thueMorseFlatConstant m * 1 :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg (by norm_num) _)
    _ = thueMorseFlatConstant m := mul_one _

private theorem thueMorse_mellin_integrand_le_gamma {s : ℂ} {x : ℝ}
    (hx : x ∈ Ioi (1 : ℝ)) :
    ‖(x : ℂ) ^ (s - 1) • thueMorseMellinKernel x‖ ≤
      x ^ (thueMorseGrowthIndex s : ℝ) * Real.exp (-x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx1 : 1 ≤ x := hx.le
  let m := thueMorseGrowthIndex s
  have hm : s.re - 1 ≤ (m : ℝ) := by
    have hsre : s.re ≤ ‖s‖ := Complex.re_le_norm s
    have hmn := growthIndex_ge_norm s
    linarith
  have hKreal : ‖thueMorseMellinKernel x‖ ≤ Real.exp (-x) := by
    rw [thueMorseMellinKernel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (thueMorseKernel_nonneg x)]
    exact thueMorseKernel_le_exp_neg hx0
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re,
    Complex.one_re]
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_le hx1 hm) hKreal (norm_nonneg _)
      (Real.rpow_nonneg hx0.le _)

private theorem integral_gamma_majorant (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ (m : ℝ) * Real.exp (-x) = (m.factorial : ℝ) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := (m : ℝ)) (b := (1 : ℝ))
    (by norm_num) (by exact lt_of_lt_of_le neg_one_lt_zero (Nat.cast_nonneg m)) (by norm_num)
  simpa [Real.rpow_one, Real.one_rpow, Real.Gamma_nat_eq_factorial] using h

private theorem gamma_majorant_integrable (m : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ (m : ℝ) * Real.exp (-x)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent
    (s := (m : ℝ) + 1) (by positivity)
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [add_sub_cancel_right]
  exact mul_comm _ _

/-- Explicit whole-plane bound for the Mellin carrier.  The binary prefix contributes the exact
quadratic-scale constant; the exponential tail contributes only a factorial. -/
theorem thueMorseMellin_norm_le_flat_add_factorial (s : ℂ) :
    ‖mellin thueMorseMellinKernel s‖ ≤
      thueMorseFlatConstant (thueMorseGrowthIndex s) +
        (thueMorseGrowthIndex s).factorial := by
  let m := thueMorseGrowthIndex s
  let f : ℝ → ℝ := fun x =>
    ‖(x : ℂ) ^ (s - 1) • thueMorseMellinKernel x‖
  let g : ℝ → ℝ := fun x => x ^ (m : ℝ) * Real.exp (-x)
  have hsint : IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (s - 1) • thueMorseMellinKernel x) (Ioi 0) :=
    thueMorseMellinKernel_isMellinFlatKernel.mellinConvergent s
  have hfint : IntegrableOn f (Ioi 0) := hsint.norm
  have hfsmall : IntegrableOn f (Ioc 0 1) :=
    hfint.mono_set Ioc_subset_Ioi_self
  have hflarge : IntegrableOn f (Ioi 1) :=
    hfint.mono_set (Ioi_subset_Ioi zero_le_one)
  have hcint : IntegrableOn (fun _ : ℝ => thueMorseFlatConstant m) (Ioc 0 1) :=
    integrableOn_const (by simp)
  have hgint : IntegrableOn g (Ioi 0) := gamma_majorant_integrable m
  have hglarg : IntegrableOn g (Ioi 1) :=
    hgint.mono_set (Ioi_subset_Ioi zero_le_one)
  have hsmall : ∫ x in Ioc (0 : ℝ) 1, f x ≤ thueMorseFlatConstant m := by
    calc
      ∫ x in Ioc (0 : ℝ) 1, f x
          ≤ ∫ _x in Ioc (0 : ℝ) 1, thueMorseFlatConstant m := by
            apply setIntegral_mono_on hfsmall hcint measurableSet_Ioc
            intro x hx
            exact thueMorse_mellin_integrand_le_flat hx
      _ = thueMorseFlatConstant m := by simp
  have hlarge : ∫ x in Ioi (1 : ℝ), f x ≤ (m.factorial : ℝ) := by
    calc
      ∫ x in Ioi (1 : ℝ), f x ≤ ∫ x in Ioi (1 : ℝ), g x := by
        apply setIntegral_mono_on hflarge hglarg measurableSet_Ioi
        intro x hx
        exact thueMorse_mellin_integrand_le_gamma hx
      _ ≤ ∫ x in Ioi (0 : ℝ), g x := by
        apply setIntegral_mono_set hgint
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
          exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
        · exact Filter.Eventually.of_forall fun x hx => zero_lt_one.trans hx
      _ = (m.factorial : ℝ) := integral_gamma_majorant m
  calc
    ‖mellin thueMorseMellinKernel s‖
        ≤ ∫ x in Ioi (0 : ℝ), f x := by
          rw [mellin]
          exact norm_integral_le_integral_norm _
    _ = (∫ x in Ioc (0 : ℝ) 1, f x) + ∫ x in Ioi (1 : ℝ), f x := by
      rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hfsmall hflarge,
        Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    _ ≤ thueMorseFlatConstant m + (m.factorial : ℝ) := add_le_add hsmall hlarge
    _ = thueMorseFlatConstant (thueMorseGrowthIndex s) +
        (thueMorseGrowthIndex s).factorial := rfl

/-- Sharp quadratic whole-plane envelope for the Mellin carrier.  The coefficient of
`‖s‖²` in the exponent is exactly `log 2 / 2`; the remaining term is of factorial scale
`O(‖s‖ log ‖s‖)`. -/
theorem thueMorseMellin_norm_le_exp_quadratic (s : ℂ) :
    ‖mellin thueMorseMellinKernel s‖ ≤
      2 * Real.exp
        (Real.log 2 / 2 * (‖s‖ + 2) ^ 2 +
          (‖s‖ + 2) * Real.log (‖s‖ + 2)) := by
  let m := thueMorseGrowthIndex s
  let R := ‖s‖ + 2
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1nat : 1 ≤ m := by
    dsimp [m, thueMorseGrowthIndex]
    omega
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1nat
  have hR1 : (1 : ℝ) ≤ R := by dsimp [R]; linarith [norm_nonneg s]
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hmR : (m : ℝ) ≤ R := (growthIndex_lt_norm_add_two s).le
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg hR1
  have hlog : Real.log (m : ℝ) ≤ Real.log R :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hm1) hmR
  have hmulLog : (m : ℝ) * Real.log (m : ℝ) ≤ R * Real.log R :=
    mul_le_mul hmR hlog hlogm hR0.le
  have htri : (m : ℝ) * ((m : ℝ) - 1) ≤ R ^ 2 := by
    nlinarith
  have hA0 : 0 ≤ Real.log 2 / 2 * R ^ 2 := by positivity
  have hflat : thueMorseFlatConstant m ≤
      Real.exp (Real.log 2 / 2 * R ^ 2) := by
    rw [thueMorseFlatConstant_eq_exp]
    apply Real.exp_le_exp.mpr
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hfacpow : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
    exact_mod_cast Nat.factorial_le_pow m
  have hpowexp : (m : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (m : ℝ)) := by
    calc
      (m : ℝ) ^ m = Real.exp (Real.log (m : ℝ)) ^ m := by
        rw [Real.exp_log (lt_of_lt_of_le zero_lt_one hm1)]
      _ = Real.exp ((m : ℝ) * Real.log (m : ℝ)) :=
        (Real.exp_nat_mul _ _).symm
  have hfac : (m.factorial : ℝ) ≤ Real.exp (R * Real.log R) := by
    calc
      (m.factorial : ℝ) ≤ (m : ℝ) ^ m := hfacpow
      _ = Real.exp ((m : ℝ) * Real.log (m : ℝ)) := hpowexp
      _ ≤ Real.exp (R * Real.log R) := Real.exp_le_exp.mpr hmulLog
  have hflat' : thueMorseFlatConstant m ≤
      Real.exp (Real.log 2 / 2 * R ^ 2 + R * Real.log R) := by
    exact hflat.trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_right (mul_nonneg hR0.le hlogR)))
  have hfac' : (m.factorial : ℝ) ≤
      Real.exp (Real.log 2 / 2 * R ^ 2 + R * Real.log R) := by
    exact hfac.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hA0))
  calc
    ‖mellin thueMorseMellinKernel s‖
        ≤ thueMorseFlatConstant m + (m.factorial : ℝ) :=
          thueMorseMellin_norm_le_flat_add_factorial s
    _ ≤ 2 * Real.exp (Real.log 2 / 2 * R ^ 2 + R * Real.log R) := by
      nlinarith
    _ = 2 * Real.exp
        (Real.log 2 / 2 * (‖s‖ + 2) ^ 2 +
          (‖s‖ + 2) * Real.log (‖s‖ + 2)) := rfl

/-- **Unconditional sharp quadratic upper bound for the entire Dirichlet continuation.**
The first factor is the explicit order-one reciprocal-Gamma envelope; the second has quadratic
coefficient exactly `log 2 / 2`.  Together with
`thueMorseEntireDirichlet_neg_half_norm_lower`, this supplies both sides of exact order two without
an assumed growth interface. -/
theorem thueMorseEntireDirichlet_norm_le_exact_order_two_envelope (s : ℂ) :
    ‖thueMorseEntireDirichlet s‖ ≤
      (‖s‖ * Real.exp (‖Real.eulerMascheroniConstant‖ * ‖s‖) *
        ((1 + ‖s‖) ^ (HilbertSchmidt.gammaGrowthIndex s) *
          Real.exp
            (‖s‖ * (1 + Real.log (HilbertSchmidt.gammaGrowthIndex s)) + 3 * ‖s‖))) *
      (2 * Real.exp
        (Real.log 2 / 2 * (‖s‖ + 2) ^ 2 +
          (‖s‖ + 2) * Real.log (‖s‖ + 2))) := by
  rw [thueMorseEntireDirichlet, norm_mul]
  exact mul_le_mul (HilbertSchmidt.norm_Gamma_inv_le_weierstrass_envelope s)
    (thueMorseMellin_norm_le_exp_quadratic s) (norm_nonneg _)
    (by positivity)

end RHTower
