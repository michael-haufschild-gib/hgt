import GaloisForLFunctions.HTGeometry.HamburgerGeneralFrequencies
import GaloisForLFunctions.HTGeometry.HamburgerFunctionalEquation
import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import Mathlib.MeasureTheory.Group.Convolution

/-!
# Positive-measure and Beurling Hamburger rigidity

Hamburger's theorem (`HamburgerFunctionalEquation`) characterizes `ζ` among Dirichlet
series supported on the positive integers `ℕ + 1`. Without coefficient nonnegativity,
uniqueness fails on `[1, ∞)` for generalized frequencies: real self-dual combinations
of even primitive Dirichlet characters share Riemann's `Γ_ℝ(s)` functional equation on
rescaled lattices `(k + 1) / √q` and can cancel finitely many sub-unit frequencies `[1, ∞)ᶜ`.

This module proves that **nonnegativity restores complete rigidity across all Borel
measures on `[1, ∞)` and all Beurling prime measures on `(1, ∞)`**:

1. **Measure-theoretic Hamburger rigidity** (`measure_eq_of_measureTheta_relation`,
   `measure_eq_of_completed_functional_equation`):
   Let `ν` be any nonnegative Borel measure on `ℝ` with `ν (Iio 1) = 0` and
   `Integrable (fun u : ℝ => 1 / u ^ 2) ν` (which automatically forces `SigmaFinite ν`).
   If `θ_ν(x) = ∫ e^{-π u² x} dν(u)` satisfies Riemann's degree-one theta law
   `θ_ν(x) = x^{-1/2} θ_ν(1/x) + α + β x^{-1/2}` for `x > 0`, then `β = -α`,
   `α.im = 0`, `-2 α.re ≥ 0`, every continuous, singular, or non-integer component of
   `ν` vanishes, and
   `ν = ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac (k + 1))`.

   *Mechanism:* Pairing the half-plane Laplace identity on `t = ε + i τ` (`ε → 0⁺`)
   against the collar-blind Fejér kernel `2 (1 - |τ|)` on `[-1, 1]` annihilates the
   Poisson side (`ν((-∞, 1)) = 0` and `1 - |±1| = 0`), cancels the reflected simple-pole
   residues (`-ρ + ρ = 0`), and leaves `2 ∫ (sin(π u)/(π u))² dν(u) = 0`. Once `ν` is
   forced onto `ℕ + 1`, imaginary-axis periodicity of `measureDual ν` and residue
   extraction (`coeff_eq_of_hamburgerSeries_periodic_re_pos`) equalize all integer weights.

2. **Beurling prime-measure selectivity** (`eq_riemannPrimeMeasure_of_beurling_theta_relation`,
   `eq_riemannPrimeMeasure_of_beurling_functional_equation`):
   For any Borel measure `P` on `(1, ∞)` (`P (Iic 1) = 0`) with finite inverse-square
   moment, its multiplicative convolution exponential
   `beurlingIntegerMeasure P = ∑_{m ≥ 0} (m!)⁻¹ P^{* m}` satisfies Riemann's degree-one
   theta law (or completed `Γ_ℝ(s)` functional equation) if and only if `P` is identically
   equal to Riemann's prime-power measure `∑_{n ≥ 2} (Λ(n) / log n) δ_n`, with forced
   polar constants `α = -1/2` and `β = 1/2`.
-/

open Complex MeasureTheory Filter Topology Set Function
open scoped ENNReal MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open GaloisForLFunctions.HTGeometry

/-! ## 1. Automatic `σ`-finiteness and theta-transform regularity -/

/-- A measure vanishing on `(-∞, 1)` concentrates almost everywhere on `[1, ∞)`. -/
theorem ae_one_le_of_measure_Iio_one_eq_zero {ν : Measure ℝ} (hsupp : ν (Iio 1) = 0) :
    ∀ᵐ u ∂ν, (1 : ℝ) ≤ u := by
  rw [ae_iff]
  simp only [not_le]
  exact hsupp

/-- Any Borel measure on `ℝ` vanishing on `(-∞, 1)` with integrable `u ↦ 1 / u²` is
automatically `σ`-finite, requiring no external typeclass hypothesis. -/
theorem sigmaFinite_of_measure_Iio_one_eq_zero {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) :
    SigmaFinite ν := by
  refine ⟨⟨{
    set := fun k => if k = 0 then Iio 1 else Icc 1 (k : ℝ)
    set_mem := fun _ => trivial
    finite := fun k => by
      rcases eq_or_ne k 0 with rfl | hk
      · simp [hsupp]
      · simp only [hk, ↓reduceIte]
        have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
        have hc0 : ENNReal.ofReal (1 / (k : ℝ) ^ 2) ≠ 0 :=
          ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
        have hle : ENNReal.ofReal (1 / (k : ℝ) ^ 2) * ν (Icc 1 (k : ℝ)) ≤
            ∫⁻ u in Icc 1 (k : ℝ), ‖(1 / u ^ 2 : ℝ)‖ₑ ∂ν := by
          rw [← setLIntegral_const]
          refine setLIntegral_mono' measurableSet_Icc fun u hu => ?_
          have hu1 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu.1
          have hbound : 1 / (k : ℝ) ^ 2 ≤ 1 / u ^ 2 :=
            one_div_le_one_div_of_le (sq_pos_of_pos hu1) (pow_le_pow_left₀ hu1.le hu.2 2)
          calc ENNReal.ofReal (1 / (k : ℝ) ^ 2)
              ≤ ENNReal.ofReal (1 / u ^ 2) := ENNReal.ofReal_le_ofReal hbound
            _ = ‖(1 / u ^ 2 : ℝ)‖ₑ := by
                rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hfin : ∫⁻ u in Icc 1 (k : ℝ), ‖(1 / u ^ 2 : ℝ)‖ₑ ∂ν < ⊤ :=
          lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hmom.hasFiniteIntegral
        exact ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hle hfin).ne hc0
    spanning := by
      ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      rcases lt_or_ge x 1 with hx | hx
      · exact ⟨0, by simp [hx]⟩
      · obtain ⟨k, hk⟩ := exists_nat_gt x
        have hk0 : k ≠ 0 := fun h0 => by rw [h0, Nat.cast_zero] at hk; linarith
        exact ⟨k, by simp [hk0, hx, hk.le]⟩
  }⟩⟩

/-- On `[1, ∞)`, integrability of `u^{-3/2}` implies integrability of `1 / u²`. -/
theorem integrable_inv_sq_of_integrable_rpow_neg_three_halves {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν) :
    Integrable (fun u : ℝ => 1 / u ^ 2) ν := by
  refine hmom.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have heq : 1 / u ^ 2 = u ^ (-2 : ℝ) := by
    rw [one_div, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le,
      Real.rpow_natCast]
  rw [heq]
  exact Real.rpow_le_rpow_of_exponent_le hu (by norm_num)

/-- Theta transform `θ_ν(x) = ∫ e^{-π u² x} dν(u)` of a Borel measure on `ℝ`. -/
def measureTheta (ν : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ u : ℝ, ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) ∂ν

/-- Mellin–Dirichlet integral `D_ν(s) = ∫ u^{-s} dν(u)` of a Borel measure on `ℝ`. -/
def measureDirichlet (ν : Measure ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ, (u : ℂ) ^ (-s) ∂ν

/-- Partial-fraction transform `L_ν(t) = ∫ t / (π (u² + t²)) dν(u)` on `Re t > 0`. -/
def measureSeries (ν : Measure ℝ) (t : ℂ) : ℂ :=
  ∫ u : ℝ, t / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2)) ∂ν

/-- Exponential Laplace dual `F_ν(t) = ∫ e^{-2π u t} dν(u)` on `Re t > 0`. -/
def measureDual (ν : Measure ℝ) (t : ℂ) : ℂ :=
  ∫ u : ℝ, cexp (-(2 * Real.pi * (u : ℂ) * t)) ∂ν

private theorem norm_exp_theta_integrand_le {u x : ℝ} (hu : 1 ≤ u) (hx : 0 < x) :
    ‖((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ)‖ ≤ (Real.pi * x)⁻¹ * (1 / u ^ 2) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hw : 0 < Real.pi * u ^ 2 * x := by positivity
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    show -Real.pi * u ^ 2 * x = -(Real.pi * u ^ 2 * x) by ring]
  calc Real.exp (-(Real.pi * u ^ 2 * x))
      ≤ (Real.pi * u ^ 2 * x)⁻¹ := FreqHamburger.exp_neg_le_inv hw
    _ = (Real.pi * x)⁻¹ * (1 / u ^ 2) := by field_simp

theorem integrable_measureTheta_integrand {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun u : ℝ => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ)) ν := by
  refine (hmom.const_mul ((Real.pi * x)⁻¹)).mono' (by fun_prop) ?_
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  exact norm_exp_theta_integrand_le hu hx

theorem norm_measureTheta_le {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {x : ℝ} (hx : 0 < x) :
    ‖measureTheta ν x‖ ≤ (Real.pi * x)⁻¹ * ∫ u : ℝ, 1 / u ^ 2 ∂ν := by
  unfold measureTheta
  calc ‖∫ u : ℝ, ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) ∂ν‖
      ≤ ∫ u : ℝ, (Real.pi * x)⁻¹ * (1 / u ^ 2) ∂ν := by
        refine norm_integral_le_of_norm_le (hmom.const_mul _) ?_
        filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
        exact norm_exp_theta_integrand_le hu hx
    _ = (Real.pi * x)⁻¹ * ∫ u : ℝ, 1 / u ^ 2 ∂ν := integral_const_mul _ _

theorem continuousOn_measureTheta {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) :
    ContinuousOn (measureTheta ν) (Ioi 0) := by
  intro x₀ hx₀
  have hx0 : (0 : ℝ) < x₀ := hx₀
  refine ContinuousAt.continuousWithinAt ?_
  change Tendsto (measureTheta ν) (𝓝 x₀) (𝓝 (measureTheta ν x₀))
  unfold measureTheta
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => (Real.pi * (x₀ / 2))⁻¹ * (1 / u ^ 2))
    (Eventually.of_forall fun x => by fun_prop) ?_ (hmom.const_mul _)
    (Eventually.of_forall fun u => (by fun_prop : Continuous fun x : ℝ =>
      ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ)).continuousAt)
  filter_upwards [Ioi_mem_nhds (half_lt_self hx0)] with x hx
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  have hx_pos : 0 < x := lt_trans (half_pos hx0) hx
  refine (norm_exp_theta_integrand_le hu hx_pos).trans
    (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact inv_anti₀ (mul_pos Real.pi_pos (half_pos hx0))
    (mul_le_mul_of_nonneg_left (le_of_lt hx) Real.pi_pos.le)

theorem measureTheta_im_eq_zero (ν : Measure ℝ) (x : ℝ) :
    (measureTheta ν x).im = 0 := by
  rw [measureTheta, integral_complex_ofReal, ofReal_im]

/-! ## 2. Mellin transform of `measureTheta` on `Re s > 0` -/

private theorem ofReal_sq_cpow_neg_div_two {u : ℝ} (hu : 0 < u) (s : ℂ) :
    ((u ^ 2 : ℝ) : ℂ) ^ (-(s / 2)) = (u : ℂ) ^ (-s) := by
  have hu2 : ((u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sq_pos_of_pos hu).ne'
  have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [Complex.cpow_def_of_ne_zero hu2, Complex.cpow_def_of_ne_zero hu0,
    ← Complex.ofReal_log (sq_pos_of_pos hu).le, ← Complex.ofReal_log hu.le,
    Real.log_pow]
  congr 1
  push_cast
  ring

/-- When `u ↦ u^{-Re s}` is `ν`-integrable (`Re s > 0`), `measureTheta ν` is Mellin-convergent
at `s / 2` and its Mellin transform equals `Γ_ℝ(s) measureDirichlet ν s`. -/
theorem hasMellin_measureTheta {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) {s : ℂ} (hs : 0 < s.re)
    (hmom_s : Integrable (fun u : ℝ => u ^ (-s.re)) ν)
    (hmom2 : Integrable (fun u : ℝ => 1 / u ^ 2) ν) :
    MellinConvergent (measureTheta ν) (s / 2) ∧
      mellin (measureTheta ν) (s / 2) = Complex.Gammaℝ s * measureDirichlet ν s := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom2
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | 1 ≤ p.1 ∧ 0 < p.2}
  have hS : MeasurableSet S :=
    (measurableSet_Ici.preimage measurable_fst).inter (measurableSet_Ioi.preimage measurable_snd)
  let G : ℝ → ℝ → ℂ := fun u x =>
    S.indicator (fun p => (p.2 : ℂ) ^ (s / 2 - 1) *
      ((Real.exp (-Real.pi * p.1 ^ 2 * p.2) : ℝ) : ℂ)) (u, x)
  have hG_meas : AEStronglyMeasurable (uncurry G) (ν.prod (volume.restrict (Ioi 0))) := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (s / 2 - 1) *
        ((Real.exp (-Real.pi * p.1 ^ 2 * p.2) : ℝ) : ℂ)) S := by
      intro p hp
      refine ContinuousAt.continuousWithinAt ?_
      refine ((continuousAt_ofReal_cpow_const _ _ (Or.inr hp.2.ne')).comp
        continuous_snd.continuousAt).mul ?_
      exact (by fun_prop : Continuous fun q : ℝ × ℝ =>
        ((Real.exp (-Real.pi * q.1 ^ 2 * q.2) : ℝ) : ℂ)).continuousAt
    exact (aestronglyMeasurable_indicator_iff hS).mpr (hcont.aestronglyMeasurable hS)
  -- On the quadrant `S` the indicator is the bare Mellin–theta integrand.
  have hG_eq : ∀ u x : ℝ, 1 ≤ u → 0 < x →
      G u x = (x : ℂ) ^ (s / 2 - 1) * ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) :=
    fun u x hu hx => Set.indicator_of_mem (show (u, x) ∈ S from ⟨hu, hx⟩) _
  -- The same integrand written as a rescaled `expNegPi` Mellin integrand.
  have hG_mellin : ∀ u x : ℝ, 1 ≤ u → 0 < x →
      G u x = (x : ℂ) ^ (s / 2 - 1) • expNegPi (u ^ 2 * x) := by
    intro u x hu hx
    rw [hG_eq u x hu hx, expNegPi, smul_eq_mul,
      show -(Real.pi * (u ^ 2 * x)) = -Real.pi * u ^ 2 * x by ring]
  have hG_int_prod : Integrable (uncurry G) (ν.prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hG_meas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu2 : 0 < u ^ 2 := by positivity
      have hm : MellinConvergent (fun x : ℝ => expNegPi (u ^ 2 * x)) (s / 2) :=
        (MellinConvergent.comp_mul_left (f := expNegPi) hu2).mpr
          (mellinConvergent_exp_neg_pi_mul (by simp; linarith))
      exact IntegrableOn.congr_fun hm (fun x hx => (hG_mellin u x hu hx).symm) measurableSet_Ioi
    · set c : ℝ := Real.pi ^ (-(s.re / 2)) * Real.Gamma (s.re / 2) with hc_def
      refine (hmom_s.const_mul c).congr ?_
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hnorm_eq : ∀ x ∈ Ioi (0 : ℝ),
          ‖G u x‖ = x ^ (s.re / 2 - 1) * Real.exp (-((Real.pi * u ^ 2) * x)) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := hx
        have hre : (s / 2 - 1).re = s.re / 2 - 1 := by simp [sub_re, div_ofNat_re]
        rw [hG_eq u x hu hx0, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hre,
          show -Real.pi * u ^ 2 * x = -((Real.pi * u ^ 2) * x) by ring]
      show c * u ^ (-s.re) = ∫ y in Ioi (0 : ℝ), ‖G u y‖
      rw [setIntegral_congr_fun measurableSet_Ioi hnorm_eq,
        Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) (by positivity)]
      -- `(1 / (π u²))^{Re s / 2} = π^{-Re s / 2} u^{-Re s}`
      have hrp : (1 / (Real.pi * u ^ 2)) ^ (s.re / 2) =
          Real.pi ^ (-(s.re / 2)) * u ^ (-s.re) := by
        rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
          Real.mul_rpow Real.pi_pos.le (sq_nonneg u), ← Real.rpow_natCast u 2,
          ← Real.rpow_mul hu0.le,
          show ((2 : ℕ) : ℝ) * -(s.re / 2) = -s.re by push_cast; ring]
      rw [hrp, hc_def]
      ring
  have hinner_x : ∀ x ∈ Ioi (0 : ℝ),
      ∫ u : ℝ, G u x ∂ν = (x : ℂ) ^ (s / 2 - 1) • measureTheta ν x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hae : (fun u : ℝ => G u x) =ᵐ[ν]
        fun u : ℝ => (x : ℂ) ^ (s / 2 - 1) * ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      exact hG_eq u x hu hx0
    rw [integral_congr_ae hae, integral_const_mul, measureTheta, smul_eq_mul]
  have hmconv : MellinConvergent (measureTheta ν) (s / 2) :=
    IntegrableOn.congr_fun hG_int_prod.integral_prod_right hinner_x measurableSet_Ioi
  refine ⟨hmconv, ?_⟩
  unfold mellin
  rw [← setIntegral_congr_fun measurableSet_Ioi hinner_x,
    (integral_integral_swap hG_int_prod).symm]
  have hae_u : (fun u : ℝ => ∫ x in Ioi (0 : ℝ), G u x) =ᵐ[ν]
      fun u : ℝ => Complex.Gammaℝ s * (u : ℂ) ^ (-s) := by
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu0
    have hcongr : ∫ x in Ioi (0 : ℝ), G u x =
        mellin (fun x : ℝ => expNegPi (u ^ 2 * x)) (s / 2) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => hG_mellin u x hu hx
    rw [hcongr, mellin_comp_mul_left expNegPi (s / 2) hu2, mellin_expNegPi_half hs,
      smul_eq_mul, ofReal_sq_cpow_neg_div_two hu0 s, mul_comm]
  rw [integral_congr_ae hae_u, integral_const_mul, measureDirichlet]

/-! ## 3. Pole parity and half-plane Laplace identity for measures -/

/-- Self-dual degree-one theta reflection on a real-valued measure theta transform forces
antisymmetric real polar constants `β = -α` and `α.im = 0`. -/
theorem pole_parity_of_measureTheta_relation {ν : Measure ℝ} {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    β = -α ∧ α.im = 0 ∧ β.im = 0 := by
  have h1 := htheta 1 one_pos
  rw [Complex.ofReal_one, Complex.one_cpow, inv_one, one_mul, mul_one] at h1
  have hβα : β = -α := by linear_combination -h1
  have h4pow : ((4 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 / 2 := by
    have := ofReal_sq_cpow_neg_half (c := 2) (by norm_num)
    norm_num at this ⊢
    exact this
  have h4 := htheta 4 (by norm_num)
  rw [h4pow, hβα] at h4
  have h4_re : measureTheta ν 4 = (1 / 2 : ℂ) * measureTheta ν (4 : ℝ)⁻¹ + (1 / 2 : ℂ) * α := by
    linear_combination h4
  have him := congrArg Complex.im h4_re
  simp only [measureTheta_im_eq_zero, add_im, mul_im, one_div, inv_re, re_ofNat, normSq_ofNat,
    inv_im, im_ofNat, neg_zero, zero_div, mul_zero] at him
  have hαim : α.im = 0 := by linarith
  have hβim : β.im = 0 := by rw [hβα, neg_im, hαim, neg_zero]
  exact ⟨hβα, hαim, hβim⟩

private theorem exp_neg_le_six_div_cube {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ 6 / y ^ 3 := by
  have h := Real.sum_le_exp_of_nonneg hy.le 4
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial,
    Nat.cast_one, div_one, pow_one] at h
  norm_num at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  have hy2 : 0 ≤ y ^ 2 := sq_nonneg y
  nlinarith

/-- On the positive real axis, Laplace integration of the measure theta relation gives
`measureSeries ν t = measureDual ν t + α / (π t) + β`. -/
theorem measureSeries_eq_of_measureTheta_relation_ofReal {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℝ} (ht : 0 < t) :
    measureSeries ν t = measureDual ν t + α / (Real.pi * t) + β := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  let S : Set (ℝ × ℝ) := {p : ℝ × ℝ | 1 ≤ p.1 ∧ 0 < p.2}
  have hS : MeasurableSet S :=
    (measurableSet_Ici.preimage measurable_fst).inter (measurableSet_Ioi.preimage measurable_snd)
  -- Left side Fubini
  let G₁ : ℝ → ℝ → ℂ := fun u x =>
    S.indicator (fun p => ((Real.exp (-(Real.pi * (p.1 ^ 2 + t ^ 2)) * p.2) : ℝ) : ℂ)) (u, x)
  have hG₁_meas : AEStronglyMeasurable (uncurry G₁) (ν.prod (volume.restrict (Ioi 0))) := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (p.1 ^ 2 + t ^ 2)) * p.2) : ℝ) : ℂ)) := by fun_prop
    exact (aestronglyMeasurable_indicator_iff hS).mpr (hc.continuousOn.aestronglyMeasurable hS)
  have hG₁_eq : ∀ u x : ℝ, 1 ≤ u → 0 < x →
      G₁ u x = ((Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) : ℝ) : ℂ) :=
    fun u x hu hx => Set.indicator_of_mem (show (u, x) ∈ S from ⟨hu, hx⟩) _
  have hG₁_int : Integrable (uncurry G₁) (ν.prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hG₁_meas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
      exact IntegrableOn.congr_fun (integrableOn_Ioi_exp_neg_mul hk).ofReal
        (fun x hx => (hG₁_eq u x hu hx).symm) measurableSet_Ioi
    · refine (hmom.const_mul (1 / Real.pi)).mono' ?_ ?_
      · exact hG₁_meas.norm.integral_prod_right'
      · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
        have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
        have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
        have hn : ∀ x ∈ Ioi (0 : ℝ),
            ‖G₁ u x‖ = Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) := by
          intro x hx
          rw [hG₁_eq u x hu hx, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
        show ‖∫ y in Ioi (0 : ℝ), ‖G₁ u y‖‖ ≤ 1 / Real.pi * (1 / u ^ 2)
        rw [setIntegral_congr_fun measurableSet_Ioi hn, integral_Ioi_exp_neg_mul hk,
          Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hk]
        calc (1 : ℝ) = 1 / Real.pi * (1 / u ^ 2) * (Real.pi * u ^ 2) := by field_simp
          _ ≤ 1 / Real.pi * (1 / u ^ 2) * (Real.pi * (u ^ 2 + t ^ 2)) := by
              gcongr; nlinarith [sq_nonneg t]
  -- Dual side Fubini
  let G₂ : ℝ → ℝ → ℂ := fun u x =>
    S.indicator (fun p => ((p.2 ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(Real.pi * p.1 ^ 2 / p.2) - Real.pi * t ^ 2 * p.2) : ℝ) : ℂ)) (u, x)
  have hG₂_meas : AEStronglyMeasurable (uncurry G₂) (ν.prod (volume.restrict (Ioi 0))) := by
    have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.2 ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(Real.pi * p.1 ^ 2 / p.2) - Real.pi * t ^ 2 * p.2) : ℝ) : ℂ)) S := by
      intro p hp
      refine ContinuousAt.continuousWithinAt ?_
      refine Complex.continuous_ofReal.continuousAt.comp ?_
      refine ((Real.continuousAt_rpow_const _ _ (Or.inl hp.2.ne')).comp
        continuous_snd.continuousAt).mul ?_
      refine Real.continuous_exp.continuousAt.comp ?_
      exact (((continuous_const.mul (continuous_fst.pow 2)).continuousAt.div
        continuous_snd.continuousAt hp.2.ne').neg).sub
        (continuous_const.mul continuous_snd).continuousAt
    exact (aestronglyMeasurable_indicator_iff hS).mpr (hc.aestronglyMeasurable hS)
  have hG₂_eq : ∀ u x : ℝ, 1 ≤ u → 0 < x → G₂ u x = ((x ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ) :=
    fun u x hu hx => Set.indicator_of_mem (show (u, x) ∈ S from ⟨hu, hx⟩) _
  have hG₂_int : Integrable (uncurry G₂) (ν.prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hG₂_meas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      exact IntegrableOn.congr_fun (integrableOn_rpow_neg_half_mul_exp_theta_dual hu0 ht).ofReal
        (fun x hx => (hG₂_eq u x hu hx).symm) measurableSet_Ioi
    · refine (hmom.const_mul (1 / t / (2 * Real.pi ^ 2 * t ^ 2))).mono'
        hG₂_meas.norm.integral_prod_right' ?_
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hn : ∀ x ∈ Ioi (0 : ℝ), ‖G₂ u x‖ =
          x ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := hx
        rw [hG₂_eq u x hu hx0, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.exp_pos _).le)]
      show ‖∫ y in Ioi (0 : ℝ), ‖G₂ u y‖‖ ≤ 1 / t / (2 * Real.pi ^ 2 * t ^ 2) * (1 / u ^ 2)
      rw [setIntegral_congr_fun measurableSet_Ioi hn,
        integral_rpow_neg_half_mul_exp_theta_dual hu0 ht,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hy : 0 < 2 * Real.pi * u * t := by positivity
      calc 1 / t * Real.exp (-(2 * Real.pi * u * t))
          ≤ 1 / t * (2 / (2 * Real.pi * u * t) ^ 2) :=
            mul_le_mul_of_nonneg_left (exp_neg_le_two_div_sq hy) (by positivity)
        _ = 1 / t / (2 * Real.pi ^ 2 * t ^ 2) * (1 / u ^ 2) := by field_simp
  -- Evaluate both outer integrals via Fubini
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ)
  have hB : 0 < Real.pi * t ^ 2 := by positivity
  have he_int : IntegrableOn e (Ioi 0) := (integrableOn_Ioi_exp_neg_mul hB).ofReal
  have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
      ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have h1 : (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) = -(1 / 2 : ℂ) := by push_cast; norm_num
    simp only [e]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx0.le, h1,
      show -((Real.pi * t ^ 2) * x) = -(Real.pi * t ^ 2) * x by ring]
  have hhe_int : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) (Ioi 0) := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact h'.congr_fun (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
  have hG₁_x : ∀ x ∈ Ioi (0 : ℝ), ∫ u : ℝ, G₁ u x ∂ν = measureTheta ν x * e x := by
    intro x hx
    have hae : (fun u : ℝ => G₁ u x) =ᵐ[ν]
        fun u : ℝ => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) * e x := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      rw [hG₁_eq u x hu hx]
      simp only [e]
      rw [← ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    rw [integral_congr_ae hae, integral_mul_const, measureTheta]
  have hG₂_x : ∀ x ∈ Ioi (0 : ℝ),
      ∫ u : ℝ, G₂ u x ∂ν = (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hcpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]; push_cast; ring_nf
    have hae : (fun u : ℝ => G₂ u x) =ᵐ[ν]
        fun u : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) *
          ((Real.exp (-Real.pi * u ^ 2 * x⁻¹) : ℝ) : ℂ) * e x := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      rw [hG₂_eq u x hu hx0]
      simp only [e]
      rw [hcpow, show -(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x =
        -Real.pi * u ^ 2 * x⁻¹ + -(Real.pi * t ^ 2) * x by ring, Real.exp_add]
      push_cast; ring
    rw [integral_congr_ae hae, measureTheta]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_mul_const]
  have hD_int : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x) (Ioi 0) :=
    IntegrableOn.congr_fun hG₂_int.integral_prod_right hG₂_x measurableSet_Ioi
  have hL_swap : ∫ x in Ioi (0 : ℝ), measureTheta ν x * e x =
      ∫ u : ℝ, (((Real.pi * (u ^ 2 + t ^ 2) : ℝ) : ℂ))⁻¹ ∂ν := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hG₁_x,
      (integral_integral_swap hG₁_int).symm]
    refine integral_congr_ae ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
    have hfn : ∀ x ∈ Ioi (0 : ℝ), G₁ u x =
        ((Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) : ℝ) : ℂ) := fun x hx =>
      hG₁_eq u x hu hx
    rw [setIntegral_congr_fun measurableSet_Ioi hfn, integral_complex_ofReal,
      integral_Ioi_exp_neg_mul hk]
    push_cast; ring
  have hD_swap : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x =
      (1 / (t : ℂ)) * measureDual ν t := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hG₂_x,
      (integral_integral_swap hG₂_int).symm]
    have hae : (fun u : ℝ => ∫ x in Ioi (0 : ℝ), G₂ u x) =ᵐ[ν]
        fun u : ℝ => (1 / (t : ℂ)) * cexp (-(2 * Real.pi * (u : ℂ) * (t : ℂ))) := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hfn : ∀ x ∈ Ioi (0 : ℝ), G₂ u x = ((x ^ (-(1 / 2 : ℝ)) *
          Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ) := fun x hx =>
        hG₂_eq u x hu hx
      rw [setIntegral_congr_fun measurableSet_Ioi hfn, integral_complex_ofReal,
        integral_rpow_neg_half_mul_exp_theta_dual hu0 ht]
      rw [ofReal_mul, Complex.ofReal_exp]
      push_cast; rfl
    rw [integral_congr_ae hae, integral_const_mul, measureDual]
  have hI0 : ∫ x in Ioi (0 : ℝ), e x = ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) := by
    rw [integral_complex_ofReal, integral_Ioi_exp_neg_mul hB]
  have hIh : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x = ((1 / t : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq ht]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), measureTheta ν x * e x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) := by
    intro x hx; rw [htheta x hx]; ring
  have hsplit : ∫ x in Ioi (0 : ℝ), measureTheta ν x * e x =
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x) +
        (α * ∫ x in Ioi (0 : ℝ), e x) +
          β * ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      integral_add hD_int (show Integrable
        (fun x : ℝ => α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) (volume.restrict (Ioi 0)) from
          (he_int.const_mul α).add (hhe_int.const_mul β)),
      integral_add (he_int.const_mul α) (hhe_int.const_mul β),
      integral_const_mul, integral_const_mul]
    ring
  rw [hL_swap, hD_swap, hI0, hIh] at hsplit
  have hser : measureSeries ν t =
      (t : ℂ) * ∫ u : ℝ, (((Real.pi * (u ^ 2 + t ^ 2) : ℝ) : ℂ))⁻¹ ∂ν := by
    unfold measureSeries
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    push_cast; ring
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hser, hsplit]
  push_cast
  field_simp

theorem integrable_measureSeries_integrand {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {t : ℂ} (ht : 0 < t.re) :
    Integrable (fun u : ℝ => t / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2))) ν := by
  set c : ℝ := min (3 / 4) ((t.re / 2) ^ 2 / (4 * (‖t‖ + t.re / 2) ^ 2))
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  refine (hmom.const_mul (‖t‖ / (Real.pi * c))).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hden := FreqHamburger.norm_sq_add_sq_ge_on_ball ht
    (Metric.mem_ball_self (half_pos ht)) hu0.le
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    div_le_iff₀ (mul_pos Real.pi_pos (lt_of_lt_of_le (by positivity) hden))]
  calc ‖t‖ = ‖t‖ / (Real.pi * c) * (1 / u ^ 2) * (Real.pi * (c * u ^ 2)) := by field_simp
    _ ≤ ‖t‖ / (Real.pi * c) * (1 / u ^ 2) * (Real.pi * ‖(u : ℂ) ^ 2 + t ^ 2‖) := by gcongr

theorem integrable_measureDual_integrand {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {t : ℂ} (ht : 0 < t.re) :
    Integrable (fun u : ℝ => cexp (-(2 * Real.pi * (u : ℂ) * t))) ν := by
  refine (hmom.const_mul (1 / (2 * Real.pi ^ 2 * t.re ^ 2))).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hre : (-(2 * (Real.pi : ℂ) * (u : ℂ) * t)).re = -(2 * Real.pi * u * t.re) := by
    simp [mul_re]
  rw [Complex.norm_exp, hre]
  have hy : 0 < 2 * Real.pi * u * t.re := by positivity
  calc Real.exp (-(2 * Real.pi * u * t.re))
      ≤ 2 / (2 * Real.pi * u * t.re) ^ 2 := exp_neg_le_two_div_sq hy
    _ = 1 / (2 * Real.pi ^ 2 * t.re ^ 2) * (1 / u ^ 2) := by field_simp

theorem differentiableOn_measureSeries {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) :
    DifferentiableOn ℂ (measureSeries ν) {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set c : ℝ := min (3 / 4) ((t₀.re / 2) ^ 2 / (4 * (‖t₀‖ + t₀.re / 2) ^ 2))
  set R : ℝ := ‖t₀‖ + t₀.re / 2
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  let F : ℂ → ℝ → ℂ := fun t u => t / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2))
  let F' : ℂ → ℝ → ℂ := fun t u =>
    ((u : ℂ) ^ 2 - t ^ 2) / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2) ^ 2)
  have hball : Metric.ball t₀ (t₀.re / 2) ∈ 𝓝 t₀ := Metric.ball_mem_nhds t₀ (half_pos h0)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') hball
    (Eventually.of_forall fun t => (by fun_prop : Measurable fun u : ℝ =>
      t / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2))).aestronglyMeasurable)
    (integrable_measureSeries_integrand hsupp hmom h0)
    ((by fun_prop : Measurable fun u : ℝ =>
      ((u : ℂ) ^ 2 - t₀ ^ 2) / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t₀ ^ 2) ^ 2)).aestronglyMeasurable)
    (bound := fun u : ℝ => ((1 + R ^ 2) / (Real.pi * c ^ 2)) * (1 / u ^ 2))
    ?_ (hmom.const_mul _) ?_
  · exact hderiv.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu t ht
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have hden : c * u ^ 2 ≤ ‖(u : ℂ) ^ 2 + t ^ 2‖ :=
      FreqHamburger.norm_sq_add_sq_ge_on_ball h0 ht hu0.le
    have htR : ‖t‖ ≤ R := by
      rw [Metric.mem_ball, dist_eq_norm] at ht
      have h1 := norm_le_norm_add_norm_sub' t t₀
      have h2 : ‖t - t₀‖ = ‖t₀ - t‖ := norm_sub_rev _ _
      dsimp only [R]; linarith
    have hnum : ‖(u : ℂ) ^ 2 - t ^ 2‖ ≤ (1 + R ^ 2) * u ^ 2 := by
      have h1 := norm_sub_le ((u : ℂ) ^ 2) (t ^ 2)
      rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0] at h1
      have ht2 : ‖t‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg t) htR 2
      have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
      nlinarith
    have hden_pos : 0 < Real.pi * (c * u ^ 2) ^ 2 := by positivity
    have hden2 : (c * u ^ 2) ^ 2 ≤ ‖(u : ℂ) ^ 2 + t ^ 2‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) hden 2
    dsimp only [F']
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, div_le_iff₀ (mul_pos Real.pi_pos (lt_of_lt_of_le (by positivity) hden2))]
    calc ‖(u : ℂ) ^ 2 - t ^ 2‖
        ≤ (1 + R ^ 2) * u ^ 2 := hnum
      _ = (1 + R ^ 2) / (Real.pi * c ^ 2) * (1 / u ^ 2) * (Real.pi * (c * u ^ 2) ^ 2) := by
          field_simp
      _ ≤ (1 + R ^ 2) / (Real.pi * c ^ 2) * (1 / u ^ 2) *
            (Real.pi * ‖(u : ℂ) ^ 2 + t ^ 2‖ ^ 2) := by gcongr
  · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu t ht
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have hden : c * u ^ 2 ≤ ‖(u : ℂ) ^ 2 + t ^ 2‖ :=
      FreqHamburger.norm_sq_add_sq_ge_on_ball h0 ht hu0.le
    have hne : (Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
        (norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hden))
    have hd_num : HasDerivAt (fun z : ℂ => z) 1 t := hasDerivAt_id t
    have hd_den : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * ((u : ℂ) ^ 2 + z ^ 2))
        ((Real.pi : ℂ) * (2 * t)) t := by
      have hsq : HasDerivAt (fun z : ℂ => (u : ℂ) ^ 2 + z ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t).const_add ((u : ℂ) ^ 2)
      simpa using hsq.const_mul (Real.pi : ℂ)
    refine (hd_num.div hd_den hne).congr_deriv ?_
    dsimp only [F']
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hq : (u : ℂ) ^ 2 + t ^ 2 ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hden)
    field_simp
    ring

theorem differentiableOn_measureDual {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) :
    DifferentiableOn ℂ (measureDual ν) {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set δ : ℝ := t₀.re / 2
  have hδ : 0 < δ := half_pos h0
  have hU_nhds : {t : ℂ | δ < t.re} ∈ 𝓝 t₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (half_lt_self h0)
  let F : ℂ → ℝ → ℂ := fun t u => cexp (-(2 * Real.pi * (u : ℂ) * t))
  let F' : ℂ → ℝ → ℂ := fun t u => -(2 * Real.pi * (u : ℂ)) * cexp (-(2 * Real.pi * (u : ℂ) * t))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') hU_nhds
    (Eventually.of_forall fun t => (by fun_prop : Measurable fun u : ℝ =>
      cexp (-(2 * Real.pi * (u : ℂ) * t))).aestronglyMeasurable)
    (integrable_measureDual_integrand hsupp hmom h0)
    ((by fun_prop : Measurable fun u : ℝ =>
      -(2 * Real.pi * (u : ℂ)) * cexp (-(2 * Real.pi * (u : ℂ) * t₀))).aestronglyMeasurable)
    (bound := fun u : ℝ => (3 / (2 * Real.pi ^ 2 * δ ^ 3)) * (1 / u ^ 2))
    ?_ (hmom.const_mul _) ?_
  · exact hderiv.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu t ht
    have ht_re : δ < t.re := ht
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    dsimp only [F']
    have hre : (-(2 * (Real.pi : ℂ) * (u : ℂ) * t)).re = -(2 * Real.pi * u * t.re) := by
      simp [mul_re]
    rw [norm_mul, norm_neg, norm_mul, norm_mul, norm_ofNat, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      abs_of_pos hu0, Complex.norm_exp, hre]
    have hy : 0 < 2 * Real.pi * u * δ := by positivity
    have hexp_le : Real.exp (-(2 * Real.pi * u * t.re)) ≤ Real.exp (-(2 * Real.pi * u * δ)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      gcongr
    calc 2 * Real.pi * u * Real.exp (-(2 * Real.pi * u * t.re))
        ≤ 2 * Real.pi * u * (6 / (2 * Real.pi * u * δ) ^ 3) :=
          mul_le_mul_of_nonneg_left (hexp_le.trans (exp_neg_le_six_div_cube hy)) (by positivity)
      _ = 3 / (2 * Real.pi ^ 2 * δ ^ 3) * (1 / u ^ 2) := by field_simp; ring
  · filter_upwards with u t _
    dsimp only [F, F']
    have hlin : HasDerivAt (fun z : ℂ => -(2 * Real.pi * (u : ℂ) * z))
        (-(2 * Real.pi * (u : ℂ))) t := by
      have h := ((hasDerivAt_id t).const_mul (2 * (Real.pi : ℂ) * (u : ℂ))).neg
      simp only [id_eq, mul_one] at h
      exact h
    exact ((Complex.hasDerivAt_exp _).comp t hlin).congr_deriv (by ring)

/-- **Half-plane Laplace identity for Borel measures.** On `Re t > 0`,
`measureSeries ν t = measureDual ν t + α / (π t) + β`. -/
theorem measureSeries_eq_of_measureTheta_relation {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    measureSeries ν t = measureDual ν t + α / (Real.pi * t) + β := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (measureSeries ν) U :=
    (differentiableOn_measureSeries hsupp hmom).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => measureDual ν z + α / (Real.pi * z) + β) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine ((differentiableOn_measureDual hsupp hmom).add ?_).add (differentiableOn_const _)
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun z hz => ?_
    have hz' : 0 < z.re := hz
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h0 => ?_
    rw [h0, zero_re] at hz'
    exact lt_irrefl _ hz'
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      measureSeries ν z = measureDual ν z + α / (Real.pi * z) + β := by
    -- Real points `1 + 1/(k+1) ↓ 1` accumulate at `1` from the positive axis.
    let r : ℕ → ℝ := fun k => 1 + 1 / ((k : ℝ) + 1)
    have hr : ∀ k, 1 < r k := fun k => by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      simp only [r]; linarith
    have hlim : Tendsto (fun k => ((r k : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 : ℝ)
        rw [add_zero] at h
        have h' := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h'
        exact h'
      · exact fun h => (hr k).ne' (Complex.ofReal_eq_one.mp h)
    exact hlim.frequently <| Frequently.of_forall fun k =>
      measureSeries_eq_of_measureTheta_relation_ofReal hsupp hmom htheta
        (lt_trans zero_lt_one (hr k))
  have hconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn h1U hfreq ht

/-! ## 4. Collar-blind Fejér pairing and measure-theoretic Hamburger rigidity -/

/-- The Fejér triangle `1 - |τ|` has unit mass on `[-1, 1]`. -/
theorem fejer_triangle_integral_one :
    ∫ τ in (-1 : ℝ)..1, (1 - |τ|) = 1 := by
  have hc : Continuous (fun τ : ℝ => 1 - |τ|) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)]
  have hL : ∫ τ in (-1 : ℝ)..0, (1 - |τ|) = ∫ τ in (-1 : ℝ)..0, (1 + τ) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le (by norm_num)] at hτ
    rw [abs_of_nonpos hτ.2]; ring
  have hR : ∫ τ in (0 : ℝ)..1, (1 - |τ|) = ∫ τ in (0 : ℝ)..1, (1 - τ) := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    rw [abs_of_nonneg hτ.1]
  have hdL : ∀ τ ∈ uIcc (-1 : ℝ) 0, HasDerivAt (fun x : ℝ => x + x ^ 2 / 2) (1 + τ) τ := by
    intro τ _
    refine ((hasDerivAt_id τ).add ((hasDerivAt_pow 2 τ).div_const 2)).congr_deriv ?_
    ring
  have hdR : ∀ τ ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - τ) τ := by
    intro τ _
    refine ((hasDerivAt_id τ).sub ((hasDerivAt_pow 2 τ).div_const 2)).congr_deriv ?_
    ring
  rw [hL, hR,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hdL ((by fun_prop : Continuous _).intervalIntegrable _ _),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hdR ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  norm_num

/-- Fourier transform of the Fejér triangle: `∫_{-1}^{1} (1 - |τ|) cos(2π u τ) dτ = sinc²(u)`. -/
theorem fejer_cos_integral {u : ℝ} (hu : u ≠ 0) :
    ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * Real.cos (2 * Real.pi * u * τ) =
      (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := by
  set ω : ℝ := 2 * Real.pi * u with hω
  have hω0 : ω ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hu
  have hcont : Continuous (fun τ : ℝ => (1 - |τ|) * Real.cos (ω * τ)) := by fun_prop
  have hsplit : ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * Real.cos (ω * τ) =
      2 * ∫ τ in (0 : ℝ)..1, (1 - τ) * Real.cos (ω * τ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)]
    have hleft : ∫ τ in (-1 : ℝ)..0, (1 - |τ|) * Real.cos (ω * τ) =
        ∫ τ in (0 : ℝ)..1, (1 - τ) * Real.cos (ω * τ) := by
      have hneg := intervalIntegral.integral_comp_neg
        (fun τ : ℝ => (1 - |τ|) * Real.cos (ω * τ)) (a := 0) (b := 1)
      simp only [neg_zero] at hneg
      rw [← hneg]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le zero_le_one] at hτ
      rw [abs_neg, abs_of_nonneg hτ.1, mul_neg, Real.cos_neg]
    have hright : ∫ τ in (0 : ℝ)..1, (1 - |τ|) * Real.cos (ω * τ) =
        ∫ τ in (0 : ℝ)..1, (1 - τ) * Real.cos (ω * τ) := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le zero_le_one] at hτ
      rw [abs_of_nonneg hτ.1]
    rw [hleft, hright, two_mul]
  let F : ℝ → ℝ := fun τ => (1 - τ) * (Real.sin (ω * τ) / ω) - Real.cos (ω * τ) / ω ^ 2
  have hderiv : ∀ τ ∈ uIcc (0 : ℝ) 1, HasDerivAt F ((1 - τ) * Real.cos (ω * τ)) τ := by
    intro τ _
    have hd1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) τ := by
      simpa using (hasDerivAt_id τ).const_sub 1
    have hd2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x) / ω) (Real.cos (ω * τ)) τ := by
      refine (((Real.hasDerivAt_sin (ω * τ)).comp τ
        ((hasDerivAt_id τ).const_mul ω)).div_const ω).congr_deriv ?_
      field_simp
    have hd3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x) / ω ^ 2)
        (-(Real.sin (ω * τ) / ω)) τ := by
      refine (((Real.hasDerivAt_cos (ω * τ)).comp τ
        ((hasDerivAt_id τ).const_mul ω)).div_const (ω ^ 2)).congr_deriv ?_
      field_simp
    refine ((hd1.mul hd2).sub hd3).congr_deriv ?_
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun τ : ℝ => (1 - τ) * Real.cos (ω * τ)).intervalIntegrable 0 1)
  rw [hsplit, hint]
  -- `2 (1 - cos ω) / ω² = (sin(π u) / (π u))²` by the half-angle formula.
  have hcos : Real.cos ω = 1 - 2 * Real.sin (Real.pi * u) ^ 2 := by
    have h2 : ω = 2 * (Real.pi * u) := by rw [hω]; ring
    rw [h2, Real.cos_two_mul, ← Real.sin_sq_add_cos_sq (Real.pi * u)]
    ring
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [F, mul_one, mul_zero, Real.sin_zero, Real.cos_zero, zero_div, sub_self, zero_mul,
    sub_zero, hcos]
  rw [hω]
  field_simp
  ring

/-- First Poisson moment on `[0, 1]`: `∫₀¹ y ε / (ε² + y²) dy ≤ (3/2) √ε` for `0 < ε ≤ 1`. -/
theorem integral_zero_one_mul_poisson_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ y in (0 : ℝ)..1, y * (ε / (ε ^ 2 + y ^ 2)) ≤ (3 / 2) * Real.sqrt ε := by
  have hc : Continuous (fun y : ℝ => y * (ε / (ε ^ 2 + y ^ 2))) :=
    continuous_id.mul (continuous_const.div (by fun_prop) fun y => by positivity)
  have hsq0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
  have hsq1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (Real.sqrt ε)) (hc.intervalIntegrable (Real.sqrt ε) 1)]
  have hI1 : ∫ y in (0 : ℝ)..Real.sqrt ε, y * (ε / (ε ^ 2 + y ^ 2)) ≤ (1 / 2) * Real.sqrt ε := by
    calc ∫ y in (0 : ℝ)..Real.sqrt ε, y * (ε / (ε ^ 2 + y ^ 2))
        ≤ ∫ _ in (0 : ℝ)..Real.sqrt ε, (1 / 2 : ℝ) := by
          refine intervalIntegral.integral_mono_on hsq0
            (hc.intervalIntegrable _ _) intervalIntegrable_const fun y _ => ?_
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg (ε - y)]
      _ = (1 / 2) * Real.sqrt ε := by
          rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring
  have hI2 : ∫ y in Real.sqrt ε..1, y * (ε / (ε ^ 2 + y ^ 2)) ≤ Real.sqrt ε := by
    calc ∫ y in Real.sqrt ε..1, y * (ε / (ε ^ 2 + y ^ 2))
        ≤ ∫ _ in Real.sqrt ε..1, Real.sqrt ε := by
          refine intervalIntegral.integral_mono_on hsq1
            (hc.intervalIntegrable _ _) intervalIntegrable_const fun y hy => ?_
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          have hy_sq : ε ≤ y ^ 2 := by
            have := mul_self_le_mul_self hsq0 hy.1
            rwa [Real.mul_self_sqrt hε0.le, ← sq] at this
          have hsq_mul : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε0.le
          -- `y ε = √ε · y · √ε ≤ √ε · y · y ≤ √ε (ε² + y²)`
          have hy0 : 0 ≤ y := hsq0.trans hy.1
          have hA : y * ε = Real.sqrt ε * y * Real.sqrt ε := by linear_combination (-y) * hsq_mul
          have hB : Real.sqrt ε * y * Real.sqrt ε ≤ Real.sqrt ε * y * y :=
            mul_le_mul_of_nonneg_left hy.1 (mul_nonneg hsq0 hy0)
          have hC : 0 ≤ Real.sqrt ε * ε ^ 2 := mul_nonneg hsq0 (sq_nonneg ε)
          nlinarith [hA, hB, hC]
      _ = (1 - Real.sqrt ε) * Real.sqrt ε := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ Real.sqrt ε := by nlinarith [sq_nonneg (Real.sqrt ε)]
  linarith

/-- The Fejér-weighted Poisson kernel at the origin has mass `→ π` as `ε → 0⁺`. -/
theorem tendsto_fejer_polar :
    Tendsto (fun ε : ℝ => ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + τ ^ 2)))
      (𝓝[>] 0) (𝓝 Real.pi) := by
  have hmain : Tendsto (fun ε : ℝ => 2 * Real.arctan (1 / ε)) (𝓝[>] 0) (𝓝 Real.pi) := by
    have hinv : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop := by
      simpa only [one_div] using tendsto_inv_nhdsGT_zero
    have hmul := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hinv).const_mul 2
    rwa [show 2 * (Real.pi / 2) = Real.pi by ring] at hmul
  have herr : Tendsto (fun ε : ℝ => ∫ τ in (-1 : ℝ)..1, |τ| * (ε / (ε ^ 2 + τ ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by
    have hmaj : Tendsto (fun ε : ℝ => 3 * Real.sqrt ε) (𝓝[>] 0) (𝓝 0) := by
      have hc := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rw [Real.sqrt_zero] at hc
      simpa only [mul_zero] using hc.const_mul 3
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε0 : (0 : ℝ) < ε := hε
      exact intervalIntegral.integral_nonneg (by norm_num) fun τ _ => by positivity
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε ⟨hε0, hε1⟩
      have hcont : Continuous (fun τ : ℝ => |τ| * (ε / (ε ^ 2 + τ ^ 2))) :=
        continuous_abs.mul (continuous_const.div (by fun_prop) fun τ => by positivity)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable 0 1)]
      have hL : ∫ τ in (-1 : ℝ)..0, |τ| * (ε / (ε ^ 2 + τ ^ 2)) =
          ∫ τ in (0 : ℝ)..1, τ * (ε / (ε ^ 2 + τ ^ 2)) := by
        have hneg := intervalIntegral.integral_comp_neg
          (fun τ : ℝ => |τ| * (ε / (ε ^ 2 + τ ^ 2))) (a := 0) (b := 1)
        simp only [neg_zero] at hneg
        rw [← hneg]
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_le zero_le_one] at hτ
        rw [abs_neg, abs_of_nonneg hτ.1, neg_sq]
      have hR : ∫ τ in (0 : ℝ)..1, |τ| * (ε / (ε ^ 2 + τ ^ 2)) =
          ∫ τ in (0 : ℝ)..1, τ * (ε / (ε ^ 2 + τ ^ 2)) := by
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_le zero_le_one] at hτ
        rw [abs_of_nonneg hτ.1]
      rw [hL, hR]
      linarith [integral_zero_one_mul_poisson_le hε0 hε1.le]
  have hsub := hmain.sub herr
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have hc1 : Continuous (fun τ : ℝ => ε / (ε ^ 2 + τ ^ 2)) :=
    continuous_const.div (by fun_prop) fun τ => by positivity
  have hc2 : Continuous (fun τ : ℝ => |τ| * (ε / (ε ^ 2 + τ ^ 2))) := continuous_abs.mul hc1
  have harctan : ∫ τ in (-1 : ℝ)..1, ε / (ε ^ 2 + τ ^ 2) = 2 * Real.arctan (1 / ε) := by
    have hd : ∀ τ ∈ uIcc (-1 : ℝ) 1,
        HasDerivAt (fun x : ℝ => Real.arctan (x / ε)) (ε / (ε ^ 2 + τ ^ 2)) τ := by
      intro τ _
      refine ((Real.hasDerivAt_arctan (τ / ε)).comp τ
        ((hasDerivAt_id τ).div_const ε)).congr_deriv ?_
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc1.intervalIntegrable _ _),
      neg_div, Real.arctan_neg, one_div]
    ring
  rw [← harctan, ← intervalIntegral.integral_sub (hc1.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun τ _ => by ring

/-- Partial fractions: `2 Re[t / (π (u² + t²))]` at `t = ε + iτ` is a pair of Poisson kernels
centred at `τ = ± u`. -/
theorem two_re_series_term_eq {u ε τ : ℝ} (hε : 0 < ε) :
    2 * ((((ε : ℂ) + (τ : ℂ) * I) /
      ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) + (τ : ℂ) * I) ^ 2)))).re =
      (1 / Real.pi) * (ε / (ε ^ 2 + (τ - u) ^ 2) + ε / (ε ^ 2 + (τ + u) ^ 2)) := by
  have hinv_re : ∀ y : ℝ, ((((ε : ℂ) + (y : ℂ) * I))⁻¹).re = ε / (ε ^ 2 + y ^ 2) := by
    intro y
    have hpos : 0 < ε ^ 2 + y ^ 2 := by positivity
    have hmul : ((ε : ℂ) + (y : ℂ) * I) *
        (((ε : ℂ) - (y : ℂ) * I) / ((ε ^ 2 + y ^ 2 : ℝ) : ℂ)) = 1 := by
      have hd : ((ε ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [mul_div_assoc', div_eq_iff hd]
      push_cast; ring_nf; rw [I_sq]; ring
    have heq : (((ε : ℂ) + (y : ℂ) * I))⁻¹ =
        ((ε : ℂ) - (y : ℂ) * I) / ((ε ^ 2 + y ^ 2 : ℝ) : ℂ) :=
      inv_eq_of_mul_eq_one_right hmul
    rw [heq, div_ofReal_re]
    simp
  set t : ℂ := (ε : ℂ) + (τ : ℂ) * I
  have hne1 : t - (u : ℂ) * I ≠ 0 := by
    intro h0
    have hr := congrArg Complex.re h0
    simp [t] at hr
    linarith
  have hne2 : t + (u : ℂ) * I ≠ 0 := by
    intro h0
    have hr := congrArg Complex.re h0
    simp [t] at hr
    linarith
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpf : (2 : ℂ) * (t / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2))) =
      (((Real.pi)⁻¹ : ℝ) : ℂ) * ((t - (u : ℂ) * I)⁻¹ + (t + (u : ℂ) * I)⁻¹) := by
    have hfac : (u : ℂ) ^ 2 + t ^ 2 = (t - (u : ℂ) * I) * (t + (u : ℂ) * I) := by
      ring_nf; rw [I_sq]; ring
    rw [hfac]
    push_cast
    field_simp
    ring
  have ht1 : t - (u : ℂ) * I = (ε : ℂ) + ((τ - u : ℝ) : ℂ) * I := by
    dsimp only [t]; push_cast; ring
  have ht2 : t + (u : ℂ) * I = (ε : ℂ) + ((τ + u : ℝ) : ℂ) * I := by
    dsimp only [t]; push_cast; ring
  have hre := congrArg Complex.re hpf
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [h2re] at hre
  rw [hre, Complex.re_ofReal_mul, add_re, ht1, ht2, hinv_re, hinv_re, one_div]

/-- A Poisson kernel centred at `∓ u` (`u ≥ 1`), integrated against the Fejér triangle, is
`O(√ε / u²)`: the triangle vanishes linearly where the centre meets the window. -/
theorem fejer_shifted_poisson_integral_le {u ε : ℝ} (hu : 1 ≤ u)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (sgn : ℝ) (hsgn : sgn = -1 ∨ sgn = 1) :
    ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (τ + sgn * u) ^ 2)) ≤
      12 * Real.sqrt ε * (1 / u ^ 2) := by
  have hc : Continuous (fun τ : ℝ => (1 - |τ|) * (ε / (ε ^ 2 + (τ + sgn * u) ^ 2))) :=
    (continuous_const.sub continuous_abs).mul
      (continuous_const.div (by fun_prop) fun τ => by positivity)
  have hdist : ∀ τ : ℝ, |τ| ≤ 1 → u - |τ| ≤ |τ + sgn * u| := by
    intro τ _
    rcases hsgn with rfl | rfl
    · have h1 := abs_sub_abs_le_abs_sub u τ
      rw [abs_of_nonneg (by linarith : 0 ≤ u), abs_sub_comm] at h1
      simpa [sub_eq_add_neg] using h1
    · rw [one_mul]
      have h1 := abs_sub_abs_le_abs_sub u (-τ)
      rw [abs_of_nonneg (by linarith : 0 ≤ u), abs_neg, sub_neg_eq_add, add_comm] at h1
      exact h1
  rcases le_or_gt u 2 with hu2 | hu2
  · have hc_dom : Continuous (fun τ : ℝ => (1 - |τ|) * (ε / (ε ^ 2 + (1 - |τ|) ^ 2))) :=
      (continuous_const.sub continuous_abs).mul
        (continuous_const.div (by fun_prop) fun τ => by positivity)
    have hle1 : ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (τ + sgn * u) ^ 2)) ≤
        ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (1 - |τ|) ^ 2)) := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable _ _) (hc_dom.intervalIntegrable _ _) fun τ hτ => ?_
      have hτ_abs : |τ| ≤ 1 := abs_le.mpr hτ
      have hnonneg : 0 ≤ 1 - |τ| := by linarith
      have hd_le : 1 - |τ| ≤ |τ + sgn * u| := by linarith [hdist τ hτ_abs]
      have hsq_le : (1 - |τ|) ^ 2 ≤ (τ + sgn * u) ^ 2 := by
        rw [← sq_abs (τ + sgn * u)]
        exact pow_le_pow_left₀ hnonneg hd_le 2
      refine mul_le_mul_of_nonneg_left ?_ hnonneg
      exact div_le_div_of_nonneg_left hε0.le (by positivity) (by linarith)
    have hdom_eval : ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (1 - |τ|) ^ 2)) ≤
        3 * Real.sqrt ε := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hc_dom.intervalIntegrable (-1) 0) (hc_dom.intervalIntegrable 0 1)]
      have hL : ∫ τ in (-1 : ℝ)..0, (1 - |τ|) * (ε / (ε ^ 2 + (1 - |τ|) ^ 2)) =
          ∫ τ in (0 : ℝ)..1, (1 - τ) * (ε / (ε ^ 2 + (1 - τ) ^ 2)) := by
        have hneg := intervalIntegral.integral_comp_neg
          (fun τ : ℝ => (1 - |τ|) * (ε / (ε ^ 2 + (1 - |τ|) ^ 2))) (a := 0) (b := 1)
        simp only [neg_zero] at hneg
        rw [← hneg]
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_le zero_le_one] at hτ
        rw [abs_neg, abs_of_nonneg hτ.1]
      have hR : ∫ τ in (0 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (1 - |τ|) ^ 2)) =
          ∫ τ in (0 : ℝ)..1, (1 - τ) * (ε / (ε ^ 2 + (1 - τ) ^ 2)) := by
        refine intervalIntegral.integral_congr fun τ hτ => ?_
        rw [uIcc_of_le zero_le_one] at hτ
        rw [abs_of_nonneg hτ.1]
      have hsub_var : ∫ τ in (0 : ℝ)..1, (1 - τ) * (ε / (ε ^ 2 + (1 - τ) ^ 2)) =
          ∫ y in (0 : ℝ)..1, y * (ε / (ε ^ 2 + y ^ 2)) := by
        simpa only [sub_zero, sub_self] using
          intervalIntegral.integral_comp_sub_left
            (fun y : ℝ => y * (ε / (ε ^ 2 + y ^ 2))) (1 : ℝ) (a := 0) (b := 1)
      rw [hL, hR, hsub_var]
      linarith [integral_zero_one_mul_poisson_le hε0 hε1]
    have hu_inv : (1 : ℝ) ≤ 4 * (1 / u ^ 2) := by
      have hu_sq : u ^ 2 ≤ 4 := by nlinarith
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    have hsq0 : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg ε
    nlinarith
  · have hε_le_sqrt : ε ≤ Real.sqrt ε := by
      have h1 : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε0.le
      have h2 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
      nlinarith [Real.sqrt_nonneg ε]
    calc ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (τ + sgn * u) ^ 2))
        ≤ ∫ _ in (-1 : ℝ)..1, 4 * Real.sqrt ε * (1 / u ^ 2) := by
          refine intervalIntegral.integral_mono_on (by norm_num)
            (hc.intervalIntegrable _ _) intervalIntegrable_const fun τ hτ => ?_
          have hτ_abs : |τ| ≤ 1 := abs_le.mpr hτ
          have hd_ge : u / 2 ≤ |τ + sgn * u| := by linarith [hdist τ hτ_abs]
          have hsq_ge : u ^ 2 / 4 ≤ ε ^ 2 + (τ + sgn * u) ^ 2 := by
            have := pow_le_pow_left₀ (by positivity) hd_ge 2
            rw [sq_abs] at this
            nlinarith [sq_nonneg ε]
          have h1τ : 1 - |τ| ≤ 1 := by linarith [abs_nonneg τ]
          have hnonneg : 0 ≤ 1 - |τ| := by linarith
          calc (1 - |τ|) * (ε / (ε ^ 2 + (τ + sgn * u) ^ 2))
              ≤ 1 * (ε / (u ^ 2 / 4)) := by
                refine mul_le_mul h1τ ?_ (by positivity) zero_le_one
                exact div_le_div_of_nonneg_left hε0.le (by positivity) hsq_ge
            _ = 4 * ε * (1 / u ^ 2) := by field_simp
            _ ≤ 4 * Real.sqrt ε * (1 / u ^ 2) := by gcongr
      _ = 8 * Real.sqrt ε * (1 / u ^ 2) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ 12 * Real.sqrt ε * (1 / u ^ 2) := by
          have : 0 ≤ Real.sqrt ε * (1 / u ^ 2) := by positivity
          linarith

/-! ### Fejér kernels on the line `t = ε + iτ` -/

/-- Fejér-weighted real part `2 (1 - |τ|) Re[t / (π (u² + t²))]` at `t = ε + iτ`. -/
def fejerSeriesKernel (ε τ u : ℝ) : ℝ :=
  2 * (1 - |τ|) * ((((ε : ℂ) + (τ : ℂ) * I) /
    ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) + (τ : ℂ) * I) ^ 2)))).re

/-- Fejér-weighted real part `2 (1 - |τ|) Re e^{-2π u t}` at `t = ε + iτ`. -/
def fejerDualKernel (ε τ u : ℝ) : ℝ :=
  2 * (1 - |τ|) * (cexp (-(2 * Real.pi * (u : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)))).re

/-- Fejér-weighted real part `2 (1 - |τ|) Re[α / (π t) + β]` at `t = ε + iτ`. -/
def fejerPolarKernel (α β : ℂ) (ε τ : ℝ) : ℝ :=
  2 * (1 - |τ|) * (α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) + β).re

/-- The series kernel is a Fejér-weighted pair of Poisson kernels centred at `τ = ± u`. -/
theorem fejerSeriesKernel_eq {ε : ℝ} (hε : 0 < ε) (τ u : ℝ) :
    fejerSeriesKernel ε τ u = (1 - |τ|) *
      ((1 / Real.pi) * (ε / (ε ^ 2 + (τ - u) ^ 2) + ε / (ε ^ 2 + (τ + u) ^ 2))) := by
  rw [fejerSeriesKernel, mul_comm 2 (1 - |τ|), mul_assoc, two_re_series_term_eq hε]

theorem fejerSeriesKernel_nonneg {ε τ : ℝ} (hε : 0 < ε) (hτ : |τ| ≤ 1) (u : ℝ) :
    0 ≤ fejerSeriesKernel ε τ u := by
  rw [fejerSeriesKernel_eq hε]
  have : 0 ≤ 1 - |τ| := by linarith
  positivity

/-- Uniform `u⁻²` majorant of the series kernel on the window `|τ| ≤ 1`, for `u ≥ 1`. -/
theorem fejerSeriesKernel_le {ε τ u : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hτ : |τ| ≤ 1)
    (hu : 1 ≤ u) : fejerSeriesKernel ε τ u ≤ (8 / (Real.pi * ε)) * (1 / u ^ 2) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have h1τ : 1 - |τ| ≤ 1 := by linarith [abs_nonneg τ]
  rw [fejerSeriesKernel_eq hε0]
  -- A Poisson kernel whose centre lies `u - 1` away is at most `4 / (ε u²)`.
  have hterm : ∀ y : ℝ, u - 1 ≤ |y| → (1 - |τ|) * (ε / (ε ^ 2 + y ^ 2)) ≤
      4 / ε * (1 / u ^ 2) := by
    intro y hy
    rcases le_or_gt u 2 with hu2 | hu2
    · have h1 : (1 - |τ|) * (ε / (ε ^ 2 + y ^ 2)) ≤ 1 / ε :=
        calc (1 - |τ|) * (ε / (ε ^ 2 + y ^ 2))
            ≤ 1 * (ε / ε ^ 2) := by
              refine mul_le_mul h1τ ?_ (by positivity) zero_le_one
              exact div_le_div_of_nonneg_left hε0.le (by positivity)
                (by nlinarith [sq_nonneg y])
          _ = 1 / ε := by field_simp
      have hu_sq : u ^ 2 ≤ 4 := by nlinarith
      have h2 : 1 / ε ≤ 4 / ε * (1 / u ^ 2) := by
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ hε0 (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hu_sq hε0.le]
      exact h1.trans h2
    · have hy2 : u / 2 ≤ |y| := by linarith
      have hysq : u ^ 2 / 4 ≤ ε ^ 2 + y ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hy2 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg ε]
      have hε_le : 4 * ε ≤ 4 / ε := by rw [le_div_iff₀ hε0]; nlinarith
      calc (1 - |τ|) * (ε / (ε ^ 2 + y ^ 2))
          ≤ 1 * (ε / (u ^ 2 / 4)) := by
            refine mul_le_mul h1τ ?_ (by positivity) zero_le_one
            exact div_le_div_of_nonneg_left hε0.le (by positivity) hysq
        _ = 4 * ε * (1 / u ^ 2) := by rw [one_mul, div_div_eq_mul_div]; ring
        _ ≤ 4 / ε * (1 / u ^ 2) := mul_le_mul_of_nonneg_right hε_le (by positivity)
  have hd1 : u - 1 ≤ |τ - u| := by
    have h1 := abs_sub_abs_le_abs_sub u τ
    rw [abs_of_pos hu0, abs_sub_comm] at h1
    linarith
  have hd2 : u - 1 ≤ |τ + u| := by
    have h1 := abs_sub_abs_le_abs_sub u (-τ)
    rw [abs_of_pos hu0, abs_neg, sub_neg_eq_add, add_comm] at h1
    linarith
  calc (1 - |τ|) * ((1 / Real.pi) *
        (ε / (ε ^ 2 + (τ - u) ^ 2) + ε / (ε ^ 2 + (τ + u) ^ 2)))
      = (1 / Real.pi) * ((1 - |τ|) * (ε / (ε ^ 2 + (τ - u) ^ 2)) +
          (1 - |τ|) * (ε / (ε ^ 2 + (τ + u) ^ 2))) := by ring
    _ ≤ (1 / Real.pi) * (4 / ε * (1 / u ^ 2) + 4 / ε * (1 / u ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hterm _ hd1) (hterm _ hd2)) (by positivity)
    _ = (8 / (Real.pi * ε)) * (1 / u ^ 2) := by field_simp; ring

theorem measurable_uncurry_fejerSeriesKernel (ε : ℝ) :
    Measurable (uncurry (fejerSeriesKernel ε)) := by
  show Measurable fun p : ℝ × ℝ => 2 * (1 - |p.1|) * ((((ε : ℂ) + (p.1 : ℂ) * I) /
    ((Real.pi : ℂ) * ((p.2 : ℂ) ^ 2 + ((ε : ℂ) + (p.1 : ℂ) * I) ^ 2)))).re
  fun_prop

theorem continuous_uncurry_fejerDualKernel (ε : ℝ) :
    Continuous (uncurry (fejerDualKernel ε)) := by
  show Continuous fun p : ℝ × ℝ =>
    2 * (1 - |p.1|) * (cexp (-(2 * Real.pi * (p.2 : ℂ) * ((ε : ℂ) + (p.1 : ℂ) * I)))).re
  fun_prop

/-- The dual kernel is a damped Fejér-weighted cosine. -/
theorem fejerDualKernel_eq (ε τ u : ℝ) :
    fejerDualKernel ε τ u = (2 * Real.exp (-2 * Real.pi * u * ε)) *
      ((1 - |τ|) * Real.cos (2 * Real.pi * u * τ)) := by
  have hexp : -(2 * (Real.pi : ℂ) * (u : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) =
      ((-2 * Real.pi * u * ε : ℝ) : ℂ) + ((-(2 * Real.pi * u * τ) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [fejerDualKernel, hexp, Complex.exp_add_mul_I, ← Complex.ofReal_exp, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.re_ofReal_mul, add_re, ofReal_re, mul_re, ofReal_re, ofReal_im,
    I_re, I_im, Real.cos_neg]
  ring

theorem abs_fejerDualKernel_le {ε τ u : ℝ} (hε : 0 < ε) (hτ : |τ| ≤ 1) (hu : 0 < u) :
    |fejerDualKernel ε τ u| ≤ (1 / (Real.pi ^ 2 * ε ^ 2)) * (1 / u ^ 2) := by
  rw [fejerDualKernel_eq, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.exp (-2 * Real.pi * u * ε)), abs_mul,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - |τ|)]
  have hy : 0 < 2 * Real.pi * u * ε := by positivity
  have hexp : Real.exp (-2 * Real.pi * u * ε) ≤ 2 / (2 * Real.pi * u * ε) ^ 2 := by
    rw [show -2 * Real.pi * u * ε = -(2 * Real.pi * u * ε) by ring]
    exact exp_neg_le_two_div_sq hy
  have hcos : (1 - |τ|) * |Real.cos (2 * Real.pi * u * τ)| ≤ 1 := by
    have h1 := Real.abs_cos_le_one (2 * Real.pi * u * τ)
    have h0 := abs_nonneg (Real.cos (2 * Real.pi * u * τ))
    nlinarith [abs_nonneg τ]
  calc 2 * Real.exp (-2 * Real.pi * u * ε) * ((1 - |τ|) * |Real.cos (2 * Real.pi * u * τ)|)
      ≤ 2 * (2 / (2 * Real.pi * u * ε) ^ 2) * 1 :=
        mul_le_mul (by linarith) hcos (by positivity) (by positivity)
    _ = (1 / (Real.pi ^ 2 * ε ^ 2)) * (1 / u ^ 2) := by field_simp

/-- A kernel on `[-1, 1] × [1, ∞)` dominated by `C u⁻²` is product-integrable. -/
theorem integrable_prod_uIoc_of_inv_sq_bound {ν : Measure ℝ} [SFinite ν]
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {f : ℝ → ℝ → ℝ} {C : ℝ}
    (hf : Measurable (uncurry f))
    (hbound : ∀ τ ∈ uIoc (-1 : ℝ) 1, ∀ᵐ u ∂ν, ‖f τ u‖ ≤ C * (1 / u ^ 2)) :
    Integrable (uncurry f) ((volume.restrict (uIoc (-1 : ℝ) 1)).prod ν) := by
  haveI : IsFiniteMeasure (volume.restrict (uIoc (-1 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, uIoc_of_le (by norm_num), Real.volume_Ioc]
        exact ENNReal.ofReal_lt_top⟩
  have hdom : Integrable (fun u : ℝ => C * (1 / u ^ 2)) ν := hmom.const_mul C
  have hsec : ∀ τ ∈ uIoc (-1 : ℝ) 1, Integrable (fun u => f τ u) ν := fun τ hτ =>
    hdom.mono' (hf.comp measurable_prodMk_left).aestronglyMeasurable (hbound τ hτ)
  rw [integrable_prod_iff hf.aestronglyMeasurable]
  refine ⟨(ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall hsec), ?_⟩
  refine (integrable_const (∫ u, C * (1 / u ^ 2) ∂ν)).mono'
    hf.aestronglyMeasurable.norm.integral_prod_right' ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall fun τ hτ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact integral_mono_ae (hsec τ hτ).norm hdom (hbound τ hτ)

theorem integrable_fejerSeriesKernel {ν : Measure ℝ} [SFinite ν] (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (uncurry (fejerSeriesKernel ε)) ((volume.restrict (uIoc (-1 : ℝ) 1)).prod ν) := by
  refine integrable_prod_uIoc_of_inv_sq_bound hmom (measurable_uncurry_fejerSeriesKernel ε)
    (C := 8 / (Real.pi * ε)) fun τ hτ => ?_
  rw [uIoc_of_le (by norm_num)] at hτ
  have hτ1 : |τ| ≤ 1 := abs_le.mpr ⟨hτ.1.le, hτ.2⟩
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (fejerSeriesKernel_nonneg hε0 hτ1 u)]
  exact fejerSeriesKernel_le hε0 hε1 hτ1 hu

theorem integrable_fejerDualKernel {ν : Measure ℝ} [SFinite ν] (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν) {ε : ℝ} (hε0 : 0 < ε) :
    Integrable (uncurry (fejerDualKernel ε)) ((volume.restrict (uIoc (-1 : ℝ) 1)).prod ν) := by
  refine integrable_prod_uIoc_of_inv_sq_bound hmom
    (continuous_uncurry_fejerDualKernel ε).measurable
    (C := 1 / (Real.pi ^ 2 * ε ^ 2)) fun τ hτ => ?_
  rw [uIoc_of_le (by norm_num)] at hτ
  have hτ1 : |τ| ≤ 1 := abs_le.mpr ⟨hτ.1.le, hτ.2⟩
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  rw [Real.norm_eq_abs]
  exact abs_fejerDualKernel_le hε0 hτ1 (lt_of_lt_of_le zero_lt_one hu)

/-- The Fejér window turns the dual kernel into the damped `sinc²` weight. -/
theorem intervalIntegral_fejerDualKernel (ε : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ∫ τ in (-1 : ℝ)..1, fejerDualKernel ε τ u =
      2 * Real.exp (-2 * Real.pi * u * ε) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 := by
  rw [intervalIntegral.integral_congr (g := fun τ => (2 * Real.exp (-2 * Real.pi * u * ε)) *
      ((1 - |τ|) * Real.cos (2 * Real.pi * u * τ))) (fun τ _ => fejerDualKernel_eq ε τ u),
    intervalIntegral.integral_const_mul, fejer_cos_integral hu]

/-- The Fejér window integral of the series kernel is `O(√ε / u²)` on `u ≥ 1`. -/
theorem intervalIntegral_fejerSeriesKernel_le {ε u : ℝ} (hu : 1 ≤ u) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∫ τ in (-1 : ℝ)..1, fejerSeriesKernel ε τ u ≤ (24 * Real.sqrt ε / Real.pi) * (1 / u ^ 2) := by
  have hc : ∀ s : ℝ, Continuous (fun τ : ℝ => (1 - |τ|) * (ε / (ε ^ 2 + (τ + s) ^ 2))) :=
    fun s => (continuous_const.sub continuous_abs).mul
      (continuous_const.div (by fun_prop) fun τ => by positivity)
  have hcongr : ∫ τ in (-1 : ℝ)..1, fejerSeriesKernel ε τ u =
      (1 / Real.pi) * ((∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (τ + (-1) * u) ^ 2))) +
        ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (τ + 1 * u) ^ 2))) := by
    rw [← intervalIntegral.integral_add ((hc _).intervalIntegrable _ _)
      ((hc _).intervalIntegrable _ _), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ _ => ?_
    simp only [fejerSeriesKernel_eq hε0, neg_one_mul, one_mul, ← sub_eq_add_neg]
    ring
  rw [hcongr]
  have hb1 := fejer_shifted_poisson_integral_le hu hε0 hε1 (-1) (Or.inl rfl)
  have hb2 := fejer_shifted_poisson_integral_le hu hε0 hε1 1 (Or.inr rfl)
  calc (1 / Real.pi) * ((∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (τ + (-1) * u) ^ 2))) +
        ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + (τ + 1 * u) ^ 2)))
      ≤ (1 / Real.pi) * (12 * Real.sqrt ε * (1 / u ^ 2) + 12 * Real.sqrt ε * (1 / u ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) (by positivity)
    _ = (24 * Real.sqrt ε / Real.pi) * (1 / u ^ 2) := by ring

private theorem re_inv_ofReal_add_mul_I {ε : ℝ} (τ : ℝ) :
    ((((ε : ℂ) + (τ : ℂ) * I))⁻¹).re = ε / (ε ^ 2 + τ ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_add_mul_I]
  simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, zero_mul, sub_zero,
    add_zero]

/-- For real antisymmetric polar constants the polar kernel is an explicit Fejér–Poisson term. -/
theorem fejerPolarKernel_eq {ε : ℝ} (ρ τ : ℝ) :
    fejerPolarKernel ((-ρ / 2 : ℝ) : ℂ) ((ρ / 2 : ℝ) : ℂ) ε τ =
      -(ρ / Real.pi) * ((1 - |τ|) * (ε / (ε ^ 2 + τ ^ 2))) + ρ * (1 - |τ|) := by
  have hdiv : ((-ρ / 2 : ℝ) : ℂ) / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) =
      ((-ρ / (2 * Real.pi) : ℝ) : ℂ) * (((ε : ℂ) + (τ : ℂ) * I))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv]; push_cast; ring
  rw [fejerPolarKernel, hdiv, add_re, Complex.re_ofReal_mul, ofReal_re, re_inv_ofReal_add_mul_I]
  ring

theorem continuous_fejerPolarKernel (α β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fejerPolarKernel α β ε) := by
  have hne : ∀ τ : ℝ, (Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I) ≠ 0 := fun τ => by
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h0 => ?_
    have hr := congrArg Complex.re h0
    simp [hε.ne'] at hr
  unfold fejerPolarKernel
  exact (continuous_const.mul (continuous_const.sub continuous_abs)).mul
    (Complex.continuous_re.comp ((continuous_const.div (by fun_prop) hne).add continuous_const))

theorem intervalIntegral_fejerPolarKernel {ε : ℝ} (hε : 0 < ε) (ρ : ℝ) :
    ∫ τ in (-1 : ℝ)..1, fejerPolarKernel ((-ρ / 2 : ℝ) : ℂ) ((ρ / 2 : ℝ) : ℂ) ε τ =
      ρ - (ρ / Real.pi) * ∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + τ ^ 2)) := by
  have hc1 : Continuous (fun τ : ℝ => (1 - |τ|) * (ε / (ε ^ 2 + τ ^ 2))) :=
    (continuous_const.sub continuous_abs).mul
      (continuous_const.div (by fun_prop) fun τ => by positivity)
  have hc2 : Continuous (fun τ : ℝ => 1 - |τ|) := continuous_const.sub continuous_abs
  rw [intervalIntegral.integral_congr (fun τ _ => fejerPolarKernel_eq (ε := ε) ρ τ),
    intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
      ((hc2.const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    fejer_triangle_integral_one]
  ring

/-- Real, Fejér-weighted form of the half-plane Laplace identity on `t = ε + iτ`. -/
theorem integral_fejerSeriesKernel_eq {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    ∫ u, fejerSeriesKernel ε τ u ∂ν =
      ∫ u, fejerDualKernel ε τ u ∂ν + fejerPolarKernel α β ε τ := by
  have ht : 0 < ((ε : ℂ) + (τ : ℂ) * I).re := by simp [hε]
  have hser : ∫ u, fejerSeriesKernel ε τ u ∂ν =
      2 * (1 - |τ|) * (measureSeries ν ((ε : ℂ) + (τ : ℂ) * I)).re := by
    have h : ∫ u : ℝ, ((((ε : ℂ) + (τ : ℂ) * I)) /
        ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) + (τ : ℂ) * I) ^ 2))).re ∂ν =
        (measureSeries ν ((ε : ℂ) + (τ : ℂ) * I)).re :=
      integral_re (integrable_measureSeries_integrand hsupp hmom ht)
    rw [← h, ← integral_const_mul]
    rfl
  have hdual : ∫ u, fejerDualKernel ε τ u ∂ν =
      2 * (1 - |τ|) * (measureDual ν ((ε : ℂ) + (τ : ℂ) * I)).re := by
    have h : ∫ u : ℝ, (cexp (-(2 * Real.pi * (u : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)))).re ∂ν =
        (measureDual ν ((ε : ℂ) + (τ : ℂ) * I)).re :=
      integral_re (integrable_measureDual_integrand hsupp hmom ht)
    rw [← h, ← integral_const_mul]
    rfl
  rw [hser, hdual, measureSeries_eq_of_measureTheta_relation hsupp hmom htheta ht,
    fejerPolarKernel, add_assoc, add_re]
  ring

/-- **Fejér pairing.** Integrating the real Laplace identity against the window `2 (1 - |τ|)`
on `[-1, 1]` and swapping integrals produces the damped `sinc²` moment of `ν`. -/
theorem fejer_pairing_identity {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
        (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν =
      (∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel ε τ u) ∂ν) -
        ∫ τ in (-1 : ℝ)..1, fejerPolarKernel α β ε τ := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hL := integrable_fejerSeriesKernel hsupp hmom hε0 hε1
  have hD := integrable_fejerDualKernel hsupp hmom hε0
  have hD_ii : IntervalIntegrable (fun τ : ℝ => ∫ u, fejerDualKernel ε τ u ∂ν) volume (-1) 1 :=
    intervalIntegrable_iff.mpr hD.integral_prod_left
  have hP_ii : IntervalIntegrable (fejerPolarKernel α β ε) volume (-1) 1 :=
    (continuous_fejerPolarKernel α β hε0).intervalIntegrable _ _
  have hint : ∫ τ in (-1 : ℝ)..1, ∫ u, fejerSeriesKernel ε τ u ∂ν =
      (∫ τ in (-1 : ℝ)..1, ∫ u, fejerDualKernel ε τ u ∂ν) +
        ∫ τ in (-1 : ℝ)..1, fejerPolarKernel α β ε τ := by
    rw [← intervalIntegral.integral_add hD_ii hP_ii]
    exact intervalIntegral.integral_congr fun τ _ =>
      integral_fejerSeriesKernel_eq hsupp hmom htheta hε0 τ
  rw [intervalIntegral_integral_swap hL, intervalIntegral_integral_swap hD] at hint
  have hdual : ∫ u, (∫ τ in (-1 : ℝ)..1, fejerDualKernel ε τ u) ∂ν =
      2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
        (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    rw [intervalIntegral_fejerDualKernel ε (lt_of_lt_of_le zero_lt_one hu).ne']
    ring
  rw [hdual] at hint
  linarith

/-- Collar-blind Fejér defect annihilation: under the degree-one theta law on `[1, ∞)`,
`∫ (sin(π u) / (π u))² dν(u) = 0`. As `ε → 0⁺` the series side is `O(√ε)` (every pole `u ≥ 1`
sits outside the open window), the polar side tends to `ρ - ρ = 0`, and the dual side tends to
`2 ∫ sinc² dν` by dominated convergence. -/
theorem integral_sinc_sq_eq_zero_of_measureTheta_relation {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν = 0 := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  obtain ⟨hβα, hαim, _⟩ := pole_parity_of_measureTheta_relation htheta
  set ρ : ℝ := -2 * α.re
  have hα_eq : α = ((-ρ / 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ρ, hαim]
  have hβ_eq : β = ((ρ / 2 : ℝ) : ℂ) := by
    rw [hβα, hα_eq]; push_cast; ring
  -- The Fejér pairing at every height `ε ∈ (0, 1]`, with the polar part evaluated.
  have hpair : ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
      2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * ε) *
          (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν =
        (∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel ε τ u) ∂ν) +
          ((ρ / Real.pi) * (∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (ε / (ε ^ 2 + τ ^ 2))) - ρ) := by
    intro ε hε0 hε1
    have h := fejer_pairing_identity hsupp hmom htheta hε0 hε1
    rw [hα_eq, hβ_eq, intervalIntegral_fejerPolarKernel hε0] at h
    linarith
  -- Pass `ε_k = 1 / (k + 1) → 0⁺`.
  let εs : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hεs_pos : ∀ k : ℕ, 0 < εs k := fun k => by dsimp only [εs]; positivity
  have hεs_le : ∀ k : ℕ, εs k ≤ 1 := fun k => by
    dsimp only [εs]
    exact div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
  have hεs_nhds : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hεs_pos⟩
  -- Dual side: dominated convergence.
  have hlim_dual : Tendsto (fun k : ℕ => 2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * εs k) *
      (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν) atTop
      (𝓝 (2 * ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν)) := by
    refine Tendsto.const_mul 2 ?_
    refine tendsto_integral_of_dominated_convergence
      (fun u : ℝ => (1 / Real.pi ^ 2) * (1 / u ^ 2))
      (fun k => Measurable.aestronglyMeasurable (by fun_prop)) (hmom.const_mul _)
      (fun k => ?_) ?_
    · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hexp_le : Real.exp (-2 * Real.pi * u * εs k) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 < 2 * Real.pi * u * εs k := mul_pos (by positivity) (hεs_pos k)
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hsin_le : (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ≤
          (1 / Real.pi ^ 2) * (1 / u ^ 2) := by
        rw [div_pow, mul_pow]
        calc Real.sin (Real.pi * u) ^ 2 / (Real.pi ^ 2 * u ^ 2)
            ≤ 1 / (Real.pi ^ 2 * u ^ 2) :=
              div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (by positivity)
          _ = (1 / Real.pi ^ 2) * (1 / u ^ 2) := by rw [one_div_mul_one_div]
      calc Real.exp (-2 * Real.pi * u * εs k) * (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2
          ≤ 1 * ((1 / Real.pi ^ 2) * (1 / u ^ 2)) :=
            mul_le_mul hexp_le hsin_le (sq_nonneg _) zero_le_one
        _ = (1 / Real.pi ^ 2) * (1 / u ^ 2) := one_mul _
    · filter_upwards with u
      have h0 : Tendsto (fun k : ℕ => -2 * Real.pi * u * εs k) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-2 * Real.pi * u)
      have hc : Tendsto (fun k : ℕ => Real.exp (-2 * Real.pi * u * εs k)) atTop (𝓝 1) := by
        have h := (Real.continuous_exp.tendsto 0).comp h0
        rw [Real.exp_zero] at h
        exact h
      simpa only [one_mul] using hc.mul_const ((Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2)
  -- Series side: the uniform `O(√ε)` collar bound.
  have hlim_poisson : Tendsto (fun k : ℕ =>
      ∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ∂ν) atTop (𝓝 0) := by
    set M₂ : ℝ := ∫ u : ℝ, 1 / u ^ 2 ∂ν
    have hmaj : Tendsto (fun k : ℕ => (24 * Real.sqrt (εs k) / Real.pi) * M₂) atTop (𝓝 0) := by
      have hsq : Tendsto (fun k : ℕ => Real.sqrt (εs k)) atTop (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        rw [Real.sqrt_zero] at h
        exact h
      simpa using ((hsq.const_mul 24).div_const Real.pi).mul_const M₂
    refine squeeze_zero' (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_) hmaj
    · refine integral_nonneg fun u => ?_
      exact intervalIntegral.integral_nonneg (by norm_num) fun τ hτ =>
        fejerSeriesKernel_nonneg (hεs_pos k) (abs_le.mpr hτ) u
    · have hε0 := hεs_pos k
      have hε1 := hεs_le k
      have hpt_le : ∀ᵐ u ∂ν, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ≤
          (24 * Real.sqrt (εs k) / Real.pi) * (1 / u ^ 2) := by
        filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
        exact intervalIntegral_fejerSeriesKernel_le hu hε0 hε1
      have hint_lhs : Integrable
          (fun u : ℝ => ∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ν := by
        refine (integrable_fejerSeriesKernel hsupp hmom hε0 hε1).integral_prod_right.congr
          (Eventually.of_forall fun u => ?_)
        show (∫ τ in uIoc (-1 : ℝ) 1, fejerSeriesKernel (εs k) τ u) =
          ∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u
        rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
          intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      calc ∫ u : ℝ, (∫ τ in (-1 : ℝ)..1, fejerSeriesKernel (εs k) τ u) ∂ν
          ≤ ∫ u : ℝ, (24 * Real.sqrt (εs k) / Real.pi) * (1 / u ^ 2) ∂ν :=
            integral_mono_ae hint_lhs (hmom.const_mul _) hpt_le
        _ = (24 * Real.sqrt (εs k) / Real.pi) * M₂ := integral_const_mul _ _
  -- Polar side: the reflected residues cancel.
  have hlim_polar : Tendsto (fun k : ℕ =>
      (ρ / Real.pi) * (∫ τ in (-1 : ℝ)..1, (1 - |τ|) * (εs k / (εs k ^ 2 + τ ^ 2))) - ρ)
      atTop (𝓝 0) := by
    have hp := ((tendsto_fejer_polar.comp hεs_nhds).const_mul (ρ / Real.pi)).sub_const ρ
    have hcancel : (ρ / Real.pi) * Real.pi - ρ = 0 := by
      rw [div_mul_cancel₀ _ Real.pi_ne_zero, sub_self]
    rwa [hcancel] at hp
  have hrhs := hlim_poisson.add hlim_polar
  rw [add_zero] at hrhs
  have hlim_zero : Tendsto (fun k : ℕ => 2 * ∫ u : ℝ, Real.exp (-2 * Real.pi * u * εs k) *
      (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν) atTop (𝓝 0) :=
    hrhs.congr' (Eventually.of_forall fun k => (hpair (hεs_pos k) (hεs_le k)).symm)
  have h2zero := tendsto_nhds_unique hlim_dual hlim_zero
  linarith

/-- Vanishing of `∫ (sin(π u) / (π u))² dν(u)` on `[1, ∞)` forces `ν` to vanish outside the
positive integers `ℕ + 1`. -/
theorem measure_compl_nat_succ_eq_zero_of_sinc_sq {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    (hsinc : ∫ u : ℝ, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν = 0) :
    ν ((Set.range fun k : ℕ => (k : ℝ) + 1)ᶜ) = 0 := by
  have hint : Integrable (fun u : ℝ => (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2) ν := by
    refine (hmom.const_mul (1 / Real.pi ^ 2)).mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, mul_pow]
    calc Real.sin (Real.pi * u) ^ 2 / (Real.pi ^ 2 * u ^ 2)
        ≤ 1 / (Real.pi ^ 2 * u ^ 2) :=
          div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (by positivity)
      _ = (1 / Real.pi ^ 2) * (1 / u ^ 2) := by field_simp
  have hae_zero : ∀ᵐ u ∂ν, (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _) hint).mp hsinc
  have hae_mem : ∀ᵐ u ∂ν, u ∈ Set.range (fun k : ℕ => (k : ℝ) + 1) := by
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp, hae_zero] with u hu hsq
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have hπu : Real.pi * u ≠ 0 := mul_ne_zero Real.pi_ne_zero hu0.ne'
    have hdiv0 : Real.sin (Real.pi * u) / (Real.pi * u) = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
    have hsin0 : Real.sin (Real.pi * u) = 0 := (div_eq_zero_iff.mp hdiv0).resolve_right hπu
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin0
    have hmu : u = (m : ℝ) := by
      have : Real.pi * (m : ℝ) = Real.pi * u := by linarith
      exact (mul_left_cancel₀ Real.pi_ne_zero this).symm
    have hm1 : (1 : ℤ) ≤ m := by
      have : (1 : ℝ) ≤ (m : ℝ) := by linarith
      exact_mod_cast this
    refine ⟨(m - 1).toNat, ?_⟩
    have hm_nat : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
    have hm_real : (((m - 1).toNat : ℤ) : ℝ) = (m : ℝ) - 1 := by exact_mod_cast hm_nat
    push_cast at hm_real
    linarith
  rw [ae_iff] at hae_mem
  exact hae_mem

/-- Any Borel measure vanishing outside the range of an injective sequence `x : ℕ → ℝ` equals
its weighted sum of Dirac masses along `x`. -/
theorem eq_sum_dirac_of_compl_range_eq_zero {ν : Measure ℝ} {x : ℕ → ℝ}
    (hinj : Function.Injective x) (hcompl : ν ((Set.range x)ᶜ) = 0) :
    ν = Measure.sum (fun k : ℕ => ν {x k} • Measure.dirac (x k)) := by
  ext s hs
  rw [Measure.sum_apply _ hs]
  set R : Set ℝ := Set.range x
  have hR_meas : MeasurableSet R := (Set.countable_range x).measurableSet
  have hs_split : ν s = ν (s ∩ R) := by
    have hdiff : ν (s \ R) = 0 := measure_mono_null (fun y hy => hy.2) hcompl
    rw [← measure_inter_add_sdiff s hR_meas, hdiff, add_zero]
  rw [hs_split]
  have hinter : s ∩ R = ⋃ k : ℕ, s ∩ {x k} := by
    ext y
    simp only [mem_inter_iff, R, mem_range, mem_iUnion, mem_singleton_iff]
    constructor
    · rintro ⟨hys, k, rfl⟩
      exact ⟨k, hys, rfl⟩
    · rintro ⟨k, hys, rfl⟩
      exact ⟨hys, k, rfl⟩
  have hdisj : Pairwise (Disjoint on fun k : ℕ => s ∩ {x k}) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun y hyi hyj => hij (hinj ?_)
    exact (mem_singleton_iff.mp hyi.2).symm.trans (mem_singleton_iff.mp hyj.2)
  rw [hinter, measure_iUnion hdisj (fun k => hs.inter (measurableSet_singleton _))]
  refine tsum_congr fun k => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  by_cases hmem : x k ∈ s
  · rw [Set.inter_eq_right.mpr (Set.singleton_subset_iff.mpr hmem), Set.indicator_of_mem hmem,
      Pi.one_apply, mul_one]
  · rw [inter_singleton_eq_empty.mpr hmem, measure_empty, Set.indicator_of_notMem hmem, mul_zero]

/-- **Measure-theoretic Hamburger rigidity (theta-relation form).**
Let `ν` be any Borel measure on `ℝ` supported in `[1, ∞)` (`ν (Iio 1) = 0`) with finite
inverse-square moment `Integrable (fun u => 1 / u²) ν`. If `measureTheta ν` obeys Riemann's
degree-one theta transformation law, then every continuous, singular, or non-integer part of
`ν` vanishes and `ν = ENNReal.ofReal (-2 * α.re) • ∑_{k ≥ 0} δ_{k + 1}`. -/
theorem measure_eq_of_measureTheta_relation {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    β = -α ∧ α.im = 0 ∧ 0 ≤ -2 * α.re ∧
      ν = ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
  obtain ⟨hβα, hαim, _⟩ := pole_parity_of_measureTheta_relation htheta
  have hsinc := integral_sinc_sq_eq_zero_of_measureTheta_relation hsupp hmom htheta
  have hcompl := measure_compl_nat_succ_eq_zero_of_sinc_sq hsupp hmom hsinc
  let x : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hx_inj : Function.Injective x := fun i j hij => by
    dsimp only [x] at hij
    exact_mod_cast add_right_cancel hij
  have hν_decomp : ν = Measure.sum (fun k : ℕ => ν {x k} • Measure.dirac (x k)) :=
    eq_sum_dirac_of_compl_range_eq_zero hx_inj hcompl
  -- Every singleton `ν {x k}` is finite since `1 / u^2` is integrable
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hfin : ∀ k : ℕ, ν {x k} ≠ ⊤ := by
    intro k
    have hc0 : ENNReal.ofReal (1 / (x k) ^ 2) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by dsimp [x]; positivity)
    have hle : ENNReal.ofReal (1 / (x k) ^ 2) * ν {x k} ≤
        ∫⁻ u in {x k}, ‖(1 / u ^ 2 : ℝ)‖ₑ ∂ν := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' (measurableSet_singleton _) fun u hu => ?_
      rw [mem_singleton_iff] at hu
      subst hu
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by dsimp [x]; positivity)]
    have hlt : ∫⁻ u in {x k}, ‖(1 / u ^ 2 : ℝ)‖ₑ ∂ν < ⊤ :=
      lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hmom.hasFiniteIntegral
    exact (ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hle hlt).ne hc0).ne
  -- Define discrete Hamburger coefficients `a 0 = 0`, `a (k + 1) = ((ν {x k}).toReal : ℂ)`
  let a : ℕ → ℂ := fun n => match n with
    | 0 => 0
    | k + 1 => (((ν {x k}).toReal : ℝ) : ℂ)
  have hmom_dirac : Integrable (fun u : ℝ => 1 / u ^ 2)
      (Measure.sum (fun k : ℕ => ν {x k} • Measure.dirac (x k))) := by
    rwa [← hν_decomp]
  have hsum_real : Summable (fun k : ℕ => (ν {x k}).toReal * ‖(1 / (x k) ^ 2 : ℝ)‖) :=
    (integrable_sum_dirac_iff (f := fun u : ℝ => 1 / u ^ 2) hfin).mp hmom_dirac
  have ha_sum : Summable (fun k : ℕ => ‖a (k + 1)‖ / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    refine hsum_real.congr fun k => ?_
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) ^ 2 := by positivity
    simp only [a, x, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_pos hk, Nat.cast_add, Nat.cast_one]
    ring
  -- Identify `measureSeries ν t` with `hamburgerSeries a t` and prove `i`-periodicity of `measureDual ν`
  have hser_eq : ∀ t : ℂ, measureSeries ν t = hamburgerSeries a t := by
    intro t
    unfold measureSeries hamburgerSeries
    conv_lhs => rw [hν_decomp, integral_sum_dirac hfin]
    refine tsum_congr fun k => ?_
    dsimp only [a, x]
    rw [Complex.real_smul, Nat.cast_add, Nat.cast_one]
    push_cast
    ring
  have hdual_per : ∀ t : ℂ, 0 < t.re → measureDual ν (t + I) = measureDual ν t := by
    intro t _
    unfold measureDual
    conv_lhs => rw [hν_decomp, integral_sum_dirac hfin]
    conv_rhs => rw [hν_decomp, integral_sum_dirac hfin]
    refine tsum_congr fun k => ?_
    congr 1
    dsimp only [x]
    rw [show -(2 * (Real.pi : ℂ) * (((k : ℝ) + 1 : ℝ) : ℂ) * (t + I)) =
      -(2 * Real.pi * (((k : ℝ) + 1 : ℝ) : ℂ) * t) +
        ((-((k : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hper : ∀ t : ℂ, 0 < t.re →
      hamburgerSeries a (t + I) - hamburgerSeries a t =
        (α / Real.pi) / (t + I) - (α / Real.pi) / t := by
    intro t ht
    have ht' : 0 < (t + I).re := by simpa using ht
    rw [← hser_eq (t + I), ← hser_eq t,
      measureSeries_eq_of_measureTheta_relation hsupp hmom htheta ht',
      measureSeries_eq_of_measureTheta_relation hsupp hmom htheta ht,
      hdual_per t ht, div_div, div_div]
    ring
  have hcoeff : ∀ k : ℕ, a (k + 1) = -(2 * α) := fun k => by
    have h := coeff_eq_of_hamburgerSeries_periodic_re_pos ha_sum (α / Real.pi) hper k
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [h]; field_simp
  -- Every integer atom carries the same mass `-2 Re α`.
  have hk_re : ∀ k : ℕ, (ν {x k}).toReal = -(2 * α.re) := fun k => by
    have h := congrArg Complex.re (hcoeff k)
    simpa only [a, ofReal_re, neg_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] using h
  have hρ_nonneg : 0 ≤ -2 * α.re := by
    linarith [hk_re 0, ENNReal.toReal_nonneg (a := ν {x 0})]
  have hνk : ∀ k : ℕ, ν {x k} = ENNReal.ofReal (-2 * α.re) := fun k => by
    rw [← ENNReal.ofReal_toReal (hfin k), hk_re k, neg_mul]
  refine ⟨hβα, hαim, hρ_nonneg, ?_⟩
  rw [hν_decomp]
  ext s hs
  rw [Measure.smul_apply, Measure.sum_apply _ hs, Measure.sum_apply _ hs, smul_eq_mul,
    ← ENNReal.tsum_mul_left]
  refine tsum_congr fun k => ?_
  simp only [Measure.smul_apply, smul_eq_mul, hνk k]
  rfl

/-- **Measure-theoretic Hamburger theorem (completed functional-equation form).**
Let `ν` be any Borel measure on `ℝ` with `ν (Iio 1) = 0` and finite `u^{-3/2}` moment
`Integrable (fun u => u ^ (-3/2)) ν`. If `Γ_ℝ(s) measureDirichlet ν s` on `Re s = 3/2` and
`Γ_ℝ(1-s) measureDirichlet ν (1-s)` on `Re s = -1/2` share a strip-holomorphic continuation
`E` of decay `O(1 / (1 + (Im s)²))` up to the polar part `α Γ_ℝ(s) + β Γ_ℝ(s - 1)`, then
`ν = ENNReal.ofReal (-2 * α.re) • ∑_{k ≥ 0} δ_{k + 1}`. -/
theorem measure_eq_of_completed_functional_equation {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0)
    (hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν)
    {E : ℂ → ℂ} {α β : ℂ} {C : ℝ}
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s * measureDirichlet ν s =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 → Complex.Gammaℝ (1 - s) * measureDirichlet ν (1 - s) =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))) :
    β = -α ∧ α.im = 0 ∧ 0 ≤ -2 * α.re ∧
      ν = ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
  have hmom2 : Integrable (fun u : ℝ => 1 / u ^ 2) ν :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hsupp hmom
  have hm34 : MellinConvergent (measureTheta ν) (3 / 4) := by
    have h := hasMellin_measureTheta hsupp (s := (3 / 2 : ℂ)) (by norm_num)
      (by simpa using hmom) hmom2
    simpa [show ((3 / 2 : ℂ) / 2) = (3 / 4 : ℂ) by ring] using h.1
  have htheta : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    have h := converse_theta_relation (ε := 1)
      (continuousOn_measureTheta hsupp hmom2)
      (continuousOn_measureTheta hsupp hmom2)
      hm34 hm34 hE hdecay
      (fun s hs => by
        have hm := hasMellin_measureTheta hsupp (s := s) (by linarith)
          (by rw [hs]; exact hmom) hmom2
        rw [hm.2]; exact hR s hs)
      (fun s hs => by
        have hs1 : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
        have hm := hasMellin_measureTheta hsupp (s := 1 - s) (by linarith)
          (by rw [hs1]; exact hmom) hmom2
        rw [one_mul, hm.2]; exact hL s hs) hx
    simpa only [one_mul] using h
  exact measure_eq_of_measureTheta_relation hsupp hmom2 htheta

/-- **Discrete generalized-frequency corollary.** For any nonnegative weights `a : ℕ → ℝ`
(`0 ≤ a n`) and arbitrary generalized frequencies `lam : ℕ → ℝ` (`1 ≤ lam n`) with
`∑ a_n / λ_n² < ∞`, Riemann's degree-one theta relation forces every active frequency
(`a n ≠ 0`) to be a positive integer `k + 1` and forces the total weight over each positive
integer `k + 1` to equal `-2 α.re`. -/
theorem nonneg_freq_rigidity_of_theta_relation {a : ℕ → ℝ} {lam : ℕ → ℝ}
    (ha : ∀ n : ℕ, 0 ≤ a n) (hlam : ∀ n : ℕ, 1 ≤ lam n)
    (hsum : Summable fun n : ℕ => a n / lam n ^ 2)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x →
      FreqHamburger.freqTheta (fun n => (a n : ℂ)) lam x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * FreqHamburger.freqTheta (fun n => (a n : ℂ)) lam x⁻¹ +
          α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    (∀ n : ℕ, a n ≠ 0 → lam n ∈ Set.range (fun k : ℕ => (k : ℝ) + 1)) ∧
      ∀ k : ℕ, (∑' n : ℕ, if lam n = (k : ℝ) + 1 then ENNReal.ofReal (a n) else 0) =
        ENNReal.ofReal (-2 * α.re) := by
  let ν : Measure ℝ := Measure.sum (fun n : ℕ => ENNReal.ofReal (a n) • Measure.dirac (lam n))
  have hc_fin : ∀ n : ℕ, ENNReal.ofReal (a n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsupp : ν (Iio 1) = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ measurableSet_Iio]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (by simp [hlam n]), mul_zero]
  have hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν := by
    refine integrable_sum_dirac hc_fin ?_
    refine hsum.congr fun n => ?_
    have hl0 : 0 < lam n := lt_of_lt_of_le zero_lt_one (hlam n)
    show a n / lam n ^ 2 = (ENNReal.ofReal (a n)).toReal * ‖1 / lam n ^ 2‖
    rw [ENNReal.toReal_ofReal (ha n), Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_one_div]
  have hθ_eq : ∀ x : ℝ, measureTheta ν x = FreqHamburger.freqTheta (fun n => (a n : ℂ)) lam x := by
    intro x
    unfold measureTheta FreqHamburger.freqTheta
    dsimp only [ν]
    rw [integral_sum_dirac hc_fin]
    refine tsum_congr fun n => ?_
    rw [ENNReal.toReal_ofReal (ha n), Complex.real_smul]
  have htheta_ν : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx; rw [hθ_eq x, hθ_eq x⁻¹]; exact htheta x hx
  obtain ⟨_, _, _, hν_eq⟩ := measure_eq_of_measureTheta_relation hsupp hmom htheta_ν
  refine ⟨fun n han => ?_, fun k => ?_⟩
  · by_contra hnot
    have hpos : 0 < a n := lt_of_le_of_ne (ha n) (Ne.symm han)
    have hle1 : ENNReal.ofReal (a n) ≤ ν {lam n} := by
      have h := Measure.le_sum (fun m : ℕ => ENNReal.ofReal (a m) • Measure.dirac (lam m)) n {lam n}
      rwa [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton _), smul_eq_mul,
        mul_one] at h
    have hzero : ν {lam n} = 0 := by
      rw [hν_eq, Measure.smul_apply, Measure.sum_apply _ (measurableSet_singleton _)]
      have hsum0 : (∑' k : ℕ, Measure.dirac ((k : ℝ) + 1) {lam n}) = 0 := by
        refine (tsum_congr fun k => ?_).trans tsum_zero
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        intro hmem
        rw [mem_singleton_iff] at hmem
        exact hnot ⟨k, hmem⟩
      rw [hsum0, smul_zero]
    rw [hzero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle1
    linarith
  · have heval := congrArg (fun μ : Measure ℝ => μ {(k : ℝ) + 1}) hν_eq
    have hlhs : ν {(k : ℝ) + 1} =
        ∑' n : ℕ, if lam n = (k : ℝ) + 1 then ENNReal.ofReal (a n) else 0 := by
      dsimp only [ν]
      rw [Measure.sum_apply _ (measurableSet_singleton _)]
      refine tsum_congr fun n => ?_
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
      by_cases h : lam n = (k : ℝ) + 1
      · simp [h]
      · simp [h]
    have hrhs : (ENNReal.ofReal (-2 * α.re) •
        Measure.sum (fun m : ℕ => Measure.dirac ((m : ℝ) + 1))) {(k : ℝ) + 1} =
        ENNReal.ofReal (-2 * α.re) := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ (measurableSet_singleton _)]
      rw [tsum_eq_single k]
      · simp
      · intro m hm
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        simp only [mem_singleton_iff]
        intro heq
        exact hm (by exact_mod_cast add_right_cancel heq)
    rw [← hlhs, heval, hrhs]

/-! ## 5. Beurling prime-measure selectivity -/

/-- Iterated multiplicative convolution `P^{* m}` of a Borel measure on `ℝ`. -/
def mulConvPow (P : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 1
  | m + 1 => P ∗ₘ mulConvPow P m

/-- Exponential multiplicative convolution `∑_{m ≥ 0} (m!)⁻¹ P^{* m}` generating the
Beurling integer measure of a prime measure `P` on `(1, ∞)`. -/
def beurlingIntegerMeasure (P : Measure ℝ) : Measure ℝ :=
  Measure.sum fun m : ℕ => ((m.factorial : ℝ≥0∞)⁻¹) • mulConvPow P m

/-- Riemann's prime-power weight `Λ(n) / log n` on `n ≥ 2` (`0` for `n ≤ 1`). -/
def riemannPrimeWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.log n else 0

/-- Riemann's prime-power measure `∑_{n ≥ 2} (Λ(n) / log n) δ_n` on `(1, ∞)`. -/
def riemannPrimeMeasure : Measure ℝ :=
  Measure.sum fun n : ℕ => ENNReal.ofReal (riemannPrimeWeight n) • Measure.dirac (n : ℝ)

theorem riemannPrimeWeight_nonneg (n : ℕ) : 0 ≤ riemannPrimeWeight n := by
  unfold riemannPrimeWeight
  split_ifs with hn
  · have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_pos hn1).le
  · exact le_rfl

theorem ofReal_riemannPrimeWeight_eq_eulerLogDirichletCoeff (n : ℕ) :
    ((riemannPrimeWeight n : ℝ) : ℂ) = RHTower.eulerLogDirichletCoeff n := by
  rcases n with _ | _ | k
  · simp [riemannPrimeWeight]
  · simp [riemannPrimeWeight]
  · have h2 : 2 ≤ k + 2 := by omega
    simp only [riemannPrimeWeight, h2, ↓reduceIte, RHTower.eulerLogDirichletCoeff,
      ofReal_div, Complex.ofReal_log (Nat.cast_nonneg (k + 2)), ofReal_natCast]

theorem riemannPrimeWeight_le_one (n : ℕ) : riemannPrimeWeight n ≤ 1 := by
  have h := RHTower.norm_eulerLogDirichletCoeff_le_one n
  rw [← ofReal_riemannPrimeWeight_eq_eulerLogDirichletCoeff, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (riemannPrimeWeight_nonneg n)] at h
  exact h

instance sfinite_mulConvPow (P : Measure ℝ) [SFinite P] : ∀ m : ℕ, SFinite (mulConvPow P m)
  | 0 => by dsimp only [mulConvPow]; infer_instance
  | m + 1 => by
      haveI := sfinite_mulConvPow P m
      dsimp only [mulConvPow]
      infer_instance

theorem mulConvPow_one (P : Measure ℝ) [SFinite P] : mulConvPow P 1 = P := by
  change P ∗ₘ Measure.dirac 1 = P
  exact Measure.mconv_dirac_one P

theorem le_beurlingIntegerMeasure (P : Measure ℝ) [SFinite P] :
    P ≤ beurlingIntegerMeasure P := by
  have h := Measure.le_sum (fun m : ℕ => ((m.factorial : ℝ≥0∞)⁻¹) • mulConvPow P m) 1
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, mulConvPow_one] at h
  exact h

theorem mulConvPow_succ_Iic_one_eq_zero {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) : ∀ m : ℕ, mulConvPow P (m + 1) (Iic 1) = 0
  | 0 => by rw [mulConvPow_one, hP]
  | m + 1 => by
      have ih := mulConvPow_succ_Iic_one_eq_zero hP m
      haveI : SFinite (mulConvPow P (m + 1)) := sfinite_mulConvPow P (m + 1)
      change (P ∗ₘ mulConvPow P (m + 1)) (Iic 1) = 0
      rw [← lintegral_indicator_one measurableSet_Iic,
        Measure.lintegral_mconv (measurable_one.indicator measurableSet_Iic)]
      have hae_x : ∀ᵐ x ∂P, (1 : ℝ) < x := by
        rw [ae_iff]; simp only [not_lt]; exact hP
      have hae_y : ∀ᵐ y ∂mulConvPow P (m + 1), (1 : ℝ) < y := by
        rw [ae_iff]; simp only [not_lt]; exact ih
      have hzero : ∀ᵐ x ∂P,
          (∫⁻ y : ℝ, (Iic (1 : ℝ)).indicator 1 (x * y) ∂mulConvPow P (m + 1)) = 0 := by
        filter_upwards [hae_x] with x hx
        have hy0 : ∀ᵐ y ∂mulConvPow P (m + 1),
            (Iic (1 : ℝ)).indicator (1 : ℝ → ℝ≥0∞) (x * y) = 0 := by
          filter_upwards [hae_y] with y hy
          have hxy : 1 < x * y := by nlinarith
          exact Set.indicator_of_notMem (by simp [not_le.mpr hxy]) _
        rw [lintegral_congr_ae hy0, lintegral_zero]
      rw [lintegral_congr_ae hzero, lintegral_zero]

theorem beurlingIntegerMeasure_Iio_one_eq_zero {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) : beurlingIntegerMeasure P (Iio 1) = 0 := by
  unfold beurlingIntegerMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  refine (tsum_congr fun m => ?_).trans tsum_zero
  rw [Measure.smul_apply, smul_eq_mul]
  rcases m with _ | m
  · simp [mulConvPow]
  · have h0 : mulConvPow P (m + 1) (Iio 1) = 0 :=
      measure_mono_null Iio_subset_Iic_self (mulConvPow_succ_Iic_one_eq_zero hP m)
    rw [h0, mul_zero]

theorem beurlingIntegerMeasure_singleton_one {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) : beurlingIntegerMeasure P {1} = 1 := by
  unfold beurlingIntegerMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton 1)]
  rw [tsum_eq_single 0]
  · simp [mulConvPow]
  · intro m hm
    rcases m with _ | m
    · exact absurd rfl hm
    · rw [Measure.smul_apply, smul_eq_mul]
      have h0 : mulConvPow P (m + 1) {1} = 0 :=
        measure_mono_null (singleton_subset_iff.mpr (mem_Iic.mpr le_rfl))
          (mulConvPow_succ_Iic_one_eq_zero hP m)
      rw [h0, mul_zero]

/-- The multiplicative test `u ↦ u^{-σ}` on `[1, ∞)` (zero below `1`), valued in `ℝ≥0∞`. -/
def beurlingPowerTest (σ u : ℝ) : ℝ≥0∞ :=
  (Ici (1 : ℝ)).indicator (fun y => ENNReal.ofReal (y ^ (-σ))) u

theorem measurable_beurlingPowerTest (σ : ℝ) : Measurable (beurlingPowerTest σ) :=
  ((by fun_prop : Measurable fun y : ℝ => y ^ (-σ)).ennreal_ofReal).indicator measurableSet_Ici

/-- Multiplicativity of `u^{-σ}` on `[1, ∞)` makes its integral against `P^{* m}` the `m`-th
power of its integral against `P`. -/
theorem lintegral_beurlingPowerTest_mulConvPow {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) (σ : ℝ) :
    ∀ m : ℕ, ∫⁻ u : ℝ, beurlingPowerTest σ u ∂mulConvPow P m =
      (∫⁻ u : ℝ, beurlingPowerTest σ u ∂P) ^ m
  | 0 => by
      rw [pow_zero]
      show ∫⁻ u : ℝ, beurlingPowerTest σ u ∂Measure.dirac 1 = 1
      rw [lintegral_dirac]
      simp [beurlingPowerTest]
  | m + 1 => by
      have ih := lintegral_beurlingPowerTest_mulConvPow hP σ m
      haveI : SFinite (mulConvPow P m) := sfinite_mulConvPow P m
      have hm_meas := measurable_beurlingPowerTest σ
      change ∫⁻ z : ℝ, beurlingPowerTest σ z ∂(P ∗ₘ mulConvPow P m) = _
      rw [Measure.lintegral_mconv hm_meas]
      have hae_x : ∀ᵐ x ∂P, (1 : ℝ) ≤ x :=
        ae_one_le_of_measure_Iio_one_eq_zero (measure_mono_null Iio_subset_Iic_self hP)
      have hae_y : ∀ᵐ y ∂mulConvPow P m, (1 : ℝ) ≤ y := by
        refine ae_one_le_of_measure_Iio_one_eq_zero ?_
        rcases m with _ | k
        · simp [mulConvPow]
        · exact measure_mono_null Iio_subset_Iic_self (mulConvPow_succ_Iic_one_eq_zero hP k)
      have hcongr : ∀ᵐ x ∂P,
          (∫⁻ y : ℝ, beurlingPowerTest σ (x * y) ∂mulConvPow P m) =
            beurlingPowerTest σ x * ∫⁻ y : ℝ, beurlingPowerTest σ y ∂mulConvPow P m := by
        filter_upwards [hae_x] with x hx
        have hinner : ∀ᵐ y ∂mulConvPow P m,
            beurlingPowerTest σ (x * y) = beurlingPowerTest σ x * beurlingPowerTest σ y := by
          filter_upwards [hae_y] with y hy
          have hxy : 1 ≤ x * y := one_le_mul_of_one_le_of_one_le hx hy
          have hx0 : 0 ≤ x := by linarith
          have hy0 : 0 ≤ y := by linarith
          simp only [beurlingPowerTest, Set.indicator_of_mem (mem_Ici.mpr hx),
            Set.indicator_of_mem (mem_Ici.mpr hy), Set.indicator_of_mem (mem_Ici.mpr hxy),
            Real.mul_rpow hx0 hy0, ENNReal.ofReal_mul (Real.rpow_nonneg hx0 _)]
        rw [lintegral_congr_ae hinner, lintegral_const_mul _ hm_meas]
      rw [lintegral_congr_ae hcongr, lintegral_mul_const _ hm_meas, ih, pow_succ']

/-- Exponential Tonelli formula: for any `σ` with `u ↦ u^{-σ}` `P`-integrable (`P(Iic 1) = 0`),
`∫⁻ u^{-σ} d(beurlingIntegerMeasure P) = ENNReal.ofReal (exp (∫ u^{-σ} dP))`. -/
theorem lintegral_beurlingPowerTest_beurlingIntegerMeasure {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) {σ : ℝ} (hmom : Integrable (fun u : ℝ => u ^ (-σ)) P) :
    ∫⁻ u : ℝ, beurlingPowerTest σ u ∂beurlingIntegerMeasure P =
      ENNReal.ofReal (Real.exp (∫ u : ℝ, u ^ (-σ) ∂P)) := by
  have hP_Iio : P (Iio 1) = 0 := measure_mono_null Iio_subset_Iic_self hP
  set L : ℝ := ∫ u : ℝ, u ^ (-σ) ∂P
  have hL_nonneg : 0 ≤ L := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP_Iio] with u hu
    exact Real.rpow_nonneg (by linarith) _
  have hL_lint : ∫⁻ u : ℝ, beurlingPowerTest σ u ∂P = ENNReal.ofReal L := by
    have hae : beurlingPowerTest σ =ᵐ[P] fun u : ℝ => ENNReal.ofReal (u ^ (-σ)) := by
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP_Iio] with u hu
      simp [beurlingPowerTest, hu]
    rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hmom]
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP_Iio] with u hu
    exact Real.rpow_nonneg (by linarith) _
  unfold beurlingIntegerMeasure
  rw [lintegral_sum_measure]
  have hterm : ∀ m : ℕ, ∫⁻ u : ℝ, beurlingPowerTest σ u ∂(((m.factorial : ℝ≥0∞)⁻¹) • mulConvPow P m) =
      ENNReal.ofReal (L ^ m / (m.factorial : ℝ)) := by
    intro m
    rw [lintegral_smul_measure, smul_eq_mul, lintegral_beurlingPowerTest_mulConvPow hP σ m,
      hL_lint, ← ENNReal.ofReal_pow hL_nonneg, div_eq_inv_mul,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_natCast]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) (Real.summable_pow_div_factorial L),
    Real.exp_eq_exp_ℝ, (NormedSpace.expSeries_div_hasSum_exp L).tsum_eq]

theorem integrable_rpow_neg_beurlingIntegerMeasure {P : Measure ℝ} [SFinite P]
    (hP : P (Iic 1) = 0) {σ : ℝ} (hmom : Integrable (fun u : ℝ => u ^ (-σ)) P) :
    Integrable (fun u : ℝ => u ^ (-σ)) (beurlingIntegerMeasure P) := by
  refine ⟨Measurable.aestronglyMeasurable (by fun_prop), ?_⟩
  rw [HasFiniteIntegral]
  have hae : (fun u : ℝ => ‖u ^ (-σ)‖ₑ) =ᵐ[beurlingIntegerMeasure P] beurlingPowerTest σ := by
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero
      (beurlingIntegerMeasure_Iio_one_eq_zero hP)] with u hu
    have hu0 : 0 ≤ u := by linarith
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0 _)]
    simp [beurlingPowerTest, hu]
  rw [lintegral_congr_ae hae, lintegral_beurlingPowerTest_beurlingIntegerMeasure hP hmom]
  exact ENNReal.ofReal_lt_top

theorem integrable_inv_sq_beurlingIntegerMeasure {P : Measure ℝ}
    (hP : P (Iic 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) P) :
    Integrable (fun u : ℝ => 1 / u ^ 2) (beurlingIntegerMeasure P) := by
  have hP_Iio : P (Iio 1) = 0 := measure_mono_null Iio_subset_Iic_self hP
  haveI : SigmaFinite P := sigmaFinite_of_measure_Iio_one_eq_zero hP_Iio hmom
  have hmom_rpow : Integrable (fun u : ℝ => u ^ (-2 : ℝ)) P := by
    refine hmom.congr ?_
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP_Iio] with u hu
    have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
    rw [one_div, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le,
      Real.rpow_natCast]
  have hint := integrable_rpow_neg_beurlingIntegerMeasure hP (σ := 2) hmom_rpow
  refine hint.congr ?_
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero
    (beurlingIntegerMeasure_Iio_one_eq_zero hP)] with u hu
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  rw [one_div, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le,
    Real.rpow_natCast]

/-- **Beurling prime-measure selectivity (theta-relation form).**
Let `P` be any Borel measure on `(1, ∞)` (`P (Iic 1) = 0`) with finite inverse-square moment
`Integrable (fun u => 1 / u²) P`. If the theta transform of `beurlingIntegerMeasure P`
satisfies Riemann's degree-one theta law, then `α = -1/2`, `β = 1/2`,
`beurlingIntegerMeasure P = ∑_{k ≥ 0} δ_{k + 1}`, and `P = riemannPrimeMeasure`. -/
theorem eq_riemannPrimeMeasure_of_beurling_theta_relation {P : Measure ℝ}
    (hP : P (Iic 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) P)
    {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x →
      measureTheta (beurlingIntegerMeasure P) x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingIntegerMeasure P) x⁻¹ +
          α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      beurlingIntegerMeasure P = Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) ∧
      P = riemannPrimeMeasure := by
  have hP_Iio : P (Iio 1) = 0 := measure_mono_null Iio_subset_Iic_self hP
  haveI : SigmaFinite P := sigmaFinite_of_measure_Iio_one_eq_zero hP_Iio hmom
  have hM_supp : beurlingIntegerMeasure P (Iio 1) = 0 :=
    beurlingIntegerMeasure_Iio_one_eq_zero hP
  have hM_mom : Integrable (fun u : ℝ => 1 / u ^ 2) (beurlingIntegerMeasure P) :=
    integrable_inv_sq_beurlingIntegerMeasure hP hmom
  obtain ⟨hβα, hαim, hρ_nonneg, hM_eq⟩ :=
    measure_eq_of_measureTheta_relation hM_supp hM_mom htheta
  -- Fix `α = -1/2`, `β = 1/2` by evaluating at `{1}`
  have h1_lhs : beurlingIntegerMeasure P {1} = 1 := beurlingIntegerMeasure_singleton_one hP
  have h1_rhs : (ENNReal.ofReal (-2 * α.re) •
      Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) {1} =
      ENNReal.ofReal (-2 * α.re) := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ (measurableSet_singleton 1)]
    rw [tsum_eq_single 0]
    · simp
    · intro k hk
      rw [Measure.dirac_apply, Set.indicator_of_notMem]
      simp only [mem_singleton_iff]
      intro heq
      have hk0 : k = 0 := by
        have : (k : ℝ) = 0 := by linarith
        exact_mod_cast this
      exact hk hk0
  have hofReal_one : ENNReal.ofReal (-2 * α.re) = 1 := by
    rw [← h1_rhs, ← hM_eq, h1_lhs]
  have hρ_eq_one : -2 * α.re = 1 := by
    have := congrArg ENNReal.toReal hofReal_one
    rwa [ENNReal.toReal_ofReal hρ_nonneg, ENNReal.toReal_one] at this
  have hα_val : α = -1 / 2 := by
    apply Complex.ext
    · simp; linarith
    · simp [hαim]
  have hβ_val : β = 1 / 2 := by rw [hβα, hα_val]; ring
  have hM_nat : beurlingIntegerMeasure P =
      Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
    rw [hM_eq, hofReal_one, one_smul]
  refine ⟨hα_val, hβ_val, hM_nat, ?_⟩
  -- Force `P` onto `ℕ` with weights `w n := (P {n}).toReal ≤ 1`
  have hP_le_M : P ≤ beurlingIntegerMeasure P := le_beurlingIntegerMeasure P
  have hP_compl_nat : P ((Set.range (Nat.cast : ℕ → ℝ))ᶜ) = 0 := by
    have hsub : (Set.range (Nat.cast : ℕ → ℝ))ᶜ ⊆
        Iic 1 ∪ (Set.range fun k : ℕ => (k : ℝ) + 1)ᶜ := by
      intro u hu
      by_cases h1 : u ≤ 1
      · exact Or.inl h1
      · refine Or.inr fun ⟨k, hk⟩ => hu ⟨k + 1, ?_⟩
        push_cast
        linarith
    have hR1_meas : MeasurableSet (Set.range fun k : ℕ => (k : ℝ) + 1) := by
      rw [show (Set.range fun k : ℕ => (k : ℝ) + 1) = ⋃ k : ℕ, {(k : ℝ) + 1} by
        ext y; simp [eq_comm]]
      exact MeasurableSet.iUnion fun k => measurableSet_singleton _
    have hM_compl : (Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)))
        ((Set.range fun k : ℕ => (k : ℝ) + 1)ᶜ) = 0 := by
      rw [Measure.sum_apply _ hR1_meas.compl]
      refine (tsum_congr fun k => ?_).trans tsum_zero
      rw [Measure.dirac_apply, Set.indicator_of_notMem]
      intro hmem
      exact hmem ⟨k, rfl⟩
    have hP_r1 : P ((Set.range fun k : ℕ => (k : ℝ) + 1)ᶜ) = 0 := by
      rw [← nonpos_iff_eq_zero, ← hM_compl, ← hM_nat]
      exact hP_le_M _
    refine measure_mono_null hsub ?_
    exact measure_union_null hP hP_r1
  have hP_decomp : P = Measure.sum (fun n : ℕ => P {(n : ℝ)} • Measure.dirac (n : ℝ)) :=
    eq_sum_dirac_of_compl_range_eq_zero Nat.cast_injective hP_compl_nat
  have hP_le_one : ∀ n : ℕ, P {(n : ℝ)} ≤ 1 := by
    intro n
    rcases n with _ | k
    · have h0 : P {(0 : ℝ)} = 0 :=
        measure_mono_null (singleton_subset_iff.mpr (mem_Iic.mpr (by norm_num : (0 : ℝ) ≤ 1))) hP
      simp [h0]
    · calc P {((k + 1 : ℕ) : ℝ)}
          ≤ beurlingIntegerMeasure P {((k + 1 : ℕ) : ℝ)} := hP_le_M _
        _ = (Measure.sum fun m : ℕ => Measure.dirac ((m : ℝ) + 1)) {((k + 1 : ℕ) : ℝ)} := by
            rw [hM_nat]
        _ = 1 := by
            rw [Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single k]
            · rw [Nat.cast_add, Nat.cast_one]; simp
            · intro m hm
              rw [Measure.dirac_apply, Set.indicator_of_notMem]
              simp only [mem_singleton_iff, Nat.cast_add, Nat.cast_one]
              intro heq
              exact hm (by exact_mod_cast add_right_cancel heq)
  have hP_fin : ∀ n : ℕ, P {(n : ℝ)} ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hP_le_one n)
  let w : ℕ → ℝ := fun n => (P {(n : ℝ)}).toReal
  have hw_nonneg : ∀ n : ℕ, 0 ≤ w n := fun _ => ENNReal.toReal_nonneg
  have hw_le_one : ∀ n : ℕ, w n ≤ 1 := fun n =>
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hP_le_one n)
  have hw0 : w 0 = 0 := by
    have h0 : P {(0 : ℝ)} = 0 :=
      measure_mono_null (singleton_subset_iff.mpr (mem_Iic.mpr (by norm_num : (0 : ℝ) ≤ 1))) hP
    simp [w, h0]
  have hw1 : w 1 = 0 := by
    have h1 : P {(1 : ℝ)} = 0 :=
      measure_mono_null (singleton_subset_iff.mpr (mem_Iic.mpr (le_refl (1 : ℝ)))) hP
    simp [w, h1]
  -- Compare `LSeries (w ·)` with `RHTower.eulerLogDirichletCoeff` on `σ ≥ 2`
  let f : ℕ → ℂ := fun n => ((w n : ℝ) : ℂ)
  have hf_sum2 : LSeriesSummable f (2 : ℂ) := by
    have h1 : LSeriesSummable (1 : ℕ → ℂ) (2 : ℂ) := LSeriesSummable_one_iff.mpr (by norm_num)
    have h1n : Summable fun n => ‖LSeries.term (1 : ℕ → ℂ) (2 : ℂ) n‖ :=
      summable_norm_iff.mpr h1
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) h1n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
      simp only [Pi.one_apply, norm_one, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (norm_nonneg _))
      dsimp only [f]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg n)]
      exact hw_le_one n
  have hf_abs : LSeries.abscissaOfAbsConv f < ⊤ :=
    hf_sum2.abscissaOfAbsConv_le.trans_lt (by simp)
  have hev_LSeries : (fun σ : ℝ => LSeries f (σ : ℂ)) =ᶠ[atTop]
      fun σ : ℝ => LSeries RHTower.eulerLogDirichletCoeff (σ : ℂ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ
    have hσ1 : 1 < ((σ : ℂ)).re := by simp; linarith
    -- First show `Integrable (fun u => u ^ (-σ)) P`
    have hmom_σ : Integrable (fun u : ℝ => u ^ (-σ)) P := by
      refine hmom.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP_Iio] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      have h2eq : 1 / u ^ 2 = u ^ (-2 : ℝ) := by
        rw [one_div, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le,
          Real.rpow_natCast]
      rw [h2eq]
      exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
    -- Evaluate `∫⁻ beurlingPowerTest σ dM` on both sides of `hM_nat`
    have htonelli := lintegral_beurlingPowerTest_beurlingIntegerMeasure hP hmom_σ
    rw [hM_nat, lintegral_sum_measure] at htonelli
    have hnat_sum : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-σ)) := by
      have hzeta_sum : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ σ) := by
        have hc := LSeriesSummable_one_iff.mpr hσ1
        have hcn := summable_norm_iff.mpr hc
        have hshift := (summable_nat_add_iff 1).mpr hcn
        refine hshift.congr fun k => ?_
        rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), norm_div, Pi.one_apply, norm_one]
        have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k), ofReal_re, Nat.cast_succ]
      refine hzeta_sum.congr fun k => ?_
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [one_div, Real.rpow_neg hkpos.le]
    have htonelli_rhs : (∑' k : ℕ, ∫⁻ u : ℝ, beurlingPowerTest σ u ∂Measure.dirac ((k : ℝ) + 1)) =
        ENNReal.ofReal (∑' k : ℕ, ((k : ℝ) + 1) ^ (-σ)) := by
      have hterm : ∀ k : ℕ,
          ∫⁻ u : ℝ, beurlingPowerTest σ u ∂Measure.dirac ((k : ℝ) + 1) =
            ENNReal.ofReal (((k : ℝ) + 1) ^ (-σ)) := by
        intro k
        rw [lintegral_dirac]
        have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
        simp [beurlingPowerTest, hk1]
      simp_rw [hterm]
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun k => Real.rpow_nonneg (by positivity) _) hnat_sum).symm
    rw [htonelli_rhs] at htonelli
    have hexp_P : Real.exp (∫ u : ℝ, u ^ (-σ) ∂P) = ∑' k : ℕ, ((k : ℝ) + 1) ^ (-σ) := by
      have := congrArg ENNReal.toReal htonelli
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,
        ENNReal.toReal_ofReal (tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _)] at this
      exact this.symm
    -- Compare with `exp (canonicalEulerLogZeta σ) = riemannZeta σ`
    have hzeta_re : (riemannZeta (σ : ℂ)).re = ∑' k : ℕ, ((k : ℝ) + 1) ^ (-σ) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hσ1]
      have hterm_eq : ∀ k : ℕ, (1 : ℂ) / ((k : ℂ) + 1) ^ (σ : ℂ) =
          ((((k : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
        intro k
        have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        rw [one_div, show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
          ← Complex.ofReal_cpow hkpos.le, ← Complex.ofReal_inv, ← Real.rpow_neg hkpos.le]
      simp_rw [hterm_eq, ← Complex.ofReal_tsum, ofReal_re]
    have hg_term : ∀ n : ℕ, LSeries.term RHTower.eulerLogDirichletCoeff (σ : ℂ) n =
        ((riemannPrimeWeight n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term_zero, riemannPrimeWeight]
      · rw [LSeries.term_of_ne_zero hn, ← ofReal_riemannPrimeWeight_eq_eulerLogDirichletCoeff]
        have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        rw [div_eq_mul_inv, show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast,
          ← Complex.ofReal_cpow hnpos.le, ← Complex.ofReal_inv, ← Real.rpow_neg hnpos.le,
          Complex.ofReal_mul]
    have hg_real : LSeries RHTower.eulerLogDirichletCoeff (σ : ℂ) =
        ((∑' n : ℕ, riemannPrimeWeight n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      unfold LSeries
      simp_rw [hg_term, ← Complex.ofReal_tsum]
    have hexp_ζ : Real.exp (∑' n : ℕ, riemannPrimeWeight n * (n : ℝ) ^ (-σ)) =
        ∑' k : ℕ, ((k : ℝ) + 1) ^ (-σ) := by
      have he := RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta (s := (σ : ℂ)) hσ1
      unfold RHTower.canonicalEulerLogZeta at he
      rw [hg_real, ← Complex.ofReal_exp] at he
      have hre := congrArg Complex.re he
      rwa [ofReal_re, hzeta_re] at hre
    have hint_eq_sum : ∫ u : ℝ, u ^ (-σ) ∂P =
        ∑' n : ℕ, riemannPrimeWeight n * (n : ℝ) ^ (-σ) :=
      Real.exp_injective (hexp_P.trans hexp_ζ.symm)
    -- Express `LSeries f (σ : ℂ)` as `((∫ u, u ^ (-σ) ∂P : ℝ) : ℂ)`
    have hf_real : LSeries f (σ : ℂ) = ((∫ u : ℝ, u ^ (-σ) ∂P : ℝ) : ℂ) := by
      have hint_P : ∫ u : ℝ, u ^ (-σ) ∂P = ∑' n : ℕ, w n * (n : ℝ) ^ (-σ) := by
        conv_lhs => rw [hP_decomp, integral_sum_dirac hP_fin]
        rfl
      rw [hint_P]
      unfold LSeries
      have hf_term : ∀ n : ℕ, LSeries.term f (σ : ℂ) n =
          ((w n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
        intro n
        rcases eq_or_ne n 0 with rfl | hn
        · simp [LSeries.term_zero, hw0]
        · rw [LSeries.term_of_ne_zero hn]
          dsimp only [f]
          have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
          rw [div_eq_mul_inv, show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast,
            ← Complex.ofReal_cpow hnpos.le, ← Complex.ofReal_inv, ← Real.rpow_neg hnpos.le,
            Complex.ofReal_mul]
      simp_rw [hf_term, ← Complex.ofReal_tsum]
    rw [hf_real, hg_real, hint_eq_sum]
  have hw_eq : ∀ n : ℕ, w n = riemannPrimeWeight n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hw0, riemannPrimeWeight]
    · have hc := LSeries.eq_of_LSeries_eventually_eq hf_abs
        RHTower.eulerLogDirichletCoeff_abscissa_lt_top hev_LSeries hn
      dsimp only [f] at hc
      rw [← ofReal_riemannPrimeWeight_eq_eulerLogDirichletCoeff] at hc
      exact Complex.ofReal_injective hc
  rw [hP_decomp]
  unfold riemannPrimeMeasure
  congr 1
  ext n : 1
  have hPn : P {(n : ℝ)} = ENNReal.ofReal (riemannPrimeWeight n) := by
    rw [← hw_eq n]
    exact (ENNReal.ofReal_toReal (hP_fin n)).symm
  rw [hPn]

/-- **Beurling prime-measure selectivity (completed functional-equation form).**
Let `P` be any Borel measure on `(1, ∞)` (`P (Iic 1) = 0`) with finite `u^{-3/2}` moment
`Integrable (fun u => u ^ (-3/2)) P`. If `M := beurlingIntegerMeasure P` satisfies Riemann's
completed `Γ_ℝ(s)` functional equation on the strip `-1/2 ≤ Re s ≤ 3/2`, then `α = -1/2`,
`β = 1/2`, `beurlingIntegerMeasure P = ∑_{k ≥ 0} δ_{k + 1}`, and `P = riemannPrimeMeasure`. -/
theorem eq_riemannPrimeMeasure_of_beurling_functional_equation {P : Measure ℝ}
    (hP : P (Iic 1) = 0)
    (hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) P)
    {E : ℂ → ℂ} {α β : ℂ} {C : ℝ}
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * measureDirichlet (beurlingIntegerMeasure P) s =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 →
      Complex.Gammaℝ (1 - s) * measureDirichlet (beurlingIntegerMeasure P) (1 - s) =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      beurlingIntegerMeasure P = Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) ∧
      P = riemannPrimeMeasure := by
  have hP_Iio : P (Iio 1) = 0 := measure_mono_null Iio_subset_Iic_self hP
  have hmom2 : Integrable (fun u : ℝ => 1 / u ^ 2) P :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hP_Iio hmom
  haveI : SigmaFinite P := sigmaFinite_of_measure_Iio_one_eq_zero hP_Iio hmom2
  have hM_supp : beurlingIntegerMeasure P (Iio 1) = 0 :=
    beurlingIntegerMeasure_Iio_one_eq_zero hP
  have hM_mom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (beurlingIntegerMeasure P) :=
    integrable_rpow_neg_beurlingIntegerMeasure hP (σ := 3 / 2) (by simpa using hmom)
  have hM_mom2 : Integrable (fun u : ℝ => 1 / u ^ 2) (beurlingIntegerMeasure P) :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hM_supp hM_mom
  have hm34 : MellinConvergent (measureTheta (beurlingIntegerMeasure P)) (3 / 4) := by
    have h := hasMellin_measureTheta hM_supp (s := (3 / 2 : ℂ)) (by norm_num)
      (by simpa using hM_mom) hM_mom2
    simpa [show ((3 / 2 : ℂ) / 2) = (3 / 4 : ℂ) by ring] using h.1
  have htheta : ∀ x : ℝ, 0 < x →
      measureTheta (beurlingIntegerMeasure P) x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta (beurlingIntegerMeasure P) x⁻¹ +
          α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    have h := converse_theta_relation (ε := 1)
      (continuousOn_measureTheta hM_supp hM_mom2)
      (continuousOn_measureTheta hM_supp hM_mom2)
      hm34 hm34 hE hdecay
      (fun s hs => by
        have hm := hasMellin_measureTheta hM_supp (s := s) (by linarith)
          (by rw [hs]; exact hM_mom) hM_mom2
        rw [hm.2]; exact hR s hs)
      (fun s hs => by
        have hs1 : (1 - s).re = 3 / 2 := by simp [hs]; norm_num
        have hm := hasMellin_measureTheta hM_supp (s := 1 - s) (by linarith)
          (by rw [hs1]; exact hM_mom) hM_mom2
        rw [one_mul, hm.2]; exact hL s hs) hx
    simpa only [one_mul] using h
  exact eq_riemannPrimeMeasure_of_beurling_theta_relation hP hmom2 htheta

theorem riemannPrimeMeasure_Iic_one_eq_zero : riemannPrimeMeasure (Iic 1) = 0 := by
  unfold riemannPrimeMeasure
  rw [Measure.sum_apply _ measurableSet_Iic]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rw [Measure.smul_apply, smul_eq_mul]
  rcases n with _ | _ | k
  · simp [riemannPrimeWeight]
  · simp [riemannPrimeWeight]
  · rw [Measure.dirac_apply' _ measurableSet_Iic, Set.indicator_of_notMem, mul_zero]
    simp only [mem_Iic, not_le]
    exact_mod_cast (by omega : 1 < k + 2)

theorem integrable_rpow_neg_three_halves_riemannPrimeMeasure :
    Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) riemannPrimeMeasure := by
  unfold riemannPrimeMeasure
  refine integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top) ?_
  have hc : LSeriesSummable (1 : ℕ → ℂ) ((3 / 2 : ℝ) : ℂ) := LSeriesSummable_one_iff.mpr (by norm_num)
  have hcn := summable_norm_iff.mpr hc
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) hcn
  rcases eq_or_ne n 0 with rfl | hn
  · simp [riemannPrimeWeight, LSeries.term_zero]
  · rw [ENNReal.toReal_ofReal (riemannPrimeWeight_nonneg n), LSeries.term_of_ne_zero hn,
      norm_div, Pi.one_apply, norm_one,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), ofReal_re]
    have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hnpos.le _),
      Real.rpow_neg hnpos.le, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (riemannPrimeWeight_le_one n)
      (Real.rpow_nonneg hnpos.le _)

/-- The exponential multiplicative convolution of `riemannPrimeMeasure` is identically the
uniform counting measure on the positive integers `∑_{k ≥ 0} δ_{k + 1}`. -/
theorem beurlingIntegerMeasure_riemannPrimeMeasure :
    beurlingIntegerMeasure riemannPrimeMeasure =
      Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
  have hP : riemannPrimeMeasure (Iic 1) = 0 := riemannPrimeMeasure_Iic_one_eq_zero
  have hP_Iio : riemannPrimeMeasure (Iio 1) = 0 := measure_mono_null Iio_subset_Iic_self hP
  have hmom : Integrable (fun u : ℝ => 1 / u ^ 2) riemannPrimeMeasure :=
    integrable_inv_sq_of_integrable_rpow_neg_three_halves hP_Iio
      integrable_rpow_neg_three_halves_riemannPrimeMeasure
  haveI : SigmaFinite riemannPrimeMeasure :=
    sigmaFinite_of_measure_Iio_one_eq_zero hP_Iio hmom
  set R : Set ℝ := Set.range (fun k : ℕ => (k : ℝ) + 1)
  have hR_meas : MeasurableSet R := by
    rw [show R = ⋃ k : ℕ, {(k : ℝ) + 1} by ext y; simp [R, eq_comm]]
    exact MeasurableSet.iUnion fun k => measurableSet_singleton _
  have hP_compl : riemannPrimeMeasure Rᶜ = 0 := by
    unfold riemannPrimeMeasure
    rw [Measure.sum_apply _ hR_meas.compl]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul]
    rcases n with _ | k
    · simp [riemannPrimeWeight]
    · rw [Measure.dirac_apply, Set.indicator_of_notMem, mul_zero]
      intro hmem
      exact hmem ⟨k, by push_cast; rfl⟩
  -- Products of positive integers are positive integers, so every convolution power stays on `R`.
  have hpow_compl : ∀ m : ℕ, mulConvPow riemannPrimeMeasure m Rᶜ = 0 := by
    intro m
    induction m with
    | zero =>
        dsimp only [mulConvPow]
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        intro hmem
        exact hmem ⟨0, by norm_num⟩
    | succ m ih =>
        haveI : SFinite (mulConvPow riemannPrimeMeasure m) := sfinite_mulConvPow _ m
        change (riemannPrimeMeasure ∗ₘ mulConvPow riemannPrimeMeasure m) Rᶜ = 0
        rw [← lintegral_indicator_one hR_meas.compl,
          Measure.lintegral_mconv (measurable_one.indicator hR_meas.compl)]
        have hae_x : ∀ᵐ x ∂riemannPrimeMeasure, x ∈ R := by
          rw [ae_iff]; exact hP_compl
        have hae_y : ∀ᵐ y ∂mulConvPow riemannPrimeMeasure m, y ∈ R := by
          rw [ae_iff]; exact ih
        have hzero : ∀ᵐ x ∂riemannPrimeMeasure,
            (∫⁻ y : ℝ, Rᶜ.indicator 1 (x * y) ∂mulConvPow riemannPrimeMeasure m) = 0 := by
          filter_upwards [hae_x] with x ⟨j, hj⟩
          have hy0 : ∀ᵐ y ∂mulConvPow riemannPrimeMeasure m,
              Rᶜ.indicator (1 : ℝ → ℝ≥0∞) (x * y) = 0 := by
            filter_upwards [hae_y] with y ⟨k, hk⟩
            refine Set.indicator_of_notMem
              (fun hnot : x * y ∈ Rᶜ => hnot ⟨(j + 1) * (k + 1) - 1, ?_⟩) _
            have hprod : 1 ≤ (j + 1) * (k + 1) := Nat.mul_pos (Nat.succ_pos j) (Nat.succ_pos k)
            have hcast : (((j + 1) * (k + 1) - 1 : ℕ) : ℝ) + 1 =
                ((j + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
              exact_mod_cast Nat.sub_add_cancel hprod
            rw [← hj, ← hk]
            show (((j + 1) * (k + 1) - 1 : ℕ) : ℝ) + 1 = ((j : ℝ) + 1) * ((k : ℝ) + 1)
            exact_mod_cast hcast
          rw [lintegral_congr_ae hy0, lintegral_zero]
        rw [lintegral_congr_ae hzero, lintegral_zero]
  set M : Measure ℝ := beurlingIntegerMeasure riemannPrimeMeasure
  have hM_compl : M Rᶜ = 0 := by
    dsimp only [M, beurlingIntegerMeasure]
    rw [Measure.sum_apply _ hR_meas.compl]
    refine (tsum_congr fun m => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul, hpow_compl m, mul_zero]
  let x : ℕ → ℝ := fun k => (k : ℝ) + 1
  have hx_inj : Function.Injective x := fun i j hij => by
    dsimp only [x] at hij
    exact_mod_cast add_right_cancel hij
  have hM_decomp : M = Measure.sum (fun k : ℕ => M {x k} • Measure.dirac (x k)) :=
    eq_sum_dirac_of_compl_range_eq_zero hx_inj hM_compl
  have hM_mom : Integrable (fun u : ℝ => 1 / u ^ 2) M :=
    integrable_inv_sq_beurlingIntegerMeasure hP hmom
  have hM_fin : ∀ k : ℕ, M {x k} ≠ ⊤ := by
    intro k
    have hc0 : ENNReal.ofReal (1 / (x k) ^ 2) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by dsimp [x]; positivity)
    have hle : ENNReal.ofReal (1 / (x k) ^ 2) * M {x k} ≤
        ∫⁻ u in {x k}, ‖(1 / u ^ 2 : ℝ)‖ₑ ∂M := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' (measurableSet_singleton _) fun u hu => ?_
      rw [mem_singleton_iff] at hu
      subst hu
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (by dsimp [x]; positivity)]
    have hlt : ∫⁻ u in {x k}, ‖(1 / u ^ 2 : ℝ)‖ₑ ∂M < ⊤ :=
      lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hM_mom.hasFiniteIntegral
    exact (ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hle hlt).ne hc0).ne
  let c : ℕ → ℂ := fun n => match n with
    | 0 => 0
    | k + 1 => (((M {x k}).toReal : ℝ) : ℂ)
  have hc_sum2 : LSeriesSummable c (2 : ℂ) := by
    have hmom_dirac : Integrable (fun u : ℝ => 1 / u ^ 2)
        (Measure.sum (fun k : ℕ => M {x k} • Measure.dirac (x k))) := by
      rwa [← hM_decomp]
    have hsum_real : Summable (fun k : ℕ => (M {x k}).toReal * ‖(1 / (x k) ^ 2 : ℝ)‖) :=
      (integrable_sum_dirac_iff (f := fun u : ℝ => 1 / u ^ 2) hM_fin).mp hmom_dirac
    have hshift : Summable (fun k : ℕ => ‖LSeries.term c (2 : ℂ) (k + 1)‖) := by
      refine hsum_real.congr fun k => ?_
      have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) ^ 2 := by positivity
      conv_rhs => rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k), norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k), re_ofNat, Real.rpow_ofNat]
      simp only [c, x, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_pos hk, Nat.cast_succ]
      ring
    exact Summable.of_norm ((summable_nat_add_iff 1).mp hshift)
  have hc_abs : LSeries.abscissaOfAbsConv c < ⊤ :=
    hc_sum2.abscissaOfAbsConv_le.trans_lt (by simp)
  have h1_abs : LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < ⊤ :=
    (show LSeriesSummable (1 : ℕ → ℂ) (2 : ℂ) from
      LSeriesSummable_one_iff.mpr (by norm_num)).abscissaOfAbsConv_le.trans_lt
      (by simp)
  have hev_eq : (fun σ : ℝ => LSeries c (σ : ℂ)) =ᶠ[atTop]
      fun σ : ℝ => LSeries (1 : ℕ → ℂ) (σ : ℂ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ
    have hσ1 : 1 < ((σ : ℂ)).re := by simp; linarith
    have hmom_σ : Integrable (fun u : ℝ => u ^ (-σ)) riemannPrimeMeasure := by
      refine hmom.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hP_Iio] with u hu
      have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
      have h2eq : 1 / u ^ 2 = u ^ (-2 : ℝ) := by
        rw [one_div, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hu0.le,
          Real.rpow_natCast]
      rw [h2eq]
      exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)
    have hM_mom_σ : Integrable (fun u : ℝ => u ^ (-σ)) M :=
      integrable_rpow_neg_beurlingIntegerMeasure hP hmom_σ
    have htonelli := lintegral_beurlingPowerTest_beurlingIntegerMeasure hP hmom_σ
    have hM_lint : ∫⁻ u : ℝ, beurlingPowerTest σ u ∂M =
        ENNReal.ofReal (∫ u : ℝ, u ^ (-σ) ∂M) := by
      have hae : beurlingPowerTest σ =ᵐ[M] fun u : ℝ => ENNReal.ofReal (u ^ (-σ)) := by
        filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero
          (beurlingIntegerMeasure_Iio_one_eq_zero hP)] with u hu
        simp [beurlingPowerTest, hu]
      rw [lintegral_congr_ae hae, ← ofReal_integral_eq_lintegral_ofReal hM_mom_σ]
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero
        (beurlingIntegerMeasure_Iio_one_eq_zero hP)] with u hu
      exact Real.rpow_nonneg (by linarith) _
    rw [hM_lint] at htonelli
    have hM_nonneg : 0 ≤ ∫ u : ℝ, u ^ (-σ) ∂M := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero
        (beurlingIntegerMeasure_Iio_one_eq_zero hP)] with u hu
      exact Real.rpow_nonneg (by linarith) _
    have hint_M_eq : ∫ u : ℝ, u ^ (-σ) ∂M = Real.exp (∫ u : ℝ, u ^ (-σ) ∂riemannPrimeMeasure) := by
      have := congrArg ENNReal.toReal htonelli
      rwa [ENNReal.toReal_ofReal hM_nonneg, ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
    -- Evaluate `∫ u ^ (-σ) d(riemannPrimeMeasure)` as `canonicalEulerLogZeta σ`
    have hint_P_eq : ((∫ u : ℝ, u ^ (-σ) ∂riemannPrimeMeasure : ℝ) : ℂ) =
        RHTower.canonicalEulerLogZeta (σ : ℂ) := by
      unfold riemannPrimeMeasure RHTower.canonicalEulerLogZeta LSeries
      rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top), Complex.ofReal_tsum]
      refine tsum_congr fun n => ?_
      rw [ENNReal.toReal_ofReal (riemannPrimeWeight_nonneg n), smul_eq_mul]
      rcases eq_or_ne n 0 with rfl | hn
      · simp [riemannPrimeWeight, LSeries.term_zero]
      · rw [LSeries.term_of_ne_zero hn, ← ofReal_riemannPrimeWeight_eq_eulerLogDirichletCoeff]
        have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        rw [div_eq_mul_inv, show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast,
          ← Complex.ofReal_cpow hnpos.le, ← Complex.ofReal_inv, ← Real.rpow_neg hnpos.le,
          Complex.ofReal_mul]
    have hLc : LSeries c (σ : ℂ) = ((∫ u : ℝ, u ^ (-σ) ∂M : ℝ) : ℂ) := by
      conv_rhs => rw [hM_decomp, integral_sum_dirac hM_fin]
      rw [Complex.ofReal_tsum]
      unfold LSeries
      rw [Summable.tsum_eq_zero_add (hc_sum2.of_re_le_re (by simp; linarith))]
      simp only [LSeries.term_zero, zero_add]
      refine tsum_congr fun k => ?_
      rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero k)]
      dsimp only [c, x]
      have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      rw [smul_eq_mul, Complex.ofReal_mul, div_eq_mul_inv,
        show ((k + 1 : ℕ) : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_cpow hkpos.le, ← Complex.ofReal_inv, ← Real.rpow_neg hkpos.le]
    have hL1 : LSeries (1 : ℕ → ℂ) (σ : ℂ) = riemannZeta (σ : ℂ) :=
      LSeries_one_eq_riemannZeta hσ1
    rw [hLc, hint_M_eq, Complex.ofReal_exp, hint_P_eq,
      RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hσ1, hL1]
  rw [hM_decomp]
  congr 1
  ext k : 1
  have hck := LSeries.eq_of_LSeries_eventually_eq hc_abs h1_abs hev_eq (Nat.succ_ne_zero k)
  dsimp only [c, Pi.one_apply] at hck
  have htoReal : (M {x k}).toReal = 1 := Complex.ofReal_injective hck
  have hMk : M {x k} = 1 := by
    rw [← ENNReal.ofReal_toReal (hM_fin k), htoReal, ENNReal.ofReal_one]
  rw [hMk, one_smul]

end GaloisForLFunctions.ArithmeticPositiveDuality
