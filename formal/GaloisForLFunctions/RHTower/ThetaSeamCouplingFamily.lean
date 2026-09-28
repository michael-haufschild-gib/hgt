import GaloisForLFunctions.RHTower.ThetaRenewalResonancePhase
import GaloisForLFunctions.RHTower.ThetaQuadratureDefectSpectralKernel
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel
import GaloisForLFunctions.RHTower.GlobalParityWall

/-!
# The coupled theta renewal family and its seam mismatch

For `0 ≤ r ≤ 1` scale the positive renewal input, `ν_r = r ν`, holding the seam value `c = Θ(1)`
fixed: `D_r = c - rN` and `X_r(z) = (a - iz) D_r(-iz) + (a + iz) D_r(iz)`, `a = 1/4`. Then:

* `D_r` is zero-free on `Re z ≥ -a`, with positive logarithmic kernel `Q_r = Σ r^m ν^{⋆m}/(m c^m)`,
  `Q̂_r = -log(1 - rN/c)`, `Q_r(0) = ra`;
* the affine law `X_r(z) = C(1 - r) + r Ξ(2z)`, `C = 2ac`;
* the inverse source `P_r = rP + (1 - r) c e^{at}` of `D_r(λ)/(λ - a)`, whose even extension has
  derivative jump `C(1 - r)` at the seam;
* `A_r(iy) = icy + ac(1 - r) + rH(-2y)`, `Im A_r(iy) > 0`, and the phase `θ_r = arg A_r(i·)`
  satisfies `y(θ_r(y) - π/2) → -a(1 - r)` for `r < 1`, while at `r = 1` the defect is
  `O(e^{-κy}/y)` with sign changes above every height.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The coupled renewal family -/

/-- The seam constant `C = 2ac = Θ(1)/2`, `a = 1/4`, `c = Θ(1)`. -/
def thetaSeamConst : ℝ := Θ 1 / 2

theorem thetaSeamConst_eq : thetaSeamConst = 2 * (1 / 4) * Θ 1 := by
  rw [thetaSeamConst]; ring

theorem thetaSeamConst_pos : 0 < thetaSeamConst := by
  have := thetaSeam_pos; rw [thetaSeamConst]; positivity

/-- The coupled causal denominator `D_r(z) = c - r N(z)`. -/
def thetaCouplingDenominator (r : ℝ) (z : ℂ) : ℂ := (Θ 1 : ℂ) - r * thetaRenewalLaplace z

theorem thetaCouplingDenominator_one : thetaCouplingDenominator 1 = thetaRenewalDenominator := by
  ext z; rw [thetaCouplingDenominator, thetaRenewalDenominator]; push_cast; ring

theorem thetaCouplingDenominator_eq (r : ℝ) (z : ℂ) :
    thetaCouplingDenominator r z = (1 - r) * (Θ 1 : ℂ) + r * thetaRenewalDenominator z := by
  rw [thetaCouplingDenominator, thetaRenewalDenominator]; ring

theorem differentiable_thetaCouplingDenominator (r : ℝ) :
    Differentiable ℂ (thetaCouplingDenominator r) :=
  (differentiable_const _).sub (differentiable_thetaRenewalLaplace.const_mul _)

/-- The coupled renewal mass `q_r = r q < 1/6`. -/
theorem integral_mul_thetaRenewalDensity (r : ℝ) :
    ∫ t in Ioi (0 : ℝ), r * thetaRenewalDensity t = r * thetaRenewalMass := by
  rw [integral_const_mul, thetaRenewalMass]

theorem mul_thetaRenewalMass_lt {r : ℝ} (hr1 : r ≤ 1) : r * thetaRenewalMass < 1 / 6 := by
  have h0 := thetaRenewalMass_pos
  have h1 := thetaRenewalMass_lt
  nlinarith

/-- `|r N(z)| ≤ r q c < c` on `Re z ≥ -1/4`: every `D_r`, `0 ≤ r ≤ 1`, is zero-free there. -/
theorem norm_coupling_mul_thetaRenewalLaplace_le {r : ℝ} (hr0 : 0 ≤ r) {z : ℂ} (hz : -(1 / 4) ≤ z.re) :
    ‖(r : ℂ) * thetaRenewalLaplace z‖ ≤ r * thetaRenewalMass * Θ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, mul_assoc,
    mul_comm thetaRenewalMass]
  exact mul_le_mul_of_nonneg_left (norm_thetaRenewalLaplace_le hz) hr0

theorem thetaCouplingDenominator_ne_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {z : ℂ}
    (hz : -(1 / 4) ≤ z.re) : thetaCouplingDenominator r z ≠ 0 := by
  have hc := thetaSeam_pos
  have hq := mul_thetaRenewalMass_lt hr1
  have hb := norm_coupling_mul_thetaRenewalLaplace_le hr0 hz
  intro h
  have he : (r : ℂ) * thetaRenewalLaplace z = (Θ 1 : ℂ) := by
    rw [thetaCouplingDenominator] at h; linear_combination -h
  rw [he, Complex.norm_real, Real.norm_of_nonneg hc.le] at hb
  nlinarith

/-- The coupled two-ended function `X_r(z) = (a - iz) D_r(-iz) + (a + iz) D_r(iz)`. -/
def thetaCouplingXi (r : ℝ) (z : ℂ) : ℂ :=
  (1 / 4 - I * z) * thetaCouplingDenominator r (-(I * z)) +
    (1 / 4 + I * z) * thetaCouplingDenominator r (I * z)

/-- **(3).** The affine law `X_r(z) = C(1 - r) + r Ξ(2z)`. -/
theorem thetaCouplingXi_eq (r : ℝ) (z : ℂ) :
    thetaCouplingXi r z = thetaSeamConst * (1 - r) + r * XiC (2 * z) := by
  have h := thetaRenewal_two_ended z
  rw [thetaCouplingXi, thetaCouplingDenominator_eq, thetaCouplingDenominator_eq, ← h,
    thetaSeamConst]
  push_cast
  ring

theorem thetaCouplingXi_zero (z : ℂ) : thetaCouplingXi 0 z = thetaSeamConst := by
  rw [thetaCouplingXi_eq]; simp

theorem thetaCouplingXi_one (z : ℂ) : thetaCouplingXi 1 z = XiC (2 * z) := by
  rw [thetaCouplingXi_eq]; simp

theorem differentiable_thetaCouplingXi (r : ℝ) : Differentiable ℂ (thetaCouplingXi r) := by
  have h : thetaCouplingXi r = fun z => thetaSeamConst * (1 - r) + r * XiC (2 * z) :=
    funext (thetaCouplingXi_eq r)
  rw [h]
  exact (differentiable_const _).add
    ((XiC_differentiable.comp (differentiable_id.const_mul 2)).const_mul _)

theorem thetaCouplingXi_neg (r : ℝ) (z : ℂ) : thetaCouplingXi r (-z) = thetaCouplingXi r z := by
  rw [thetaCouplingXi_eq, thetaCouplingXi_eq, mul_neg, XiC_even]

theorem thetaCouplingXi_conj (r : ℝ) (z : ℂ) :
    thetaCouplingXi r ((starRingEnd ℂ) z) = (starRingEnd ℂ) (thetaCouplingXi r z) := by
  have h2 : (2 : ℂ) * (starRingEnd ℂ) z = (starRingEnd ℂ) (2 * z) := by
    rw [map_mul, map_ofNat]
  rw [thetaCouplingXi_eq, thetaCouplingXi_eq, h2, XiC_conj]
  simp

theorem thetaCouplingXi_ofReal (r y : ℝ) :
    thetaCouplingXi r (y : ℂ) = ((thetaSeamConst * (1 - r) + r * Xi (2 * y) : ℝ) : ℂ) := by
  rw [thetaCouplingXi_eq, show (2 : ℂ) * y = ((2 * y : ℝ) : ℂ) by push_cast; ring, XiC_ofReal]
  push_cast; ring

/-- Scaling the seam constant with the input, `c_r = r c`, gives `r Ξ(2z)`: the zero set does
not move. -/
theorem scaledSeam_two_ended (r : ℝ) (z : ℂ) :
    (1 / 4 - I * z) * ((r : ℂ) * Θ 1 - r * thetaRenewalLaplace (-(I * z))) +
      (1 / 4 + I * z) * ((r : ℂ) * Θ 1 - r * thetaRenewalLaplace (I * z)) = r * XiC (2 * z) := by
  rw [← thetaRenewal_two_ended z, thetaRenewalDenominator, thetaRenewalDenominator]; ring

/-! ## The coupled logarithmic kernel -/

/-- **(2).** The coupled logarithmic kernel `Q_r(t) = Σ_{m≥1} r^m ν^{⋆m}(t)/(m c^m)`. -/
def thetaCouplingLogKernel (r t : ℝ) : ℝ :=
  ∑' m : ℕ, r ^ (m + 1) * (thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1)))

theorem summable_thetaCouplingLogKernel_terms (r t : ℝ) :
    Summable fun m : ℕ => r ^ (m + 1) * (thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1))) := by
  obtain ⟨C, _, hC⟩ := exists_bound_thetaRenewalIncrement |t|
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial (|r| * (C / Θ 1 * |t|))).mul_left
    (|r| * (C / Θ 1))) fun m => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  have h := abs_thetaRenewalLogKernel_term_le hC m le_rfl
  calc |r| ^ (m + 1) * |thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1))|
      ≤ |r| ^ (m + 1) * (C / Θ 1 * ((C / Θ 1 * |t|) ^ m / m.factorial)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = |r| * (C / Θ 1) * ((|r| * (C / Θ 1 * |t|)) ^ m / m.factorial) := by
        rw [mul_pow, pow_succ]; ring

theorem thetaCouplingLogKernel_one : thetaCouplingLogKernel 1 = thetaRenewalLogKernel := by
  ext t; simp [thetaCouplingLogKernel, thetaRenewalLogKernel]

/-- **(2).** `Q_r > 0` on `t > 0` for every `r > 0`. -/
theorem thetaCouplingLogKernel_pos {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    0 < thetaCouplingLogKernel r t := by
  have hc := thetaSeam_pos
  exact (summable_thetaCouplingLogKernel_terms r t).tsum_pos
    (fun m => mul_nonneg (by positivity) (div_nonneg (thetaRenewalPower_pos m ht).le (by positivity)))
    0 (mul_pos (by positivity) (div_pos (thetaRenewalPower_pos 0 ht) (by positivity)))

/-- `Q_r(0) = r a`, against the physical seam value `Q(0) = a`. -/
theorem thetaCouplingLogKernel_zero (r : ℝ) : thetaCouplingLogKernel r 0 = r * (1 / 4) := by
  have hc := thetaSeam_pos
  rw [thetaCouplingLogKernel, tsum_eq_single 0 fun m hm => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp [thetaRenewalPower, GaloisForLFunctions.HTGeometry.volterraConv]]
  simp only [thetaRenewalPower, thetaRenewalIncrement_zero, Nat.cast_zero, zero_add, pow_one,
    one_mul]
  field_simp

/-- The Laplace transform `Q̂_r(s)`. -/
def thetaCouplingLogKernelLaplace (r : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaCouplingLogKernel r t : ℂ)

/-- **(2).** `Q̂_r(s) = -log(1 - r N(s)/c)` on `Re s ≥ -1/4`, `0 ≤ r ≤ 1`. -/
theorem thetaCouplingLogKernelLaplace_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {s : ℂ}
    (hs : -(1 / 4) ≤ s.re) :
    thetaCouplingLogKernelLaplace r s =
      -Complex.log (1 - r * thetaRenewalLaplace s / (Θ 1 : ℂ)) := by
  have hc := thetaSeam_pos
  have hcC : ((Θ 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hq0 := thetaRenewalMass_pos
  have hq1 := thetaRenewalMass_lt
  set F : ℕ → ℝ → ℂ := fun m t =>
    cexp (-(s * t)) * ((r ^ (m + 1) * (thetaRenewalPower m t / ((m + 1) * Θ 1 ^ (m + 1))) : ℝ) : ℂ)
  have hnormF : ∀ m t, ‖F m t‖ = r ^ (m + 1) * (Real.exp (-(s.re * t)) * |thetaRenewalPower m t| /
      ((m + 1) * Θ 1 ^ (m + 1))) := by
    intro m t
    simp only [F]
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg hr0, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < ((m : ℝ) + 1) * Θ 1 ^ (m + 1))]
    have hre : (-(s * (t : ℂ))).re = -(s.re * t) := by simp
    rw [hre]; ring
  have hFi : ∀ m, Integrable (F m) (volume.restrict (Ioi 0)) := by
    intro m
    have h := ((integrableOn_exp_mul_abs_thetaRenewalPower (σ := -s.re) (by linarith) m).div_const
      (((m : ℝ) + 1) * Θ 1 ^ (m + 1))).const_mul (r ^ (m + 1))
    refine h.mono' ((by have := continuous_thetaRenewalPower m; fun_prop : Continuous (F m))
      |>.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    rw [hnormF, neg_mul]
  have hFle : ∀ m, (∫ t in Ioi (0 : ℝ), ‖F m t‖) ≤ thetaRenewalMass ^ (m + 1) / (m + 1) := by
    intro m
    rw [← integral_thetaRenewalDensityPower, ← integral_div]
    refine setIntegral_mono_on (hFi m).norm ((integrableOn_thetaRenewalDensityPower m).div_const _)
      measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    rw [hnormF, abs_of_pos (thetaRenewalPower_pos m ht0), thetaRenewalPower_eq_density]
    have h1 : Real.exp (-(s.re * t)) * Real.exp (-(t / 4)) ≤ 1 := by
      rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 := (thetaRenewalDensityPower_le m ht0.le).1
    have hr : r ^ (m + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc r ^ (m + 1) * (Real.exp (-(s.re * t)) * (Θ 1 ^ (m + 1) * Real.exp (-(t / 4)) *
          thetaRenewalDensityPower m t)) * ((m : ℝ) + 1)
        = r ^ (m + 1) * (Real.exp (-(s.re * t)) * Real.exp (-(t / 4))) *
          (thetaRenewalDensityPower m t * ((m + 1) * Θ 1 ^ (m + 1))) := by ring
      _ ≤ 1 * 1 * (thetaRenewalDensityPower m t * ((m + 1) * Θ 1 ^ (m + 1))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hr h1 (by positivity) zero_le_one)
            (by positivity)
      _ = _ := by ring
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one (x := thetaRenewalMass)
    (by rw [abs_of_pos hq0]; linarith)
  have hsumm : Summable fun m => ∫ t in Ioi (0 : ℝ), ‖F m t‖ :=
    Summable.of_nonneg_of_le (fun m => integral_nonneg fun t => norm_nonneg _) hFle hlog.summable
  have hpt : ∀ t : ℝ, cexp (-(s * t)) * (thetaCouplingLogKernel r t : ℂ) = ∑' m, F m t := by
    intro t
    rw [thetaCouplingLogKernel, Complex.ofReal_tsum, ← tsum_mul_left]
  have hFint : ∀ m, (∫ t in Ioi (0 : ℝ), F m t) =
      (r * thetaRenewalLaplace s) ^ (m + 1) / (((m : ℂ) + 1) * (Θ 1 : ℂ) ^ (m + 1)) := by
    intro m
    rw [mul_pow, ← integral_cexp_mul_thetaRenewalPower hs m, mul_div_assoc, div_eq_mul_inv,
      ← integral_mul_const, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [F]
    push_cast
    field_simp
  have hz : ‖(r : ℂ) * thetaRenewalLaplace s / (Θ 1 : ℂ)‖ < 1 := by
    have hb := norm_coupling_mul_thetaRenewalLaplace_le hr0 hs
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hc.le, div_lt_one hc]
    have := mul_thetaRenewalMass_lt hr1
    nlinarith
  rw [thetaCouplingLogKernelLaplace]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hFi hsumm]
  simp_rw [hFint]
  have hser := Complex.hasSum_taylorSeries_neg_log hz
  have hser1 := (hasSum_nat_add_iff' 1).mpr hser
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.cast_zero, div_zero,
    sub_zero] at hser1
  rw [← hser1.tsum_eq]
  refine tsum_congr fun m => ?_
  push_cast
  rw [div_pow]
  field_simp

/-- `D_r(s) = c exp(-Q̂_r(s))` on `Re s ≥ -1/4`, `0 ≤ r ≤ 1`. -/
theorem thetaCouplingDenominator_eq_exp {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {s : ℂ}
    (hs : -(1 / 4) ≤ s.re) :
    thetaCouplingDenominator r s = (Θ 1 : ℂ) * cexp (-thetaCouplingLogKernelLaplace r s) := by
  have hc := thetaSeam_pos
  have hcC : ((Θ 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hne : 1 - r * thetaRenewalLaplace s / (Θ 1 : ℂ) ≠ 0 := by
    intro h
    apply thetaCouplingDenominator_ne_zero hr0 hr1 hs
    have h1 := sub_eq_zero.mp h
    rw [eq_div_iff hcC, one_mul] at h1
    rw [thetaCouplingDenominator, h1, sub_self]
  rw [thetaCouplingLogKernelLaplace_eq hr0 hr1 hs, neg_neg, Complex.exp_log hne,
    thetaCouplingDenominator]
  field_simp

/-! ## The inverse source and its seam cusp -/

/-- The inverse source `P_r(t) = r P(t) + (1 - r) c e^{at}` of `D_r(λ)/(λ - a)`. -/
def thetaCouplingProfile (r t : ℝ) : ℝ :=
  r * thetaLogProfile t + (1 - r) * Θ 1 * Real.exp (t / 4)

/-- `∫₀^∞ e^{-λt} P_r(t) dt = D_r(λ)/(λ - a)` for `Re λ > a`. -/
theorem integral_cexp_mul_thetaCouplingProfile (r : ℝ) {s : ℂ} (hs : 1 / 4 < s.re) :
    ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaCouplingProfile r t : ℂ) =
      thetaCouplingDenominator r s / (s - 1 / 4) := by
  have hne : s - 1 / 4 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hne' : 1 / 4 - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have ha : (1 / 4 - s).re < 0 := by simp; linarith
  have hE := integrableOn_exp_mul_complex_Ioi ha 0
  have hR := integrableOn_cexp_mul_thetaLogTail (s := s) (by linarith)
  have hsplit : ∀ t : ℝ, cexp (-(s * t)) * (thetaCouplingProfile r t : ℂ) =
      ((r : ℂ) + (1 - r) * Θ 1) * cexp ((1 / 4 - s) * t) +
        r * (cexp (-(s * t)) * (thetaLogTail t : ℂ)) := by
    intro t
    rw [thetaCouplingProfile, thetaLogProfile_eq_add]
    push_cast
    rw [show (1 / 4 - s) * (t : ℂ) = -(s * t) + t / 4 by ring, Complex.exp_add]
    ring
  simp_rw [hsplit]
  rw [integral_add (hE.const_mul _) (hR.const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_mul_complex_Ioi ha 0, integral_cexp_mul_thetaLogTail,
    thetaCouplingDenominator_eq, thetaRenewalDenominator_eq]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show (-1 : ℂ) / (1 / 4 - s) = 1 / (s - 1 / 4) by rw [div_eq_div_iff hne' hne]; ring,
    eq_div_iff hne, add_mul, mul_assoc, one_div_mul_cancel hne, mul_one]
  ring

/-- `P'(0) = 0`: the physical inverse source is smooth and even through the seam. -/
theorem hasDerivAt_thetaLogProfile_zero : HasDerivAt thetaLogProfile 0 0 := by
  have h := hasDerivAt_thetaLogProfile 0
  rwa [thetaRenewalIncrement_zero, show thetaLogProfile 0 = Θ 1 by simp [thetaLogProfile],
    sub_self] at h

theorem hasDerivAt_thetaCouplingProfile_zero (r : ℝ) :
    HasDerivAt (thetaCouplingProfile r) ((1 - r) * Θ 1 / 4) 0 := by
  have h1 := hasDerivAt_thetaLogProfile_zero.const_mul r
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (t / 4)) (Real.exp (0 / 4) * (1 / 4)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const 4).exp.congr_deriv (by simp)
  exact (h1.add (h2.const_mul ((1 - r) * Θ 1))).congr_deriv
    (by rw [zero_div, Real.exp_zero]; ring)

/-- Right derivative of the even extension `P_r(|t|)` at the seam. -/
theorem hasDerivWithinAt_thetaCouplingProfile_abs_Ici (r : ℝ) :
    HasDerivWithinAt (fun t => thetaCouplingProfile r |t|) ((1 - r) * Θ 1 / 4) (Ici 0) 0 := by
  refine (hasDerivAt_thetaCouplingProfile_zero r).hasDerivWithinAt.congr (fun t ht => ?_) (by simp)
  rw [abs_of_nonneg ht]

/-- Left derivative of the even extension `P_r(|t|)` at the seam. -/
theorem hasDerivWithinAt_thetaCouplingProfile_abs_Iic (r : ℝ) :
    HasDerivWithinAt (fun t => thetaCouplingProfile r |t|) (-((1 - r) * Θ 1 / 4)) (Iic 0) 0 := by
  have h0 : HasDerivAt (thetaCouplingProfile r) ((1 - r) * Θ 1 / 4) (-0) := by
    rw [neg_zero]; exact hasDerivAt_thetaCouplingProfile_zero r
  have h := h0.comp (0 : ℝ) (hasDerivAt_neg 0)
  refine (h.hasDerivWithinAt.congr (fun t ht => ?_) (by simp)).congr_deriv (by ring)
  simp only [Function.comp_apply]
  rw [abs_of_nonpos ht]

/-- **The seam cusp.** The even extension of `P_r` has derivative jump `2ac(1 - r) = C(1 - r)`. -/
theorem thetaCouplingProfile_seam_jump (r : ℝ) :
    (1 - r) * Θ 1 / 4 - -((1 - r) * Θ 1 / 4) = thetaSeamConst * (1 - r) := by
  rw [thetaSeamConst]; ring

/-! ## The critical-axis channel and the seam mismatch -/

/-- The coupled channel `A_r(λ) = (a + λ) D_r(λ)`. -/
def thetaCouplingA (r : ℝ) (lam : ℂ) : ℂ := (1 / 4 + lam) * thetaCouplingDenominator r lam

theorem thetaCouplingA_one : thetaCouplingA 1 = thetaLoopA := by
  ext lam; rw [thetaCouplingA, thetaCouplingDenominator_one, thetaLoopA]

/-- **(3a).** `A_r(iy) = icy + ac(1 - r) + r H(-2y)`. -/
theorem thetaCouplingA_I_mul_eq (r y : ℝ) :
    thetaCouplingA r (y * I) = I * (Θ 1 : ℂ) * y + (Θ 1 : ℂ) * (1 - r) / 4 +
      r * thetaOneSidedConnection (-(2 * y) : ℝ) := by
  have h := thetaLoopA_I_mul_eq y
  rw [thetaLoopA] at h
  rw [thetaCouplingA, thetaCouplingDenominator_eq, mul_add, mul_left_comm _ (r : ℂ), h]
  ring

theorem re_thetaCouplingA_I_mul (r y : ℝ) :
    (thetaCouplingA r (y * I)).re =
      Θ 1 * (1 - r) / 4 + r * (thetaOneSidedConnection (-(2 * y) : ℝ)).re := by
  rw [thetaCouplingA_I_mul_eq]; simp

theorem im_thetaCouplingA_I_mul (r y : ℝ) :
    (thetaCouplingA r (y * I)).im = (1 - r) * Θ 1 * y + r * thetaLoopCharge y := by
  rw [thetaCouplingA_I_mul_eq, thetaLoopCharge_eq]; simp; ring

/-- The positive quadrant law: `Im A_r(iy) > 0` for `y > 0`, `0 ≤ r ≤ 1`. -/
theorem im_thetaCouplingA_I_mul_pos {r y : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hy : 0 < y) :
    0 < (thetaCouplingA r (y * I)).im := by
  have hc := thetaSeam_pos
  have hv := thetaLoopCharge_pos hy
  rw [im_thetaCouplingA_I_mul]
  rcases eq_or_lt_of_le hr0 with h | h
  · subst h; simp; positivity
  · have : 0 ≤ (1 - r) * Θ 1 * y := by
      have : 0 ≤ 1 - r := by linarith
      positivity
    nlinarith

/-- The one-sided connection vanishes at high frequency: `H(-2y) → 0`. -/
theorem tendsto_thetaOneSidedConnection_neg_two_mul :
    Tendsto (fun y : ℝ => thetaOneSidedConnection (-(2 * y) : ℝ)) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun y => thetaCuspFullSource 0 / y) ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with y hy
    have h := norm_thetaOneSidedConnection_ofReal_le (u := -(2 * y)) (by linarith)
    rw [abs_neg, abs_of_pos (by linarith)] at h
    calc _ ≤ 2 * thetaCuspFullSource 0 / (2 * y) := h
      _ = thetaCuspFullSource 0 / y := by field_simp
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- Each reflected channel contributes `ac(1 - r)` at high frequency. -/
theorem tendsto_thetaCouplingA_sub (r : ℝ) :
    Tendsto (fun y : ℝ => thetaCouplingA r (y * I) - I * (Θ 1 : ℂ) * y) atTop
      (𝓝 ((Θ 1 : ℂ) * (1 - r) / 4)) := by
  have h := (tendsto_thetaOneSidedConnection_neg_two_mul.const_mul (r : ℂ)).const_add
    ((Θ 1 : ℂ) * (1 - r) / 4)
  rw [mul_zero, add_zero] at h
  refine h.congr fun y => ?_
  rw [thetaCouplingA_I_mul_eq]; ring

theorem thetaCouplingDenominator_conj (r : ℝ) (s : ℂ) :
    thetaCouplingDenominator r ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (thetaCouplingDenominator r s) := by
  rw [thetaCouplingDenominator_eq, thetaCouplingDenominator_eq, thetaRenewalDenominator_conj]
  simp

/-- The reflected channel on the critical axis is the conjugate: `B_r(iy) = conj A_r(iy)`. -/
theorem reflected_thetaCouplingA_I_mul (r y : ℝ) :
    (1 / 4 - (y * I : ℂ)) * thetaCouplingDenominator r (-(y * I)) =
      (starRingEnd ℂ) (thetaCouplingA r (y * I)) := by
  rw [thetaCouplingA, map_mul, ← thetaCouplingDenominator_conj]
  congr 1
  · simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring
  · congr 1; simp

theorem tendsto_reflected_thetaCouplingA_add (r : ℝ) :
    Tendsto (fun y : ℝ => (1 / 4 - (y * I : ℂ)) * thetaCouplingDenominator r (-(y * I)) +
      I * (Θ 1 : ℂ) * y) atTop (𝓝 ((Θ 1 : ℂ) * (1 - r) / 4)) := by
  have h := (Complex.continuous_conj.tendsto _).comp (tendsto_thetaCouplingA_sub r)
  have hv : (starRingEnd ℂ) ((Θ 1 : ℂ) * (1 - r) / 4) = (Θ 1 : ℂ) * (1 - r) / 4 := by
    simp [map_div₀, map_ofNat]
  rw [hv] at h
  refine h.congr fun y => ?_
  simp only [Function.comp_apply, reflected_thetaCouplingA_I_mul, map_sub, map_mul,
    Complex.conj_I, Complex.conj_ofReal]
  ring

/-- `iyN(iy) → ac`: integration by parts against `ν(0) = ac`. -/
theorem tendsto_I_mul_thetaRenewalLaplace :
    Tendsto (fun y : ℝ => I * y * thetaRenewalLaplace (y * I)) atTop (𝓝 ((Θ 1 : ℂ) / 4)) := by
  obtain ⟨K, hK⟩ : ∃ K, ∀ y : ℝ, ‖((y : ℂ) * I)‖ * ‖thetaRenewalLaplace (y * I)‖ ≤ K :=
    ⟨_, fun y => norm_mul_thetaRenewalLaplace_le (B := 0) (by simp)⟩
  have hN : Tendsto (fun y : ℝ => thetaRenewalLaplace (y * I)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun y => K / y) ?_ (tendsto_const_nhds.div_atTop tendsto_id)
    filter_upwards [eventually_gt_atTop 0] with y hy
    have h := hK y
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hy.le] at h
    rw [le_div_iff₀ hy]; linarith
  have h := ((tendsto_thetaOneSidedConnection_neg_two_mul.add (hN.div_const 4)).const_sub
    ((Θ 1 : ℂ) / 4))
  rw [zero_div, add_zero, sub_zero] at h
  refine h.congr fun y => ?_
  have hA := thetaLoopA_I_mul_eq y
  rw [thetaLoopA, thetaRenewalDenominator] at hA
  linear_combination hA

/-! ## The seam mismatch order parameter -/

/-- For `Im z > 0`, `arg z = π/2 - arctan(Re z / Im z)`. -/
theorem arg_eq_pi_div_two_sub_arctan {z : ℂ} (him : 0 < z.im) :
    Complex.arg z = Real.pi / 2 - Real.arctan (z.re / z.im) := by
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr fun h => by rw [h] at him; simp at him
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [Complex.arg_of_im_pos him, Real.arccos_eq_pi_div_two_sub_arcsin]
  congr 1
  have hlt : |z.re / ‖z‖| < 1 := by
    rw [abs_div, abs_norm, div_lt_one hnz]
    exact Complex.abs_re_lt_norm.mpr him.ne'
  rw [Real.arcsin_eq_arctan (abs_lt.mp hlt)]
  congr 1
  have hsq : √(1 - (z.re / ‖z‖) ^ 2) = z.im / ‖z‖ := by
    rw [show 1 - (z.re / ‖z‖) ^ 2 = (z.im / ‖z‖) ^ 2 by field_simp; linarith,
      Real.sqrt_sq (by positivity)]
  rw [hsq]
  field_simp

/-- The coupled critical-axis phase `θ_r(y) = arg A_r(iy)`. -/
def thetaCouplingPhase (r y : ℝ) : ℝ := Complex.arg (thetaCouplingA r (y * I))

theorem thetaCouplingPhase_one : thetaCouplingPhase 1 = thetaResonancePhase := by
  ext y; rw [thetaCouplingPhase, thetaCouplingA_one, thetaResonancePhase]

theorem thetaCouplingPhase_eq_arctan {r y : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hy : 0 < y) :
    thetaCouplingPhase r y = Real.pi / 2 -
      Real.arctan ((thetaCouplingA r (y * I)).re / (thetaCouplingA r (y * I)).im) :=
  arg_eq_pi_div_two_sub_arctan (im_thetaCouplingA_I_mul_pos hr0 hr1 hy)

theorem thetaCouplingPhase_mem_Ioo {r y : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hy : 0 < y) :
    thetaCouplingPhase r y ∈ Ioo 0 Real.pi := by
  rw [thetaCouplingPhase_eq_arctan hr0 hr1 hy]
  have h1 := Real.arctan_lt_pi_div_two ((thetaCouplingA r (y * I)).re /
    (thetaCouplingA r (y * I)).im)
  have h2 := Real.neg_pi_div_two_lt_arctan ((thetaCouplingA r (y * I)).re /
    (thetaCouplingA r (y * I)).im)
  constructor <;> linarith

/-- **(3b).** `y (θ_r(y) - π/2) → -a(1 - r)` for `0 ≤ r < 1`. -/
theorem tendsto_mul_thetaCouplingPhase_sub {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun y => y * (thetaCouplingPhase r y - Real.pi / 2)) atTop
      (𝓝 (-(1 / 4 * (1 - r)))) := by
  have hc := thetaSeam_pos
  set u : ℝ → ℝ := fun y => (thetaCouplingA r (y * I)).re
  set v : ℝ → ℝ := fun y => (thetaCouplingA r (y * I)).im
  have hH := tendsto_thetaOneSidedConnection_neg_two_mul
  have hu : Tendsto u atTop (𝓝 (Θ 1 * (1 - r) / 4)) := by
    have h := ((Complex.continuous_re.tendsto 0).comp hH).const_mul r |>.const_add
      (Θ 1 * (1 - r) / 4)
    simp only [Function.comp_apply, Complex.zero_re, mul_zero, add_zero] at h
    exact h.congr fun y => (re_thetaCouplingA_I_mul r y).symm
  have hv : Tendsto (fun y => v y / y) atTop (𝓝 (Θ 1)) := by
    have h := tendsto_thetaLoopCharge_div
    have h2 := (h.const_mul r).const_add ((1 - r) * Θ 1)
    have e : (1 - r) * Θ 1 + r * Θ 1 = Θ 1 := by ring
    rw [e] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [v, im_thetaCouplingA_I_mul]
    field_simp
  -- `y w(y) → (1 - r)/4`
  have hyw : Tendsto (fun y => u y / (v y / y)) atTop (𝓝 (Θ 1 * (1 - r) / 4 / Θ 1)) :=
    hu.div hv hc.ne'
  rw [show Θ 1 * (1 - r) / 4 / Θ 1 = 1 / 4 * (1 - r) by field_simp] at hyw
  have hw : Tendsto (fun y => u y / v y) atTop (𝓝 0) := by
    have h := hyw.div_atTop tendsto_id
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [id]
    field_simp
  -- the cubic arctan error
  have herr : Tendsto (fun y => y * (Real.arctan (u y / v y) - u y / v y)) atTop (𝓝 0) := by
    have hcube : Tendsto (fun y => (u y / (v y / y)) * (u y / v y) ^ 2 / 3) atTop (𝓝 0) := by
      have := (hyw.mul (hw.pow 2)).div_const 3
      simpa using this
    have habs : Tendsto (fun y => |(u y / (v y / y)) * (u y / v y) ^ 2 / 3|) atTop (𝓝 0) := by
      simpa using hcube.abs
    refine squeeze_zero_norm' ?_ habs
    · filter_upwards [eventually_gt_atTop 0] with y hy
      have hb := GaloisForLFunctions.HTGeometry.abs_arctan_sub_self_le_cube (u y / v y)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hy]
      have key : ∀ w : ℝ, y * (|w| ^ 3 / 3) = |y * w * w ^ 2 / 3| := fun w => by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos hy, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 3)]
        ring
      calc y * |Real.arctan (u y / v y) - u y / v y| ≤ y * (|u y / v y| ^ 3 / 3) :=
            mul_le_mul_of_nonneg_left hb hy.le
        _ = |u y / (v y / y) * (u y / v y) ^ 2 / 3| := by
            rw [show u y / (v y / y) = y * (u y / v y) by field_simp]
            exact key _
  have hmain : Tendsto (fun y => -(u y / (v y / y) + y * (Real.arctan (u y / v y) - u y / v y)))
      atTop (𝓝 (-(1 / 4 * (1 - r) + 0))) := (hyw.add herr).neg
  rw [add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [thetaCouplingPhase_eq_arctan hr0 hr1.le hy]
  simp only [u, v]
  field_simp
  ring

/-- At the physical coupling the phase defect is exponentially small:
`|θ₁(y) - π/2| ≤ C e^{-κy}/y`. -/
theorem exists_abs_thetaResonancePhase_sub_le {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < Real.pi / 2) :
    ∃ C Y : ℝ, 0 ≤ C ∧ ∀ y, Y ≤ y →
      |thetaResonancePhase y - Real.pi / 2| ≤ C * Real.exp (-(κ * y)) / y := by
  have hc := thetaSeam_pos
  obtain ⟨C, Y₀, hC, hY₀, hb⟩ := exists_thetaResonancePhase_bounds hκ hκ2
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp eventually_thetaLoopCharge_ge
  refine ⟨2 * C / Θ 1, max Y₀ Y₁, by positivity, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith [le_max_left Y₀ Y₁]
  have hv := hY₁ y (le_trans (le_max_right _ _) hy)
  have hvp := thetaLoopCharge_pos hy0
  have hu := (hb y (le_trans (le_max_left _ _) hy)).1
  rw [thetaResonancePhase_eq_arctan hy0, sub_sub_cancel_left, abs_neg]
  refine (GaloisForLFunctions.HTGeometry.abs_arctan_le_abs _).trans ?_
  rw [abs_div, abs_of_pos hvp, div_le_div_iff₀ hvp hy0]
  have hu' : |(thetaLoopA (y * I)).re| ≤ C * Real.exp (-(κ * y)) := by
    have := abs_nonneg (deriv Xi (2 * y)); linarith
  have hE := Real.exp_pos (-(κ * y))
  calc |(thetaLoopA (y * I)).re| * y ≤ C * Real.exp (-(κ * y)) * y :=
        mul_le_mul_of_nonneg_right hu' hy0.le
    _ = 2 * C / Θ 1 * Real.exp (-(κ * y)) * (Θ 1 / 2 * y) := by field_simp
    _ ≤ 2 * C / Θ 1 * Real.exp (-(κ * y)) * thetaLoopCharge y :=
        mul_le_mul_of_nonneg_left hv (by positivity)

/-- At the physical coupling the phase crosses `π/2` in both directions above every height. -/
theorem exists_thetaResonancePhase_gt_lt (Y : ℝ) :
    (∃ y > Y, Real.pi / 2 < thetaResonancePhase y) ∧
      ∃ y > Y, thetaResonancePhase y < Real.pi / 2 := by
  have key : ∀ y > 0, thetaResonancePhase y - Real.pi / 2 =
      -Real.arctan (Xi (2 * y) / 2 / thetaLoopCharge y) := by
    intro y hy
    rw [thetaResonancePhase_eq_arctan hy, re_thetaLoopA_I_mul]; ring
  obtain ⟨t, ht, hneg⟩ := exists_Xi_neg_gt (2 * max Y 0)
  obtain ⟨t', ht', hpos⟩ := exists_Xi_pos_gt (2 * max Y 0)
  have hY := le_max_left Y 0
  have hY0 := le_max_right Y 0
  refine ⟨⟨t / 2, by linarith, ?_⟩, ⟨t' / 2, by linarith, ?_⟩⟩
  · have hy : 0 < t / 2 := by linarith
    have h := key _ hy
    rw [show 2 * (t / 2) = t by ring] at h
    have hv := thetaLoopCharge_pos hy
    have : Real.arctan (Xi t / 2 / thetaLoopCharge (t / 2)) < 0 :=
      Real.arctan_zero ▸ Real.arctan_strictMono (div_neg_of_neg_of_pos (by linarith) hv)
    linarith
  · have hy : 0 < t' / 2 := by linarith
    have h := key _ hy
    rw [show 2 * (t' / 2) = t' by ring] at h
    have hv := thetaLoopCharge_pos hy
    have : 0 < Real.arctan (Xi t' / 2 / thetaLoopCharge (t' / 2)) :=
      Real.arctan_zero ▸ Real.arctan_strictMono (div_pos (by linarith) hv)
    linarith

end

end RHTower
