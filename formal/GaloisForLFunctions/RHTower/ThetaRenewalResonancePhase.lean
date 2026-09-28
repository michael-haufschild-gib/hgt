import GaloisForLFunctions.RHTower.ThetaRenewalFeedbackLoop
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCompletedPrimeGammaSpectralFlowIdentification

/-!
# The renormalized resonance phase and its Zeno crossing law

For `y ≥ 0` the channel `A(iy) = (a + iy) D(iy)` lies in the slit plane, so the phase
`θ(y) = arg A(iy)` is smooth, `θ(0) = 0`, `θ(y) ∈ (0, π)` for `y > 0`, and
`θ(y) - π/2 = -arctan(u(y)/v(y))` with `u = Re A(iy) = Ξ(2y)/2`, `v = Im A(iy)`.

* **(11c).** `θ' = (u v' - v u')/(u² + v²) = Re (A'/A)(iy)`, and the order-one Hadamard product
  of `D` gives the absolutely convergent resonance sum
  `θ'(y) = a/(a² + y²) + β + ∑_ζ Re[(iy - ζ)⁻¹ + ζ⁻¹]`.
* **(11a).** `v' = c - 2 Im H'(-2y)` is bounded (Cauchy estimates for `H` on a strip) and
  `v' → c`, by interpolation from `v - cy → 0` and a bound on `v''`.
* **(11d).** Horizontal decay of `Ξ` and a Cauchy estimate for `Ξ'` give
  `|u| + |u'| = O(e^{-κy})`, `|θ'| = O(e^{-κy}/y)` and `∫_Y^∞ |θ'| = O(e^{-κY})` for `κ < π/2`;
  `θ → π/2`.
* **(11e), Zeno law.** At a critical zero `θ = π/2` and `d_j = 2θ'(y_j)`; crossings of both
  orientations occur above every height.
* The completed prime–Gamma Stokes flow has one zero, so no injective reparametrization times a
  nowhere-vanishing factor can match it with `θ - π/2`.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta
open scoped ComplexConjugate

namespace RHTower

noncomputable section

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## Strip bounds for the one-sided connection and for `Ξ` -/

/-- The strip constant `M_H = ∫₀^∞ k(x) e^{x/2} dx`. -/
def thetaConnectionStripConst : ℝ :=
  ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (x / 2)

theorem norm_thetaOneSidedConnection_le_strip {w : ℂ} (hw : |w.im| ≤ 1 / 2) :
    ‖thetaOneSidedConnection w‖ ≤ thetaConnectionStripConst := by
  have hint : IntegrableOn (fun x => thetaCuspFullSource x * Real.exp (x / 2)) (Ioi 0) := by
    have h := (HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource (1 / 2)).integrableOn
      (s := Ioi 0)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    ring_nf
  rw [thetaOneSidedConnection, thetaConnectionStripConst]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on ?_ hint measurableSet_Ioi
    fun x hx => ?_)
  · exact IntegrableOn.congr_fun (integrableOn_cexp_mul_thetaCuspFullSource (I * w) (Ioi 0)).norm
      (fun x _ => by rw [norm_mul, norm_mul, mul_comm]) measurableSet_Ioi
  · have hx0 : 0 < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (thetaCuspFullSource_pos_all x).le,
      Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (thetaCuspFullSource_pos_all x).le
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, ofReal_re, mul_im, ofReal_im,
      mul_zero, sub_zero]
    rw [abs_le] at hw
    nlinarith

theorem norm_deriv_thetaOneSidedConnection_le {w : ℂ} (hw : |w.im| ≤ 1 / 4) :
    ‖deriv thetaOneSidedConnection w‖ ≤ 4 * thetaConnectionStripConst := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := w) (R := 1 / 4)
    (C := thetaConnectionStripConst) (by norm_num)
    differentiable_thetaOneSidedConnection.diffContOnCl fun z hz => by
      refine norm_thetaOneSidedConnection_le_strip ?_
      have h1 : |z.im - w.im| ≤ 1 / 4 := by
        have := Complex.abs_im_le_norm (z - w)
        rw [Complex.sub_im, ← dist_eq_norm, Metric.mem_sphere.mp hz] at this
        exact this
      rw [abs_le] at hw h1 ⊢
      constructor <;> linarith
  rwa [div_eq_mul_inv, show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num, mul_comm] at h

theorem differentiable_deriv_thetaOneSidedConnection :
    Differentiable ℂ (deriv thetaOneSidedConnection) := fun z =>
  ((differentiable_thetaOneSidedConnection.differentiableOn.analyticOnNhd isOpen_univ).deriv z
    (mem_univ z)).differentiableAt

theorem norm_deriv_deriv_thetaOneSidedConnection_le (u : ℝ) :
    ‖deriv (deriv thetaOneSidedConnection) u‖ ≤ 16 * thetaConnectionStripConst := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (u : ℂ)) (R := 1 / 4)
    (C := 4 * thetaConnectionStripConst) (by norm_num)
    differentiable_deriv_thetaOneSidedConnection.diffContOnCl fun z hz => by
      refine norm_deriv_thetaOneSidedConnection_le ?_
      have := Complex.abs_im_le_norm (z - u)
      rw [Complex.sub_im, ofReal_im, sub_zero, ← dist_eq_norm, Metric.mem_sphere.mp hz] at this
      exact this
  rw [div_eq_mul_inv, show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at h
  linarith

theorem deriv_Xi_eq_re (t : ℝ) : ((deriv Xi t : ℝ) : ℂ) = deriv XiC t := by
  have h1 := (hasDerivAt_Xi_deriv t).ofReal_comp
  have h2 := (XiC_differentiable (t : ℂ)).hasDerivAt.comp_ofReal
  exact h1.unique (h2.congr_of_eventuallyEq (Eventually.of_forall fun s => by
    simp [XiC_ofReal]))

/-- `|Ξ'(t)| ≤ C e^{-δ|t|}` for `2δ < π/2`, by a Cauchy estimate in the horizontal strip. -/
theorem exists_abs_deriv_Xi_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv Xi t| ≤ C * Real.exp (-(δ * |t|)) := by
  obtain ⟨C, hC, hXi⟩ := exists_norm_XiC_horizontal_le (A := 1 / 2) (δ := δ) (by norm_num)
    hδ0 hδ
  refine ⟨4 * C * Real.exp (δ / 4), by positivity, fun t => ?_⟩
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (t : ℂ)) (R := 1 / 4)
    (C := C * Real.exp (δ / 4) * Real.exp (-(δ * |t|))) (by norm_num)
    XiC_differentiable.diffContOnCl fun z hz => by
      have hdist : ‖z - t‖ = 1 / 4 := by rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hz
      have him : |z.im| ≤ 1 / 4 := by
        have := Complex.abs_im_le_norm (z - t); simpa [hdist] using this
      have hre : |z.re - t| ≤ 1 / 4 := by
        have := Complex.abs_re_le_norm (z - t); simpa [hdist] using this
      have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
      have hb := hXi z.re z.im (by linarith)
      rw [← hz] at hb
      refine hb.trans ?_
      rw [mul_assoc, ← Real.exp_add]
      gcongr
      have := abs_sub_abs_le_abs_sub t z.re
      rw [abs_sub_comm] at hre
      nlinarith [abs_nonneg t]
  rw [← deriv_Xi_eq_re, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv,
    show ((1 : ℝ) / 4)⁻¹ = 4 by norm_num] at h
  linarith

/-- **Interpolation.** If `f → 0` at `+∞` and `|f''| ≤ M`, then `f' → 0`. -/
theorem tendsto_deriv_of_tendsto_of_abs_deriv_deriv_le {f f' f'' : ℝ → ℝ} {M : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hM : ∀ y, |f'' y| ≤ M) (hlim : Tendsto f atTop (𝓝 0)) :
    Tendsto f' atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (2 * (M + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε * δ / 4) (by positivity)
  refine ⟨N, fun y hy => ?_⟩
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' (lt_add_of_pos_right y hδ)
    (fun t _ => (hf t).continuousAt.continuousWithinAt) (fun t _ => hf t)
  obtain ⟨η, hη, hslope'⟩ := exists_hasDerivAt_eq_slope f' f'' hξ.1
    (fun t _ => (hf' t).continuousAt.continuousWithinAt) (fun t _ => hf' t)
  have h1 := hN y hy
  have h2 := hN (y + δ) (by linarith)
  rw [Real.dist_eq, sub_zero] at h1 h2
  have hfξ : |f' ξ| ≤ ε / 2 := by
    rw [hslope, show y + δ - y = δ by ring, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
    calc |f (y + δ) - f y| ≤ |f (y + δ)| + |f y| := abs_sub _ _
      _ ≤ ε * δ / 4 + ε * δ / 4 := by linarith
      _ = ε / 2 * δ := by ring
  have hdiff : |f' ξ - f' y| ≤ M * δ := by
    have hne : ξ - y ≠ 0 := by linarith [hξ.1]
    have hmul : f' ξ - f' y = f'' η * (ξ - y) := by
      rw [hslope']; field_simp
    rw [hmul, abs_mul]
    have hξy : |ξ - y| ≤ δ := by rw [abs_of_pos (by linarith [hξ.1])]; linarith [hξ.2]
    exact mul_le_mul (hM η) hξy (abs_nonneg _) hM0
  have hMδ : M * δ < ε / 2 := by
    rw [hδdef, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq, sub_zero]
  calc |f' y| ≤ |f' ξ| + |f' ξ - f' y| := by
        have := abs_sub_abs_le_abs_sub (f' ξ) (f' y)
        linarith [abs_sub_comm (f' ξ) (f' y), abs_sub_abs_le_abs_sub (f' y) (f' ξ)]
    _ < ε := by linarith

/-! ## The seam charge and its derivatives -/

/-- `v'(y) = c - 2 Im H'(-2y)`. -/
def thetaLoopChargeDeriv (y : ℝ) : ℝ :=
  Θ 1 - 2 * (deriv thetaOneSidedConnection ((-(2 * y) : ℝ) : ℂ)).im

theorem hasDerivAt_thetaOneSidedConnection_neg_two_mul (y : ℝ) :
    HasDerivAt (fun y : ℝ => thetaOneSidedConnection ((-(2 * y) : ℝ) : ℂ))
      (deriv thetaOneSidedConnection ((-(2 * y) : ℝ) : ℂ) * (-2)) y := by
  have hl : HasDerivAt (fun y : ℝ => (((-(2 * y) : ℝ)) : ℂ)) (-2 : ℂ) y := by
    have := ((hasDerivAt_id y).const_mul (-2 : ℝ)).ofReal_comp
    simpa using this
  exact (differentiable_thetaOneSidedConnection _).hasDerivAt.comp y hl

theorem hasDerivAt_thetaLoopCharge (y : ℝ) :
    HasDerivAt thetaLoopCharge (thetaLoopChargeDeriv y) y := by
  have h := (hasDerivAt_im_comp (hasDerivAt_thetaOneSidedConnection_neg_two_mul y)).const_add
    0 |>.add ((hasDerivAt_id y).const_mul (Θ 1))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · simp only [thetaLoopChargeDeriv, mul_im, mul_one]; simp; ring
  · simp only [thetaLoopCharge_eq]; simp; ring

/-- `v''(y) = 4 Im H''(-2y)`. -/
def thetaLoopChargeDeriv2 (y : ℝ) : ℝ :=
  4 * (deriv (deriv thetaOneSidedConnection) ((-(2 * y) : ℝ) : ℂ)).im

theorem hasDerivAt_thetaLoopChargeDeriv (y : ℝ) :
    HasDerivAt thetaLoopChargeDeriv (thetaLoopChargeDeriv2 y) y := by
  have hl : HasDerivAt (fun y : ℝ => (((-(2 * y) : ℝ)) : ℂ)) (-2 : ℂ) y := by
    have := ((hasDerivAt_id y).const_mul (-2 : ℝ)).ofReal_comp
    simpa using this
  have h1 := (differentiable_deriv_thetaOneSidedConnection _).hasDerivAt.comp y hl
  have h := ((hasDerivAt_im_comp h1).const_mul (-2)).const_add (Θ 1)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  · simp only [thetaLoopChargeDeriv2, mul_im]; simp; ring
  · simp only [thetaLoopChargeDeriv, Function.comp_def]; ring

theorem abs_thetaLoopChargeDeriv2_le (y : ℝ) :
    |thetaLoopChargeDeriv2 y| ≤ 64 * thetaConnectionStripConst := by
  rw [thetaLoopChargeDeriv2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have := (Complex.abs_im_le_norm _).trans (norm_deriv_deriv_thetaOneSidedConnection_le (-(2 * y)))
  linarith

theorem abs_thetaLoopChargeDeriv_le (y : ℝ) :
    |thetaLoopChargeDeriv y| ≤ Θ 1 + 8 * thetaConnectionStripConst := by
  have hc := thetaSeam_pos
  rw [thetaLoopChargeDeriv]
  have h := (Complex.abs_im_le_norm _).trans (norm_deriv_thetaOneSidedConnection_le
    (w := ((-(2 * y) : ℝ) : ℂ)) (by simp))
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos hc, abs_mul, abs_two]
  linarith

/-- **(11a).** `v'(y) → c`: the seam derivative also cancels asymptotically. -/
theorem tendsto_thetaLoopChargeDeriv : Tendsto thetaLoopChargeDeriv atTop (𝓝 (Θ 1)) := by
  have h := tendsto_deriv_of_tendsto_of_abs_deriv_deriv_le (f := fun y => thetaLoopCharge y - Θ 1 * y)
    (f' := fun y => thetaLoopChargeDeriv y - Θ 1) (f'' := thetaLoopChargeDeriv2)
    (M := 64 * thetaConnectionStripConst)
    (fun y => ((hasDerivAt_thetaLoopCharge y).sub ((hasDerivAt_id y).const_mul (Θ 1))).congr_deriv
      (by simp))
    (fun y => (hasDerivAt_thetaLoopChargeDeriv y).sub_const _) abs_thetaLoopChargeDeriv2_le
    tendsto_thetaLoopCharge_sub
  have := h.add_const (Θ 1)
  simpa using this

/-! ## The resonance phase `θ(y) = arg A(iy)` -/

/-- The resonance phase `θ(y) = arg A(iy)`. -/
def thetaResonancePhase (y : ℝ) : ℝ := Complex.arg (thetaLoopA (y * I))

/-- The phase velocity `θ'(y) = Im[(d/dy A(iy)) / A(iy)]`. -/
def thetaResonancePhaseDeriv (y : ℝ) : ℝ :=
  ((deriv thetaLoopA (y * I) * I) / thetaLoopA (y * I)).im

theorem thetaLoopA_I_mul_mem_slitPlane {y : ℝ} (hy : 0 ≤ y) :
    thetaLoopA (y * I) ∈ slitPlane := by
  rcases eq_or_lt_of_le hy with h0 | hpos
  · left
    subst h0
    rw [ofReal_zero, zero_mul, thetaLoopA, add_zero, thetaRenewalDenominator_zero_eq]
    simp only [mul_re, div_ofNat_re, one_re, ofReal_re, div_ofNat_im, one_im, ofReal_im,
      zero_div, mul_zero, sub_zero]
    linarith [thetaRenewalLaplaceReal_zero_lt]
  · right
    exact (thetaLoopCharge_pos hpos).ne'

theorem hasDerivAt_thetaLoopA_I_mul (y : ℝ) :
    HasDerivAt (fun y : ℝ => thetaLoopA (y * I)) (deriv thetaLoopA (y * I) * I) y := by
  have hl : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I y := by
    have := (hasDerivAt_id (y : ℂ)).mul_const I
    simpa using this.comp_ofReal
  exact (differentiable_thetaLoopA (y * I)).hasDerivAt.comp y hl

theorem re_deriv_thetaLoopA_path (y : ℝ) : (deriv thetaLoopA (y * I) * I).re = deriv Xi (2 * y) := by
  have h1 := hasDerivAt_re_comp (hasDerivAt_thetaLoopA_I_mul y)
  have h2 : HasDerivAt (fun t : ℝ => (thetaLoopA (t * I)).re) (deriv Xi (2 * y)) y := by
    have h := ((hasDerivAt_Xi_deriv (2 * y)).comp y ((hasDerivAt_id y).const_mul 2)).div_const 2
    refine (h.congr_deriv (by simp)).congr_of_eventuallyEq
      (Eventually.of_forall fun t => ?_)
    simp only [re_thetaLoopA_I_mul, Function.comp_def]
  exact h1.unique h2

theorem im_deriv_thetaLoopA_path (y : ℝ) :
    (deriv thetaLoopA (y * I) * I).im = thetaLoopChargeDeriv y :=
  (hasDerivAt_im_comp (hasDerivAt_thetaLoopA_I_mul y)).unique (hasDerivAt_thetaLoopCharge y)

/-- `θ' = (u v' - v u')/(u² + v²)` with `u = Re A(iy) = Ξ(2y)/2`, `u' = Ξ'(2y)`, `v = Im A(iy)`. -/
theorem thetaResonancePhaseDeriv_eq (y : ℝ) :
    thetaResonancePhaseDeriv y =
      ((thetaLoopA (y * I)).re * thetaLoopChargeDeriv y - thetaLoopCharge y * deriv Xi (2 * y)) /
        ((thetaLoopA (y * I)).re ^ 2 + thetaLoopCharge y ^ 2) := by
  rw [thetaResonancePhaseDeriv, Complex.div_im, im_deriv_thetaLoopA_path,
    re_deriv_thetaLoopA_path, Complex.normSq_apply, thetaLoopCharge]
  ring

/-- The phase velocity is the real part of the logarithmic derivative of `A` on the axis. -/
theorem thetaResonancePhaseDeriv_eq_logDeriv (y : ℝ) :
    thetaResonancePhaseDeriv y = (logDeriv thetaLoopA (y * I)).re := by
  rw [thetaResonancePhaseDeriv, logDeriv_apply, mul_div_right_comm, mul_comm, Complex.mul_im,
    I_re, I_im]
  ring

theorem hasDerivAt_thetaResonancePhase {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt thetaResonancePhase (thetaResonancePhaseDeriv y) y := by
  have h := hasDerivAt_im_comp ((hasDerivAt_thetaLoopA_I_mul y).clog_real
    (thetaLoopA_I_mul_mem_slitPlane hy))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [thetaResonancePhase, Complex.log_im]

/-- The resonance terms `(z - ζ)⁻¹ + ζ⁻¹` are absolutely summable off the divisor. -/
theorem summable_norm_resonanceTerm {z : ℂ}
    (hz : ∀ q, z ≠ GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint thetaRenewalDenominator q) :
    Summable fun q => ‖(z - GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint
      thetaRenewalDenominator q)⁻¹ + (GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint
        thetaRenewalDenominator q)⁻¹‖ := by
  have h := (summable_canonicalProductE1LogDerivTerm zeroCopyPoint_thetaRenewal_ne_zero
    summable_inv_sq_thetaRenewalZeros hz).neg
  refine summable_norm_iff.mpr (h.congr fun q => ?_)
  have hne : GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint thetaRenewalDenominator q - z ≠ 0 :=
    sub_ne_zero.mpr (hz q).symm
  rw [show z - GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint thetaRenewalDenominator q =
    -(GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint thetaRenewalDenominator q - z) by ring,
    inv_neg]
  ring

/-- **(11c).** The renormalized resonance sum:
`θ'(y) = a/(a² + y²) + β + ∑_ζ Re[(iy - ζ)⁻¹ + ζ⁻¹]`, absolutely convergent. -/
theorem thetaResonancePhaseDeriv_eq_resonanceSum (y : ℝ) :
    thetaResonancePhaseDeriv y = (1 / 4) / ((1 / 4) ^ 2 + y ^ 2) + thetaRenewalDrift +
      ∑' q, ((y * I - GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint
        thetaRenewalDenominator q)⁻¹ + (GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint
          thetaRenewalDenominator q)⁻¹).re := by
  have hD : thetaRenewalDenominator (y * I) ≠ 0 := thetaRenewalDenominator_ne_zero (by simp)
  have hq : ∀ q, (y : ℂ) * I ≠ GaloisForLFunctions.EntireZeroDivisor.zeroCopyPoint
      thetaRenewalDenominator q := fun q h => hD (h ▸ thetaRenewalDenominator_zeroCopyPoint q)
  have ha : (1 / 4 : ℂ) + y * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hfun : thetaLoopA = fun lam => (1 / 4 + lam) * thetaRenewalDenominator lam := rfl
  rw [thetaResonancePhaseDeriv_eq_logDeriv, hfun, logDeriv_mul (y * I) ha hD (by fun_prop)
    (differentiable_thetaRenewalDenominator _), logDeriv_thetaRenewalDenominator hD]
  have hlin : logDeriv (fun lam : ℂ => 1 / 4 + lam) (y * I) = 1 / (1 / 4 + y * I) := by
    rw [logDeriv_apply, deriv_const_add, deriv_id'']
  rw [hlin, add_re, add_re, ofReal_re, Complex.re_tsum (summable_norm_iff.mp
    (summable_norm_resonanceTerm hq))]
  have hre : ((1 : ℂ) / (1 / 4 + y * I)).re = (1 / 4) / ((1 / 4) ^ 2 + y ^ 2) := by
    rw [Complex.div_re, Complex.normSq_apply]
    simp
    field_simp
  rw [hre]
  ring

theorem thetaResonancePhase_zero : thetaResonancePhase 0 = 0 := by
  rw [thetaResonancePhase, ofReal_zero, zero_mul, Complex.arg_eq_zero_iff]
  have h := thetaLoopA_I_mul_mem_slitPlane (y := 0) le_rfl
  rw [ofReal_zero, zero_mul] at h
  refine ⟨?_, ?_⟩
  · rcases h with h | h
    · exact h.le
    · rw [thetaLoopA, add_zero, thetaRenewalDenominator_zero_eq] at h; simp at h
  · rw [thetaLoopA, add_zero, thetaRenewalDenominator_zero_eq]; simp

/-- For `y > 0`, `θ(y) - π/2 = -arctan(u(y)/v(y))`. -/
theorem thetaResonancePhase_eq_arctan {y : ℝ} (hy : 0 < y) :
    thetaResonancePhase y =
      Real.pi / 2 - Real.arctan ((thetaLoopA (y * I)).re / thetaLoopCharge y) := by
  have hv := thetaLoopCharge_pos hy
  set z := thetaLoopA (y * I)
  have him : 0 < z.im := hv
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr fun h => by rw [h] at him; simp at him
  have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [thetaResonancePhase, Complex.arg_of_im_pos him, Real.arccos_eq_pi_div_two_sub_arcsin]
  congr 1
  have hlt : |z.re / ‖z‖| < 1 := by
    rw [abs_div, abs_norm, div_lt_one hnz]
    exact Complex.abs_re_lt_norm.mpr him.ne'
  rw [Real.arcsin_eq_arctan (abs_lt.mp hlt)]
  congr 1
  have hsq : √(1 - (z.re / ‖z‖) ^ 2) = z.im / ‖z‖ := by
    rw [show 1 - (z.re / ‖z‖) ^ 2 = (z.im / ‖z‖) ^ 2 by field_simp; linarith,
      Real.sqrt_sq (by positivity)]
  rw [hsq, thetaLoopCharge]
  change z.re / ‖z‖ / (z.im / ‖z‖) = z.re / z.im
  field_simp

/-- For `y > 0` the phase lies in `(0, π)`. -/
theorem thetaResonancePhase_mem_Ioo {y : ℝ} (hy : 0 < y) :
    thetaResonancePhase y ∈ Ioo 0 Real.pi := by
  rw [thetaResonancePhase_eq_arctan hy]
  have h1 := Real.arctan_lt_pi_div_two ((thetaLoopA (y * I)).re / thetaLoopCharge y)
  have h2 := Real.neg_pi_div_two_lt_arctan ((thetaLoopA (y * I)).re / thetaLoopCharge y)
  constructor <;> linarith

theorem eventually_thetaLoopCharge_ge : ∀ᶠ y in atTop, Θ 1 / 2 * y ≤ thetaLoopCharge y := by
  have hc := thetaSeam_pos
  filter_upwards [(tendsto_thetaLoopCharge_sub.eventually (Metric.ball_mem_nhds 0
    (by positivity : (0 : ℝ) < Θ 1 / 2))), eventually_ge_atTop 1] with y hy hy1
  rw [Real.dist_eq, sub_zero, abs_lt] at hy
  nlinarith

theorem exists_abs_Xi_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |Xi t| ≤ C * Real.exp (-(δ * |t|)) := by
  obtain ⟨C, hC, h⟩ := exists_norm_XiC_horizontal_le (A := 0) (δ := δ) (by norm_num) hδ0 hδ
  refine ⟨C, hC, fun t => ?_⟩
  have := h t 0 (by simp)
  simpa [XiC_ofReal] using this

/-- `θ(y) → π/2`. -/
theorem tendsto_thetaResonancePhase : Tendsto thetaResonancePhase atTop (𝓝 (Real.pi / 2)) := by
  obtain ⟨C, hC, hXi⟩ := exists_abs_Xi_le (δ := 0) le_rfl (by linarith [Real.pi_pos])
  have hc := thetaSeam_pos
  have hratio : Tendsto (fun y : ℝ => (thetaLoopA ((y : ℂ) * I)).re / thetaLoopCharge y) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun y => C / (Θ 1 / 2 * y)) ?_ ?_
    · filter_upwards [eventually_thetaLoopCharge_ge, eventually_gt_atTop 0] with y hy hy0
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (thetaLoopCharge_pos hy0), re_thetaLoopA_I_mul]
      have h1 := hXi (2 * y)
      simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at h1
      rw [abs_div, abs_two]
      have hvp := thetaLoopCharge_pos hy0
      calc |Xi (2 * y)| / 2 / thetaLoopCharge y ≤ C / thetaLoopCharge y := by
            gcongr; linarith [abs_nonneg (Xi (2 * y))]
        _ ≤ C / (Θ 1 / 2 * y) := div_le_div_of_nonneg_left hC (by positivity) hy
    · exact tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by positivity))
  have h := (Real.continuous_arctan.tendsto 0).comp hratio
  rw [Real.arctan_zero] at h
  have := (tendsto_const_nhds (x := Real.pi / 2)).sub h
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with y hy
  rw [thetaResonancePhase_eq_arctan hy]; rfl

/-- **(11d).** For `0 < κ < π/2`: `|u| + |u'| = O(e^{-κy})` and `|θ'(y)| = O(e^{-κy}/y)`. -/
theorem exists_thetaResonancePhase_bounds {κ : ℝ} (hκ : 0 < κ) (hκ2 : κ < Real.pi / 2) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧ ∀ y, Y₀ ≤ y →
      |(thetaLoopA (y * I)).re| + |deriv Xi (2 * y)| ≤ C * Real.exp (-(κ * y)) ∧
      |thetaResonancePhaseDeriv y| ≤ C * Real.exp (-(κ * y)) / y := by
  have hc := thetaSeam_pos
  obtain ⟨C₁, hC₁, hXi⟩ := exists_abs_Xi_le (δ := κ / 2) (by linarith) (by linarith)
  obtain ⟨C₂, hC₂, hXi'⟩ := exists_abs_deriv_Xi_le (δ := κ / 2) (by linarith) (by linarith)
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp eventually_thetaLoopCharge_ge
  set V₁ := Θ 1 + 8 * thetaConnectionStripConst
  have hV₁ : 0 ≤ V₁ := (abs_nonneg _).trans (abs_thetaLoopChargeDeriv_le 0)
  set C := C₁ + C₂ + (C₁ / 2) * V₁ / (Θ 1 / 2) ^ 2 + C₂ / (Θ 1 / 2)
  refine ⟨C, max Y₁ 1, by positivity, le_max_right _ _, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : 0 < y := by linarith
  have hv := hY₁ y (le_trans (le_max_left _ _) hy)
  have hvpos := thetaLoopCharge_pos hy0
  have hexp : Real.exp (-(κ / 2 * |2 * y|)) = Real.exp (-(κ * y)) := by
    rw [abs_of_pos (by linarith)]; ring_nf
  have hu : |(thetaLoopA (y * I)).re| ≤ C₁ / 2 * Real.exp (-(κ * y)) := by
    rw [re_thetaLoopA_I_mul, abs_div, abs_two]
    have := hXi (2 * y); rw [hexp] at this; linarith
  have hu' : |deriv Xi (2 * y)| ≤ C₂ * Real.exp (-(κ * y)) := by
    have := hXi' (2 * y); rwa [hexp] at this
  have hE := Real.exp_pos (-(κ * y))
  refine ⟨?_, ?_⟩
  · have hP : 0 ≤ C₁ / 2 * V₁ / (Θ 1 / 2) ^ 2 := by positivity
    have hQ : 0 ≤ C₂ / (Θ 1 / 2) := by positivity
    have : C₁ / 2 * Real.exp (-(κ * y)) + C₂ * Real.exp (-(κ * y)) ≤ C * Real.exp (-(κ * y)) := by
      rw [← add_mul]; gcongr; simp only [C]; linarith
    linarith
  · rw [thetaResonancePhaseDeriv_eq]
    set u := (thetaLoopA (y * I)).re
    set v := thetaLoopCharge y
    have hvd := abs_thetaLoopChargeDeriv_le y
    have hden : v ^ 2 ≤ u ^ 2 + v ^ 2 := by nlinarith
    rw [abs_div, abs_of_pos (by positivity : 0 < u ^ 2 + v ^ 2)]
    have hnum : |u * thetaLoopChargeDeriv y - v * deriv Xi (2 * y)| ≤
        C₁ / 2 * Real.exp (-(κ * y)) * V₁ + v * (C₂ * Real.exp (-(κ * y))) := by
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos hvpos]
      gcongr
    have hv2 : Θ 1 / 2 * y ≤ v := hv
    calc |u * thetaLoopChargeDeriv y - v * deriv Xi (2 * y)| / (u ^ 2 + v ^ 2)
        ≤ (C₁ / 2 * Real.exp (-(κ * y)) * V₁ + v * (C₂ * Real.exp (-(κ * y)))) / v ^ 2 :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = C₁ / 2 * Real.exp (-(κ * y)) * V₁ / v ^ 2 + C₂ * Real.exp (-(κ * y)) / v := by
          field_simp
      _ ≤ C₁ / 2 * Real.exp (-(κ * y)) * V₁ / (Θ 1 / 2 * y) ^ 2 +
            C₂ * Real.exp (-(κ * y)) / (Θ 1 / 2 * y) := by
          gcongr
      _ = (C₁ / 2 * V₁ / (Θ 1 / 2) ^ 2) * Real.exp (-(κ * y)) / y ^ 2 +
            (C₂ / (Θ 1 / 2)) * Real.exp (-(κ * y)) / y := by
          field_simp
      _ ≤ (C₁ / 2 * V₁ / (Θ 1 / 2) ^ 2) * Real.exp (-(κ * y)) / y +
            (C₂ / (Θ 1 / 2)) * Real.exp (-(κ * y)) / y := by
          have hyy : y ≤ y ^ 2 := by nlinarith
          gcongr
      _ ≤ C * Real.exp (-(κ * y)) / y := by
          rw [← add_div, ← add_mul]
          have hP : 0 ≤ C₁ / 2 * V₁ / (Θ 1 / 2) ^ 2 := by positivity
          have hQ : 0 ≤ C₂ / (Θ 1 / 2) := by positivity
          gcongr
          simp only [C]; linarith

theorem continuous_thetaResonancePhaseDeriv : Continuous thetaResonancePhaseDeriv := by
  have hA : Continuous fun y : ℝ => thetaLoopA (y * I) :=
    differentiable_thetaLoopA.continuous.comp (by fun_prop)
  have hA' : Continuous fun y : ℝ => deriv thetaLoopA (y * I) :=
    (differentiableOn_univ.mp ((differentiable_thetaLoopA.differentiableOn.analyticOnNhd
      isOpen_univ).deriv.differentiableOn)).continuous.comp (by fun_prop)
  exact continuous_im.comp ((hA'.mul continuous_const).div hA fun y =>
    thetaLoopA_ne_zero (by simp))

/-- **(11d), variation budget.** `∫_Y^∞ |θ'| = O(e^{-κY})` for every `0 < κ < π/2`. -/
theorem exists_integral_abs_thetaResonancePhaseDeriv_le {κ : ℝ} (hκ : 0 < κ)
    (hκ2 : κ < Real.pi / 2) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ ∀ Y, Y₀ ≤ Y →
      IntegrableOn (fun y => |thetaResonancePhaseDeriv y|) (Ioi Y) ∧
      ∫ y in Ioi Y, |thetaResonancePhaseDeriv y| ≤ C * Real.exp (-(κ * Y)) := by
  obtain ⟨C, Y₀, hC, hY₀, hb⟩ := exists_thetaResonancePhase_bounds hκ hκ2
  refine ⟨C / κ, Y₀, by positivity, fun Y hY => ?_⟩
  have hdom : IntegrableOn (fun y => C * Real.exp (-κ * y)) (Ioi Y) :=
    (integrableOn_exp_mul_Ioi (by linarith) Y).const_mul C
  have hbound : ∀ y ∈ Ioi Y, |thetaResonancePhaseDeriv y| ≤ C * Real.exp (-κ * y) := by
    intro y hy
    have hyY : Y₀ ≤ y := le_trans hY (le_of_lt hy)
    have hy1 : 1 ≤ y := le_trans hY₀ hyY
    have h := (hb y hyY).2
    have hE := Real.exp_pos (-(κ * y))
    calc |thetaResonancePhaseDeriv y| ≤ C * Real.exp (-(κ * y)) / y := h
      _ ≤ C * Real.exp (-(κ * y)) := div_le_self (by positivity) hy1
      _ = C * Real.exp (-κ * y) := by ring_nf
  have hint : IntegrableOn (fun y => |thetaResonancePhaseDeriv y|) (Ioi Y) :=
    hdom.mono' (continuous_thetaResonancePhaseDeriv.abs.aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => by
        rw [Real.norm_eq_abs, abs_abs]; exact hbound y hy))
  refine ⟨hint, (setIntegral_mono_on hint hdom measurableSet_Ioi hbound).trans (le_of_eq ?_)⟩
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) Y]
  field_simp

/-- **(11e).** At a positive critical zero `θ(y_j) = π/2` and `d_j = 2 θ'(y_j)`. -/
theorem thetaResonancePhase_at_zero {y : ℝ} (hy0 : 0 < y) (hy : Xi (2 * y) = 0) :
    thetaResonancePhase y = Real.pi / 2 ∧
      thetaLoopBoundaryValue y = 2 * thetaResonancePhaseDeriv y := by
  have hu : (thetaLoopA (y * I)).re = 0 := by rw [re_thetaLoopA_I_mul, hy]; ring
  have hv := thetaLoopCharge_pos hy0
  refine ⟨by rw [thetaResonancePhase_eq_arctan hy0, hu, zero_div, Real.arctan_zero, sub_zero], ?_⟩
  rw [thetaResonancePhaseDeriv_eq, hu, thetaLoopBoundaryValue, thetaLoopSlope_eq_deriv]
  field_simp
  ring

/-- **Zeno crossing law.** Above every height the phase crosses `π/2` with both orientations,
while the total variation beyond height `Y` is `O(e^{-κY})`. -/
theorem exists_thetaResonancePhase_crossing {s : ℝ} (hs : s = 1 ∨ s = -1) (Y : ℝ) :
    ∃ y > Y, Xi (2 * y) = 0 ∧ thetaResonancePhase y = Real.pi / 2 ∧
      0 < s * thetaResonancePhaseDeriv y := by
  obtain ⟨γ, hγ, hXi, hd⟩ := exists_simpleCrossing_above (-s)
    (by rcases hs with h | h <;> simp [h]) (2 * max Y 0)
  have hy0 : 0 < γ / 2 := by linarith [le_max_right Y 0]
  have h2 : 2 * (γ / 2) = γ := by ring
  have hXi' : Xi (2 * (γ / 2)) = 0 := by rw [h2]; exact hXi
  obtain ⟨hθ, hdθ⟩ := thetaResonancePhase_at_zero hy0 hXi'
  refine ⟨γ / 2, by linarith [le_max_left Y 0], hXi', hθ, ?_⟩
  have hv := thetaLoopCharge_pos hy0
  have hb : 0 < s * thetaLoopBoundaryValue (γ / 2) := by
    rw [thetaLoopBoundaryValue, thetaLoopSlope_eq_deriv, h2, mul_div_assoc', lt_div_iff₀ hv]
    nlinarith
  rw [hdθ] at hb
  linarith

/-- **Rejection of the Stokes-winding transfer.** The completed prime–Gamma Stokes flow
`F(t) = -8t ξ'/ξ(1/2 + 2|t|)` has a single zero, while `θ - π/2` has infinitely many positive
zeros; no injective reparametrization `φ` and nowhere-vanishing factor `g` give
`θ(y) - π/2 = g(y) F(φ(y))` on `(0, ∞)`. -/
theorem not_exists_reparam_stokesFlow_thetaResonancePhase :
    ¬ ∃ φ g : ℝ → ℝ, Function.Injective φ ∧ (∀ y, g y ≠ 0) ∧ ∀ y, 0 < y →
      thetaResonancePhase y - Real.pi / 2 =
        g y * gammaSewnCriticalCompletedPrimeGammaCrossingFlow (φ y) := by
  rintro ⟨φ, g, hφ, hg, heq⟩
  have hZ := infinite_zeros_boundaryValue_sign (s := 1) (Or.inl rfl)
  obtain ⟨y₁, hy₁, y₂, hy₂, hne⟩ := hZ.nontrivial
  have hzero : ∀ y ∈ {y : ℝ | 0 < y ∧ Xi (2 * y) = 0 ∧ 0 < 1 * thetaLoopBoundaryValue y},
      φ y = 0 := by
    intro y hy
    have hθ := (thetaResonancePhase_at_zero hy.1 hy.2.1).1
    have h := heq y hy.1
    rw [hθ, sub_self] at h
    have hF : gammaSewnCriticalCompletedPrimeGammaCrossingFlow (φ y) = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left (hg y)
    exact (gammaSewnCriticalCompletedPrimeGammaCrossingFlow_eq_zero_iff _).mp hF
  exact hne (hφ ((hzero y₁ hy₁).trans (hzero y₂ hy₂).symm))

end

end RHTower
