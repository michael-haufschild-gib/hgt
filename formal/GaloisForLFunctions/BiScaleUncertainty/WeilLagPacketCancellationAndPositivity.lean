import GaloisForLFunctions.BiScaleUncertainty.EffectiveTranslatedPairingAndMultiplicityDefect
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitWeilEnergy

/-!
# Prime-lag packet cancellation and single-probe Weil positivity

For a real compactly supported `C²` source `f` vanishing outside `[−w, w]`, the stationary
prime–polar packet `stationaryPacket f τ` is expressed in `BiScaleUncertainty` through the first-order
hyperbolic gauge derivative `gaugeDerivative f u = f'(u) − f(u)/2` and the normalized Chebyshev error
`normalizedLogError t = e^{−t/2}(ψ(e^t) − e^t)`. In `RHTower`, the prime-deficit flux balance
expresses the incoming amplitude `ccmPrimeDeficitIncoming t = e^{−t/2} D(t)` (`D(t) = ∫_0^t (e^u − ψ(e^u)) du`)
and the outgoing amplitude `ccmPrimeDeficitOutgoing t` in terms of the arithmetic Weil lag
`weilLagFunctionReal t` up to the archimedean term `e^{−t/2}(log(2π) − trivialZeroSeriesReal(e^t))`.

This module bridges the two theories by introducing the dual hyperbolic gauge derivative
`dualGaugeDerivative f u = f'(u) + f(u)/2`, the second-order Weil pole operator
`weilPoleOperator f u = dualGaugeDerivative (gaugeDerivative f) u = f''(u) − f(u)/4`, and the
iterated gauge derivative `doubleGaugeDerivative f u = gaugeDerivative (gaugeDerivative f) u`, and
establishing three main results:

1. **Exact polar annihilation and second-order prime-lag packet identities**
   (`integral_exp_half_mul_weilPoleOperator_eq_zero`,
   `integral_exp_neg_half_mul_weilPoleOperator_eq_zero`,
   `integral_normalizedLogError_mul_gaugeDerivative_eq_incoming`,
   `integral_normalizedLogError_mul_gaugeDerivative_eq_outgoing`,
   `stationaryPacket_eq_incoming_integral`, `stationaryPacket_eq_outgoing_integral`,
   `stationaryPacket_eq_weilLag_sub_trivialZero`,
   `stationaryPacket_eq_central_weilLag_add_oscillation`):
   Because `(d/dt)(e^{t/2}(f' − f/2)(t − τ)) = e^{t/2}(f'' − f/4)(t − τ)` and
   `(d/dt)(e^{−t/2}(f' + f/2)(t − τ)) = e^{−t/2}(f'' − f/4)(t − τ)`, the second-order kernel
   `weilPoleOperator f (· − τ)` annihilates the entire two-dimensional polar space
   `span{e^{t/2}, e^{−t/2}}` on `[τ − w, τ + w]`. Moreover, since `gaugeDerivative f − dualGaugeDerivative f = −f`,
   the forward polar residual satisfies
   `−∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt = ∫_{τ−w}^{τ+w} (t − τ) e^{−t/2} weilPoleOperator f (t − τ) dt`.
   Integrating the local Chebyshev gauge formula by parts against `ccmPrimeDeficitIncoming` and
   `ccmPrimeDeficitOutgoing` eliminates the `e^{−t/2} log(2π)` archimedean term in
   `ccmPrimeDeficitOutgoing_eq_weilLag` identically: for every `τ > w`,
   * `stationaryPacket f τ = −∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt − ∫_{τ−w}^{τ+w} ccmPrimeDeficitIncoming t * doubleGaugeDerivative f (t − τ) dt`,
   * `stationaryPacket f τ = −∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt + ∫_{τ−w}^{τ+w} ccmPrimeDeficitOutgoing t * weilPoleOperator f (t − τ) dt`,
   * `stationaryPacket f τ = ∫_{τ−w}^{τ+w} weilLagFunctionReal t * weilPoleOperator f (t − τ) dt`
     `+ ∫_{τ−w}^{τ+w} e^{−t/2} ((t − τ) − trivialZeroSeriesReal (e^t)) * weilPoleOperator f (t − τ) dt`.

2. **Pointwise finite-shift bounds for general `C²_c` sources and `splineProbe`**
   (`abs_stationaryPacket_le_local_incoming`, `abs_stationaryPacket_le_local_outgoing`,
   `abs_stationaryPacket_le_local_weilLag`,
   `abs_stationaryPacket_splineProbe_le_local_incoming`,
   `abs_stationaryPacket_splineProbe_le_local_weilLag`):
   Explicit bounds on `weilPoleOperator splineProbe` (`≤ (5/8) e⁴`) and
   `doubleGaugeDerivative splineProbe` (`≤ (9/8) e⁴`) bound `|stationaryPacket splineProbe τ|` at
   every shift `τ > 4` directly by the local `L¹` norm of `ccmPrimeDeficitIncoming` or
   `weilLagFunctionReal` on `[τ − 4, τ + 4]` plus an `O(e^{−τ/2})` archimedean tail.

3. **Universal autocorrelation probes and single-probe Weil positivity**
   (`seesAllZeros_autocorr`, `seesAllZeros_autocorr_splineProbe`,
   `riemannHypothesis_iff_autocorr_packet_bddAbove_of_universal`,
   `forall_weilTest_nonneg_iff_autocorr_splineProbe_bddAbove`,
   `forall_levyWeilEnergy_nonneg_iff_autocorr_splineProbe_bddAbove`,
   `riemannHypothesis_iff_weilLagPoleConvolution_autocorr_splineProbe_bddAbove`):
   Reflection symmetry of the nontrivial zeros (`ρ ↦ 1 − ρ̄`) implies that the autocorrelation
   `autocorr U` of any universal probe `U` is again a universal probe; in particular,
   `SeesAllZeros (autocorr splineProbe)`. Consequently, a one-sided bound on the translated pairing
   `τ ↦ stationaryPacket (autocorr U) τ` — or on the pure Weil-lag pole convolution
   `τ ↦ ∫_{τ−2w}^{τ+2w} weilLagFunctionReal t * weilPoleOperator (autocorr U) (t − τ) dt` — for a
   single universal probe `U` (and explicitly for `U = splineProbe`) is unconditionally equivalent
   to `RiemannHypothesis`, to universal positivity of the complete Weil functional across all test
   functions, and to critical collapse of the Weil functional.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators Convolution CompactlySupported ComplexConjugate
open RHTower.WeilDeletion (unif upow unif_nonneg upow_nonneg integrable_unif integrable_upow
  integral_unif integral_upow hasCompactSupport_upow paperFT_unif paperFT_upow
  norm_paperFT_unif_le norm_paperFT_upow_le support_upow_subset)

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## §1. Dual gauge derivative, Weil pole operator, and iterated gauge derivative -/

/-- The dual hyperbolic gauge derivative `(D_+ f)(u) = f'(u) + f(u)/2 = e^{−u/2}(e^{u/2} f(u))'`. -/
def dualGaugeDerivative (f : ℝ → ℝ) (u : ℝ) : ℝ := deriv f u + f u / 2

/-- The second-order Weil pole operator `(D_+ D_− f)(u) = (f' − f/2)' + (f' − f/2)/2 = f''(u) − f(u)/4`. -/
def weilPoleOperator (f : ℝ → ℝ) (u : ℝ) : ℝ := dualGaugeDerivative (gaugeDerivative f) u

/-- The iterated hyperbolic gauge derivative `(D_−² f)(u) = (f' − f/2)' − (f' − f/2)/2 = f''(u) − f'(u) + f(u)/4`. -/
def doubleGaugeDerivative (f : ℝ → ℝ) (u : ℝ) : ℝ := gaugeDerivative (gaugeDerivative f) u

/-- A continuous function vanishing strictly outside `[−w, w]` also vanishes on `|v| ≥ w`. -/
theorem eq_zero_of_continuous_of_le_abs {g : ℝ → ℝ} (hg : Continuous g) {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → g v = 0) {v : ℝ} (hv : w ≤ |v|) : g v = 0 := by
  by_contra hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne.preimage hg) v hne
  set x := if 0 ≤ v then v + ε / 2 else v - ε / 2
  have hxball : x ∈ Metric.ball v ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    by_cases hv0 : 0 ≤ v
    · simp only [x, if_pos hv0, add_sub_cancel_left, abs_of_pos (half_pos hε), half_lt_self hε]
    · simp only [x, if_neg hv0, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hε),
        half_lt_self hε]
  have hwx : w < |x| := by
    by_cases hv0 : 0 ≤ v
    · simp only [x, if_pos hv0]
      rw [abs_of_nonneg hv0] at hv
      rw [abs_of_pos (by linarith)]
      linarith
    · simp only [x, if_neg hv0]
      push Not at hv0
      rw [abs_of_neg hv0] at hv
      rw [abs_of_neg (by linarith)]
      linarith
  exact hball hxball (hw x hwx)

theorem contDiff_one_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (deriv f) := by
  have hf' : ContDiff ℝ ((1 : ℕ) + 1) f := hf
  exact (contDiff_succ_iff_deriv.mp hf').2.2

theorem contDiff_one_gaugeDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (gaugeDerivative f) :=
  (contDiff_one_deriv hf).sub ((hf.of_le (by norm_num)).div_const 2)

theorem contDiff_one_dualGaugeDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (dualGaugeDerivative f) :=
  (contDiff_one_deriv hf).add ((hf.of_le (by norm_num)).div_const 2)

theorem continuous_dualGaugeDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (dualGaugeDerivative f) :=
  (hf.continuous_deriv le_rfl).add (hf.continuous.div_const 2)

theorem continuous_weilPoleOperator {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (weilPoleOperator f) :=
  continuous_dualGaugeDerivative (contDiff_one_gaugeDerivative hf)

theorem continuous_doubleGaugeDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (doubleGaugeDerivative f) :=
  continuous_gaugeDerivative (contDiff_one_gaugeDerivative hf)

theorem hasCompactSupport_dualGaugeDerivative {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (dualGaugeDerivative f) := by
  have h2 : HasCompactSupport (fun u => f u / 2) := by
    have h := hfc.mul_right (f' := fun _ : ℝ => (2 : ℝ)⁻¹)
    have he : (fun u => f u / 2) = f * fun _ : ℝ => (2 : ℝ)⁻¹ := by
      funext u; simp [div_eq_mul_inv]
    rw [he]; exact h
  show HasCompactSupport (fun u => deriv f u + f u / 2)
  exact hfc.deriv.add h2

theorem hasCompactSupport_weilPoleOperator {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (weilPoleOperator f) :=
  hasCompactSupport_dualGaugeDerivative (hasCompactSupport_gaugeDerivative hfc)

theorem hasCompactSupport_doubleGaugeDerivative {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (doubleGaugeDerivative f) :=
  hasCompactSupport_gaugeDerivative (hasCompactSupport_gaugeDerivative hfc)

theorem dualGaugeDerivative_eq_zero_of_lt_abs {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {v : ℝ} (hv : w < |v|) :
    dualGaugeDerivative f v = 0 := by
  have hd : deriv f v = 0 := by
    have hev : f =ᶠ[𝓝 v] (fun _ => 0) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨{x | w < |x|},
        (isOpen_lt continuous_const continuous_abs).mem_nhds hv, fun x hx => hw x hx⟩
    rw [hev.deriv_eq, deriv_const]
  simp [dualGaugeDerivative, hd, hw v hv]

theorem weilPoleOperator_eq_zero_of_lt_abs {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {v : ℝ} (hv : w < |v|) :
    weilPoleOperator f v = 0 :=
  dualGaugeDerivative_eq_zero_of_lt_abs (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h) hv

theorem doubleGaugeDerivative_eq_zero_of_lt_abs {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {v : ℝ} (hv : w < |v|) :
    doubleGaugeDerivative f v = 0 :=
  gaugeDerivative_eq_zero_of_lt_abs (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h) hv

theorem deriv_gaugeDerivative_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (u : ℝ) :
    deriv (gaugeDerivative f) u = deriv (deriv f) u - deriv f u / 2 := by
  have hd1 : DifferentiableAt ℝ (deriv f) u := (contDiff_one_deriv hf).differentiable one_ne_zero u
  have hd2 : DifferentiableAt ℝ f u := (hf.of_le (by norm_num)).differentiable one_ne_zero u
  exact (hd1.hasDerivAt.sub (hd2.hasDerivAt.div_const 2)).deriv

theorem deriv_dualGaugeDerivative_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (u : ℝ) :
    deriv (dualGaugeDerivative f) u = deriv (deriv f) u + deriv f u / 2 := by
  have hd1 : DifferentiableAt ℝ (deriv f) u := (contDiff_one_deriv hf).differentiable one_ne_zero u
  have hd2 : DifferentiableAt ℝ f u := (hf.of_le (by norm_num)).differentiable one_ne_zero u
  exact (hd1.hasDerivAt.add (hd2.hasDerivAt.div_const 2)).deriv

/-- Explicit formula `(D_+ D_− f)(u) = f''(u) − f(u)/4` for `f ∈ C²`. -/
theorem weilPoleOperator_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (u : ℝ) :
    weilPoleOperator f u = deriv (deriv f) u - f u / 4 := by
  unfold weilPoleOperator dualGaugeDerivative
  rw [deriv_gaugeDerivative_eq hf u]
  unfold gaugeDerivative
  ring

/-- The gauge derivatives `D_+` and `D_−` commute on `C²`: `D_− (D_+ f) = D_+ (D_− f)`. -/
theorem gaugeDerivative_dualGaugeDerivative_eq_weilPoleOperator {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (u : ℝ) :
    gaugeDerivative (dualGaugeDerivative f) u = weilPoleOperator f u := by
  rw [weilPoleOperator_eq hf u]
  unfold gaugeDerivative
  rw [deriv_dualGaugeDerivative_eq hf u]
  unfold dualGaugeDerivative
  ring

/-- Explicit formula `(D_−² f)(u) = f''(u) − f'(u) + f(u)/4` for `f ∈ C²`. -/
theorem doubleGaugeDerivative_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (u : ℝ) :
    doubleGaugeDerivative f u = deriv (deriv f) u - deriv f u + f u / 4 := by
  unfold doubleGaugeDerivative gaugeDerivative
  rw [deriv_gaugeDerivative_eq hf u]
  unfold gaugeDerivative
  ring

/-- Exact decomposition `D_−² f = weilPoleOperator f − D_− f`. -/
theorem doubleGaugeDerivative_eq_weilPoleOperator_sub_gaugeDerivative {f : ℝ → ℝ} (u : ℝ) :
    doubleGaugeDerivative f u = weilPoleOperator f u - gaugeDerivative f u := by
  unfold doubleGaugeDerivative weilPoleOperator gaugeDerivative dualGaugeDerivative
  ring

/-! ## §2. Exact polar mode annihilation and constant-mode identity for `weilPoleOperator` -/

/-- `(d/dt)(e^{−t/2} g(t − τ)) = e^{−t/2} (D_− g)(t − τ)`. -/
theorem hasDerivAt_exp_neg_half_mul_sub {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (τ t : ℝ) :
    HasDerivAt (fun t => Real.exp (-t / 2) * g (t - τ))
      (Real.exp (-t / 2) * gaugeDerivative g (t - τ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
    simpa using ((hasDerivAt_id t).neg.div_const 2).exp
  have h2 : HasDerivAt (fun t => g (t - τ)) (deriv g (t - τ)) t := by
    simpa using ((hg.differentiable one_ne_zero) (t - τ)).hasDerivAt.comp t
      ((hasDerivAt_id t).sub_const τ)
  exact (h1.mul h2).congr_deriv (by unfold gaugeDerivative; ring)

/-- `(d/dt)(e^{t/2} g(t − τ)) = e^{t/2} (D_+ g)(t − τ)`. -/
theorem hasDerivAt_exp_half_mul_sub {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (τ t : ℝ) :
    HasDerivAt (fun t => Real.exp (t / 2) * g (t - τ))
      (Real.exp (t / 2) * dualGaugeDerivative g (t - τ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    simpa using ((hasDerivAt_id t).div_const 2).exp
  have h2 : HasDerivAt (fun t => g (t - τ)) (deriv g (t - τ)) t := by
    simpa using ((hg.differentiable one_ne_zero) (t - τ)).hasDerivAt.comp t
      ((hasDerivAt_id t).sub_const τ)
  exact (h1.mul h2).congr_deriv (by unfold dualGaugeDerivative; ring)

/-- `(d/dt)(e^{t/2} (D_− f)(t − τ)) = e^{t/2} (weilPoleOperator f)(t − τ)`. -/
theorem hasDerivAt_exp_half_mul_gaugeDerivative_sub {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (τ t : ℝ) :
    HasDerivAt (fun t => Real.exp (t / 2) * gaugeDerivative f (t - τ))
      (Real.exp (t / 2) * weilPoleOperator f (t - τ)) t :=
  hasDerivAt_exp_half_mul_sub (contDiff_one_gaugeDerivative hf) τ t

/-- `(d/dt)(e^{−t/2} (D_+ f)(t − τ)) = e^{−t/2} (weilPoleOperator f)(t − τ)`. -/
theorem hasDerivAt_exp_neg_half_mul_dualGaugeDerivative_sub {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (τ t : ℝ) :
    HasDerivAt (fun t => Real.exp (-t / 2) * dualGaugeDerivative f (t - τ))
      (Real.exp (-t / 2) * weilPoleOperator f (t - τ)) t := by
  have h := hasDerivAt_exp_neg_half_mul_sub (contDiff_one_dualGaugeDerivative hf) τ t
  rwa [gaugeDerivative_dualGaugeDerivative_eq_weilPoleOperator hf (t - τ)] at h

/-- **Annihilation of the growing polar mode `e^{t/2}`.** For `f ∈ C²` vanishing outside `[−w, w]`
(`w ≥ 0`), `∫_{τ−w}^{τ+w} e^{t/2} (weilPoleOperator f)(t − τ) dt = 0`. -/
theorem integral_exp_half_mul_weilPoleOperator_eq_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) (τ : ℝ) :
    (∫ t in Icc (τ - w) (τ + w), Real.exp (t / 2) * weilPoleOperator f (t - τ)) = 0 := by
  have hab : τ - w ≤ τ + w := by linarith
  have hcont : Continuous (fun t => Real.exp (t / 2) * weilPoleOperator f (t - τ)) :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      ((continuous_weilPoleOperator hf).comp (continuous_id.sub continuous_const))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_exp_half_mul_gaugeDerivative_sub hf τ t)
      (hcont.intervalIntegrable _ _)]
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative (hf.of_le (by norm_num))
  have hgw : gaugeDerivative f w = 0 :=
    eq_zero_of_continuous_of_le_abs hgc (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_of_nonneg hw0])
  have hgnw : gaugeDerivative f (-w) = 0 :=
    eq_zero_of_continuous_of_le_abs hgc (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_neg, abs_of_nonneg hw0])
  simp [hgw, hgnw]

/-- **Annihilation of the decaying polar mode `e^{−t/2}`.** For `f ∈ C²` vanishing outside
`[−w, w]` (`w ≥ 0`), `∫_{τ−w}^{τ+w} e^{−t/2} (weilPoleOperator f)(t − τ) dt = 0`. -/
theorem integral_exp_neg_half_mul_weilPoleOperator_eq_zero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) (τ : ℝ) :
    (∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * weilPoleOperator f (t - τ)) = 0 := by
  have hab : τ - w ≤ τ + w := by linarith
  have hcont : Continuous (fun t => Real.exp (-t / 2) * weilPoleOperator f (t - τ)) :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      ((continuous_weilPoleOperator hf).comp (continuous_id.sub continuous_const))
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_exp_neg_half_mul_dualGaugeDerivative_sub hf τ t)
      (hcont.intervalIntegrable _ _)]
  have hdc : Continuous (dualGaugeDerivative f) :=
    continuous_dualGaugeDerivative (hf.of_le (by norm_num))
  have hdw : dualGaugeDerivative f w = 0 :=
    eq_zero_of_continuous_of_le_abs hdc (fun _ h => dualGaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_of_nonneg hw0])
  have hdnw : dualGaugeDerivative f (-w) = 0 :=
    eq_zero_of_continuous_of_le_abs hdc (fun _ h => dualGaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_neg, abs_of_nonneg hw0])
  simp [hdw, hdnw]

/-- **Constant-mode integral of `weilPoleOperator`.** For `f ∈ C²` vanishing outside `[−w, w]`
(`w ≥ 0`), `∫_{τ−w}^{τ+w} (weilPoleOperator f)(t − τ) dt = −(1/4) ∫_{−w}^w f(u) du`. -/
theorem integral_weilPoleOperator_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) (τ : ℝ) :
    (∫ t in Icc (τ - w) (τ + w), weilPoleOperator f (t - τ)) =
      -(1 / 4) * ∫ u in Icc (-w) w, f u := by
  have hab : τ - w ≤ τ + w := by linarith
  have hw0' : -w ≤ w := by linarith
  have hd1 : ContDiff ℝ 1 (deriv f) := contDiff_one_deriv hf
  have hd_deriv : ∀ u : ℝ, HasDerivAt (deriv f) (deriv (deriv f) u) u :=
    fun u => (hd1.differentiable one_ne_zero u).hasDerivAt
  have hdd_cont : Continuous (deriv (deriv f)) := hd1.continuous_deriv le_rfl
  have hdd_zero : (∫ u in (-w)..w, deriv (deriv f) u) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd_deriv u)
      (hdd_cont.intervalIntegrable _ _)]
    have hdc : Continuous (deriv f) := hd1.continuous
    have hdz : ∀ v : ℝ, w < |v| → deriv f v = 0 := fun v hv => by
      have hev : f =ᶠ[𝓝 v] (fun _ => 0) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨{x | w < |x|},
          (isOpen_lt continuous_const continuous_abs).mem_nhds hv, fun x hx => hw x hx⟩
      rw [hev.deriv_eq, deriv_const]
    have hdw : deriv f w = 0 :=
      eq_zero_of_continuous_of_le_abs hdc hdz (by rw [abs_of_nonneg hw0])
    have hdnw : deriv f (-w) = 0 :=
      eq_zero_of_continuous_of_le_abs hdc hdz (by rw [abs_neg, abs_of_nonneg hw0])
    simp [hdw, hdnw]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_right (weilPoleOperator f) τ]
  simp only [sub_sub_cancel_left, add_sub_cancel_left]
  have hcongr : (∫ u in (-w)..w, weilPoleOperator f u) =
      ∫ u in (-w)..w, (deriv (deriv f) u - f u / 4) :=
    intervalIntegral.integral_congr fun u _ => weilPoleOperator_eq hf u
  rw [hcongr, intervalIntegral.integral_sub (hdd_cont.intervalIntegrable _ _)
    ((hf.continuous.div_const 4).intervalIntegrable _ _), hdd_zero, zero_sub,
    intervalIntegral.integral_div, intervalIntegral.integral_of_le hw0',
    ← integral_Icc_eq_integral_Ioc]
  ring

/-- **Forward exponential residual via `weilPoleOperator`.** Since
`gaugeDerivative f − dualGaugeDerivative f = −f`, differentiating
`t ↦ e^{−t/2}(f(t − τ) − (t − τ) dualGaugeDerivative f (t − τ))` yields
`−∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt = ∫_{τ−w}^{τ+w} (t − τ) e^{−t/2} weilPoleOperator f (t − τ) dt`. -/
theorem neg_integral_exp_neg_half_mul_eq_weilPoleOperator {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) (τ : ℝ) :
    -(∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * f (t - τ)) =
      ∫ t in Icc (τ - w) (τ + w),
        (t - τ) * Real.exp (-t / 2) * weilPoleOperator f (t - τ) := by
  have hab : τ - w ≤ τ + w := by linarith
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun t => Real.exp (-t / 2) * f (t - τ) -
        (t - τ) * (Real.exp (-t / 2) * dualGaugeDerivative f (t - τ)))
      (-(Real.exp (-t / 2) * f (t - τ)) -
        (t - τ) * Real.exp (-t / 2) * weilPoleOperator f (t - τ)) t := by
    intro t
    have h1 := hasDerivAt_exp_neg_half_mul_sub (hf.of_le (by norm_num)) τ t
    have h2 := ((hasDerivAt_id t).sub_const τ).mul
      (hasDerivAt_exp_neg_half_mul_dualGaugeDerivative_sub hf τ t)
    refine (h1.sub h2).congr_deriv ?_
    unfold gaugeDerivative dualGaugeDerivative
    ring
  have h1 : IntervalIntegrable (fun t => -(Real.exp (-t / 2) * f (t - τ)))
      volume (τ - w) (τ + w) :=
    (((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      (hf.continuous.comp (continuous_id.sub continuous_const))).neg).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun t => (t - τ) * Real.exp (-t / 2) * weilPoleOperator f (t - τ))
      volume (τ - w) (τ + w) :=
    (((continuous_id.sub continuous_const).mul
      (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).mul
      ((continuous_weilPoleOperator hf).comp
        (continuous_id.sub continuous_const))).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := τ - w) (b := τ + w)
    (fun t _ => hderiv t) (h1.sub h2)
  have hfw : f w = 0 :=
    eq_zero_of_continuous_of_le_abs hf.continuous hw (by rw [abs_of_nonneg hw0])
  have hfnw : f (-w) = 0 :=
    eq_zero_of_continuous_of_le_abs hf.continuous hw (by rw [abs_neg, abs_of_nonneg hw0])
  have hdc : Continuous (dualGaugeDerivative f) :=
    continuous_dualGaugeDerivative (hf.of_le (by norm_num))
  have hdw : dualGaugeDerivative f w = 0 :=
    eq_zero_of_continuous_of_le_abs hdc (fun _ h => dualGaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_of_nonneg hw0])
  have hdnw : dualGaugeDerivative f (-w) = 0 :=
    eq_zero_of_continuous_of_le_abs hdc (fun _ h => dualGaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_neg, abs_of_nonneg hw0])
  simp only [add_sub_cancel_left, sub_sub_cancel_left, hfw, hfnw, hdw, hdnw,
    mul_zero, sub_zero] at hibp
  rw [intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_neg,
    intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hibp
  linarith

/-! ## §3. Second-order integration by parts against `ccmPrimeDeficitIncoming` and `ccmPrimeDeficitOutgoing` -/

private theorem deficit_intervalIntegrable' (a b : ℝ) :
    IntervalIntegrable (fun t => Real.exp t - Chebyshev.psi (Real.exp t)) volume a b :=
  (Real.continuous_exp.intervalIntegrable a b).sub
    (Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable

/-- `ccmLogChebyshevDeficitPrimitive` is absolutely continuous on every compact interval. -/
theorem absolutelyContinuousOnInterval_ccmLogChebyshevDeficitPrimitive (a b : ℝ) :
    AbsolutelyContinuousOnInterval ccmLogChebyshevDeficitPrimitive a b := by
  have hi := deficit_intervalIntegrable' a b
  have h : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in a..t, Real.exp s - Chebyshev.psi (Real.exp s)) a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have heq : ccmLogChebyshevDeficitPrimitive = fun t =>
      ccmLogChebyshevDeficitPrimitive a +
        ∫ s in a..t, Real.exp s - Chebyshev.psi (Real.exp s) := by
    funext t
    exact (intervalIntegral.integral_add_adjacent_intervals
      (deficit_intervalIntegrable' 0 a)
      (deficit_intervalIntegrable' a t)).symm
  rw [heq]
  have hc : ContDiff ℝ 1 (fun _ : ℝ => ccmLogChebyshevDeficitPrimitive a) := contDiff_const
  exact hc.contDiffOn.absolutelyContinuousOnInterval.fun_add h

/-- `ccmPrimeDeficitIncoming` is absolutely continuous on every compact interval. -/
theorem absolutelyContinuousOnInterval_ccmPrimeDeficitIncoming (a b : ℝ) :
    AbsolutelyContinuousOnInterval ccmPrimeDeficitIncoming a b := by
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-t / 2)) := by fun_prop
  exact he.contDiffOn.absolutelyContinuousOnInterval.fun_mul
    (absolutelyContinuousOnInterval_ccmLogChebyshevDeficitPrimitive a b)

/-- `ccmPrimeDeficitFluxState` is `C¹` on `ℝ`. -/
theorem contDiff_ccmPrimeDeficitFluxState : ContDiff ℝ 1 ccmPrimeDeficitFluxState := by
  rw [show (1 : WithTop ℕ∞) = (0 : ℕ) + 1 by rfl, contDiff_succ_iff_deriv]
  refine ⟨fun t => (hasDerivAt_ccmPrimeDeficitFluxState t).differentiableAt, by simp, ?_⟩
  rw [Nat.cast_zero, contDiff_zero,
    show deriv ccmPrimeDeficitFluxState =
      fun t => ccmPrimeDeficitFluxState t / 2 - ccmPrimeDeficitIncoming t from
      funext fun t => (hasDerivAt_ccmPrimeDeficitFluxState t).deriv]
  exact (continuous_ccmPrimeDeficitFluxState.div_const 2).sub continuous_ccmPrimeDeficitIncoming

/-- `ccmPrimeDeficitOutgoing` is absolutely continuous on every compact interval. -/
theorem absolutelyContinuousOnInterval_ccmPrimeDeficitOutgoing (a b : ℝ) :
    AbsolutelyContinuousOnInterval ccmPrimeDeficitOutgoing a b :=
  contDiff_ccmPrimeDeficitFluxState.contDiffOn.absolutelyContinuousOnInterval.fun_sub
    (absolutelyContinuousOnInterval_ccmPrimeDeficitIncoming a b)

/-- Almost-everywhere derivative of `ccmPrimeDeficitIncoming`:
`(d/dt) ccmPrimeDeficitIncoming t = −(1/2) ccmPrimeDeficitIncoming t − normalizedLogError t`. -/
theorem ae_hasDerivAt_ccmPrimeDeficitIncoming :
    ∀ᵐ t : ℝ ∂volume, HasDerivAt ccmPrimeDeficitIncoming
      (-(1 / 2) * ccmPrimeDeficitIncoming t - normalizedLogError t) t := by
  filter_upwards [ae_hasDerivAt_ccmLogChebyshevDeficitPrimitive] with t ht
  have he : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
    simpa using ((hasDerivAt_id t).neg.div_const 2).exp
  refine (he.mul ht).congr_deriv ?_
  unfold ccmPrimeDeficitIncoming normalizedLogError logError
  ring

/-- Almost-everywhere derivative of `ccmPrimeDeficitOutgoing`:
`(d/dt) ccmPrimeDeficitOutgoing t = (1/2) ccmPrimeDeficitOutgoing t + normalizedLogError t`. -/
theorem ae_hasDerivAt_ccmPrimeDeficitOutgoing :
    ∀ᵐ t : ℝ ∂volume, HasDerivAt ccmPrimeDeficitOutgoing
      (1 / 2 * ccmPrimeDeficitOutgoing t + normalizedLogError t) t := by
  filter_upwards [ae_hasDerivAt_ccmPrimeDeficitIncoming] with t ht
  refine ((hasDerivAt_ccmPrimeDeficitFluxState t).sub ht).congr_deriv ?_
  unfold ccmPrimeDeficitOutgoing
  ring

/-- **Integration by parts of the Chebyshev gauge convolution against `ccmPrimeDeficitIncoming`.**
For `f ∈ C²` vanishing outside `[−w, w]` (`w ≥ 0`) and any `τ ∈ ℝ`,
`∫_{τ−w}^{τ+w} Ẽ(t) (D_− f)(t − τ) dt = ∫_{τ−w}^{τ+w} ccmPrimeDeficitIncoming t * (D_−² f)(t − τ) dt`. -/
theorem integral_normalizedLogError_mul_gaugeDerivative_eq_incoming {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) (τ : ℝ) :
    (∫ t in Icc (τ - w) (τ + w), normalizedLogError t * gaugeDerivative f (t - τ)) =
      ∫ t in Icc (τ - w) (τ + w),
        ccmPrimeDeficitIncoming t * doubleGaugeDerivative f (t - τ) := by
  set a := τ - w
  set b := τ + w
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hG : ContDiff ℝ 1 (fun t => gaugeDerivative f (t - τ)) :=
    (contDiff_one_gaugeDerivative hf).comp (contDiff_id.sub contDiff_const)
  have hAC : AbsolutelyContinuousOnInterval
      (fun t => ccmPrimeDeficitIncoming t * gaugeDerivative f (t - τ)) a b :=
    (absolutelyContinuousOnInterval_ccmPrimeDeficitIncoming a b).fun_mul
      hG.contDiffOn.absolutelyContinuousOnInterval
  have hint := hAC.integral_deriv_eq_sub
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative (hf.of_le (by norm_num))
  have hgw : gaugeDerivative f w = 0 :=
    eq_zero_of_continuous_of_le_abs hgc (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_of_nonneg hw0])
  have hgnw : gaugeDerivative f (-w) = 0 :=
    eq_zero_of_continuous_of_le_abs hgc (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_neg, abs_of_nonneg hw0])
  have hbd : ccmPrimeDeficitIncoming b * gaugeDerivative f (b - τ) -
      ccmPrimeDeficitIncoming a * gaugeDerivative f (a - τ) = 0 := by
    simp [a, b, hgw, hgnw]
  rw [hbd] at hint
  have hae : (∫ t in a..b, deriv (fun s => ccmPrimeDeficitIncoming s * gaugeDerivative f (s - τ)) t) =
      ∫ t in a..b, (ccmPrimeDeficitIncoming t * doubleGaugeDerivative f (t - τ) -
        normalizedLogError t * gaugeDerivative f (t - τ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_hasDerivAt_ccmPrimeDeficitIncoming] with t ht _
    have hGt : HasDerivAt (fun s => gaugeDerivative f (s - τ))
        (deriv (gaugeDerivative f) (t - τ)) t := by
      simpa using ((contDiff_one_gaugeDerivative hf).differentiable one_ne_zero (t - τ)).hasDerivAt.comp
        t ((hasDerivAt_id t).sub_const τ)
    have hprod := (ht.mul hGt).deriv
    rw [hprod]
    unfold doubleGaugeDerivative gaugeDerivative
    ring
  have hI1 : IntervalIntegrable
      (fun t => ccmPrimeDeficitIncoming t * doubleGaugeDerivative f (t - τ)) volume a b :=
    (continuous_ccmPrimeDeficitIncoming.mul
      ((continuous_doubleGaugeDerivative hf).comp
        (continuous_id.sub continuous_const))).intervalIntegrable a b
  have hI2 : IntervalIntegrable
      (fun t => normalizedLogError t * gaugeDerivative f (t - τ)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hmax : IntegrableOn normalizedLogError (Icc a b) := by
      have h1 : IntegrableOn (fun t => Real.exp (-t / 2) * Chebyshev.psi (Real.exp t)) (Icc a b) :=
        ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).integrableOn_Icc).mul_continuousOn
          (by
            --Wait: `Chebyshev.psi` is monotone, not continuous!
            sorry)
    sorry
  sorry
