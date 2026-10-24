import GaloisForLFunctions.BiScaleUncertainty.SplineProbeFiniteShiftBounds
import GaloisForLFunctions.BiScaleUncertainty.TranslatedPairingEnvelopeLaw
import GaloisForLFunctions.BiScaleUncertainty.SimpleZeroPacketCriterion
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
  unfold doubleGaugeDerivative
  rw [gaugeDerivative, deriv_gaugeDerivative_eq hf u, gaugeDerivative]
  ring

/-- Exact decomposition `D_−² f = weilPoleOperator f − D_− f`. -/
theorem doubleGaugeDerivative_eq_weilPoleOperator_sub_gaugeDerivative {f : ℝ → ℝ} (u : ℝ) :
    doubleGaugeDerivative f u = weilPoleOperator f u - gaugeDerivative f u := by
  unfold doubleGaugeDerivative weilPoleOperator gaugeDerivative dualGaugeDerivative
  ring

/-! ## §2. Exact polar mode annihilation and constant-mode identity for `weilPoleOperator` -/

/-- `(d/dt)(g(t − τ)) = g'(t − τ)`. -/
theorem hasDerivAt_comp_sub_const {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (τ t : ℝ) :
    HasDerivAt (fun s => g (s - τ)) (deriv g (t - τ)) t := by
  simpa only [Function.comp_def, id_eq, one_smul] using
    ((hg.differentiable one_ne_zero) (t - τ)).hasDerivAt.scomp t
      ((hasDerivAt_id t).sub_const τ)

/-- `(d/dt)(e^{−t/2} g(t − τ)) = e^{−t/2} (D_− g)(t − τ)`. -/
theorem hasDerivAt_exp_neg_half_mul_sub {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (τ t : ℝ) :
    HasDerivAt (fun t => Real.exp (-t / 2) * g (t - τ))
      (Real.exp (-t / 2) * gaugeDerivative g (t - τ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
    simpa using ((hasDerivAt_id t).neg.div_const 2).exp
  have h2 := hasDerivAt_comp_sub_const hg τ t
  exact (h1.mul h2).congr_deriv (by unfold gaugeDerivative; ring)

/-- `(d/dt)(e^{t/2} g(t − τ)) = e^{t/2} (D_+ g)(t − τ)`. -/
theorem hasDerivAt_exp_half_mul_sub {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (τ t : ℝ) :
    HasDerivAt (fun t => Real.exp (t / 2) * g (t - τ))
      (Real.exp (t / 2) * dualGaugeDerivative g (t - τ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    simpa using ((hasDerivAt_id t).div_const 2).exp
  have h2 := hasDerivAt_comp_sub_const hg τ t
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
    dsimp only [id_eq]
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
For `f ∈ C²` vanishing outside `[−w, w]` (`w ≥ 0`) and any `τ ≥ w`,
`∫_{τ−w}^{τ+w} Ẽ(t) (D_− f)(t − τ) dt = ∫_{τ−w}^{τ+w} ccmPrimeDeficitIncoming t * (D_−² f)(t − τ) dt`. -/
theorem integral_normalizedLogError_mul_gaugeDerivative_eq_incoming {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w ≤ τ) :
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
    have hGt := hasDerivAt_comp_sub_const (contDiff_one_gaugeDerivative hf) τ t
    exact (ht.mul hGt).deriv.trans (by unfold doubleGaugeDerivative gaugeDerivative; ring)
  have hI1 : IntervalIntegrable
      (fun t => ccmPrimeDeficitIncoming t * doubleGaugeDerivative f (t - τ)) volume a b :=
    (continuous_ccmPrimeDeficitIncoming.mul
      ((continuous_doubleGaugeDerivative hf).comp
        (continuous_id.sub continuous_const))).intervalIntegrable a b
  have hI2 : IntervalIntegrable
      (fun t => normalizedLogError t * gaugeDerivative f (t - τ)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hnorm : IntegrableOn normalizedLogError (Icc a b) :=
      (integrableOn_normalizedLogError_Icc b).mono_set
        (Icc_subset_Icc (by simp only [a]; linarith) le_rfl)
    exact hnorm.mul_continuousOn
      ((hgc.comp (continuous_id.sub continuous_const)).continuousOn) isCompact_Icc
  rw [hae, intervalIntegral.integral_sub hI1 hI2, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc] at hint
  linarith

/-- **Integration by parts of the Chebyshev gauge convolution against `ccmPrimeDeficitOutgoing`.**
For `f ∈ C²` vanishing outside `[−w, w]` (`w ≥ 0`) and any `τ ≥ w`,
`∫_{τ−w}^{τ+w} Ẽ(t) (D_− f)(t − τ) dt = −∫_{τ−w}^{τ+w} ccmPrimeDeficitOutgoing t * (weilPoleOperator f)(t − τ) dt`. -/
theorem integral_normalizedLogError_mul_gaugeDerivative_eq_outgoing {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w ≤ τ) :
    (∫ t in Icc (τ - w) (τ + w), normalizedLogError t * gaugeDerivative f (t - τ)) =
      -∫ t in Icc (τ - w) (τ + w),
        ccmPrimeDeficitOutgoing t * weilPoleOperator f (t - τ) := by
  set a := τ - w
  set b := τ + w
  have hab : a ≤ b := by simp only [a, b]; linarith
  have hG : ContDiff ℝ 1 (fun t => gaugeDerivative f (t - τ)) :=
    (contDiff_one_gaugeDerivative hf).comp (contDiff_id.sub contDiff_const)
  have hAC : AbsolutelyContinuousOnInterval
      (fun t => ccmPrimeDeficitOutgoing t * gaugeDerivative f (t - τ)) a b :=
    (absolutelyContinuousOnInterval_ccmPrimeDeficitOutgoing a b).fun_mul
      hG.contDiffOn.absolutelyContinuousOnInterval
  have hint := hAC.integral_deriv_eq_sub
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative (hf.of_le (by norm_num))
  have hgw : gaugeDerivative f w = 0 :=
    eq_zero_of_continuous_of_le_abs hgc (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_of_nonneg hw0])
  have hgnw : gaugeDerivative f (-w) = 0 :=
    eq_zero_of_continuous_of_le_abs hgc (fun _ h => gaugeDerivative_eq_zero_of_lt_abs hw h)
      (by rw [abs_neg, abs_of_nonneg hw0])
  have hbd : ccmPrimeDeficitOutgoing b * gaugeDerivative f (b - τ) -
      ccmPrimeDeficitOutgoing a * gaugeDerivative f (a - τ) = 0 := by
    simp [a, b, hgw, hgnw]
  rw [hbd] at hint
  have hae : (∫ t in a..b, deriv (fun s => ccmPrimeDeficitOutgoing s * gaugeDerivative f (s - τ)) t) =
      ∫ t in a..b, (ccmPrimeDeficitOutgoing t * weilPoleOperator f (t - τ) +
        normalizedLogError t * gaugeDerivative f (t - τ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_hasDerivAt_ccmPrimeDeficitOutgoing] with t ht _
    have hGt := hasDerivAt_comp_sub_const (contDiff_one_gaugeDerivative hf) τ t
    exact (ht.mul hGt).deriv.trans (by unfold weilPoleOperator dualGaugeDerivative; ring)
  have hI1 : IntervalIntegrable
      (fun t => ccmPrimeDeficitOutgoing t * weilPoleOperator f (t - τ)) volume a b :=
    (continuous_ccmPrimeDeficitOutgoing.mul
      ((continuous_weilPoleOperator hf).comp
        (continuous_id.sub continuous_const))).intervalIntegrable a b
  have hI2 : IntervalIntegrable
      (fun t => normalizedLogError t * gaugeDerivative f (t - τ)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have hnorm : IntegrableOn normalizedLogError (Icc a b) :=
      (integrableOn_normalizedLogError_Icc b).mono_set
        (Icc_subset_Icc (by simp only [a]; linarith) le_rfl)
    exact hnorm.mul_continuousOn
      ((hgc.comp (continuous_id.sub continuous_const)).continuousOn) isCompact_Icc
  rw [hae, intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc] at hint
  linarith

/-! ## §4. Exact local packet and gauge-convolution identities via the Weil lag -/

/-- For `f` vanishing outside `[−w, w]` and `τ > w`, `stationaryGaugeConvolution f τ` equals the
local integral on `[τ − w, τ + w]`. -/
theorem stationaryGaugeConvolution_eq_local {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {τ : ℝ} (hτ : w < τ) :
    stationaryGaugeConvolution f τ =
      ∫ t in Icc (τ - w) (τ + w), normalizedLogError t * gaugeDerivative f (t - τ) := by
  unfold stationaryGaugeConvolution
  have hsub : Icc (τ - w) (τ + w) ⊆ Ioi (0 : ℝ) := fun t ht => by
    simp only [mem_Ioi]; linarith [ht.1]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsub fun t ht => ?_
  have ht2 := ht.2
  simp only [mem_Icc, not_and_or, not_le] at ht2
  have hw' : w < |t - τ| := by
    rcases ht2 with hlt | hgt
    · exact lt_abs.mpr (Or.inr (by linarith))
    · exact lt_abs.mpr (Or.inl (by linarith))
  rw [gaugeDerivative_eq_zero_of_lt_abs hw hw', mul_zero]

/-- **General local Chebyshev gauge formula for `stationaryPacket f τ`.** For `f ∈ C¹_c` vanishing
outside `[−w, w]` (`w ≥ 0`) and `τ > w`,
`P_f(τ) = −∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt − ∫_{τ−w}^{τ+w} Ẽ(t) (D_− f)(t − τ) dt`. -/
theorem stationaryPacket_eq_local_gauge {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w < τ) :
    stationaryPacket f τ =
      -(∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * f (t - τ)) -
        ∫ t in Icc (τ - w) (τ + w),
          normalizedLogError t * gaugeDerivative f (t - τ) := by
  let F : C_c(ℝ, ℝ) := ⟨⟨f, hf.continuous⟩, hfc⟩
  obtain ⟨N, hN1, -⟩ := exists_cutoff_between (a := τ + w) (by linarith)
  have hgauge : stationaryPacket f τ =
      forwardResidual f N (-τ) - chebyshevGaugeConvolution f N (-τ) :=
    stationaryPacket_eq_gauge F hf hw0 hw hN1
  rw [hgauge]
  have hsub : Icc (τ - w) (τ + w) ⊆ Icc 0 (cutoff N) :=
    Icc_subset_Icc (by linarith) hN1.le
  have hres : forwardResidual f N (-τ) =
      -∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * f (t - τ) := by
    unfold forwardResidual
    rw [hw (-τ) (lt_abs.mpr (Or.inr (by linarith))), zero_sub]
    congr 1
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub fun t ht => by
      have ht2 := ht.2
      simp only [mem_Icc, not_and_or, not_le] at ht2
      have hw' : w < |-τ + t| := by
        rcases ht2 with hlt | hgt
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl (by linarith))
      rw [hw _ hw', mul_zero]]
    exact setIntegral_congr_fun measurableSet_Icc fun t _ => by rw [show -τ + t = t - τ by ring]
  have hconv : chebyshevGaugeConvolution f N (-τ) =
      ∫ t in Icc (τ - w) (τ + w),
        normalizedLogError t * gaugeDerivative f (t - τ) := by
    unfold chebyshevGaugeConvolution
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub fun t ht => by
      have ht2 := ht.2
      simp only [mem_Icc, not_and_or, not_le] at ht2
      have hw' : w < |-τ + t| := by
        rcases ht2 with hlt | hgt
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl (by linarith))
      rw [gaugeDerivative_eq_zero_of_lt_abs hw hw', mul_zero]]
    exact setIntegral_congr_fun measurableSet_Icc fun t _ => by rw [show -τ + t = t - τ by ring]
  rw [hres, hconv]

/-- **Second-order incoming-deficit representation of `stationaryGaugeConvolution`.** For `f ∈ C²`
vanishing outside `[−w, w]` (`w ≥ 0`) and `τ > w`,
`stationaryGaugeConvolution f τ = ∫_{τ−w}^{τ+w} ccmPrimeDeficitIncoming t * (D_−² f)(t − τ) dt`. -/
theorem stationaryGaugeConvolution_eq_incoming_integral {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) {τ : ℝ} (hτ : w < τ) :
    stationaryGaugeConvolution f τ =
      ∫ t in Icc (τ - w) (τ + w),
        ccmPrimeDeficitIncoming t * doubleGaugeDerivative f (t - τ) := by
  rw [stationaryGaugeConvolution_eq_local hw hτ,
    integral_normalizedLogError_mul_gaugeDerivative_eq_incoming hf hw0 hw hτ.le]

/-- **Second-order outgoing-flux representation of `stationaryGaugeConvolution`.** For `f ∈ C²`
vanishing outside `[−w, w]` (`w ≥ 0`) and `τ > w`,
`stationaryGaugeConvolution f τ = −∫_{τ−w}^{τ+w} ccmPrimeDeficitOutgoing t * (weilPoleOperator f)(t − τ) dt`. -/
theorem stationaryGaugeConvolution_eq_outgoing_integral {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) {τ : ℝ} (hτ : w < τ) :
    stationaryGaugeConvolution f τ =
      -∫ t in Icc (τ - w) (τ + w),
        ccmPrimeDeficitOutgoing t * weilPoleOperator f (t - τ) := by
  rw [stationaryGaugeConvolution_eq_local hw hτ,
    integral_normalizedLogError_mul_gaugeDerivative_eq_outgoing hf hw0 hw hτ.le]

/-- **Incoming-deficit representation of `stationaryPacket f τ`.** For `f ∈ C²_c` vanishing outside
`[−w, w]` (`w ≥ 0`) and `τ > w`,
`P_f(τ) = −∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt − ∫_{τ−w}^{τ+w} ccmPrimeDeficitIncoming t * (D_−² f)(t − τ) dt`. -/
theorem stationaryPacket_eq_incoming_integral {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w < τ) :
    stationaryPacket f τ =
      -(∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * f (t - τ)) -
        ∫ t in Icc (τ - w) (τ + w),
          ccmPrimeDeficitIncoming t * doubleGaugeDerivative f (t - τ) := by
  rw [stationaryPacket_eq_local_gauge (hf.of_le (by norm_num)) hfc hw0 hw hτ,
    integral_normalizedLogError_mul_gaugeDerivative_eq_incoming hf hw0 hw hτ.le]

/-- **Outgoing-flux representation of `stationaryPacket f τ`.** For `f ∈ C²_c` vanishing outside
`[−w, w]` (`w ≥ 0`) and `τ > w`,
`P_f(τ) = −∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt + ∫_{τ−w}^{τ+w} ccmPrimeDeficitOutgoing t * (weilPoleOperator f)(t − τ) dt`. -/
theorem stationaryPacket_eq_outgoing_integral {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w < τ) :
    stationaryPacket f τ =
      -(∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * f (t - τ)) +
        ∫ t in Icc (τ - w) (τ + w),
          ccmPrimeDeficitOutgoing t * weilPoleOperator f (t - τ) := by
  rw [stationaryPacket_eq_local_gauge (hf.of_le (by norm_num)) hfc hw0 hw hτ,
    integral_normalizedLogError_mul_gaugeDerivative_eq_outgoing hf hw0 hw hτ.le, sub_neg_eq_add]

/-- On `[τ − w, τ + w]` with `τ > w`, `t ↦ e^{−t/2} trivialZeroSeriesReal(e^t)` is continuous,
since it equals `weilLagFunctionReal t + e^{−t/2} log(2π) − ccmPrimeDeficitOutgoing t` by
`ccmPrimeDeficitOutgoing_eq_weilLag`. -/
theorem continuousOn_exp_neg_half_mul_trivialZeroSeriesReal {w τ : ℝ} (hτ : w < τ) :
    ContinuousOn (fun t => Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t))
      (Icc (τ - w) (τ + w)) := by
  have hc : Continuous (fun t => weilLagFunctionReal t +
      Real.exp (-t / 2) * Real.log (2 * Real.pi) - ccmPrimeDeficitOutgoing t) :=
    (continuous_weilLagFunctionReal.add
      ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul continuous_const)).sub
      continuous_ccmPrimeDeficitOutgoing
  refine hc.continuousOn.congr fun t ht => ?_
  have ht0 : 0 < t := by linarith [ht.1]
  have h := ccmPrimeDeficitOutgoing_eq_weilLag ht0
  linarith

/-- **Exact `log(2π)` cancellation in the outgoing-flux integral.** Because `weilPoleOperator`
annihilates `e^{−t/2}` on `[τ − w, τ + w]`, the `e^{−t/2} log(2π)` term in
`ccmPrimeDeficitOutgoing_eq_weilLag` vanishes identically upon integration against
`weilPoleOperator f (· − τ)`: for every `τ > w`,
`∫_{τ−w}^{τ+w} ccmPrimeDeficitOutgoing t * (weilPoleOperator f)(t − τ) dt`
`= ∫_{τ−w}^{τ+w} weilLagFunctionReal t * (weilPoleOperator f)(t − τ) dt`
`  − ∫_{τ−w}^{τ+w} e^{−t/2} trivialZeroSeriesReal(e^t) * (weilPoleOperator f)(t − τ) dt`. -/
theorem integral_outgoing_mul_weilPoleOperator_eq_weilLag {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0) {τ : ℝ} (hτ : w < τ) :
    (∫ t in Icc (τ - w) (τ + w), ccmPrimeDeficitOutgoing t * weilPoleOperator f (t - τ)) =
      (∫ t in Icc (τ - w) (τ + w), weilLagFunctionReal t * weilPoleOperator f (t - τ)) -
        ∫ t in Icc (τ - w) (τ + w),
          Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) * weilPoleOperator f (t - τ) := by
  set s := Icc (τ - w) (τ + w)
  have hwc : Continuous (fun t => weilPoleOperator f (t - τ)) :=
    (continuous_weilPoleOperator hf).comp (continuous_id.sub continuous_const)
  have hI_lag : IntegrableOn (fun t => weilLagFunctionReal t * weilPoleOperator f (t - τ)) s :=
    (continuous_weilLagFunctionReal.mul hwc).integrableOn_Icc
  have hI_log : IntegrableOn
      (fun t => Real.log (2 * Real.pi) * (Real.exp (-t / 2) * weilPoleOperator f (t - τ))) s :=
    (continuous_const.mul ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      hwc)).integrableOn_Icc
  have hI_sum : IntegrableOn
      (fun t => weilLagFunctionReal t * weilPoleOperator f (t - τ) +
        Real.log (2 * Real.pi) * (Real.exp (-t / 2) * weilPoleOperator f (t - τ))) s :=
    hI_lag.add hI_log
  have hI_triv : IntegrableOn
      (fun t => Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) *
        weilPoleOperator f (t - τ)) s :=
    ((continuousOn_exp_neg_half_mul_trivialZeroSeriesReal hτ).mul
      hwc.continuousOn).integrableOn_compact isCompact_Icc
  have hcongr : (∫ t in s, ccmPrimeDeficitOutgoing t * weilPoleOperator f (t - τ)) =
      ∫ t in s, ((weilLagFunctionReal t * weilPoleOperator f (t - τ) +
        Real.log (2 * Real.pi) * (Real.exp (-t / 2) * weilPoleOperator f (t - τ))) -
        Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) * weilPoleOperator f (t - τ)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    rw [ccmPrimeDeficitOutgoing_eq_weilLag ht0]
    ring
  rw [hcongr, integral_sub hI_sum hI_triv, integral_add hI_lag hI_log,
    integral_const_mul, integral_exp_neg_half_mul_weilPoleOperator_eq_zero hf hw0 hw τ,
    mul_zero, add_zero]

/-- **Weil-lag representation of `stationaryPacket f τ` (`log(2π)`-free).** For `f ∈ C²_c`
vanishing outside `[−w, w]` (`w ≥ 0`) and `τ > w`,
`P_f(τ) = ∫_{τ−w}^{τ+w} weilLagFunctionReal t * (weilPoleOperator f)(t − τ) dt`
`  − ∫_{τ−w}^{τ+w} e^{−t/2} f(t − τ) dt`
`  − ∫_{τ−w}^{τ+w} e^{−t/2} trivialZeroSeriesReal(e^t) * (weilPoleOperator f)(t − τ) dt`. -/
theorem stationaryPacket_eq_weilLag_sub_trivialZero {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w < τ) :
    stationaryPacket f τ =
      (∫ t in Icc (τ - w) (τ + w), weilLagFunctionReal t * weilPoleOperator f (t - τ)) -
        (∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * f (t - τ)) -
        ∫ t in Icc (τ - w) (τ + w),
          Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) * weilPoleOperator f (t - τ) := by
  rw [stationaryPacket_eq_outgoing_integral hf hfc hw0 hw hτ,
    integral_outgoing_mul_weilPoleOperator_eq_weilLag hf hw0 hw hτ]
  ring

/-- **Unified `weilPoleOperator` representation of `stationaryPacket f τ`.** Absorbing the forward
exponential residual via `neg_integral_exp_neg_half_mul_eq_weilPoleOperator`, for `τ > w`:
`P_f(τ) = ∫_{τ−w}^{τ+w} weilLagFunctionReal t * (weilPoleOperator f)(t − τ) dt`
`  + ∫_{τ−w}^{τ+w} e^{−t/2} ((t − τ) − trivialZeroSeriesReal(e^t)) * (weilPoleOperator f)(t − τ) dt`. -/
theorem stationaryPacket_eq_weilLag_unified {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w < τ) :
    stationaryPacket f τ =
      (∫ t in Icc (τ - w) (τ + w), weilLagFunctionReal t * weilPoleOperator f (t - τ)) +
        ((∫ t in Icc (τ - w) (τ + w),
            (t - τ) * Real.exp (-t / 2) * weilPoleOperator f (t - τ)) -
          ∫ t in Icc (τ - w) (τ + w),
            Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) *
              weilPoleOperator f (t - τ)) := by
  have h1 := stationaryPacket_eq_weilLag_sub_trivialZero hf hfc hw0 hw hτ
  have h2 := neg_integral_exp_neg_half_mul_eq_weilPoleOperator hf hw0 hw τ
  linarith

/-- **Central Weil-lag value plus local oscillation decomposition.** Subtracting any reference
value `c` (in particular `c = weilLagFunctionReal τ`) separates `−(c/4) ∫_{−w}^w f` from the local
oscillation of `weilLagFunctionReal`:
`∫_{τ−w}^{τ+w} Φ(t) (weilPoleOperator f)(t − τ) dt = −(c/4) ∫_{−w}^w f(u) du + ∫_{τ−w}^{τ+w} (Φ(t) − c) (weilPoleOperator f)(t − τ) dt`. -/
theorem integral_weilLag_mul_weilPoleOperator_eq_central_add_oscillation {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    (c τ : ℝ) :
    (∫ t in Icc (τ - w) (τ + w), weilLagFunctionReal t * weilPoleOperator f (t - τ)) =
      -(c / 4) * (∫ u in Icc (-w) w, f u) +
        ∫ t in Icc (τ - w) (τ + w),
          (weilLagFunctionReal t - c) * weilPoleOperator f (t - τ) := by
  set s := Icc (τ - w) (τ + w)
  have hwc : Continuous (fun t => weilPoleOperator f (t - τ)) :=
    (continuous_weilPoleOperator hf).comp (continuous_id.sub continuous_const)
  have h1 : IntegrableOn (fun t => (weilLagFunctionReal t - c) * weilPoleOperator f (t - τ)) s :=
    ((continuous_weilLagFunctionReal.sub continuous_const).mul hwc).integrableOn_Icc
  have h2 : IntegrableOn (fun t => c * weilPoleOperator f (t - τ)) s :=
    (continuous_const.mul hwc).integrableOn_Icc
  have hsplit : (∫ t in s, weilLagFunctionReal t * weilPoleOperator f (t - τ)) =
      ∫ t in s, ((weilLagFunctionReal t - c) * weilPoleOperator f (t - τ) +
        c * weilPoleOperator f (t - τ)) :=
    setIntegral_congr_fun measurableSet_Icc fun t _ => by ring
  rw [hsplit, integral_add h1 h2, integral_const_mul,
    integral_weilPoleOperator_eq hf hw0 hw τ]
  ring

/-! ## §5. Pointwise finite-shift bounds for general `C²_c` sources and `splineProbe` -/

/-- The pure Weil-lag pole convolution `∫_{τ−w}^{τ+w} Φ(t) (weilPoleOperator f)(t − τ) dt`. -/
def weilLagPoleConvolution (f : ℝ → ℝ) (w τ : ℝ) : ℝ :=
  ∫ t in Icc (τ - w) (τ + w), weilLagFunctionReal t * weilPoleOperator f (t - τ)

private theorem abs_setIntegral_le_setIntegral_abs (g : ℝ → ℝ) (s : Set ℝ) :
    |∫ t in s, g t| ≤ ∫ t in s, |g t| := by
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm g

/-- Pointwise bound on `|stationaryPacket f τ - weilLagPoleConvolution f w τ|` for `τ > w`:
the difference between the full packet and the pure Weil-lag pole convolution decays as
`O(e^{−(τ−w)/2})`, bounded explicitly by the `L¹` norms of `f` and `weilPoleOperator f`. -/
theorem abs_stationaryPacket_sub_weilLagPoleConvolution_le {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w) (hw : ∀ v : ℝ, w < |v| → f v = 0)
    {τ : ℝ} (hτ : w < τ) :
    |stationaryPacket f τ - weilLagPoleConvolution f w τ| ≤
      Real.exp (-(τ - w) / 2) *
        ((∫ u in Icc (-w) w, |f u|) +
          ∫ u in Icc (-w) w, |weilPoleOperator f u|) := by
  rw [stationaryPacket_eq_weilLag_sub_trivialZero hf hfc hw0 hw hτ, weilLagPoleConvolution]
  set I₁ := ∫ t in Icc (τ - w) (τ + w), Real.exp (-t / 2) * f (t - τ)
  set I₂ := ∫ t in Icc (τ - w) (τ + w),
    Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) * weilPoleOperator f (t - τ)
  have hab : τ - w ≤ τ + w := by linarith
  have hw0' : -w ≤ w := by linarith
  have hI₁ : |I₁| ≤ Real.exp (-(τ - w) / 2) * ∫ u in Icc (-w) w, |f u| := by
    have hsh : (∫ t in Icc (τ - w) (τ + w), |f (t - τ)|) = ∫ u in Icc (-w) w, |f u| := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hw0',
        intervalIntegral.integral_comp_sub_right (fun u => |f u|) τ]
      simp only [sub_sub_cancel_left, add_sub_cancel_left]
    calc |I₁| ≤ ∫ t in Icc (τ - w) (τ + w), |Real.exp (-t / 2) * f (t - τ)| :=
          abs_setIntegral_le_setIntegral_abs _ _
      _ ≤ ∫ t in Icc (τ - w) (τ + w), Real.exp (-(τ - w) / 2) * |f (t - τ)| := by
          refine setIntegral_mono_on
            (((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
              (hf.continuous.comp (continuous_id.sub continuous_const))).abs.integrableOn_Icc)
            ((continuous_const.mul
              ((hf.continuous.comp (continuous_id.sub continuous_const)).abs)).integrableOn_Icc)
            measurableSet_Icc fun t ht => ?_
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (by linarith [ht.1])) (abs_nonneg _)
      _ = Real.exp (-(τ - w) / 2) * ∫ u in Icc (-w) w, |f u| := by
          rw [integral_const_mul, hsh]
  have hI₂ : |I₂| ≤ Real.exp (-(τ - w) / 2) * ∫ u in Icc (-w) w, |weilPoleOperator f u| := by
    have hwc : Continuous (weilPoleOperator f) := continuous_weilPoleOperator hf
    have hsh : (∫ t in Icc (τ - w) (τ + w), |weilPoleOperator f (t - τ)|) =
        ∫ u in Icc (-w) w, |weilPoleOperator f u| := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hw0',
        intervalIntegral.integral_comp_sub_right (fun u => |weilPoleOperator f u|) τ]
      simp only [sub_sub_cancel_left, add_sub_cancel_left]
    have hint_lhs : IntegrableOn
        (fun t => |Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) *
          weilPoleOperator f (t - τ)|) (Icc (τ - w) (τ + w)) :=
      (((continuousOn_exp_neg_half_mul_trivialZeroSeriesReal hτ).mul
        (hwc.comp (continuous_id.sub continuous_const)).continuousOn).abs
          ).integrableOn_compact isCompact_Icc
    calc |I₂| ≤ ∫ t in Icc (τ - w) (τ + w),
          |Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) *
            weilPoleOperator f (t - τ)| :=
          abs_setIntegral_le_setIntegral_abs _ _
      _ ≤ ∫ t in Icc (τ - w) (τ + w),
          Real.exp (-(τ - w) / 2) * |weilPoleOperator f (t - τ)| := by
          refine setIntegral_mono_on hint_lhs
            ((continuous_const.mul
              ((hwc.comp (continuous_id.sub continuous_const)).abs)).integrableOn_Icc)
            measurableSet_Icc fun t ht => ?_
          have ht0 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr (by linarith [ht.1])
          have hz0 := trivialZeroSeriesReal_nonneg ht0
          have hz1 := trivialZeroSeriesReal_le_one ht0
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hz0]
          have hprod : Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t) ≤
              Real.exp (-(τ - w) / 2) :=
            calc Real.exp (-t / 2) * trivialZeroSeriesReal (Real.exp t)
                ≤ Real.exp (-t / 2) * 1 := mul_le_mul_of_nonneg_left hz1 (Real.exp_pos _).le
              _ = Real.exp (-t / 2) := mul_one _
              _ ≤ Real.exp (-(τ - w) / 2) := Real.exp_le_exp.mpr (by linarith [ht.1])
          exact mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
      _ = Real.exp (-(τ - w) / 2) * ∫ u in Icc (-w) w, |weilPoleOperator f u| := by
          rw [integral_const_mul, hsh]
  calc |weilLagPoleConvolution f w τ - I₁ - I₂ - weilLagPoleConvolution f w τ|
      = |-I₁ - I₂| := by ring_nf
    _ ≤ |-I₁| + |I₂| := abs_sub _ _
    _ = |I₁| + |I₂| := by rw [abs_neg]
    _ ≤ Real.exp (-(τ - w) / 2) * (∫ u in Icc (-w) w, |f u|) +
        Real.exp (-(τ - w) / 2) * ∫ u in Icc (-w) w, |weilPoleOperator f u| :=
        add_le_add hI₁ hI₂
    _ = _ := by ring

/-- Second derivative of `cubicSpline`:
`B''(x) = (1/4) (upow 1 1 (x + 2) − 2 upow 1 1 x + upow 1 1 (x − 2))`. -/
theorem hasDerivAt_upow_one_two (x : ℝ) :
    HasDerivAt (upow 1 2) (1 / 2 * (upow 1 1 (x + 1) - upow 1 1 (x - 1))) x := by
  have hconv : upow 1 2 = fun y : ℝ =>
      1 / 2 * ((∫ t in (0 : ℝ)..y + 1, upow 1 1 t) -
        ∫ t in (0 : ℝ)..y - 1, upow 1 1 t) := by
    ext y
    have h : upow 1 2 y =
        1 / (2 * 1) * ((∫ t in (0 : ℝ)..y + 1, upow 1 1 t) -
          ∫ t in (0 : ℝ)..y - 1, upow 1 1 t) :=
      unif_convolution_eq one_pos (integrable_upow 1 1) y
    rw [h]; ring
  have hc : Continuous (upow 1 1) := (contDiff_upow one_pos 0).continuous
  have hprim : ∀ u : ℝ, HasDerivAt (fun z : ℝ => ∫ t in (0 : ℝ)..z, upow 1 1 t) (upow 1 1 u) u :=
    fun u => (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hd1 : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y + 1, upow 1 1 t) (upow 1 1 (x + 1)) x := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hprim (x + 1)).scomp x ((hasDerivAt_id x).add_const 1)
  have hd2 : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y - 1, upow 1 1 t) (upow 1 1 (x - 1)) x := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hprim (x - 1)).scomp x ((hasDerivAt_id x).sub_const 1)
  rw [hconv]
  exact (hd1.sub hd2).const_mul (1 / 2 : ℝ)

theorem abs_deriv_deriv_cubicSpline_le_quarter (x : ℝ) :
    |deriv (deriv cubicSpline) x| ≤ 1 / 4 := by
  have hd : HasDerivAt (deriv cubicSpline)
      (1 / 2 * (1 / 2 * (upow 1 1 (x + 1 + 1) - upow 1 1 (x + 1 - 1)) -
        1 / 2 * (upow 1 1 (x - 1 + 1) - upow 1 1 (x - 1 - 1)))) x := by
    rw [funext deriv_cubicSpline_eq]
    have h1 : HasDerivAt (fun y => upow 1 2 (y + 1))
        (1 / 2 * (upow 1 1 (x + 1 + 1) - upow 1 1 (x + 1 - 1))) x := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hasDerivAt_upow_one_two (x + 1)).scomp x ((hasDerivAt_id x).add_const 1)
    have h2 : HasDerivAt (fun y => upow 1 2 (y - 1))
        (1 / 2 * (upow 1 1 (x - 1 + 1) - upow 1 1 (x - 1 - 1))) x := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hasDerivAt_upow_one_two (x - 1)).scomp x ((hasDerivAt_id x).sub_const 1)
    exact (h1.sub h2).const_mul (1 / 2)
  rw [hd.deriv]
  have h1 := upow_nonneg one_pos 1 (x + 1 + 1)
  have h2 := upow_one_le_half 1 (x + 1 + 1)
  have h3 := upow_nonneg one_pos 1 (x + 1 - 1)
  have h4 := upow_one_le_half 1 (x + 1 - 1)
  have h5 := upow_nonneg one_pos 1 (x - 1 + 1)
  have h6 := upow_one_le_half 1 (x - 1 + 1)
  have h7 := upow_nonneg one_pos 1 (x - 1 - 1)
  have h8 := upow_one_le_half 1 (x - 1 - 1)
  have heq : x + 1 - 1 = x - 1 + 1 := by ring
  rw [heq] at h3 h4 ⊢
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Explicit formula for `weilPoleOperator splineProbe`:
`weilPoleOperator splineProbe x = eˣ (B''(x) + 2 B'(x) + (3/4) B(x))`. -/
theorem weilPoleOperator_splineProbe_eq (x : ℝ) :
    weilPoleOperator splineProbe x =
      Real.exp x * (deriv (deriv cubicSpline) x + 2 * deriv cubicSpline x +
        3 / 4 * cubicSpline x) := by
  unfold weilPoleOperator dualGaugeDerivative
  have hd : HasDerivAt (gaugeDerivative splineProbe)
      (Real.exp x * (deriv cubicSpline x + 1 / 2 * cubicSpline x) +
        Real.exp x * (deriv (deriv cubicSpline) x + 1 / 2 * deriv cubicSpline x)) x := by
    rw [funext gaugeDerivative_splineProbe_eq]
    have hB1 : DifferentiableAt ℝ cubicSpline x := (hasDerivAt_cubicSpline x).differentiableAt
    have hB2 : DifferentiableAt ℝ (deriv cubicSpline) x :=
      (contDiff_one_deriv contDiff_cubicSpline).differentiable one_ne_zero x
    exact (Real.hasDerivAt_exp x).mul (hB2.hasDerivAt.add (hB1.hasDerivAt.const_mul (1 / 2)))
  rw [hd.deriv, gaugeDerivative_splineProbe_eq x]
  ring

/-- Pointwise bound `|weilPoleOperator splineProbe x| ≤ (9/8) e⁴`. -/
theorem abs_weilPoleOperator_splineProbe_le (x : ℝ) :
    |weilPoleOperator splineProbe x| ≤ 9 / 8 * Real.exp 4 := by
  by_cases hx : 4 < |x|
  · rw [weilPoleOperator_eq_zero_of_lt_abs (fun _ h => splineProbe_eq_zero h) hx, abs_zero]
    positivity
  · push Not at hx
    rw [weilPoleOperator_splineProbe_eq, abs_mul, abs_of_pos (Real.exp_pos x)]
    have hexp : Real.exp x ≤ Real.exp 4 := Real.exp_le_exp.mpr ((le_abs_self x).trans hx)
    have hdd := abs_deriv_deriv_cubicSpline_le_quarter x
    have hd := abs_deriv_cubicSpline_le_quarter x
    have hc0 := cubicSpline_nonneg x
    have hc1 := cubicSpline_le_half x
    have hsum : |deriv (deriv cubicSpline) x + 2 * deriv cubicSpline x +
        3 / 4 * cubicSpline x| ≤ 9 / 8 := by
      rw [abs_le] at hdd hd ⊢
      constructor <;> linarith
    nlinarith [Real.exp_pos x,
      abs_nonneg (deriv (deriv cubicSpline) x + 2 * deriv cubicSpline x + 3 / 4 * cubicSpline x)]

/-- Pointwise bound `|doubleGaugeDerivative splineProbe x| ≤ (13/8) e⁴`. -/
theorem abs_doubleGaugeDerivative_splineProbe_le (x : ℝ) :
    |doubleGaugeDerivative splineProbe x| ≤ 13 / 8 * Real.exp 4 := by
  rw [doubleGaugeDerivative_eq_weilPoleOperator_sub_gaugeDerivative]
  have h1 := abs_weilPoleOperator_splineProbe_le x
  have h2 := abs_gaugeDerivative_splineProbe_le x
  have h3 := abs_sub (weilPoleOperator splineProbe x) (gaugeDerivative splineProbe x)
  linarith

/-- `L¹` norm bound `∫ |weilPoleOperator splineProbe| ≤ 9 e⁴`. -/
theorem integral_abs_weilPoleOperator_splineProbe_le :
    (∫ u : ℝ, |weilPoleOperator splineProbe u|) ≤ 9 * Real.exp 4 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-4 : ℝ) 4) fun u hu => by
    simp only [mem_Icc, not_and_or, not_le] at hu
    have h4 : 4 < |u| := by
      rcases hu with hlt | hgt
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl hgt)
    rw [weilPoleOperator_eq_zero_of_lt_abs (fun _ h => splineProbe_eq_zero h) h4, abs_zero]]
  have hle : (∫ u in Icc (-4 : ℝ) 4, |weilPoleOperator splineProbe u|) ≤
      ∫ _u in Icc (-4 : ℝ) 4, (9 / 8 * Real.exp 4 : ℝ) := by
    refine setIntegral_mono_on
      ((continuous_weilPoleOperator contDiff_splineProbe).abs.integrableOn_Icc)
      (integrableOn_const (by norm_num)) measurableSet_Icc fun u _ =>
        abs_weilPoleOperator_splineProbe_le u
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul] at hle
  linarith

/-- `L¹` norm bound `∫ |doubleGaugeDerivative splineProbe| ≤ 13 e⁴`. -/
theorem integral_abs_doubleGaugeDerivative_splineProbe_le :
    (∫ u : ℝ, |doubleGaugeDerivative splineProbe u|) ≤ 13 * Real.exp 4 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-4 : ℝ) 4) fun u hu => by
    simp only [mem_Icc, not_and_or, not_le] at hu
    have h4 : 4 < |u| := by
      rcases hu with hlt | hgt
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl hgt)
    rw [doubleGaugeDerivative_eq_zero_of_lt_abs (fun _ h => splineProbe_eq_zero h) h4, abs_zero]]
  have hle : (∫ u in Icc (-4 : ℝ) 4, |doubleGaugeDerivative splineProbe u|) ≤
      ∫ _u in Icc (-4 : ℝ) 4, (13 / 8 * Real.exp 4 : ℝ) := by
    refine setIntegral_mono_on
      ((continuous_doubleGaugeDerivative contDiff_splineProbe).abs.integrableOn_Icc)
      (integrableOn_const (by norm_num)) measurableSet_Icc fun u _ =>
        abs_doubleGaugeDerivative_splineProbe_le u
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul] at hle
  linarith

/-- **Finite-shift bound for `stationaryPacket splineProbe τ` via `ccmPrimeDeficitIncoming`.**
For every `τ > 4`,
`|stationaryPacket splineProbe τ| ≤ 4 e^{2 − τ/2} + (13/8) e⁴ ∫_{τ−4}^{τ+4} |ccmPrimeDeficitIncoming t| dt`. -/
theorem abs_stationaryPacket_splineProbe_le_local_incoming {τ : ℝ} (hτ : 4 < τ) :
    |stationaryPacket splineProbe τ| ≤
      4 * Real.exp (2 - τ / 2) +
        13 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitIncoming t| := by
  rw [stationaryPacket_eq_incoming_integral contDiff_splineProbe hasCompactSupport_splineProbe
    (by norm_num : (0 : ℝ) ≤ 4) (fun _ hv => splineProbe_eq_zero hv) hτ]
  set I₁ := ∫ t in Icc (τ - 4) (τ + 4), Real.exp (-t / 2) * splineProbe (t - τ)
  set I₂ := ∫ t in Icc (τ - 4) (τ + 4),
    ccmPrimeDeficitIncoming t * doubleGaugeDerivative splineProbe (t - τ)
  have hI₁0 : 0 ≤ I₁ := setIntegral_nonneg measurableSet_Icc fun t _ =>
    mul_nonneg (Real.exp_pos _).le (splineProbe_nonneg _)
  have hI₁_le : I₁ ≤ 4 * Real.exp (2 - τ / 2) := by
    have hle : I₁ ≤ ∫ _t in Icc (τ - 4) (τ + 4), (1 / 2 * Real.exp (2 - τ / 2) : ℝ) := by
      refine setIntegral_mono_on
        (((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
          (contDiff_splineProbe.continuous.comp (continuous_id.sub continuous_const))).integrableOn_Icc)
        (integrableOn_const (by norm_num)) measurableSet_Icc fun t ht => ?_
      unfold splineProbe tiltedSource
      rw [one_mul, ← mul_assoc, ← Real.exp_add]
      have hexp : Real.exp (-t / 2 + (t - τ)) ≤ Real.exp (2 - τ / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.2])
      have hsp := cubicSpline_le_half (t - τ)
      nlinarith [Real.exp_pos (-t / 2 + (t - τ)), cubicSpline_nonneg (t - τ)]
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hle
    linarith
  have hI₂_le : |I₂| ≤
      13 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitIncoming t| := by
    calc |I₂| ≤ ∫ t in Icc (τ - 4) (τ + 4),
          |ccmPrimeDeficitIncoming t * doubleGaugeDerivative splineProbe (t - τ)| :=
          abs_setIntegral_le_setIntegral_abs _ _
      _ ≤ ∫ t in Icc (τ - 4) (τ + 4),
          13 / 8 * Real.exp 4 * |ccmPrimeDeficitIncoming t| := by
          refine setIntegral_mono_on
            ((continuous_ccmPrimeDeficitIncoming.mul
              ((continuous_doubleGaugeDerivative contDiff_splineProbe).comp
                (continuous_id.sub continuous_const))).abs.integrableOn_Icc)
            ((continuous_const.mul
              continuous_ccmPrimeDeficitIncoming.abs).integrableOn_Icc)
            measurableSet_Icc fun t _ => ?_
          rw [abs_mul, mul_comm (13 / 8 * Real.exp 4)]
          exact mul_le_mul_of_nonneg_left (abs_doubleGaugeDerivative_splineProbe_le _)
            (abs_nonneg _)
      _ = 13 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitIncoming t| :=
          integral_const_mul _ _
  calc |-I₁ - I₂| ≤ |-I₁| + |I₂| := abs_sub _ _
    _ = I₁ + |I₂| := by rw [abs_neg, abs_of_nonneg hI₁0]
    _ ≤ 4 * Real.exp (2 - τ / 2) +
        13 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitIncoming t| :=
      add_le_add hI₁_le hI₂_le

/-- **Finite-shift bound for `stationaryPacket splineProbe τ` via `ccmPrimeDeficitOutgoing`.**
For every `τ > 4`,
`|stationaryPacket splineProbe τ| ≤ 4 e^{2 − τ/2} + (9/8) e⁴ ∫_{τ−4}^{τ+4} |ccmPrimeDeficitOutgoing t| dt`. -/
theorem abs_stationaryPacket_splineProbe_le_local_outgoing {τ : ℝ} (hτ : 4 < τ) :
    |stationaryPacket splineProbe τ| ≤
      4 * Real.exp (2 - τ / 2) +
        9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitOutgoing t| := by
  rw [stationaryPacket_eq_outgoing_integral contDiff_splineProbe hasCompactSupport_splineProbe
    (by norm_num : (0 : ℝ) ≤ 4) (fun _ hv => splineProbe_eq_zero hv) hτ]
  set I₁ := ∫ t in Icc (τ - 4) (τ + 4), Real.exp (-t / 2) * splineProbe (t - τ)
  set I₂ := ∫ t in Icc (τ - 4) (τ + 4),
    ccmPrimeDeficitOutgoing t * weilPoleOperator splineProbe (t - τ)
  have hI₁0 : 0 ≤ I₁ := setIntegral_nonneg measurableSet_Icc fun t _ =>
    mul_nonneg (Real.exp_pos _).le (splineProbe_nonneg _)
  have hI₁_le : I₁ ≤ 4 * Real.exp (2 - τ / 2) := by
    have hle : I₁ ≤ ∫ _t in Icc (τ - 4) (τ + 4), (1 / 2 * Real.exp (2 - τ / 2) : ℝ) := by
      refine setIntegral_mono_on
        (((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
          (contDiff_splineProbe.continuous.comp (continuous_id.sub continuous_const))).integrableOn_Icc)
        (integrableOn_const (by norm_num)) measurableSet_Icc fun t ht => ?_
      unfold splineProbe tiltedSource
      rw [one_mul, ← mul_assoc, ← Real.exp_add]
      have hexp : Real.exp (-t / 2 + (t - τ)) ≤ Real.exp (2 - τ / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.2])
      have hsp := cubicSpline_le_half (t - τ)
      nlinarith [Real.exp_pos (-t / 2 + (t - τ)), cubicSpline_nonneg (t - τ)]
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hle
    linarith
  have hI₂_le : |I₂| ≤
      9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitOutgoing t| := by
    calc |I₂| ≤ ∫ t in Icc (τ - 4) (τ + 4),
          |ccmPrimeDeficitOutgoing t * weilPoleOperator splineProbe (t - τ)| :=
          abs_setIntegral_le_setIntegral_abs _ _
      _ ≤ ∫ t in Icc (τ - 4) (τ + 4),
          9 / 8 * Real.exp 4 * |ccmPrimeDeficitOutgoing t| := by
          refine setIntegral_mono_on
            ((continuous_ccmPrimeDeficitOutgoing.mul
              ((continuous_weilPoleOperator contDiff_splineProbe).comp
                (continuous_id.sub continuous_const))).abs.integrableOn_Icc)
            ((continuous_const.mul
              continuous_ccmPrimeDeficitOutgoing.abs).integrableOn_Icc)
            measurableSet_Icc fun t _ => ?_
          rw [abs_mul, mul_comm (9 / 8 * Real.exp 4)]
          exact mul_le_mul_of_nonneg_left (abs_weilPoleOperator_splineProbe_le _)
            (abs_nonneg _)
      _ = 9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitOutgoing t| :=
          integral_const_mul _ _
  calc |-I₁ + I₂| ≤ |-I₁| + |I₂| := abs_add_le _ _
    _ = I₁ + |I₂| := by rw [abs_neg, abs_of_nonneg hI₁0]
    _ ≤ 4 * Real.exp (2 - τ / 2) +
        9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitOutgoing t| :=
      add_le_add hI₁_le hI₂_le

/-- **Finite-shift bound for `stationaryPacket splineProbe τ` via `weilLagFunctionReal`.**
For every `τ > 4`,
`|stationaryPacket splineProbe τ| ≤ 13 e^{6 − τ/2} + (9/8) e⁴ ∫_{τ−4}^{τ+4} |weilLagFunctionReal t| dt`. -/
theorem abs_stationaryPacket_splineProbe_le_local_weilLag {τ : ℝ} (hτ : 4 < τ) :
    |stationaryPacket splineProbe τ| ≤
      13 * Real.exp (6 - τ / 2) +
        9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |weilLagFunctionReal t| := by
  have hdiff := abs_stationaryPacket_sub_weilLagPoleConvolution_le contDiff_splineProbe
    hasCompactSupport_splineProbe (by norm_num : (0 : ℝ) ≤ 4) (fun _ hv => splineProbe_eq_zero hv) hτ
  have hU_int : (∫ u in Icc (-4 : ℝ) 4, |splineProbe u|) ≤ 4 * Real.exp 4 := by
    have hle : (∫ u in Icc (-4 : ℝ) 4, |splineProbe u|) ≤
        ∫ _u in Icc (-4 : ℝ) 4, (1 / 2 * Real.exp 4 : ℝ) := by
      refine setIntegral_mono_on
        (contDiff_splineProbe.continuous.abs.integrableOn_Icc)
        (integrableOn_const (by norm_num)) measurableSet_Icc fun u _ => ?_
      rw [abs_of_nonneg (splineProbe_nonneg u)]
      exact splineProbe_le u
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul] at hle
    linarith
  have hW_int : (∫ u in Icc (-4 : ℝ) 4, |weilPoleOperator splineProbe u|) ≤ 9 * Real.exp 4 := by
    refine (setIntegral_le_integral
      ((continuous_weilPoleOperator contDiff_splineProbe).abs.integrable_of_hasCompactSupport
        ((hasCompactSupport_weilPoleOperator hasCompactSupport_splineProbe).comp_left abs_zero))
      (Eventually.of_forall fun _ => abs_nonneg _)).trans
      integral_abs_weilPoleOperator_splineProbe_le
  have hexp : Real.exp (-(τ - 4) / 2) * (4 * Real.exp 4 + 9 * Real.exp 4) =
      13 * Real.exp (6 - τ / 2) := by
    rw [show 4 * Real.exp 4 + 9 * Real.exp 4 = 13 * Real.exp 4 by ring,
      mul_left_comm, ← Real.exp_add]
    congr 2; ring
  have hdiff' : |stationaryPacket splineProbe τ - weilLagPoleConvolution splineProbe 4 τ| ≤
      13 * Real.exp (6 - τ / 2) := by
    calc |stationaryPacket splineProbe τ - weilLagPoleConvolution splineProbe 4 τ|
        ≤ Real.exp (-(τ - 4) / 2) *
            ((∫ u in Icc (-4 : ℝ) 4, |splineProbe u|) +
              ∫ u in Icc (-4 : ℝ) 4, |weilPoleOperator splineProbe u|) := hdiff
      _ ≤ Real.exp (-(τ - 4) / 2) * (4 * Real.exp 4 + 9 * Real.exp 4) :=
          mul_le_mul_of_nonneg_left (add_le_add hU_int hW_int) (Real.exp_pos _).le
      _ = 13 * Real.exp (6 - τ / 2) := hexp
  have hconv : |weilLagPoleConvolution splineProbe 4 τ| ≤
      9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |weilLagFunctionReal t| := by
    unfold weilLagPoleConvolution
    calc |∫ t in Icc (τ - 4) (τ + 4),
            weilLagFunctionReal t * weilPoleOperator splineProbe (t - τ)|
        ≤ ∫ t in Icc (τ - 4) (τ + 4),
            |weilLagFunctionReal t * weilPoleOperator splineProbe (t - τ)| :=
          abs_setIntegral_le_setIntegral_abs _ _
      _ ≤ ∫ t in Icc (τ - 4) (τ + 4),
            9 / 8 * Real.exp 4 * |weilLagFunctionReal t| := by
          refine setIntegral_mono_on
            ((continuous_weilLagFunctionReal.mul
              ((continuous_weilPoleOperator contDiff_splineProbe).comp
                (continuous_id.sub continuous_const))).abs.integrableOn_Icc)
            ((continuous_const.mul
              continuous_weilLagFunctionReal.abs).integrableOn_Icc)
            measurableSet_Icc fun t _ => ?_
          rw [abs_mul, mul_comm (9 / 8 * Real.exp 4)]
          exact mul_le_mul_of_nonneg_left (abs_weilPoleOperator_splineProbe_le _)
            (abs_nonneg _)
      _ = 9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |weilLagFunctionReal t| :=
          integral_const_mul _ _
  calc |stationaryPacket splineProbe τ|
      = |(stationaryPacket splineProbe τ - weilLagPoleConvolution splineProbe 4 τ) +
          weilLagPoleConvolution splineProbe 4 τ| := by ring_nf
    _ ≤ |stationaryPacket splineProbe τ - weilLagPoleConvolution splineProbe 4 τ| +
        |weilLagPoleConvolution splineProbe 4 τ| := abs_add_le _ _
    _ ≤ 13 * Real.exp (6 - τ / 2) +
        9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |weilLagFunctionReal t| :=
      add_le_add hdiff' hconv

/-! ## §6. Universal autocorrelation probes and single-probe Weil positivity -/

/-- If `f` vanishes outside `[−w, w]`, then its autocorrelation `autocorr f` vanishes outside
`[−2w, 2w]`. -/
theorem autocorr_eq_zero_of_two_mul_lt_abs {f : ℝ → ℝ} {w : ℝ}
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {v : ℝ} (hv : 2 * w < |v|) :
    autocorr f v = 0 := by
  unfold autocorr
  have hzero : (fun u : ℝ => f u * f (u + v)) = fun _ => 0 := by
    funext u
    by_cases hu : w < |u|
    · rw [hw u hu, zero_mul]
    · push Not at hu
      have htri : |v| ≤ |u + v| + |u| := by
        calc |v| = |(u + v) - u| := by ring_nf
          _ ≤ |u + v| + |u| := abs_sub (u + v) u
      have huv : w < |u + v| := by linarith
      rw [hw (u + v) huv, mul_zero]
  rw [hzero, integral_zero]

/-- **Universal probes are closed under autocorrelation.** Because `𝒵` is invariant under
reflection `ρ ↦ 1 − ρ̄` (`Zeta23.zetaZeroConfig.reflect_mem`) and
`ĥ_U(γ_ρ) = Û(γ_ρ) conj Û(γ_{1−ρ̄})`, any universal probe `U` (`SeesAllZeros U`) has a universal
autocorrelation `SeesAllZeros (autocorr U)`. -/
theorem seesAllZeros_autocorr {U : ℝ → ℝ} (hU : Continuous U) (hUc : HasCompactSupport U)
    (hsees : SeesAllZeros U) : SeesAllZeros (autocorr U) := by
  intro ρ
  rw [paperFT_autocorr hU hUc, conj_gammaOf]
  have hmem : Zeta23.reflect ρ ∈ 𝒵 := Zeta23.zetaZeroConfig.reflect_mem ρ ρ.2
  exact mul_ne_zero (hsees ρ) (fun h0 => hsees ⟨_, hmem⟩ (by simpa using congrArg (starRingEnd ℂ) h0))

/-- The explicit autocorrelation `autocorr splineProbe` is a `C²_c` universal probe supported in
`[−8, 8]`. -/
theorem seesAllZeros_autocorr_splineProbe : SeesAllZeros (autocorr splineProbe) :=
  seesAllZeros_autocorr contDiff_splineProbe.continuous hasCompactSupport_splineProbe
    seesAllZeros_splineProbe

/-- **RH from the translated pairing of one universal probe.** For any universal probe `U ∈ C²_c`,
`RiemannHypothesis` is unconditionally equivalent to a one-sided upper bound on the translated
pairing `τ ↦ stationaryPacket (autocorr U) τ`. -/
theorem riemannHypothesis_iff_autocorr_packet_bddAbove_of_universal {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) (hUc : HasCompactSupport U) (hsees : SeesAllZeros U) :
    RiemannHypothesis ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket (autocorr U) τ ≤ K :=
  riemannHypothesis_iff_packet_bddAbove_of_universal
    (contDiff_autocorr hU hUc) (hasCompactSupport_autocorr hUc)
    (seesAllZeros_autocorr hU.continuous hUc hsees)

/-- **Zero-width bound from the translated pairing of one universal probe.** For any universal
probe `U ∈ C²_c` and `β ≥ 0`, `XiZeroHalfPlaneBound β` is unconditionally equivalent to
`stationaryPacket (autocorr U) τ ≤ K e^{βτ}` eventually. -/
theorem xiZeroHalfPlaneBound_iff_autocorr_packet_upper_of_universal {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) (hUc : HasCompactSupport U) (hsees : SeesAllZeros U)
    {β : ℝ} (hβ : 0 ≤ β) :
    XiZeroHalfPlaneBound β ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        stationaryPacket (autocorr U) τ ≤ K * Real.exp (β * τ) :=
  xiZeroHalfPlaneBound_iff_packet_upper_of_universal
    (contDiff_autocorr hU hUc) (hasCompactSupport_autocorr hUc)
    (seesAllZeros_autocorr hU.continuous hUc hsees) hβ

/-- **Single-probe Weil positivity criterion (`autocorr splineProbe`).** A one-sided upper bound
on the translated pairing `τ ↦ stationaryPacket (autocorr splineProbe) τ` of the single explicit
probe `splineProbe` is unconditionally equivalent to `RiemannHypothesis`, to universal positivity
of the complete Weil functional across all real `C²_c` sources, and to universal critical collapse
`W(h_f) = criticalWeilEnergy f`. -/
theorem riemannHypothesis_iff_autocorr_splineProbe_packet_bddAbove :
    RiemannHypothesis ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket (autocorr splineProbe) τ ≤ K :=
  riemannHypothesis_iff_autocorr_packet_bddAbove_of_universal
    contDiff_splineProbe hasCompactSupport_splineProbe seesAllZeros_splineProbe

/-- Universal complete Weil positivity and critical collapse under `RiemannHypothesis`: for every
real `C²_c` source `f`, `literatureRHS (weilTest f f) = criticalWeilEnergy f ≥ 0`. -/
theorem literatureRHS_weilTest_eq_criticalWeilEnergy_of_riemannHypothesis
    (hRH : RiemannHypothesis) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Zeta23.EF.literatureRHS (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      (criticalWeilEnergy f : ℂ) ∧
    0 ≤ (Zeta23.EF.literatureRHS
      (Zeta23.EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re := by
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => (f u : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  have hW := literatureRHS_weilTest_of_blind hf hfc hblind
  refine ⟨hW, ?_⟩
  rw [hW, ofReal_re]
  exact tsum_nonneg fun _ => by positivity

/-- Universal positivity and critical collapse of the bi-scale Lévy–Weil functional under
`RiemannHypothesis`: for every `g : RealWeilTestFn`,
`Ω(0) h_g(0) + 𝒥(g) − 2⟨h_g, ν⟩ = criticalWeilEnergy g.source ≥ 0`. -/
theorem levyWeilEnergy_eq_criticalWeilEnergy_of_riemannHypothesis
    (hRH : RiemannHypothesis) (g : RealWeilTestFn) :
    Zeta23.EF.gammaBracket 0 * autocorr g.source 0 + biScaleLevyEnergy g.source -
        2 * SignedPrimePolar.pairing g.supportScale (autocorr g.source) =
      criticalWeilEnergy g.source ∧
    0 ≤ Zeta23.EF.gammaBracket 0 * autocorr g.source 0 + biScaleLevyEnergy g.source -
        2 * SignedPrimePolar.pairing g.supportScale (autocorr g.source) := by
  obtain ⟨hW, hpos⟩ := literatureRHS_weilTest_eq_criticalWeilEnergy_of_riemannHypothesis
    hRH g.contDiff_source g.hasCompactSupport_source
  rw [← re_literatureRHS_weilTest_eq_levy g]
  refine ⟨?_, hpos⟩
  rw [hW, ofReal_re]

/-- **Universal translated-pairing collapse from a single probe (`splineProbe`).** A one-sided
upper bound on the single translated pairing `stationaryPacket (autocorr splineProbe)` is
unconditionally equivalent to a one-sided upper bound on `stationaryPacket (autocorr f)` for every
real `C²_c` source `f`, and implies universal Weil positivity across all `RealWeilTestFn`. -/
theorem forall_autocorr_packet_bddAbove_iff_autocorr_splineProbe_bddAbove :
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → HasCompactSupport f →
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket (autocorr f) τ ≤ K) ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket (autocorr splineProbe) τ ≤ K := by
  refine ⟨fun h => h splineProbe contDiff_splineProbe hasCompactSupport_splineProbe, fun h f hf hfc => ?_⟩
  have hRH := riemannHypothesis_iff_autocorr_splineProbe_packet_bddAbove.mpr h
  have hblind : ∀ ρ : 𝒵, 1 / 2 < (ρ : ℂ).re →
      Zeta23.paperFT (fun u => ((autocorr f u : ℝ) : ℂ)) (Zeta23.gammaOf ρ) = 0 := fun ρ hρ => by
    rw [re_eq_half_of_mem hRH ρ] at hρ
    exact absurd hρ (lt_irrefl _)
  obtain ⟨T, hT⟩ := (autocorr_packet_envelope hf hfc hblind).1 1 one_pos
  exact ⟨T, criticalWeilEnergy f + 1, fun τ hτ => (le_abs_self _).trans (hT τ hτ)⟩

/-- **Equivalence of upper bounds on `stationaryPacket` and `weilLagPoleConvolution`.** Because
`|stationaryPacket f τ - weilLagPoleConvolution f w τ| = O(e^{−(τ−w)/2})` for `τ > w`, an upper
growth bound `≤ K e^{βτ}` (`β ≥ 0`) on `stationaryPacket f` is unconditionally equivalent to the
same bound on the pure Weil-lag pole convolution `weilLagPoleConvolution f w`. -/
theorem stationaryPacket_upper_iff_weilLagPoleConvolution_upper {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → f v = 0) {β : ℝ} (hβ : 0 ≤ β) :
    (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K * Real.exp (β * τ)) ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → weilLagPoleConvolution f w τ ≤ K * Real.exp (β * τ) := by
  set C := (∫ u in Icc (-w) w, |f u|) + ∫ u in Icc (-w) w, |weilPoleOperator f u|
  have hC0 : 0 ≤ C := add_nonneg
    (setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _)
    (setIntegral_nonneg measurableSet_Icc fun _ _ => abs_nonneg _)
  have hdiff : ∀ τ : ℝ, w + 1 ≤ τ →
      |stationaryPacket f τ - weilLagPoleConvolution f w τ| ≤ C * Real.exp (β * τ) := by
    intro τ hτ
    have hτw : w < τ := by linarith
    have hexp1 : Real.exp (-(τ - w) / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hexp2 : 1 ≤ Real.exp (β * τ) :=
      Real.one_le_exp (mul_nonneg hβ (by linarith))
    calc |stationaryPacket f τ - weilLagPoleConvolution f w τ|
        ≤ Real.exp (-(τ - w) / 2) * C :=
          abs_stationaryPacket_sub_weilLagPoleConvolution_le hf hfc hw0 hw hτw
      _ ≤ 1 * C := mul_le_mul_of_nonneg_right hexp1 hC0
      _ = C * 1 := by ring
      _ ≤ C * Real.exp (β * τ) := mul_le_mul_of_nonneg_left hexp2 hC0
  constructor
  · rintro ⟨T, K, hK⟩
    refine ⟨max T (w + 1), K + C, fun τ hτ => ?_⟩
    have h1 := hK τ (le_of_max_le_left hτ)
    have h2 := (abs_sub_le_iff.mp (hdiff τ (le_of_max_le_right hτ))).2
    linarith
  · rintro ⟨T, K, hK⟩
    refine ⟨max T (w + 1), K + C, fun τ hτ => ?_⟩
    have h1 := hK τ (le_of_max_le_left hτ)
    have h2 := (abs_sub_le_iff.mp (hdiff τ (le_of_max_le_right hτ))).1
    linarith

/-- Specialization of `stationaryPacket_upper_iff_weilLagPoleConvolution_upper` to `β = 0`:
eventual boundedness above of `stationaryPacket f` is unconditionally equivalent to eventual
boundedness above of `weilLagPoleConvolution f w`. -/
theorem stationaryPacket_bddAbove_iff_weilLagPoleConvolution_bddAbove {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → f v = 0) :
    (∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → stationaryPacket f τ ≤ K) ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → weilLagPoleConvolution f w τ ≤ K := by
  simpa only [zero_mul, Real.exp_zero, mul_one] using
    stationaryPacket_upper_iff_weilLagPoleConvolution_upper hf hfc hw0 hw le_rfl

/-- **Pure Weil-lag pole-convolution criterion for `XiZeroHalfPlaneBound β`.** For any universal
probe `U ∈ C²_c` vanishing outside `[−w, w]` (`w ≥ 0`) and `β ≥ 0`, `XiZeroHalfPlaneBound β` is
unconditionally equivalent to `weilLagPoleConvolution U w τ ≤ K e^{βτ}` eventually. -/
theorem xiZeroHalfPlaneBound_iff_weilLagPoleConvolution_upper_of_universal {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) (hUc : HasCompactSupport U) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → U v = 0) (hsees : SeesAllZeros U) {β : ℝ} (hβ : 0 ≤ β) :
    XiZeroHalfPlaneBound β ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → weilLagPoleConvolution U w τ ≤ K * Real.exp (β * τ) :=
  (xiZeroHalfPlaneBound_iff_packet_upper_of_universal hU hUc hsees hβ).trans
    (stationaryPacket_upper_iff_weilLagPoleConvolution_upper hU hUc hw0 hw hβ)

/-- **Pure Weil-lag pole-convolution criterion for `RiemannHypothesis`.** For any universal probe
`U ∈ C²_c` vanishing outside `[−w, w]` (`w ≥ 0`), `RiemannHypothesis` is unconditionally equivalent
to eventual boundedness above of `τ ↦ weilLagPoleConvolution U w τ`. -/
theorem riemannHypothesis_iff_weilLagPoleConvolution_bddAbove_of_universal {U : ℝ → ℝ}
    (hU : ContDiff ℝ 2 U) (hUc : HasCompactSupport U) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ v : ℝ, w < |v| → U v = 0) (hsees : SeesAllZeros U) :
    RiemannHypothesis ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → weilLagPoleConvolution U w τ ≤ K :=
  (riemannHypothesis_iff_packet_bddAbove_of_universal hU hUc hsees).trans
    (stationaryPacket_bddAbove_iff_weilLagPoleConvolution_bddAbove hU hUc hw0 hw)

/-- Explicit `splineProbe` Weil-lag pole-convolution criterion for `RiemannHypothesis`:
`RiemannHypothesis ↔ ∃ T K : ℝ, ∀ τ ≥ T, ∫_{τ−4}^{τ+4} Φ(t) (weilPoleOperator splineProbe)(t − τ) dt ≤ K`. -/
theorem riemannHypothesis_iff_weilLagPoleConvolution_splineProbe_bddAbove :
    RiemannHypothesis ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ → weilLagPoleConvolution splineProbe 4 τ ≤ K :=
  riemannHypothesis_iff_weilLagPoleConvolution_bddAbove_of_universal
    contDiff_splineProbe hasCompactSupport_splineProbe (by norm_num)
    (fun _ hv => splineProbe_eq_zero hv) seesAllZeros_splineProbe

/-- Explicit `autocorr splineProbe` Weil-lag pole-convolution criterion for `RiemannHypothesis`:
`RiemannHypothesis ↔ ∃ T K : ℝ, ∀ τ ≥ T, ∫_{τ−8}^{τ+8} Φ(t) (weilPoleOperator (autocorr splineProbe))(t − τ) dt ≤ K`. -/
theorem riemannHypothesis_iff_weilLagPoleConvolution_autocorr_splineProbe_bddAbove :
    RiemannHypothesis ↔
      ∃ T K : ℝ, ∀ τ : ℝ, T ≤ τ →
        weilLagPoleConvolution (autocorr splineProbe) 8 τ ≤ K :=
  riemannHypothesis_iff_weilLagPoleConvolution_bddAbove_of_universal
    (contDiff_autocorr contDiff_splineProbe hasCompactSupport_splineProbe)
    (hasCompactSupport_autocorr hasCompactSupport_splineProbe) (by norm_num)
    (fun _ hv => autocorr_eq_zero_of_two_mul_lt_abs (fun _ h => splineProbe_eq_zero h)
      (by linarith))
    seesAllZeros_autocorr_splineProbe

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
