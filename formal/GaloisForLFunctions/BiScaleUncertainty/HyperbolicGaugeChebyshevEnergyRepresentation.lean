import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarPacket
import GaloisForLFunctions.HTGeometry.BlockWindowFubini
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# Hyperbolic-gauge Chebyshev energy representation of the signed prime–polar packet

For a compact `C¹` source `f` the signed prime–polar packet of cutoff `L = log(N+2)`,

`P(u) = Σ_{n ≤ N+2} Λ(n) n^{-1/2} f(u + log n) − ∫_0^L 2 cosh(t/2) f(u+t) dt`,

is an exact affine function of the normalized Chebyshev error `Ẽ(t) = e^{−t/2}(ψ(e^t) − e^t)`:

`P(u) = f(u) − ∫_0^L e^{−t/2} f(u+t) dt + Ẽ(L) f(u+L) − ∫_0^L Ẽ(t) (f' − f/2)(u+t) dt`.

The operator `f ↦ f' − f/2 = e^{u/2} (e^{−u/2} f)'` is the derivative in the hyperbolic gauge of the
critical line.  Stieltjes summation against `ψ(e^t)` turns the von Mangoldt atoms into the boundary
value `Ẽ(L) f(u+L)`, the origin value `f(u)` (from `ψ(1) − 1 = −1`), and the convolution of `Ẽ` with
the gauge derivative; the polar density `2cosh(t/2) = e^{t/2} + e^{−t/2}` supplies the forward
exponential residual.

Consequences.

* **Energy representation.**  `packetEnergy f N = ∫ (R f + Ẽ(L) f(·+L) − D f)²` with `R` the forward
  residual and `D` the Chebyshev gauge convolution; the convolution energy is the quadratic form of
  `Ẽ` against the positive-definite kernel `autocorr (f' − f/2)`:
  `∫ (D f)² = ∫_0^L ∫_0^L Ẽ(s) Ẽ(t) autocorr (f' − f/2) (t − s) ds dt`.
* **Young bound.**  `∫ (D f)² ≤ ‖f' − f/2‖₁² ∫_0^L Ẽ²`, so the packet energy is controlled by the
  mean-square normalized Chebyshev error, the source energy and the boundary value:
  `packetEnergy f N ≤ 3 (10 + Ẽ(L)²) autocorr f 0 + 3 ‖f' − f/2‖₁² ∫_0^L Ẽ(t)² dt`,
  and conversely the Chebyshev quadratic form against every gauge-derivative kernel is controlled by
  the packet energy: `∫ (D f)² ≤ 3 packetEnergy f N + 3 (10 + Ẽ(L)²) autocorr f 0`.
* **Mean-square dictionary.**  `∫_0^L Ẽ(t)² dt = ∫_1^{e^L} (ψ(x) − x)² / x² dx`.

Thus uniform stabilization of the signed packet energy over all compact `C¹` sources is equivalent,
up to source constants, to at most linear growth of the mean-square Chebyshev error
`∫_1^X (ψ(x) − x)²/x² dx` in `log X`.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The normalized Chebyshev error and the hyperbolic gauge derivative -/

/-- `Ẽ(t) = e^{−t/2} (ψ(e^t) − e^t)`. -/
def normalizedLogError (t : ℝ) : ℝ := Real.exp (-t / 2) * logError t

/-- The hyperbolic gauge derivative `f' − f/2`. -/
def gaugeDerivative (f : ℝ → ℝ) (u : ℝ) : ℝ := deriv f u - f u / 2

/-- The forward exponential residual `f(u) − ∫_0^L e^{−t/2} f(u+t) dt`. -/
def forwardResidual (f : ℝ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  f u - ∫ t in Icc 0 (cutoff N), Real.exp (-t / 2) * f (u + t)

/-- The Chebyshev gauge convolution `∫_0^L Ẽ(t) (f' − f/2)(u+t) dt`. -/
def chebyshevGaugeConvolution (f : ℝ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  ∫ t in Icc 0 (cutoff N), normalizedLogError t * gaugeDerivative f (u + t)

theorem measurable_logError : Measurable logError := by
  unfold logError
  exact (Chebyshev.psi_mono.measurable.comp Real.measurable_exp).sub Real.measurable_exp

theorem measurable_normalizedLogError : Measurable normalizedLogError :=
  (Real.measurable_exp.comp (measurable_id.neg.div_const 2)).mul measurable_logError

/-- On `[0, L]` the Chebyshev error is bounded by `ψ(e^L) + e^L`. -/
theorem abs_logError_le {L t : ℝ} (htL : t ≤ L) :
    |logError t| ≤ Chebyshev.psi (Real.exp L) + Real.exp L := by
  unfold logError
  have h1 : 0 ≤ Chebyshev.psi (Real.exp t) := Chebyshev.psi_nonneg _
  have h2 : Chebyshev.psi (Real.exp t) ≤ Chebyshev.psi (Real.exp L) :=
    Chebyshev.psi_mono (Real.exp_le_exp.2 htL)
  have h3 : Real.exp t ≤ Real.exp L := Real.exp_le_exp.2 htL
  have h4 : 0 < Real.exp t := Real.exp_pos t
  rw [abs_le]
  constructor <;> linarith

theorem abs_normalizedLogError_le {L t : ℝ} (ht0 : 0 ≤ t) (htL : t ≤ L) :
    |normalizedLogError t| ≤ Chebyshev.psi (Real.exp L) + Real.exp L := by
  unfold normalizedLogError
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := abs_logError_le htL
  have he : Real.exp (-t / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  calc Real.exp (-t / 2) * |logError t| ≤ 1 * |logError t| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ = |logError t| := one_mul _
    _ ≤ _ := h

/-! ## Stieltjes summation against the Chebyshev function -/

/-- **Stieltjes summation against `ψ(e^t)`.**  For `G` with continuous derivative `Q`,
`Σ_{n ≤ N+2} Λ(n) G(log n) − ∫_0^L G e^x = G(0) + G(L) (ψ(e^L) − e^L) − ∫_0^L Q (ψ(e^x) − e^x)`. -/
theorem stieltjes_vonMangoldt_identity (G Q : ℝ → ℝ) (hQ : Continuous Q)
    (hG : ∀ x, HasDerivAt G (Q x) x) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n * G (Real.log n)) -
        (∫ x in Icc 0 (cutoff N), G x * Real.exp x) =
      G 0 + G (cutoff N) * logError (cutoff N) -
        ∫ x in Icc 0 (cutoff N), Q x * logError x := by
  set L := cutoff N with hL
  have hL0 : 0 ≤ L := cutoff_nonneg N
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun x => (hG x).continuousAt
  -- the step integral
  have hterm : ∀ n ∈ Finset.Icc 1 (N + 2),
      (∫ x in Icc 0 L, Q x * (if Real.log (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0))
        = ArithmeticFunction.vonMangoldt n * (G L - G (Real.log n)) := by
    intro n hn
    obtain ⟨hn0, hnL⟩ := node_bounds N n hn
    have hind : (fun x => Q x * (if Real.log (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n
        else 0)) = (Ici (Real.log (n : ℝ))).indicator
          (fun x => Q x * ArithmeticFunction.vonMangoldt n) := by
      funext x
      by_cases hx : Real.log (n : ℝ) ≤ x
      · simp [hx]
      · simp [hx]
    have hset : Icc 0 L ∩ Ici (Real.log (n : ℝ)) = Icc (Real.log (n : ℝ)) L := by
      ext x
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨_, hxL⟩, hxn⟩; exact ⟨hxn, hxL⟩
      · rintro ⟨hxn, hxL⟩; exact ⟨⟨hn0.trans hxn, hxL⟩, hxn⟩
    rw [hind, setIntegral_indicator measurableSet_Ici, hset,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hnL,
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) (hQ.intervalIntegrable _ _)]
    ring
  have hstepint : (∫ x in Icc 0 L, Q x * step N x) =
      ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n * (G L - G (Real.log n)) := by
    have hfun : (fun x => Q x * step N x) = fun x => ∑ n ∈ Finset.Icc 1 (N + 2),
        Q x * (if Real.log (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n else 0) := by
      funext x; unfold step; rw [Finset.mul_sum]
    rw [hfun, integral_finsetSum _ (fun n _ => ?_)]
    · exact Finset.sum_congr rfl hterm
    · have hind : (fun x => Q x * (if Real.log (n : ℝ) ≤ x then ArithmeticFunction.vonMangoldt n
          else 0)) = (Ici (Real.log (n : ℝ))).indicator
            (fun x => Q x * ArithmeticFunction.vonMangoldt n) := by
        funext x
        by_cases hx : Real.log (n : ℝ) ≤ x
        · simp [hx]
        · simp [hx]
      rw [hind]
      exact ((hQ.mul continuous_const).integrableOn_Icc).indicator measurableSet_Ici
  -- the Chebyshev error integral
  have hQexp : IntegrableOn (fun x => Q x * Real.exp x) (Icc 0 L) :=
    (hQ.mul Real.continuous_exp).integrableOn_Icc
  have herr : (∫ x in Icc 0 L, Q x * logError x) =
      (∫ x in Icc 0 L, Q x * step N x) - ∫ x in Icc 0 L, Q x * Real.exp x := by
    have hstep_i : IntegrableOn (fun x => Q x * step N x) (Icc 0 L) := by
      refine ((integrable_mul_logError Q hQ N).add hQexp).congr_fun (fun x hx => ?_)
        measurableSet_Icc
      simp only [Pi.add_apply]
      rw [step_eq N hx.2, logError]; ring
    rw [← integral_sub hstep_i hQexp]
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    rw [step_eq N hx.2, logError]; ring
  -- integration by parts
  have hibp : (∫ x in Icc 0 L, G x * Real.exp x) =
      G L * Real.exp L - G 0 - ∫ x in Icc 0 L, Q x * Real.exp x := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt (a := (0 : ℝ))
      (b := L) hGc.continuousOn Real.continuous_exp.continuousOn (fun x _ => hG x)
      (fun x _ => Real.hasDerivAt_exp x) (hQ.intervalIntegrable _ _)
      (Real.continuous_exp.intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le hL0, intervalIntegral.integral_of_le hL0,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, Real.exp_zero, mul_one] at h
    exact h
  -- the boundary value of the error
  have hbd : logError L = (∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n) -
      Real.exp L := by
    rw [logError, ← step_eq N le_rfl]
    congr 1
    unfold step
    exact Finset.sum_congr rfl fun n hn => if_pos (node_bounds N n hn).2
  -- assemble
  have hsum : (∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n * G (Real.log n)) =
      (∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n) * G L -
        ∫ x in Icc 0 L, Q x * step N x := by
    rw [hstepint, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsum, hibp, herr, hbd]
  ring

/-! ## The pointwise gauge representation of the signed packet -/

theorem exp_neg_half_log_eq {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-Real.log (n : ℝ) / 2) = (Real.sqrt (n : ℝ))⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [neg_div, Real.exp_neg, exp_half_log_eq_sqrt hn0]

/-- The gauge derivative of a `C¹` compact source is continuous with compact support. -/
theorem continuous_gaugeDerivative {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (gaugeDerivative f) :=
  (hf.continuous_deriv le_rfl).sub ((hf.continuous).div_const 2)

theorem hasCompactSupport_gaugeDerivative {f : ℝ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (gaugeDerivative f) := by
  have h2 : HasCompactSupport (fun u => f u / 2) := by
    have h := hfc.mul_right (f' := fun _ : ℝ => (2 : ℝ)⁻¹)
    have he : (fun u => f u / 2) = f * fun _ : ℝ => (2 : ℝ)⁻¹ := by
      funext u; simp [div_eq_mul_inv]
    rw [he]; exact h
  show HasCompactSupport (fun u => deriv f u - f u / 2)
  exact hfc.deriv.sub h2

/-- The hyperbolic gauge derivative differentiates `t ↦ e^{−t/2} f(u+t)`. -/
theorem hasDerivAt_exp_neg_half_mul {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (u t : ℝ) :
    HasDerivAt (fun t => Real.exp (-t / 2) * f (u + t))
      (Real.exp (-t / 2) * gaugeDerivative f (u + t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t / 2)) (Real.exp (-t / 2) * (-1 / 2)) t := by
    have := ((hasDerivAt_id t).neg.div_const 2).exp
    simpa using this
  have h2 : HasDerivAt (fun t => f (u + t)) (deriv f (u + t)) t :=
    ((hf.differentiable one_ne_zero) (u + t)).hasDerivAt.comp_const_add u t
  exact (h1.mul h2).congr_deriv (by unfold gaugeDerivative; ring)

/-- **Pointwise gauge representation of the signed packet.** -/
theorem signedSource_eq_gauge (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) (u : ℝ) :
    signedSource f N u =
      forwardResidual f N u + normalizedLogError (cutoff N) * f (u + cutoff N) -
        chebyshevGaugeConvolution f N u := by
  set L := cutoff N with hL
  set G : ℝ → ℝ := fun t => Real.exp (-t / 2) * f (u + t) with hG
  set Q : ℝ → ℝ := fun t => Real.exp (-t / 2) * gaugeDerivative f (u + t) with hQ
  have hQc : Continuous Q := by
    rw [hQ]
    exact (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      ((continuous_gaugeDerivative hf).comp (continuous_const.add continuous_id))
  have hGd : ∀ t, HasDerivAt G (Q t) t := fun t => hasDerivAt_exp_neg_half_mul hf u t
  have hst := stieltjes_vonMangoldt_identity G Q hQc hGd N
  -- the atomic part
  have hatom : atomicSource f N u =
      ∑ n ∈ Finset.Icc 1 (N + 2), ArithmeticFunction.vonMangoldt n * G (Real.log n) := by
    change (∑ n ∈ Finset.Icc 1 (N + 2), primeWeight n * f (u + Real.log n)) = _
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hG, primeWeight]
    rw [exp_neg_half_log_eq (Finset.mem_Icc.mp hn).1]
    ring
  -- the polar part
  have hpolar : polarSource f N u =
      (∫ x in Icc 0 L, G x * Real.exp x) + ∫ t in Icc 0 L, Real.exp (-t / 2) * f (u + t) := by
    change (∫ t in Icc 0 L, polarDensity t * f (u + t)) = _
    have h1 : IntegrableOn (fun x => G x * Real.exp x) (Icc 0 L) :=
      (((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
        (f.continuous.comp (continuous_const.add continuous_id))).mul
          Real.continuous_exp).integrableOn_Icc
    have h2 : IntegrableOn (fun t => Real.exp (-t / 2) * f (u + t)) (Icc 0 L) :=
      ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
        (f.continuous.comp (continuous_const.add continuous_id))).integrableOn_Icc
    rw [← integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    simp only [hG, polarDensity, Real.cosh_eq]
    have he : Real.exp (-t / 2) * Real.exp t = Real.exp (t / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [show -(t / 2) = -t / 2 by ring]
    nlinarith only [congrArg (fun z : ℝ => z * f (u + t)) he]
  -- the signed source
  have hsigned : signedSource f N u = atomicSource f N u - polarSource f N u := rfl
  have hG0 : G 0 = f u := by simp [hG]
  have hGL : G L * logError L = normalizedLogError L * f (u + L) := by
    simp only [hG, normalizedLogError]; ring
  have hconv : (∫ x in Icc 0 L, Q x * logError x) = chebyshevGaugeConvolution f N u := by
    unfold chebyshevGaugeConvolution normalizedLogError
    refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
    simp only [hQ]; ring
  rw [hsigned, hatom, hpolar, forwardResidual]
  rw [hG0, hGL, hconv] at hst
  linarith only [hst]

/-- **Energy representation of the signed packet.** -/
theorem packetEnergy_eq_gauge (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    packetEnergy f N =
      ∫ u, (forwardResidual f N u + normalizedLogError (cutoff N) * f (u + cutoff N) -
        chebyshevGaugeConvolution f N u) ^ 2 := by
  unfold packetEnergy autocorr
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [add_zero, ← signedSource_eq_gauge f hf N u]
  ring

/-! ## Windowed translates: continuity, compact support and Fubini -/

section Windowed

variable {L : ℝ}

/-- A bounded measurable window weight against a continuous compact kernel translate is
continuous in the translation parameter. -/
theorem continuous_windowedTranslate {φ k : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hφM : ∀ t, |φ t| ≤ M) (hk : Continuous k) (hkc : HasCompactSupport k) :
    Continuous fun u => ∫ t in Icc 0 L, φ t * k (u + t) := by
  obtain ⟨C, hC⟩ := hk.bounded_above_of_compact_support hkc
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hφM 0)
  refine continuous_of_dominated (bound := fun _ => M * C) (fun u => ?_) (fun u => ?_) ?_ ?_
  · exact (hφ.mul (hk.measurable.comp (measurable_const.add measurable_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (hφM t) ?_ (abs_nonneg _) hM0
    rw [← Real.norm_eq_abs]; exact hC _
  · exact integrableOn_const (C := M * C) measure_Icc_lt_top.ne
  · exact Filter.Eventually.of_forall fun t =>
      continuous_const.mul (hk.comp (continuous_id.add continuous_const))

theorem hasCompactSupport_windowedTranslate {φ k : ℝ → ℝ} (hkc : HasCompactSupport k) :
    HasCompactSupport fun u => ∫ t in Icc 0 L, φ t * k (u + t) := by
  obtain ⟨R, _, hR⟩ := hkc.exists_pos_le_norm
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R - L) (b := R)) ?_
  intro u hu
  by_contra hout
  apply hu
  refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
  rw [hR (u + t) ?_, mul_zero]
  rw [Real.norm_eq_abs]
  simp only [mem_Icc, not_and_or, not_le] at hout
  rcases hout with h | h
  · exact le_abs.2 (Or.inr (by linarith [ht.2]))
  · exact le_abs.2 (Or.inl (by linarith [ht.1]))

/-- **Window Fubini.**  A bounded measurable window weight and a bounded measurable kernel that
vanishes for large translation parameter may be integrated in either order. -/
theorem integral_windowedTranslate_swap {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ}
    (hφM : ∀ t, |φ t| ≤ M) {k : ℝ → ℝ → ℝ} (hk : Measurable (Function.uncurry k)) {C R : ℝ}
    (hkb : ∀ u t, |k u t| ≤ C) (hkR : ∀ u t, R < |u| → k u t = 0) :
    (∫ u, ∫ t in Icc 0 L, φ t * k u t) = ∫ t in Icc 0 L, φ t * ∫ u, k u t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hφM 0)
  have hw₁ : Integrable (fun u : ℝ => (Icc (-R) R).indicator (fun _ => C) u) volume :=
    (integrableOn_const (C := C) measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hw₂ : Integrable (fun _ : ℝ => M) (volume.restrict (Icc 0 L)) :=
    integrableOn_const (C := M) measure_Icc_lt_top.ne
  have hmeas : AEStronglyMeasurable (Function.uncurry fun u t => φ t * k u t)
      (volume.prod (volume.restrict (Icc 0 L))) := by
    refine Measurable.aestronglyMeasurable ?_
    show Measurable fun p : ℝ × ℝ => φ p.2 * k p.1 p.2
    exact (hφ.comp measurable_snd).mul hk
  have hbound : ∀ᵐ p ∂(volume.prod (volume.restrict (Icc 0 L))),
      ‖Function.uncurry (fun u t => φ t * k u t) p‖ ≤
        (Icc (-R) R).indicator (fun _ => C) p.1 * M := by
    refine Filter.Eventually.of_forall fun p => ?_
    show |φ p.2 * k p.1 p.2| ≤ (Icc (-R) R).indicator (fun _ => C) p.1 * M
    rw [abs_mul]
    by_cases hp : p.1 ∈ Icc (-R) R
    · rw [Set.indicator_of_mem hp]
      calc |φ p.2| * |k p.1 p.2| ≤ M * C := mul_le_mul (hφM _) (hkb _ _) (abs_nonneg _) hM0
        _ = C * M := mul_comm _ _
    · rw [Set.indicator_of_notMem hp, zero_mul]
      have hz : k p.1 p.2 = 0 := by
        apply hkR
        simp only [mem_Icc, not_and_or, not_le] at hp
        rcases hp with h | h
        · exact lt_abs.2 (Or.inr (by linarith))
        · exact lt_abs.2 (Or.inl h)
      rw [hz, abs_zero, mul_zero]
  have h := GaloisForLFunctions.HTGeometry.integral_swap_of_dominated_prod hw₁ hw₂ hmeas hbound
  rw [h]
  exact setIntegral_congr_fun measurableSet_Icc fun t _ => integral_const_mul _ _

end Windowed

/-! ## The Chebyshev gauge convolution: continuity, support, Young bound and quadratic form -/

/-- The window-indicator of the normalized Chebyshev error is bounded everywhere by
`ψ(e^L) + e^L`. -/
theorem abs_indicator_normalizedLogError_le (L t : ℝ) :
    |(Icc 0 L).indicator normalizedLogError t| ≤ Chebyshev.psi (Real.exp L) + Real.exp L := by
  by_cases ht : t ∈ Icc 0 L
  · rw [Set.indicator_of_mem ht]; exact abs_normalizedLogError_le ht.1 ht.2
  · rw [Set.indicator_of_notMem ht, abs_zero]
    exact add_nonneg (Chebyshev.psi_nonneg _) (Real.exp_pos _).le

theorem chebyshevGaugeConvolution_eq_indicator (f : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    chebyshevGaugeConvolution f N u =
      ∫ t in Icc 0 (cutoff N), (Icc 0 (cutoff N)).indicator normalizedLogError t *
        gaugeDerivative f (u + t) := by
  unfold chebyshevGaugeConvolution
  exact (setIntegral_congr_fun measurableSet_Icc fun t ht => by
    rw [Set.indicator_of_mem ht]).symm

theorem continuous_chebyshevGaugeConvolution (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ))
    (N : ℕ) : Continuous (chebyshevGaugeConvolution f N) := by
  have h := continuous_windowedTranslate (L := cutoff N)
    (measurable_normalizedLogError.indicator measurableSet_Icc)
    (abs_indicator_normalizedLogError_le (cutoff N)) (continuous_gaugeDerivative hf)
    (hasCompactSupport_gaugeDerivative f.hasCompactSupport)
  convert h using 1
  funext u
  exact chebyshevGaugeConvolution_eq_indicator f N u

theorem hasCompactSupport_chebyshevGaugeConvolution (f : C_c(ℝ, ℝ)) (N : ℕ) :
    HasCompactSupport (chebyshevGaugeConvolution f N) := by
  have h := hasCompactSupport_windowedTranslate (L := cutoff N)
    (φ := (Icc 0 (cutoff N)).indicator normalizedLogError)
    (hasCompactSupport_gaugeDerivative f.hasCompactSupport)
  convert h using 1
  funext u
  exact chebyshevGaugeConvolution_eq_indicator f N u

theorem chebyshevGaugeConvolution_eq_lineConvolution (f : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    chebyshevGaugeConvolution f N u =
      GaloisForLFunctions.HTGeometry.lineConvolution (gaugeDerivative f)
        (fun y => (Icc 0 (cutoff N)).indicator normalizedLogError (-y)) u := by
  unfold chebyshevGaugeConvolution GaloisForLFunctions.HTGeometry.lineConvolution
  rw [← integral_indicator measurableSet_Icc]
  have hfun : (fun t => (Icc 0 (cutoff N)).indicator
      (fun t => normalizedLogError t * gaugeDerivative f (u + t)) t) =
      fun t => gaugeDerivative f (u + t) *
        (Icc 0 (cutoff N)).indicator normalizedLogError (-(u - (u + t))) := by
    funext t
    rw [Set.indicator_mul_left, mul_comm]
    congr 2; ring
  rw [hfun]
  exact integral_add_left_eq_self (fun s => gaugeDerivative f s *
    (Icc 0 (cutoff N)).indicator normalizedLogError (-(u - s))) u

theorem integral_indicator_normalizedLogError_sq (L : ℝ) :
    (∫ y, ((Icc 0 L).indicator normalizedLogError (-y)) ^ 2) =
      ∫ t in Icc 0 L, normalizedLogError t ^ 2 := by
  have hfun : (fun y => ((Icc 0 L).indicator normalizedLogError (-y)) ^ 2) =
      fun y => (Icc 0 L).indicator (fun t => normalizedLogError t ^ 2) (-y) := by
    funext y
    by_cases h : -y ∈ Icc 0 L
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_pow two_ne_zero]
  rw [hfun, integral_neg_eq_self, integral_indicator measurableSet_Icc]

theorem integrableOn_normalizedLogError_sq (L : ℝ) :
    IntegrableOn (fun t => normalizedLogError t ^ 2) (Icc 0 L) := by
  refine Measure.integrableOn_of_bounded (M := (Chebyshev.psi (Real.exp L) + Real.exp L) ^ 2)
    measure_Icc_lt_top.ne (measurable_normalizedLogError.pow_const 2).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_normalizedLogError_le ht.1 ht.2) 2

/-- **Young bound for the gauge convolution:**
`∫ (D f)² ≤ ‖f' − f/2‖₁² ∫_0^L Ẽ²`. -/
theorem integral_sq_chebyshevGaugeConvolution_le (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    (∫ u, chebyshevGaugeConvolution f N u ^ 2) ≤
      (∫ u, |gaugeDerivative f u|) ^ 2 * ∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2 := by
  set g : ℝ → ℝ := gaugeDerivative (f : ℝ → ℝ) with hg
  set V : ℝ → ℝ := fun y => (Icc 0 (cutoff N)).indicator normalizedLogError (-y) with hV
  have hgc : Continuous g := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport g := hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hVm : Measurable V :=
    (measurable_normalizedLogError.indicator measurableSet_Icc).comp measurable_neg
  have hV2 : Integrable (fun y => V y ^ 2) := by
    have h1 : Integrable ((Icc 0 (cutoff N)).indicator fun t => normalizedLogError t ^ 2) :=
      (integrableOn_normalizedLogError_sq (cutoff N)).integrable_indicator measurableSet_Icc
    have h2 := h1.comp_neg
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hV]
    by_cases h : -y ∈ Icc 0 (cutoff N)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_pow two_ne_zero]
  have hgabs : Integrable (fun t => |g t|) :=
    hgc.abs.integrable_of_hasCompactSupport (hgs.comp_left abs_zero)
  have hline : GaloisForLFunctions.HTGeometry.lineConvolution g V = chebyshevGaugeConvolution f N := by
    funext u
    exact (chebyshevGaugeConvolution_eq_lineConvolution f N u).symm
  have hconv : Integrable (fun x => GaloisForLFunctions.HTGeometry.lineConvolution g V x ^ 2) := by
    rw [hline]
    exact integrable_sq (continuous_chebyshevGaugeConvolution f hf N)
      (hasCompactSupport_chebyshevGaugeConvolution f N)
  have h := GaloisForLFunctions.HTGeometry.integral_sq_lineConvolution_le hgc.measurable hVm
    hgabs hV2 hconv
  rw [hline] at h
  rwa [show (∫ y, V y ^ 2) = ∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2 from
    integral_indicator_normalizedLogError_sq (cutoff N)] at h

/-- **Quadratic form of the normalized Chebyshev error against the gauge kernel:**
`∫ (D f)² = ∫_0^L ∫_0^L Ẽ(s) Ẽ(t) autocorr (f' − f/2) (t − s) dt ds`. -/
theorem integral_sq_chebyshevGaugeConvolution_eq (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    (∫ u, chebyshevGaugeConvolution f N u ^ 2) =
      ∫ s in Icc 0 (cutoff N), normalizedLogError s *
        ∫ t in Icc 0 (cutoff N), normalizedLogError t * autocorr (gaugeDerivative f) (t - s) := by
  set L := cutoff N with hL
  set g : ℝ → ℝ := gaugeDerivative (f : ℝ → ℝ) with hg
  set E : ℝ → ℝ := (Icc 0 L).indicator normalizedLogError with hE
  set D : ℝ → ℝ := chebyshevGaugeConvolution f N with hD
  have hgc : Continuous g := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport g := hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hEm : Measurable E := measurable_normalizedLogError.indicator measurableSet_Icc
  have hEb : ∀ t, |E t| ≤ Chebyshev.psi (Real.exp L) + Real.exp L :=
    abs_indicator_normalizedLogError_le L
  have hDc : Continuous D := continuous_chebyshevGaugeConvolution f hf N
  have hDs : HasCompactSupport D := hasCompactSupport_chebyshevGaugeConvolution f N
  obtain ⟨Cg, hCg⟩ := hgc.bounded_above_of_compact_support hgs
  obtain ⟨CD, hCD⟩ := hDc.bounded_above_of_compact_support hDs
  obtain ⟨Rg, _, hRg⟩ := hgs.exists_pos_le_norm
  obtain ⟨RD, _, hRD⟩ := hDs.exists_pos_le_norm
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
  have hCD0 : 0 ≤ CD := (norm_nonneg _).trans (hCD 0)
  have hDdef : ∀ u, D u = ∫ t in Icc 0 L, E t * g (u + t) := fun u =>
    chebyshevGaugeConvolution_eq_indicator f N u
  -- the square as a window integral
  have hsq : ∀ u, D u ^ 2 = ∫ s in Icc 0 L, E s * (g (u + s) * D u) := by
    intro u
    rw [sq, hDdef u, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    rw [← hDdef u]; ring
  -- first swap
  have hswap1 : (∫ u, ∫ s in Icc 0 L, E s * (g (u + s) * D u)) =
      ∫ s in Icc 0 L, E s * ∫ u, g (u + s) * D u := by
    refine integral_windowedTranslate_swap hEm hEb (k := fun u s => g (u + s) * D u)
      (C := Cg * CD) (R := RD) ?_ ?_ ?_
    · exact ((hgc.comp (continuous_fst.add continuous_snd)).mul
        (hDc.comp continuous_fst)).measurable
    · intro u s
      rw [abs_mul]
      refine mul_le_mul ?_ ?_ (abs_nonneg _) hCg0
      · rw [← Real.norm_eq_abs]; exact hCg _
      · rw [← Real.norm_eq_abs]; exact hCD _
    · intro u s hu
      rw [hRD u (by rw [Real.norm_eq_abs]; exact hu.le), mul_zero]
  -- the inner integral as a window integral in the second variable
  have hinner : ∀ s, (∫ u, g (u + s) * D u) =
      ∫ t in Icc 0 L, E t * autocorr g (t - s) := by
    intro s
    have h1 : (∫ u, g (u + s) * D u) = ∫ u, ∫ t in Icc 0 L, E t * (g (u + s) * g (u + t)) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      show g (u + s) * D u = ∫ t in Icc 0 L, E t * (g (u + s) * g (u + t))
      rw [hDdef u, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
      ring
    have h2 : (∫ u, ∫ t in Icc 0 L, E t * (g (u + s) * g (u + t))) =
        ∫ t in Icc 0 L, E t * ∫ u, g (u + s) * g (u + t) := by
      refine integral_windowedTranslate_swap hEm hEb (k := fun u t => g (u + s) * g (u + t))
        (C := Cg * Cg) (R := Rg + |s|) ?_ ?_ ?_
      · exact ((hgc.comp (continuous_fst.add continuous_const)).mul
          (hgc.comp (continuous_fst.add continuous_snd))).measurable
      · intro u t
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) hCg0
        · rw [← Real.norm_eq_abs]; exact hCg _
        · rw [← Real.norm_eq_abs]; exact hCg _
      · intro u t hu
        have : Rg ≤ ‖u + s‖ := by
          rw [Real.norm_eq_abs]
          have := abs_add_le (u + s) (-s)
          rw [add_neg_cancel_right, abs_neg] at this
          linarith
        rw [hRg (u + s) this, zero_mul]
    have h3 : ∀ t, (∫ u, g (u + s) * g (u + t)) = autocorr g (t - s) := by
      intro t
      unfold autocorr
      have := integral_add_right_eq_self (μ := volume) (fun v => g v * g (v + (t - s))) s
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only
      congr 2; ring
    rw [h1, h2]
    exact setIntegral_congr_fun measurableSet_Icc fun t _ => by rw [h3 t]
  -- assemble
  calc (∫ u, D u ^ 2) = ∫ u, ∫ s in Icc 0 L, E s * (g (u + s) * D u) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_); exact hsq u
    _ = ∫ s in Icc 0 L, E s * ∫ u, g (u + s) * D u := hswap1
    _ = ∫ s in Icc 0 L, E s * ∫ t in Icc 0 L, E t * autocorr g (t - s) := by
        refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
        rw [hinner s]
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
        rw [hE, Set.indicator_of_mem hs]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
        rw [Set.indicator_of_mem ht]

/-! ## The forward exponential residual -/

theorem integral_exp_neg_half_Icc_le {L : ℝ} (hL : 0 ≤ L) :
    (∫ t in Icc 0 L, Real.exp (-t / 2)) ≤ 2 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => -2 * Real.exp (-t / 2)) (Real.exp (-t / 2)) t := by
    intro t
    have h : HasDerivAt (fun y : ℝ => -2 * Real.exp (-y / 2))
        (-2 * (Real.exp (-t / 2) * (-1 / 2))) t :=
      (((hasDerivAt_neg t).div_const 2).exp).const_mul (-2)
    refine h.congr_deriv ?_
    ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).intervalIntegrable _ _)]
  have : 0 < Real.exp (-L / 2) := Real.exp_pos _
  have h0 : Real.exp (-(0 : ℝ) / 2) = 1 := by norm_num
  rw [h0]
  linarith

theorem forwardResidual_eq (f : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    forwardResidual f N u = f u - ∫ t in Icc 0 (cutoff N),
      (Icc 0 (cutoff N)).indicator (fun t => Real.exp (-t / 2)) t * f (u + t) := by
  unfold forwardResidual
  congr 1
  exact (setIntegral_congr_fun measurableSet_Icc fun t ht => by rw [Set.indicator_of_mem ht]).symm

theorem abs_indicator_exp_neg_half_le (L t : ℝ) :
    |(Icc 0 L).indicator (fun t => Real.exp (-t / 2)) t| ≤ 1 := by
  by_cases ht : t ∈ Icc 0 L
  · rw [Set.indicator_of_mem ht, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    linarith [ht.1]
  · rw [Set.indicator_of_notMem ht, abs_zero]; exact zero_le_one

theorem measurable_indicator_exp_neg_half (L : ℝ) :
    Measurable ((Icc 0 L).indicator fun t => Real.exp (-t / 2)) :=
  (Real.measurable_exp.comp (measurable_id.neg.div_const 2)).indicator measurableSet_Icc

/-- The exponential window weight `1_{[0,L]}(t) e^{−t/2}`. -/
def expWindow (L : ℝ) : ℝ → ℝ := (Icc 0 L).indicator fun t => Real.exp (-t / 2)

theorem measurable_expWindow (L : ℝ) : Measurable (expWindow L) :=
  measurable_indicator_exp_neg_half L

theorem abs_expWindow_le (L t : ℝ) : |expWindow L t| ≤ 1 := abs_indicator_exp_neg_half_le L t

theorem expWindow_nonneg (L t : ℝ) : 0 ≤ expWindow L t := by
  unfold expWindow
  by_cases ht : t ∈ Icc 0 L
  · rw [Set.indicator_of_mem ht]; exact (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem ht]

theorem integral_expWindow_le {L : ℝ} (hL : 0 ≤ L) : (∫ t in Icc 0 L, expWindow L t) ≤ 2 := by
  have : (∫ t in Icc 0 L, expWindow L t) = ∫ t in Icc 0 L, Real.exp (-t / 2) :=
    setIntegral_congr_fun measurableSet_Icc fun t ht => by
      unfold expWindow; rw [Set.indicator_of_mem ht]
  rw [this]; exact integral_exp_neg_half_Icc_le hL

theorem integrableOn_expWindow (L : ℝ) : IntegrableOn (expWindow L) (Icc 0 L) :=
  Measure.integrableOn_of_bounded (M := 1) measure_Icc_lt_top.ne
    (measurable_expWindow L).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_expWindow_le L t)

theorem hasCompactSupport_sq (f : C_c(ℝ, ℝ)) : HasCompactSupport fun u => (f : ℝ → ℝ) u ^ 2 := by
  have h := f.hasCompactSupport.mul_right (f' := (f : ℝ → ℝ))
  have he : (fun u => (f : ℝ → ℝ) u ^ 2) = (f : ℝ → ℝ) * (f : ℝ → ℝ) := by
    funext u; simp [sq]
  rw [he]; exact h

/-- Weighted Cauchy–Schwarz on the exponential window. -/
theorem windowed_average_sq_le (f : C_c(ℝ, ℝ)) (L u : ℝ) :
    (∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t)) ^ 2 ≤
      (∫ t in Icc 0 L, expWindow L t) *
        ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) ^ 2 := by
  obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hgm : AEStronglyMeasurable (fun t => (f : ℝ → ℝ) (u + t)) (volume.restrict (Icc 0 L)) :=
    (f.continuous.comp (continuous_const.add continuous_id)).measurable.aestronglyMeasurable
  have hwg2 : Integrable (fun t => expWindow L t * (f : ℝ → ℝ) (u + t) ^ 2)
      (volume.restrict (Icc 0 L)) := by
    refine Measure.integrableOn_of_bounded (M := Cf ^ 2) measure_Icc_lt_top.ne
      (((measurable_expWindow L).mul
        ((f.continuous.comp (continuous_const.add continuous_id)).pow 2).measurable).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    calc |expWindow L t| * |(f : ℝ → ℝ) (u + t)| ^ 2 ≤ 1 * Cf ^ 2 := by
          refine mul_le_mul (abs_expWindow_le L t) (pow_le_pow_left₀ (abs_nonneg _) ?_ 2)
            (by positivity) zero_le_one
          rw [← Real.norm_eq_abs]; exact hCf _
      _ = Cf ^ 2 := one_mul _
  exact GaloisForLFunctions.HTGeometry.sq_integral_weighted_le (μ := volume.restrict (Icc 0 L))
    (w := expWindow L) (g := fun t => (f : ℝ → ℝ) (u + t)) (expWindow_nonneg L)
    (measurable_expWindow L).aestronglyMeasurable hgm (integrableOn_expWindow L) hwg2

/-- The windowed square energy integrates exactly to the window mass times the source energy. -/
theorem integral_windowed_sq_eq (f : C_c(ℝ, ℝ)) (L : ℝ) :
    (∫ u, ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) ^ 2) =
      (∫ t in Icc 0 L, expWindow L t) * autocorr f 0 := by
  obtain ⟨Cf, hCf⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨Rf, _, hRf⟩ := f.hasCompactSupport.exists_pos_le_norm
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ → ℝ,
      k = fun u t => (Icc 0 L).indicator (fun t => (f : ℝ → ℝ) (u + t) ^ 2) t := ⟨_, rfl⟩
  have hkm : Measurable (Function.uncurry k) := by
    have he : Function.uncurry k = (Prod.snd ⁻¹' Icc 0 L).indicator
        (fun p : ℝ × ℝ => (f : ℝ → ℝ) (p.1 + p.2) ^ 2) := by
      funext p
      show k p.1 p.2 = _
      by_cases hp : p.2 ∈ Icc 0 L
      · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Icc 0 L from hp), hk]
        simp only
        rw [Set.indicator_of_mem hp]
      · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Icc 0 L from hp), hk]
        simp only
        rw [Set.indicator_of_notMem hp]
    rw [he]
    exact ((f.continuous.comp (continuous_fst.add continuous_snd)).pow 2).measurable.indicator
      (measurable_snd measurableSet_Icc)
  have hkb : ∀ u t, |k u t| ≤ Cf ^ 2 := by
    intro u t
    rw [hk]
    simp only
    rw [← Real.norm_eq_abs]
    refine (norm_indicator_le_norm_self (fun t => (f : ℝ → ℝ) (u + t) ^ 2) t).trans ?_
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [← Real.norm_eq_abs]; exact hCf _
  have hkR : ∀ u t, Rf + |L| < |u| → k u t = 0 := by
    intro u t hu
    rw [hk]
    simp only
    by_cases ht : t ∈ Icc 0 L
    · rw [Set.indicator_of_mem ht]
      have : Rf ≤ ‖u + t‖ := by
        rw [Real.norm_eq_abs]
        have h1 := abs_add_le (u + t) (-t)
        rw [add_neg_cancel_right, abs_neg] at h1
        have h2 : |t| ≤ |L| := by
          rw [abs_of_nonneg ht.1, abs_of_nonneg (ht.1.trans ht.2)]; exact ht.2
        linarith
      rw [hRf _ this, zero_pow two_ne_zero]
    · rw [Set.indicator_of_notMem ht]
  have hswap := integral_windowedTranslate_swap (L := L) (measurable_expWindow L)
    (abs_expWindow_le L) hkm hkb hkR
  have h1 : (∫ u, ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) ^ 2) =
      ∫ u, ∫ t in Icc 0 L, expWindow L t * k u t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    rw [hk]
    simp only
    rw [Set.indicator_of_mem ht]
  have h2 : (∫ t in Icc 0 L, expWindow L t * ∫ u, k u t) =
      ∫ t in Icc 0 L, expWindow L t * autocorr f 0 := by
    refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
    congr 1
    rw [← integral_sq_eq_autocorr_zero, ← integral_add_right_eq_self (μ := volume)
      (fun v => (f : ℝ → ℝ) v ^ 2) t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show k u t = (f : ℝ → ℝ) (u + t) ^ 2
    rw [hk]
    simp only
    rw [Set.indicator_of_mem ht]
  rw [h1, hswap, h2, integral_mul_const]

theorem forwardResidual_eq_expWindow (f : ℝ → ℝ) (N : ℕ) (u : ℝ) :
    forwardResidual f N u =
      f u - ∫ t in Icc 0 (cutoff N), expWindow (cutoff N) t * f (u + t) :=
  forwardResidual_eq f N u

/-- **Forward residual energy bound:** `∫ (R f)² ≤ 10 autocorr f 0`. -/
theorem integral_sq_forwardResidual_le (f : C_c(ℝ, ℝ)) (N : ℕ) :
    (∫ u, forwardResidual f N u ^ 2) ≤ 10 * autocorr f 0 := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = cutoff N := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := hL ▸ cutoff_nonneg N
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ,
      A = fun u => ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ → ℝ,
      B = fun u => ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) ^ 2 := ⟨_, rfl⟩
  have hAu : ∀ u, A u = ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) := fun u => by
    rw [hA]
  have hBu : ∀ u, B u = ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) ^ 2 := fun u => by
    rw [hB]
  have hAc : Continuous A := by
    rw [hA]
    exact continuous_windowedTranslate (φ := expWindow L) (k := (f : ℝ → ℝ))
      (measurable_expWindow L) (abs_expWindow_le L) f.continuous f.hasCompactSupport
  have hAs : HasCompactSupport A := by
    rw [hA]
    exact hasCompactSupport_windowedTranslate (φ := expWindow L) (k := (f : ℝ → ℝ))
      f.hasCompactSupport
  have hBc : Continuous B := by
    rw [hB]
    exact continuous_windowedTranslate (φ := expWindow L) (k := fun u => (f : ℝ → ℝ) u ^ 2)
      (measurable_expWindow L) (abs_expWindow_le L) (f.continuous.pow 2) (hasCompactSupport_sq f)
  have hBs : HasCompactSupport B := by
    rw [hB]
    exact hasCompactSupport_windowedTranslate (φ := expWindow L) (k := fun u => (f : ℝ → ℝ) u ^ 2)
      (hasCompactSupport_sq f)
  have hB0 : ∀ u, 0 ≤ B u := fun u => by
    rw [hBu]; exact integral_nonneg fun t => mul_nonneg (expWindow_nonneg _ t) (sq_nonneg _)
  have hAB : ∀ u, A u ^ 2 ≤ 2 * B u := fun u => by
    rw [hAu, hBu]
    exact (windowed_average_sq_le f L u).trans
      (mul_le_mul_of_nonneg_right (integral_expWindow_le hL0) (hBu u ▸ hB0 u))
  have hBint : (∫ u, B u) = (∫ t in Icc 0 L, expWindow L t) * autocorr f 0 := by
    rw [hB]; exact integral_windowed_sq_eq f L
  have hA2 : (∫ u, A u ^ 2) ≤ 4 * autocorr f 0 := by
    calc (∫ u, A u ^ 2) ≤ ∫ u, 2 * B u :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
            ((hBc.integrable_of_hasCompactSupport hBs).const_mul 2)
            (Filter.Eventually.of_forall hAB)
      _ = 2 * ((∫ t in Icc 0 L, expWindow L t) * autocorr f 0) := by
          rw [integral_const_mul, hBint]
      _ ≤ 4 * autocorr f 0 := by
          have := mul_le_mul_of_nonneg_right (integral_expWindow_le hL0) (autocorr_zero_nonneg f)
          linarith
  have hres : ∀ u, forwardResidual f N u = (f : ℝ → ℝ) u - A u := fun u => by
    rw [hAu, hL]; exact forwardResidual_eq_expWindow f N u
  have hf2 : Integrable fun u => (f : ℝ → ℝ) u ^ 2 := integrable_sq f.continuous f.hasCompactSupport
  have hA2i : Integrable fun u => A u ^ 2 := integrable_sq hAc hAs
  have hint : Integrable fun u => 2 * (f : ℝ → ℝ) u ^ 2 + 2 * A u ^ 2 :=
    (hf2.const_mul 2).add (hA2i.const_mul 2)
  calc (∫ u, forwardResidual f N u ^ 2) ≤ ∫ u, (2 * (f : ℝ → ℝ) u ^ 2 + 2 * A u ^ 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hint
          (Filter.Eventually.of_forall fun u => by
            show forwardResidual f N u ^ 2 ≤ 2 * (f : ℝ → ℝ) u ^ 2 + 2 * A u ^ 2
            rw [hres u]; nlinarith [sq_nonneg ((f : ℝ → ℝ) u + A u)])
    _ = 2 * (∫ u, (f : ℝ → ℝ) u ^ 2) + 2 * ∫ u, A u ^ 2 := by
        rw [integral_add (hf2.const_mul 2) (hA2i.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 10 * autocorr f 0 := by
        rw [integral_sq_eq_autocorr_zero]
        linarith

/-! ## Transfer between the packet energy and the mean-square Chebyshev error -/

theorem integral_sq_shift (f : C_c(ℝ, ℝ)) (c : ℝ) :
    (∫ u, (f : ℝ → ℝ) (u + c) ^ 2) = autocorr f 0 := by
  rw [← integral_sq_eq_autocorr_zero]
  exact integral_add_right_eq_self (fun v => (f : ℝ → ℝ) v ^ 2) c

/-- **Packet energy is controlled by the mean-square Chebyshev error:**
`packetEnergy f N ≤ 3 (10 + Ẽ(L)²) autocorr f 0 + 3 ‖f' − f/2‖₁² ∫_0^L Ẽ²`. -/
theorem packetEnergy_le_chebyshev_mean_square (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    packetEnergy f N ≤ 3 * (10 + normalizedLogError (cutoff N) ^ 2) * autocorr f 0 +
      3 * (∫ u, |gaugeDerivative f u|) ^ 2 *
        ∫ t in Icc 0 (cutoff N), normalizedLogError t ^ 2 := by
  set L := cutoff N with hL
  set R : ℝ → ℝ := forwardResidual f N with hR
  set B : ℝ → ℝ := fun u => normalizedLogError L * (f : ℝ → ℝ) (u + L) with hB
  set D : ℝ → ℝ := chebyshevGaugeConvolution f N with hD
  have hReq : R = fun u => (f : ℝ → ℝ) u - ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) := by
    funext u; exact forwardResidual_eq_expWindow f N u
  have hRc : Continuous R := by
    rw [hReq]
    exact f.continuous.sub (continuous_windowedTranslate (measurable_expWindow L)
      (abs_expWindow_le L) f.continuous f.hasCompactSupport)
  have hRs : HasCompactSupport R := by
    rw [hReq]
    exact f.hasCompactSupport.sub (hasCompactSupport_windowedTranslate f.hasCompactSupport)
  have hBc : Continuous B := continuous_const.mul (f.continuous.comp (continuous_id.add continuous_const))
  have hBs : HasCompactSupport B :=
    (hasCompactSupport_comp_add f.hasCompactSupport L).mul_left
  have hDc : Continuous D := continuous_chebyshevGaugeConvolution f hf N
  have hDs : HasCompactSupport D := hasCompactSupport_chebyshevGaugeConvolution f N
  have hR2 : Integrable fun u => R u ^ 2 := integrable_sq hRc hRs
  have hB2i : Integrable fun u => B u ^ 2 := integrable_sq hBc hBs
  have hD2 : Integrable fun u => D u ^ 2 := integrable_sq hDc hDs
  have hRB : Integrable fun u => R u ^ 2 + B u ^ 2 := hR2.add hB2i
  have hRBD : Integrable fun u => R u ^ 2 + B u ^ 2 + D u ^ 2 := hRB.add hD2
  have hint : Integrable fun u => 3 * (R u ^ 2 + B u ^ 2 + D u ^ 2) := hRBD.const_mul 3
  have hB2 : (∫ u, B u ^ 2) = normalizedLogError L ^ 2 * autocorr f 0 := by
    have : (fun u => B u ^ 2) = fun u => normalizedLogError L ^ 2 * (f : ℝ → ℝ) (u + L) ^ 2 := by
      funext u; simp only [hB]; ring
    rw [this, integral_const_mul, integral_sq_shift]
  rw [packetEnergy_eq_gauge f hf N]
  calc (∫ u, (R u + B u - D u) ^ 2) ≤ ∫ u, 3 * (R u ^ 2 + B u ^ 2 + D u ^ 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hint
          (Filter.Eventually.of_forall fun u => by
            nlinarith [sq_nonneg (R u - B u), sq_nonneg (R u + D u), sq_nonneg (B u + D u)])
    _ = 3 * ((∫ u, R u ^ 2) + (∫ u, B u ^ 2) + ∫ u, D u ^ 2) := by
        rw [integral_const_mul, integral_add hRB hD2, integral_add hR2 hB2i]
    _ ≤ _ := by
        have h1 := integral_sq_forwardResidual_le f N
        have h2 := integral_sq_chebyshevGaugeConvolution_le f hf N
        rw [hB2]
        nlinarith [h1, h2]

/-- **The Chebyshev gauge energy is controlled by the packet energy:**
`∫ (D f)² ≤ 3 packetEnergy f N + 3 (10 + Ẽ(L)²) autocorr f 0`. -/
theorem chebyshevGauge_energy_le_packetEnergy (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    (∫ u, chebyshevGaugeConvolution f N u ^ 2) ≤
      3 * packetEnergy f N + 3 * (10 + normalizedLogError (cutoff N) ^ 2) * autocorr f 0 := by
  set L := cutoff N with hL
  set R : ℝ → ℝ := forwardResidual f N with hR
  set B : ℝ → ℝ := fun u => normalizedLogError L * (f : ℝ → ℝ) (u + L) with hB
  set D : ℝ → ℝ := chebyshevGaugeConvolution f N with hD
  set P : ℝ → ℝ := ((signedSource f N : C_c(ℝ, ℝ)) : ℝ → ℝ) with hP
  have hReq : R = fun u => (f : ℝ → ℝ) u - ∫ t in Icc 0 L, expWindow L t * (f : ℝ → ℝ) (u + t) := by
    funext u; exact forwardResidual_eq_expWindow f N u
  have hRc : Continuous R := by
    rw [hReq]
    exact f.continuous.sub (continuous_windowedTranslate (measurable_expWindow L)
      (abs_expWindow_le L) f.continuous f.hasCompactSupport)
  have hRs : HasCompactSupport R := by
    rw [hReq]
    exact f.hasCompactSupport.sub (hasCompactSupport_windowedTranslate f.hasCompactSupport)
  have hBc : Continuous B := continuous_const.mul (f.continuous.comp (continuous_id.add continuous_const))
  have hBs : HasCompactSupport B :=
    (hasCompactSupport_comp_add f.hasCompactSupport L).mul_left
  have hPc : Continuous P := (signedSource f N).continuous
  have hPs : HasCompactSupport P := (signedSource f N).hasCompactSupport
  have hR2 : Integrable fun u => R u ^ 2 := integrable_sq hRc hRs
  have hB2i : Integrable fun u => B u ^ 2 := integrable_sq hBc hBs
  have hP2i : Integrable fun u => P u ^ 2 := integrable_sq hPc hPs
  have hRB : Integrable fun u => R u ^ 2 + B u ^ 2 := hR2.add hB2i
  have hRBP : Integrable fun u => R u ^ 2 + B u ^ 2 + P u ^ 2 := hRB.add hP2i
  have hint : Integrable fun u => 3 * (R u ^ 2 + B u ^ 2 + P u ^ 2) := hRBP.const_mul 3
  have hB2 : (∫ u, B u ^ 2) = normalizedLogError L ^ 2 * autocorr f 0 := by
    have : (fun u => B u ^ 2) = fun u => normalizedLogError L ^ 2 * (f : ℝ → ℝ) (u + L) ^ 2 := by
      funext u; simp only [hB]; ring
    rw [this, integral_const_mul, integral_sq_shift]
  have hP2 : (∫ u, P u ^ 2) = packetEnergy f N := integral_sq_eq_autocorr_zero _
  have hDeq : ∀ u, D u = R u + B u - P u := fun u => by
    have := signedSource_eq_gauge f hf N u
    simp only [hD, hR, hB, hP]; linarith
  calc (∫ u, D u ^ 2) = ∫ u, (R u + B u - P u) ^ 2 := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show D u ^ 2 = (R u + B u - P u) ^ 2
        rw [hDeq u]
    _ ≤ ∫ u, 3 * (R u ^ 2 + B u ^ 2 + P u ^ 2) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hint
          (Filter.Eventually.of_forall fun u => by
            nlinarith [sq_nonneg (R u - B u), sq_nonneg (R u + P u), sq_nonneg (B u + P u)])
    _ = 3 * ((∫ u, R u ^ 2) + (∫ u, B u ^ 2) + ∫ u, P u ^ 2) := by
        rw [integral_const_mul, integral_add hRB hP2i, integral_add hR2 hB2i]
    _ ≤ _ := by
        have h1 := integral_sq_forwardResidual_le f N
        rw [hB2, hP2]
        nlinarith [h1]

/-! ## The mean-square dictionary -/

/-- `∫_0^L Ẽ(t)² dt = ∫_1^{e^L} (ψ(x) − x)² / x² dx`. -/
theorem integral_normalizedLogError_sq_eq (L : ℝ) :
    (∫ t in Icc 0 L, normalizedLogError t ^ 2) =
      ∫ x in Icc 1 (Real.exp L), (Chebyshev.psi x - x) ^ 2 / x ^ 2 := by
  have himg : Icc (1 : ℝ) (Real.exp L) = Real.exp '' Icc 0 L := by
    rw [Real.image_exp_Icc, Real.exp_zero]
  rw [himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun s _ => (Real.hasDerivAt_exp s).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [abs_of_pos (Real.exp_pos t), smul_eq_mul]
  unfold normalizedLogError logError
  have he : Real.exp (-t / 2) ^ 2 = (Real.exp t)⁻¹ := by
    rw [sq, ← Real.exp_add, show -t / 2 + -t / 2 = -t by ring, Real.exp_neg]
  have hpos := (Real.exp_pos t).ne'
  rw [mul_pow, he]
  field_simp

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
