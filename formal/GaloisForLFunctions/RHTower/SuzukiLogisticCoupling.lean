import GaloisForLFunctions.RHTower.SuzukiPairedSeamScalar
import GaloisForLFunctions.RHTower.SuzukiCarlemanFlatPortAsymptotic
import GaloisForLFunctions.HTGeometry.ReflectionIntegral
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments

/-!
# The logistic cross coupling and its exact weighted norm

The `L`-derivative of the Carleman cutoff factor `(1+e^{v-L})⁻¹` is the logistic density
`k(t) = e^t/(1+e^t)²`, so the cross-orientation block of a paired seam is convolution by `k`:

`(K F)(L) = ∫ F(v) k(v-L) dv`.

Conjugating by the weight `e^{σL}` turns `K` into convolution by `e^{σt}k(t)`, whose total mass is
the logistic moment

`m_σ = ∫ e^{-σt} k(t) dt = Γ(1+σ)Γ(1-σ) = σπ / sin(πσ)`,

finite exactly on `|σ| < 1` and equal to `1` at `σ = 0`.  Young's inequality then bounds the
conjugated block on `L²` by `m_σ`, so the cross coupling is a bounded zero-order operator on the
whole open Gamma strip, with its first singularity at height one.
-/

open Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

/-! ## The logistic kernel is even -/

theorem logisticKernel_neg (t : ℝ) : logisticKernel (-t) = logisticKernel t := by
  have hpos : (0:ℝ) < Real.exp t := Real.exp_pos t
  have hne : (1 : ℝ) + Real.exp t ≠ 0 := by positivity
  rw [logisticKernel, logisticKernel, Real.exp_neg]
  field_simp
  ring

/-! ## The logistic moment -/

/-- The two-sided Laplace transform of the logistic density. -/
def logisticMoment (σ : ℝ) : ℝ := ∫ t : ℝ, Real.exp (-σ * t) * logisticKernel t

theorem measurable_expMul_logisticKernel (σ : ℝ) :
    Measurable fun t : ℝ => Real.exp (-σ * t) * logisticKernel t :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    continuous_logisticKernel.measurable

theorem expMul_logisticKernel_nonneg (σ t : ℝ) :
    0 ≤ Real.exp (-σ * t) * logisticKernel t :=
  mul_nonneg (Real.exp_pos _).le (logisticKernel_pos t).le

/-- Inside the open unit strip the weighted logistic density is integrable: it is dominated by
the two-sided exponential of rate `1 - |σ|`. -/
theorem integrable_expMul_logisticKernel {σ : ℝ} (hσ : |σ| < 1) :
    Integrable (fun t : ℝ => Real.exp (-σ * t) * logisticKernel t) := by
  have hrate : (0:ℝ) < 1 - |σ| := by linarith
  have hmaj : Integrable (fun t : ℝ => Real.exp (-(1 - |σ|) * |t|)) := by
    have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hrate
    simpa using h
  refine Integrable.mono' hmaj (measurable_expMul_logisticKernel σ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have hk : logisticKernel t ≤ Real.exp (-|t|) := logisticKernel_le_exp_neg_abs t
  have hexpo : -σ * t ≤ |σ| * |t| := by
    have h := neg_abs_le (σ * t)
    have habs : |σ * t| = |σ| * |t| := abs_mul σ t
    have : -(|σ| * |t|) ≤ σ * t := by rw [← habs]; exact h
    linarith
  have hmono : Real.exp (-σ * t) * logisticKernel t
      ≤ Real.exp (|σ| * |t|) * Real.exp (-|t|) := by
    apply mul_le_mul (Real.exp_le_exp.mpr hexpo) hk (logisticKernel_pos t).le (Real.exp_pos _).le
  have hcomb : Real.exp (|σ| * |t|) * Real.exp (-|t|) = Real.exp (-(1 - |σ|) * |t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (expMul_logisticKernel_nonneg σ t)]
  calc Real.exp (-σ * t) * logisticKernel t
      ≤ Real.exp (|σ| * |t|) * Real.exp (-|t|) := hmono
    _ = Real.exp (-(1 - |σ|) * |t|) := hcomb

/-- **`(17)`: the logistic moment is the reflection value.**  For `0 < σ < 1` the substitution
`z = e^t` turns the moment into the Euler beta integral `Β(1-σ,1+σ) = Γ(1-σ)Γ(1+σ)`. -/
theorem logisticMoment_eq_of_pos {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    logisticMoment σ = σ * Real.pi / Real.sin (Real.pi * σ) := by
  have h := GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_logistic h0 h1
  rw [logisticMoment]
  simpa only [logisticKernel] using h

/-- The logistic moment is even, because the logistic density is. -/
theorem logisticMoment_neg (σ : ℝ) : logisticMoment (-σ) = logisticMoment σ := by
  have hrefl : (∫ t : ℝ, Real.exp (-σ * -t) * logisticKernel (-t))
      = ∫ t : ℝ, Real.exp (-σ * t) * logisticKernel t :=
    integral_neg_eq_self (fun t => Real.exp (-σ * t) * logisticKernel t) volume
  rw [logisticMoment, logisticMoment, ← hrefl]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show Real.exp (- -σ * t) * logisticKernel t
      = Real.exp (-σ * -t) * logisticKernel (-t)
  rw [logisticKernel_neg]
  congr 2
  ring

/-- **`(7)`, the moment in closed form** on the punctured strip. -/
theorem logisticMoment_eq {σ : ℝ} (hσ : |σ| < 1) (hne : σ ≠ 0) :
    logisticMoment σ = σ * Real.pi / Real.sin (Real.pi * σ) := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have h0 : 0 < -σ := by linarith
    have h1 : -σ < 1 := by
      have := abs_lt.mp hσ
      linarith [this.1]
    have hval := logisticMoment_eq_of_pos h0 h1
    rw [← logisticMoment_neg σ, hval]
    rw [show Real.pi * -σ = -(Real.pi * σ) by ring, Real.sin_neg]
    field_simp
  · have h1 : σ < 1 := (abs_lt.mp hσ).2
    exact logisticMoment_eq_of_pos hpos h1

/-- At the centre of the strip the logistic moment is one: the logistic density is a probability
density. -/
theorem logisticMoment_zero : logisticMoment 0 = 1 := by
  rw [logisticMoment]
  have : ∀ t : ℝ, Real.exp (-0 * t) * logisticKernel t = logisticKernel t := by
    intro t
    rw [show -0 * t = (0:ℝ) by ring, Real.exp_zero, one_mul]
  simp only [this]
  exact integral_logisticKernel

theorem logisticMoment_nonneg (σ : ℝ) : 0 ≤ logisticMoment σ := by
  rw [logisticMoment]
  exact integral_nonneg fun t => expMul_logisticKernel_nonneg σ t

/-! ## The cutoff derivative -/

/-- **`(15)`: differentiating the Carleman cutoff factor in the cutoff scale produces the logistic
density.** -/
theorem hasDerivAt_carlemanCutoffFactor_left (v L : ℝ) :
    HasDerivAt (fun M : ℝ => carlemanCutoffFactor M v) (logisticKernel (v - L)) L := by
  have hpos : (0:ℝ) < 1 + Real.exp (v - L) := by
    have := Real.exp_pos (v - L)
    linarith
  have hne : (1 : ℝ) + Real.exp (v - L) ≠ 0 := ne_of_gt hpos
  have hinner : HasDerivAt (fun M : ℝ => v - M) (-1) L := by
    simpa using (hasDerivAt_id' L).const_sub v
  have hexp : HasDerivAt (fun M : ℝ => Real.exp (v - M)) (Real.exp (v - L) * (-1)) L :=
    hinner.exp
  have hbase : HasDerivAt (fun M : ℝ => 1 + Real.exp (v - M)) (Real.exp (v - L) * (-1)) L := by
    simpa using hexp.const_add (1:ℝ)
  have hinv := hbase.inv hne
  have hval : -(Real.exp (v - L) * (-1)) / (1 + Real.exp (v - L)) ^ 2
      = logisticKernel (v - L) := by
    rw [logisticKernel]
    ring
  have hfun : (fun M : ℝ => carlemanCutoffFactor M v)
      = fun M : ℝ => (1 + Real.exp (v - M))⁻¹ := by
    funext M
    rw [carlemanCutoffFactor]
  rw [hfun, ← hval]
  exact hinv

/-! ## The weighted cross block -/

/-- **`(6)`: the logistic cross coupling** `(K F)(L) = ∫ F(v) k(v-L) dv`.  A profile supported on
the physical ray is extended by zero, so this is the truncated convolution of the card. -/
def logisticCoupling (F : ℝ → ℝ) (L : ℝ) : ℝ := ∫ v : ℝ, F v * logisticKernel (v - L)

/-- **`(16)`: conjugation by the Gamma weight turns the cross block into convolution by
`e^{σt}k(t)`.** -/
theorem expMul_logisticCoupling_eq (σ : ℝ) (F : ℝ → ℝ) (L : ℝ) :
    Real.exp (σ * L) * logisticCoupling F L
      = GaloisForLFunctions.HTGeometry.lineConvolution
          (fun y => Real.exp (σ * y) * logisticKernel y)
          (fun x => Real.exp (σ * x) * F x) L := by
  have hsub : (∫ y : ℝ, F (L - y) * logisticKernel (L - y - L))
      = ∫ v : ℝ, F v * logisticKernel (v - L) :=
    integral_sub_left_eq_self (fun v => F v * logisticKernel (v - L)) volume L
  rw [GaloisForLFunctions.HTGeometry.lineConvolution, logisticCoupling, ← hsub,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have hker : logisticKernel (L - y - L) = logisticKernel y := by
    rw [show L - y - L = -y by ring, logisticKernel_neg]
  have hexp : Real.exp (σ * L) = Real.exp (σ * y) * Real.exp (σ * (L - y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  show Real.exp (σ * L) * (F (L - y) * logisticKernel (L - y - L))
      = Real.exp (σ * y) * logisticKernel y * (Real.exp (σ * (L - y)) * F (L - y))
  rw [hker, hexp]
  ring

/-- **`(7)`: the exact weighted bound.**  The Gamma-conjugated logistic cross block is bounded on
`L²` by the logistic moment, for every `|σ| < 1`.  Stated for the squared `ℝ≥0∞` energies, so no
integrability hypothesis is needed. -/
theorem lintegral_sq_expMul_logisticCoupling_le {σ : ℝ} (hσ : |σ| < 1) {F : ℝ → ℝ}
    (hF : Measurable F) :
    (∫⁻ L : ℝ, ‖Real.exp (σ * L) * logisticCoupling F L‖ₑ ^ 2)
      ≤ ENNReal.ofReal (logisticMoment σ) ^ 2
        * ∫⁻ x : ℝ, ‖Real.exp (σ * x) * F x‖ₑ ^ 2 := by
  set ρ : ℝ → ℝ := fun y => Real.exp (σ * y) * logisticKernel y with hρdef
  set u : ℝ → ℝ := fun x => Real.exp (σ * x) * F x with hudef
  have hρmeas : Measurable ρ :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      continuous_logisticKernel.measurable
  have humeas : Measurable u :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hF
  have hρnn : ∀ y, 0 ≤ ρ y := fun y =>
    mul_nonneg (Real.exp_pos _).le (logisticKernel_pos y).le
  have hbound : ∀ L : ℝ, ‖Real.exp (σ * L) * logisticCoupling F L‖ₑ
      ≤ ∫⁻ y : ℝ, ‖ρ y‖ₑ * ‖u (L - y)‖ₑ := by
    intro L
    rw [expMul_logisticCoupling_eq σ F L, GaloisForLFunctions.HTGeometry.lineConvolution]
    refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
    exact lintegral_congr fun y => enorm_mul _ _
  have hmain := GaloisForLFunctions.HTGeometry.lintegral_enorm_sq_le_of_convolution_bound
    hρmeas.enorm humeas.enorm hbound
  have hmass : (∫⁻ y : ℝ, ‖ρ y‖ₑ) = ENNReal.ofReal (logisticMoment σ) := by
    have hint : Integrable ρ := by
      have hneg : |(-σ)| < 1 := by rwa [abs_neg]
      have h := integrable_expMul_logisticKernel hneg
      refine h.congr (Filter.Eventually.of_forall fun t => ?_)
      rw [hρdef]
      ring_nf
    have hmoment : (∫ y : ℝ, ρ y) = logisticMoment σ := by
      have hneg : logisticMoment (-σ) = logisticMoment σ := logisticMoment_neg σ
      rw [← hneg, logisticMoment]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      rw [hρdef]
      ring_nf
    rw [← hmoment, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall hρnn)]
    exact (lintegral_congr fun y => (Real.enorm_eq_ofReal (hρnn y)))
  rw [hmass] at hmain
  exact hmain

/-! ## Terminal coercivity -/

/-- **`(20)`: the terminal coefficient is positive on a far ray.**  Whatever the finite constant
assembled from the Gamma defect, the logistic moment and the prime adjacency norm, and whatever
exponentially small remainder accompanies it, `2L` eventually dominates. -/
theorem eventually_terminal_coercive (c C : ℝ) {E : ℝ → ℝ}
    (hE : ∀ L : ℝ, |E L| ≤ C * Real.exp (-L)) :
    ∀ᶠ L : ℝ in atTop, 0 < 2 * L - c + E L := by
  have hC : 0 ≤ C := by
    have h := hE 0
    have hpos : (0:ℝ) < Real.exp (-0) := Real.exp_pos _
    nlinarith [abs_nonneg (E 0)]
  have hexp : ∀ᶠ L : ℝ in atTop, C * Real.exp (-L) ≤ 1 := by
    have hlim : Tendsto (fun L : ℝ => C * Real.exp (-L)) atTop (𝓝 (C * 0)) :=
      Filter.Tendsto.const_mul C
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    rw [mul_zero] at hlim
    exact hlim.eventually_le_const (show (0:ℝ) < 1 by norm_num)
  filter_upwards [hexp, eventually_gt_atTop ((c + 1) / 2)] with L hL1 hL2
  have hEbound : -(1:ℝ) ≤ E L := by
    have h := hE L
    have := abs_le.mp h
    linarith [this.1]
  have : c + 1 < 2 * L := by
    have := (div_lt_iff₀ (by norm_num : (0:ℝ) < 2)).mp hL2
    linarith
  linarith

end

end RHTower
