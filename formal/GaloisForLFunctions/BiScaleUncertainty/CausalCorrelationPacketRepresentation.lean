import GaloisForLFunctions.BiScaleUncertainty.CausalExponentialResponseAndLaplaceEnergy

/-!
# The causal correlation representation of the signed prime–polar packet

Let `K(x) = e^{−x/2} 1_{x ≥ 0}` be the causal kernel, `g = f' − f/2` the gauge derivative of a
compactly supported `C¹` source `f`, and `R_N = K ⋆ ν_N` the causal response of the signed
prime–polar measure.  The causal kernel inverts the gauge derivative,

`f(x) = −∫ K(t) g(x + t) dt`,

so the signed packet is the correlation of the response with the gauge derivative,

`signedSource f N (u) = −∫ R_N(t) g(u + t) dt`.

Consequently the packet energy is a Gram energy of `R_N` against the autocorrelation of `g`,

`packetEnergy f N = ∬ R_N(t) R_N(s) autocorr g (s − t) = ∫ autocorr g · autocorr R_N`,

it is bounded by the Laplace Gram energy through Young's inequality,

`packetEnergy f N ≤ ‖g‖₁² · laplaceEnergy N`,

and the autocorrelation of the source is recovered from that of its gauge derivative by the
Laplace kernel (Green's identity for `d/dx − 1/2`):

`autocorr f (x) = ∫ autocorr g (y) e^{−|x+y|/2} dy = (autocorr g ⋆ e^{−|·|/2})(x)`.

Thus every compact-source Gram energy of the field is the Laplace Gram energy filtered through a
positive-definite kernel, and the whole arithmetic content of every packet sits in the single
response `R_N`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## Compact-support bookkeeping -/

theorem hasCompactSupport_comp_const_add {g : ℝ → ℝ} (hg : HasCompactSupport g) (u : ℝ) :
    HasCompactSupport fun t => g (u + t) :=
  hg.comp_homeomorph (Homeomorph.addLeft u)

/-- A compactly supported factor kills any product along `+∞`. -/
theorem tendsto_mul_comp_const_add_atTop {k g : ℝ → ℝ} (hg : HasCompactSupport g) (u : ℝ) :
    Tendsto (fun t => k t * g (u + t)) atTop (𝓝 0) := by
  obtain ⟨R, -, hR⟩ := hg.exists_pos_le_norm
  refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨R + |u|, fun t ht => ?_⟩)
  have h : R ≤ ‖u + t‖ := by
    rw [Real.norm_eq_abs]
    have := neg_abs_le u
    calc R ≤ u + t := by linarith
      _ ≤ |u + t| := le_abs_self _
  show (0 : ℝ) = k t * g (u + t)
  rw [hR _ h, mul_zero]

theorem integral_shift_mul_shift_eq_autocorr (g : ℝ → ℝ) (t s : ℝ) :
    (∫ u, g (u + t) * g (u + s)) = autocorr g (s - t) := by
  unfold autocorr
  rw [← integral_add_right_eq_self (μ := volume) (fun u => g u * g (u + (s - t))) t]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show g (u + t) * g (u + s) = g (u + t) * g (u + t + (s - t))
  rw [show u + t + (s - t) = u + s by ring]

/-! ## The causal kernel inverts the gauge derivative -/

/-- **Causal reconstruction:** `f(u) = −∫ K(t) (f' − f/2)(u + t) dt` for compact `C¹` sources. -/
theorem causal_reconstruction (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (u : ℝ) :
    (∫ t, causalKernel t * gaugeDerivative f (u + t)) = -f u := by
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) :=
    hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hexp : Continuous fun t : ℝ => Real.exp (-t / 2) :=
    Real.continuous_exp.comp (continuous_id.neg.div_const 2)
  have hFc : Continuous fun t => Real.exp (-t / 2) * f (u + t) :=
    hexp.mul (f.continuous.comp (continuous_const.add continuous_id))
  have hF'c : Continuous fun t => Real.exp (-t / 2) * gaugeDerivative f (u + t) :=
    hexp.mul (hgc.comp (continuous_const.add continuous_id))
  have hF's : HasCompactSupport fun t => Real.exp (-t / 2) * gaugeDerivative f (u + t) :=
    (hasCompactSupport_comp_const_add hgs u).mul_left
  have hlim : Tendsto (fun t => Real.exp (-t / 2) * f (u + t)) atTop (𝓝 0) :=
    tendsto_mul_comp_const_add_atTop f.hasCompactSupport u
  have hint : IntegrableOn (fun t => Real.exp (-t / 2) * gaugeDerivative f (u + t)) (Ioi 0) :=
    (hF'c.integrable_of_hasCompactSupport hF's).integrableOn
  have h1 : (∫ t, causalKernel t * gaugeDerivative f (u + t)) =
      ∫ t in Ici (0 : ℝ), causalKernel t * gaugeDerivative f (u + t) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [causalKernel_of_neg (not_le.1 ht), zero_mul]
  have h2 : (∫ t in Ici (0 : ℝ), causalKernel t * gaugeDerivative f (u + t)) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * gaugeDerivative f (u + t) := by
    rw [integral_Ici_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    show causalKernel t * gaugeDerivative f (u + t) = Real.exp (-t / 2) * gaugeDerivative f (u + t)
    rw [causalKernel_of_nonneg (le_of_lt ht)]
  rw [h1, h2, integral_Ioi_of_hasDerivAt_of_tendsto hFc.continuousWithinAt
    (fun t _ => hasDerivAt_exp_neg_half_mul hf u t) hint hlim]
  simp

/-- Shifted causal reconstruction: `f(u + s) = −∫ K(t − s) g(u + t) dt`. -/
theorem causal_reconstruction_shift (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (u s : ℝ) :
    (∫ t, causalKernel (t - s) * gaugeDerivative f (u + t)) = -f (u + s) := by
  rw [← causal_reconstruction f hf (u + s), ← integral_sub_right_eq_self (μ := volume)
    (fun t => causalKernel t * gaugeDerivative f (u + s + t)) s]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show causalKernel (t - s) * gaugeDerivative f (u + t) =
    causalKernel (t - s) * gaugeDerivative f (u + s + (t - s))
  rw [show u + s + (t - s) = u + t by ring]

/-! ## The packet as a correlation of the causal response -/

/-- **The signed packet is the causal response correlated with the gauge derivative.** -/
theorem signedSource_eq_neg_integral_causalResponse (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) (u : ℝ) :
    signedSource f N u = -∫ t, causalResponse N t * gaugeDerivative f (u + t) := by
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) :=
    hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hgu : Integrable fun t => gaugeDerivative f (u + t) :=
    (hgc.comp (continuous_const.add continuous_id)).integrable_of_hasCompactSupport
      (hasCompactSupport_comp_const_add hgs u)
  have h1 : signedSource f N u = pairing N fun s => f (u + s) := rfl
  have h2 : ∀ s, f (u + s) =
      (-1 : ℝ) * ∫ t, causalKernel (t - s) * gaugeDerivative f (u + t) := by
    intro s
    rw [causal_reconstruction_shift f hf u s]; ring
  have h4 : (∫ t, pairing N fun s => causalKernel (t - s) * gaugeDerivative f (u + t)) =
      pairing N fun s => ∫ t, causalKernel (t - s) * gaugeDerivative f (u + t) := by
    refine integral_pairing_of_dominated N _ ?_ hgu (C := 1) fun t s => ?_
    · exact (measurable_causalKernel.comp (measurable_fst.sub measurable_snd)).mul
        (hgc.measurable.comp (measurable_const.add measurable_fst))
    · rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_left (abs_causalKernel_le_one _) (abs_nonneg _)
  rw [h1, pairing_congr_window N (fun s _ => h2 s), pairing_const_mul, neg_one_mul, ← h4]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show (pairing N fun s => causalKernel (t - s) * gaugeDerivative f (u + t)) =
    (pairing N fun s => causalKernel (t - s)) * gaugeDerivative f (u + t)
  exact pairing_mul_const N _ _

/-! ## Exchange of an integrable weight against a shifted bounded kernel -/

/-- Fubini for `∫ φ(u) ∫ R(t) g(u + t)`, with `φ, R ∈ L¹` and `g` bounded. -/
theorem integral_integral_shift_swap {φ R : ℝ → ℝ} (hφ : Integrable φ) (hφm : Measurable φ)
    (hR : Integrable R) (hRm : Measurable R) {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) :
    (∫ u, φ u * ∫ t, R t * g (u + t)) = ∫ t, R t * ∫ u, φ u * g (u + t) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun u t => φ u * (R t * g (u + t)))
      (volume.prod volume) :=
    ((hφm.comp measurable_fst).mul ((hRm.comp measurable_snd).mul
      (hg.comp (measurable_fst.add measurable_snd)))).aestronglyMeasurable
  have hprod : Integrable (Function.uncurry fun u t => φ u * (R t * g (u + t)))
      (volume.prod volume) := by
    refine Integrable.mono' (hφ.norm.mul_prod (hR.norm.mul_const M)) hmeas
      (Eventually.of_forall fun p => ?_)
    show |φ p.1 * (R p.2 * g (p.1 + p.2))| ≤ ‖φ p.1‖ * (‖R p.2‖ * M)
    rw [abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hgM _) (abs_nonneg _)) (abs_nonneg _)
  calc (∫ u, φ u * ∫ t, R t * g (u + t)) = ∫ u, ∫ t, φ u * (R t * g (u + t)) := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        show φ u * ∫ t, R t * g (u + t) = ∫ t, φ u * (R t * g (u + t))
        exact (integral_const_mul _ _).symm
    _ = ∫ t, ∫ u, φ u * (R t * g (u + t)) := integral_integral_swap hprod
    _ = ∫ t, R t * ∫ u, φ u * g (u + t) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show (∫ u, φ u * (R t * g (u + t))) = R t * ∫ u, φ u * g (u + t)
        rw [← integral_const_mul]
        exact integral_congr_ae (Eventually.of_forall fun u => by ring)

/-! ## Gram and autocorrelation forms of the packet energy -/

theorem abs_causalResponse_le_const (N : ℕ) (t : ℝ) :
    |causalResponse N t| ≤ mass N * Real.exp (cutoff N / 2) :=
  (abs_causalResponse_le N t).trans
    (mul_le_of_le_one_right (mul_nonneg (mass_nonneg N) (Real.exp_pos _).le)
      (causalKernel_le_one t))

/-- **Gram form:** the packet energy is the Gram energy of the causal response against the
autocorrelation of the gauge derivative. -/
theorem packetEnergy_eq_causal_gram (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    packetEnergy f N =
      ∫ t, causalResponse N t *
        ∫ s, causalResponse N s * autocorr (gaugeDerivative f) (s - t) := by
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) :=
    hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hgm : Measurable (gaugeDerivative f) := hgc.measurable
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  have hgM : ∀ x, |gaugeDerivative f x| ≤ M := fun x => by
    rw [← Real.norm_eq_abs]; exact hM x
  have hRi : Integrable (causalResponse N) := integrable_causalResponse N
  have hRm : Measurable (causalResponse N) := measurable_causalResponse N
  have hSeq : ∀ u, signedSource f N u =
      -∫ t, causalResponse N t * gaugeDerivative f (u + t) :=
    fun u => signedSource_eq_neg_integral_causalResponse f hf N u
  have hSi : Integrable ((signedSource f N : C_c(ℝ, ℝ)) : ℝ → ℝ) :=
    (signedSource f N).continuous.integrable_of_hasCompactSupport
      (signedSource f N).hasCompactSupport
  have hSm : Measurable ((signedSource f N : C_c(ℝ, ℝ)) : ℝ → ℝ) :=
    (signedSource f N).continuous.measurable
  have h0 : packetEnergy f N = ∫ u, signedSource f N u * signedSource f N u := by
    unfold packetEnergy autocorr
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show signedSource f N u * signedSource f N (u + 0) = signedSource f N u * signedSource f N u
    rw [add_zero]
  have h1 : (∫ u, signedSource f N u * signedSource f N u) =
      -∫ t, causalResponse N t * ∫ u, signedSource f N u * gaugeDerivative f (u + t) := by
    rw [← integral_integral_shift_swap hSi hSm hRi hRm hgm hgM, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show signedSource f N u * signedSource f N u =
      -(signedSource f N u * ∫ t, causalResponse N t * gaugeDerivative f (u + t))
    rw [hSeq u]; ring
  have h2 : ∀ t, (∫ u, signedSource f N u * gaugeDerivative f (u + t)) =
      -∫ s, causalResponse N s * autocorr (gaugeDerivative f) (s - t) := by
    intro t
    have hgt : Integrable fun u => gaugeDerivative f (u + t) :=
      (hgc.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_add hgs t)
    have hgtm : Measurable fun u => gaugeDerivative f (u + t) :=
      hgm.comp (measurable_id.add_const t)
    calc (∫ u, signedSource f N u * gaugeDerivative f (u + t))
        = -∫ u, gaugeDerivative f (u + t) *
            ∫ s, causalResponse N s * gaugeDerivative f (u + s) := by
          rw [← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          show signedSource f N u * gaugeDerivative f (u + t) =
            -(gaugeDerivative f (u + t) * ∫ s, causalResponse N s * gaugeDerivative f (u + s))
          rw [hSeq u]; ring
      _ = -∫ s, causalResponse N s * ∫ u, gaugeDerivative f (u + t) * gaugeDerivative f (u + s) := by
          rw [integral_integral_shift_swap hgt hgtm hRi hRm hgm hgM]
      _ = -∫ s, causalResponse N s * autocorr (gaugeDerivative f) (s - t) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun s => ?_)
          show causalResponse N s * (∫ u, gaugeDerivative f (u + t) * gaugeDerivative f (u + s)) =
            causalResponse N s * autocorr (gaugeDerivative f) (s - t)
          rw [integral_shift_mul_shift_eq_autocorr]
  rw [h0, h1]
  rw [show (fun t => causalResponse N t * ∫ u, signedSource f N u * gaugeDerivative f (u + t)) =
      fun t => -(causalResponse N t * ∫ s, causalResponse N s * autocorr (gaugeDerivative f) (s - t))
      from funext fun t => by rw [h2 t]; ring]
  rw [integral_neg, neg_neg]

/-- **Autocorrelation form:** `packetEnergy f N = ⟨autocorr (f' − f/2), autocorr R_N⟩_{L²}`. -/
theorem packetEnergy_eq_integral_autocorr_mul_autocorr (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    packetEnergy f N =
      ∫ y, autocorr (gaugeDerivative f) y * autocorr (causalResponse N) y := by
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) :=
    hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hhc : Continuous (autocorr (gaugeDerivative f)) :=
    GaloisForLFunctions.BiScaleUncertainty.continuous_autocorr_compact ⟨⟨_, hgc⟩, hgs⟩
  have hhi : Integrable (autocorr (gaugeDerivative f)) :=
    hhc.integrable_of_hasCompactSupport (hasCompactSupport_autocorr hgs)
  have hRi : Integrable (causalResponse N) := integrable_causalResponse N
  have hRm : Measurable (causalResponse N) := measurable_causalResponse N
  rw [packetEnergy_eq_causal_gram f hf N]
  calc (∫ t, causalResponse N t * ∫ s, causalResponse N s * autocorr (gaugeDerivative f) (s - t))
      = ∫ t, causalResponse N t * ∫ y, autocorr (gaugeDerivative f) y * causalResponse N (t + y) := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        show causalResponse N t * (∫ s, causalResponse N s * autocorr (gaugeDerivative f) (s - t)) =
          causalResponse N t * ∫ y, autocorr (gaugeDerivative f) y * causalResponse N (t + y)
        congr 1
        rw [← integral_add_left_eq_self (μ := volume)
          (fun s => causalResponse N s * autocorr (gaugeDerivative f) (s - t)) t]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show causalResponse N (t + y) * autocorr (gaugeDerivative f) (t + y - t) =
          autocorr (gaugeDerivative f) y * causalResponse N (t + y)
        rw [add_sub_cancel_left, mul_comm]
    _ = ∫ y, autocorr (gaugeDerivative f) y * ∫ t, causalResponse N t * causalResponse N (t + y) :=
        integral_integral_shift_swap hRi hRm hhi hhc.measurable hRm (abs_causalResponse_le_const N)
    _ = ∫ y, autocorr (gaugeDerivative f) y * autocorr (causalResponse N) y := rfl

/-! ## Young's bound by the Laplace energy -/

/-- **Every compact packet energy is bounded by the Laplace Gram energy:**
`packetEnergy f N ≤ ‖f' − f/2‖₁² · laplaceEnergy N`. -/
theorem packetEnergy_le_laplaceEnergy (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    packetEnergy f N ≤ (∫ t, |gaugeDerivative f t|) ^ 2 * laplaceEnergy N := by
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) :=
    hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hgi : Integrable (gaugeDerivative f) := hgc.integrable_of_hasCompactSupport hgs
  have hRm : Measurable (causalResponse N) := measurable_causalResponse N
  have hSeq : ∀ u, signedSource f N u =
      -∫ t, causalResponse N t * gaugeDerivative f (u + t) :=
    fun u => signedSource_eq_neg_integral_causalResponse f hf N u
  -- the packet is a line convolution of `g` with the reflected response
  have hconv : ∀ u, GaloisForLFunctions.HTGeometry.lineConvolution (gaugeDerivative f)
      (fun x => causalResponse N (-x)) u = ∫ t, causalResponse N t * gaugeDerivative f (u + t) := by
    intro u
    unfold GaloisForLFunctions.HTGeometry.lineConvolution
    rw [← integral_add_left_eq_self (μ := volume)
      (fun t => gaugeDerivative f t * causalResponse N (-(u - t))) u]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show gaugeDerivative f (u + t) * causalResponse N (-(u - (u + t))) =
      causalResponse N t * gaugeDerivative f (u + t)
    rw [show -(u - (u + t)) = t by ring, mul_comm]
  have hS2 : ∀ u, signedSource f N u ^ 2 = GaloisForLFunctions.HTGeometry.lineConvolution
      (gaugeDerivative f) (fun x => causalResponse N (-x)) u ^ 2 := fun u => by
    rw [hconv, hSeq u, neg_sq]
  have h0 : packetEnergy f N = ∫ u, signedSource f N u ^ 2 := by
    unfold packetEnergy autocorr
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show signedSource f N u * signedSource f N (u + 0) = signedSource f N u ^ 2
    rw [add_zero, sq]
  have hRneg : (∫ x, causalResponse N (-x) ^ 2) = ∫ t, causalResponse N t ^ 2 :=
    integral_neg_eq_self (μ := volume) fun t => causalResponse N t ^ 2
  have hconv2 : Integrable fun u => GaloisForLFunctions.HTGeometry.lineConvolution
      (gaugeDerivative f) (fun x => causalResponse N (-x)) u ^ 2 :=
    (integrable_sq (signedSource f N).continuous (signedSource f N).hasCompactSupport).congr
      (Eventually.of_forall fun u => hS2 u)
  rw [h0, ← integral_sq_causalResponse_eq_laplaceEnergy, ← hRneg]
  calc (∫ u, signedSource f N u ^ 2)
      = ∫ u, GaloisForLFunctions.HTGeometry.lineConvolution (gaugeDerivative f)
          (fun x => causalResponse N (-x)) u ^ 2 :=
        integral_congr_ae (Eventually.of_forall hS2)
    _ ≤ (∫ t, |gaugeDerivative f t|) ^ 2 * ∫ x, causalResponse N (-x) ^ 2 :=
        GaloisForLFunctions.HTGeometry.integral_sq_lineConvolution_le hgc.measurable
          (hRm.comp measurable_neg) hgi.abs (integrable_sq_causalResponse N).comp_neg hconv2

/-! ## Green's identity for the gauge derivative -/

/-- **Green's identity:** `autocorr f (x) = ∫ autocorr (f' − f/2)(y) e^{−|x + y|/2} dy`. -/
theorem autocorr_eq_integral_autocorr_gauge_mul_laplace (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (x : ℝ) :
    autocorr f x = ∫ y, autocorr (gaugeDerivative f) y * laplaceKernel (x + y) := by
  have hgc : Continuous (gaugeDerivative f) := continuous_gaugeDerivative hf
  have hgs : HasCompactSupport (gaugeDerivative f) :=
    hasCompactSupport_gaugeDerivative f.hasCompactSupport
  have hgm : Measurable (gaugeDerivative f) := hgc.measurable
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  have hgM : ∀ y, |gaugeDerivative f y| ≤ M := fun y => by
    rw [← Real.norm_eq_abs]; exact hM y
  have hhc : Continuous (autocorr (gaugeDerivative f)) :=
    GaloisForLFunctions.BiScaleUncertainty.continuous_autocorr_compact ⟨⟨_, hgc⟩, hgs⟩
  have hhi : Integrable (autocorr (gaugeDerivative f)) :=
    hhc.integrable_of_hasCompactSupport (hasCompactSupport_autocorr hgs)
  have hfi : Integrable (f : ℝ → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hKx : Integrable fun s => causalKernel (s - x) := integrable_causalKernel.comp_sub_right x
  have hKxm : Measurable fun s => causalKernel (s - x) :=
    measurable_causalKernel.comp (measurable_id.sub_const x)
  -- step 1: `∫ f(u) g(u + s) du = −∫ K(t) autocorr g (t − s) dt`
  have h1 : ∀ s, (∫ u, f u * gaugeDerivative f (u + s)) =
      -∫ t, causalKernel t * autocorr (gaugeDerivative f) (t - s) := by
    intro s
    have hgsI : Integrable fun u => gaugeDerivative f (u + s) :=
      (hgc.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_add hgs s)
    have hgsm : Measurable fun u => gaugeDerivative f (u + s) := hgm.comp (measurable_id.add_const s)
    calc (∫ u, f u * gaugeDerivative f (u + s))
        = -∫ u, gaugeDerivative f (u + s) * ∫ t, causalKernel t * gaugeDerivative f (u + t) := by
          rw [← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          show f u * gaugeDerivative f (u + s) =
            -(gaugeDerivative f (u + s) * ∫ t, causalKernel t * gaugeDerivative f (u + t))
          rw [causal_reconstruction f hf u]; ring
      _ = -∫ t, causalKernel t * ∫ u, gaugeDerivative f (u + s) * gaugeDerivative f (u + t) := by
          rw [integral_integral_shift_swap hgsI hgsm integrable_causalKernel measurable_causalKernel
            hgm hgM]
      _ = -∫ t, causalKernel t * autocorr (gaugeDerivative f) (t - s) := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          show causalKernel t * (∫ u, gaugeDerivative f (u + s) * gaugeDerivative f (u + t)) =
            causalKernel t * autocorr (gaugeDerivative f) (t - s)
          rw [integral_shift_mul_shift_eq_autocorr]
  -- step 2: `autocorr f x = ∫ K(s − x) ∫ K(t) h(t − s)`
  have h2 : autocorr f x =
      ∫ s, causalKernel (s - x) * ∫ t, causalKernel t * autocorr (gaugeDerivative f) (t - s) := by
    unfold autocorr
    calc (∫ u, f u * f (u + x))
        = -∫ u, f u * ∫ s, causalKernel (s - x) * gaugeDerivative f (u + s) := by
          rw [← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun u => ?_)
          show f u * f (u + x) = -(f u * ∫ s, causalKernel (s - x) * gaugeDerivative f (u + s))
          rw [causal_reconstruction_shift f hf u x]; ring
      _ = -∫ s, causalKernel (s - x) * ∫ u, f u * gaugeDerivative f (u + s) := by
          rw [integral_integral_shift_swap hfi f.continuous.measurable hKx hKxm hgm hgM]
      _ = ∫ s, causalKernel (s - x) * ∫ t, causalKernel t * autocorr (gaugeDerivative f) (t - s) := by
          rw [← integral_neg]
          refine integral_congr_ae (Eventually.of_forall fun s => ?_)
          show -(causalKernel (s - x) * ∫ u, f u * gaugeDerivative f (u + s)) =
            causalKernel (s - x) * ∫ t, causalKernel t * autocorr (gaugeDerivative f) (t - s)
          rw [h1 s]; ring
  -- step 3: substitute `t = s + y` and swap
  have h3 : ∀ s, (∫ t, causalKernel t * autocorr (gaugeDerivative f) (t - s)) =
      ∫ y, autocorr (gaugeDerivative f) y * causalKernel (s + y) := by
    intro s
    rw [← integral_add_left_eq_self (μ := volume)
      (fun t => causalKernel t * autocorr (gaugeDerivative f) (t - s)) s]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show causalKernel (s + y) * autocorr (gaugeDerivative f) (s + y - s) =
      autocorr (gaugeDerivative f) y * causalKernel (s + y)
    rw [add_sub_cancel_left, mul_comm]
  rw [h2]
  simp_rw [h3]
  rw [integral_integral_shift_swap hKx hKxm hhi hhc.measurable measurable_causalKernel
    abs_causalKernel_le_one]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show autocorr (gaugeDerivative f) y * (∫ s, causalKernel (s - x) * causalKernel (s + y)) =
    autocorr (gaugeDerivative f) y * laplaceKernel (x + y)
  congr 1
  have := integral_causalKernel_mul x (-y)
  simp only [sub_neg_eq_add] at this
  rw [this]

/-- Convolution form of Green's identity: `autocorr f = autocorr (f' − f/2) ⋆ e^{−|·|/2}`. -/
theorem autocorr_eq_laplace_convolution (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (x : ℝ) :
    autocorr f x = ∫ y, laplaceKernel y * autocorr (gaugeDerivative f) (x - y) := by
  rw [autocorr_eq_integral_autocorr_gauge_mul_laplace f hf x,
    ← integral_add_right_eq_self (μ := volume)
      (fun y => laplaceKernel y * autocorr (gaugeDerivative f) (x - y)) x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show autocorr (gaugeDerivative f) y * laplaceKernel (x + y) =
    laplaceKernel (y + x) * autocorr (gaugeDerivative f) (x - (y + x))
  rw [show x - (y + x) = -y by ring, autocorr_neg, add_comm x y, mul_comm]

/-- The Laplace kernel is the Gram kernel of the field's compact sources in the gauge: the
compact packet energy of `f` is the energy of `ν_N` against `autocorr g ⋆ laplaceKernel`. -/
theorem packetEnergy_eq_pairing_laplace_convolution (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 1 (f : ℝ → ℝ)) (N : ℕ) :
    packetEnergy f N = pairing N fun t => pairing N fun s =>
      ∫ y, laplaceKernel y * autocorr (gaugeDerivative f) (s - t - y) := by
  rw [packetEnergy_eq_iterated_pairing]
  congr 1
  funext t
  congr 1
  funext s
  exact autocorr_eq_laplace_convolution f hf (s - t)

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
