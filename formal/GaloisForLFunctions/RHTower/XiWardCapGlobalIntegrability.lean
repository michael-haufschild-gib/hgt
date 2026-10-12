import GaloisForLFunctions.RHTower.XiLogDerivLineIntegrability
import GaloisForLFunctions.RHTower.XiWardSchwarzCapSourcePairing
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.SeamFluxCompletion

/-!
# The global Ward cap integrals converge absolutely for almost every canonical level

The WD route needs a *global one-sided cap family with uniform integrability*.  The finite caps

  `I_H(τ, s) = ∫_{−H}^{H} K_τ(x) · T(x − θ(s) i) dx`

(`xiWardSchwarzCapFactorIntegral`) pair the Schwarz two-pole kernel `K_τ` with the literal completed
prime–archimedean source trace `T` on the lower cap line at the canonical level
`θ(s) = ¼ + arctan(s)/(2π) ∈ (0, ½)`.  The corpus had them only as interval integrals
(`ae_forall_intervalIntegrable_xiWardSchwarzCapFactor`).  This file settles the integrability half
of the Need.

**Theorem** (`ae_forall_integrable_xiWardSchwarzCapFactor`).  For almost every canonical parameter
`s`, for every `τ`, the cap integrand is absolutely integrable on `ℝ`.  Consequently
(`ae_forall_tendsto_xiWardSchwarzCapFactorIntegral`) the finite caps converge as `H → ∞`, uniformly
in nothing more than `τ` being fixed, to the global cap `∫_ℝ K_τ T`.

The ingredients:
* on the cap line `T(x − θ i) = i · ξ'/ξ(½ + θ + ix)` off the countably many zeros
  (`continuedPrimeArchSourceRelativeTrace_capLine`);
* `|K_τ(x)| ≤ 31 |τ| (1 + τ²) / (1 + x²)` (`norm_xiWardSchwarzCapDifference_le`);
* `∫ |ξ'/ξ(σ + ix)| / (1 + x²) dx < ∞` for almost every `σ ∈ (½, 1)`
  (`ae_integrable_norm_logDeriv_xi_line`);
* the canonical chart `s ↦ θ(s)` pulls null sets back to null sets
  (`ae_comp_xiWardTransverseLevel`).

What remains of the Need is the one-sided sign of the global cap, which carries RH.
-/

open Complex MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-! ## The canonical chart pulls null sets back to null sets -/

theorem xiWardTransverseCoordinate_level (t : ℝ) :
    xiWardTransverseCoordinate (xiWardTransverseLevel t) = t := by
  unfold xiWardTransverseCoordinate xiWardTransverseLevel
  rw [show 2 * Real.pi * (1 / 4 + Real.arctan t / (2 * Real.pi) - 1 / 4) = Real.arctan t by
    field_simp [Real.pi_ne_zero]; ring]
  exact Real.tan_arctan t

theorem differentiableOn_xiWardTransverseCoordinate :
    DifferentiableOn ℝ xiWardTransverseCoordinate (Ioo (0 : ℝ) (1 / 2)) := by
  intro a ha
  have hcos : Real.cos (2 * Real.pi * (a - 1 / 4)) ≠ 0 := by
    apply (Real.cos_pos_of_mem_Ioo ⟨_, _⟩).ne'
    · nlinarith [Real.pi_pos, ha.1]
    · nlinarith [Real.pi_pos, ha.2]
  have hinner : DifferentiableAt ℝ (fun a : ℝ => 2 * Real.pi * (a - 1 / 4)) a := by fun_prop
  exact (DifferentiableAt.comp (g := Real.tan) a (Real.differentiableAt_tan.mpr hcos)
    hinner).differentiableWithinAt

/-- **Transfer.**  A property of almost every level in `(0, ½)` holds at the canonical level of
almost every parameter. -/
theorem ae_comp_xiWardTransverseLevel {P : ℝ → Prop}
    (h : ∀ᵐ a ∂(volume : Measure ℝ), a ∈ Ioo (0 : ℝ) (1 / 2) → P a) :
    ∀ᵐ t ∂(volume : Measure ℝ), P (xiWardTransverseLevel t) := by
  set N : Set ℝ := {a | ¬ (a ∈ Ioo (0 : ℝ) (1 / 2) → P a)} with hN
  have hN0 : volume N = 0 := by rw [ae_iff] at h; exact h
  have himg : volume (xiWardTransverseCoordinate '' (N ∩ Ioo (0 : ℝ) (1 / 2))) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (differentiableOn_xiWardTransverseCoordinate.mono inter_subset_right)
      (measure_mono_null inter_subset_left hN0)
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) himg
  have hmem := xiWardTransverseLevel_mem_Ioo t
  refine ⟨xiWardTransverseLevel t, ⟨fun hP => ht (hP hmem), hmem⟩, xiWardTransverseCoordinate_level t⟩

/-! ## The kernel decays like `1/x²` -/

/-- `|K_τ(x)| ≤ 31 |τ| (1 + τ²) / (1 + x²)`. -/
theorem norm_xiWardSchwarzCapDifference_le (tau s x : ℝ) :
    ‖xiWardSchwarzCapDifference tau s x‖ ≤ 31 * |tau| * (1 + tau ^ 2) / (1 + x ^ 2) := by
  rw [xiWardSchwarzCapDifference_eq]
  set a : ℝ := 51 / 100 + xiWardTransverseLevel s with ha
  have hlev := xiWardTransverseLevel_mem_Ioo s
  have ha0 : 51 / 100 ≤ a := by rw [ha]; linarith [hlev.1]
  have ha1 : a ≤ 2 := by rw [ha]; linarith [hlev.2]
  have hn : ∀ y : ℝ, ‖((a : ℝ) : ℂ) + I * ((y : ℝ) : ℂ)‖ = Real.sqrt (a ^ 2 + y ^ 2) := by
    intro y
    rw [show ((a : ℝ) : ℂ) + I * ((y : ℝ) : ℂ) = (a : ℂ) + (y : ℂ) * I by ring, Complex.norm_def,
      Complex.normSq_add_mul_I]
  have hD : ‖(((a : ℝ) : ℂ) + I * ((tau + x : ℝ) : ℂ)) * (((a : ℝ) : ℂ) + I * ((x - tau : ℝ) : ℂ))‖ =
      Real.sqrt (a ^ 2 + (tau + x) ^ 2) * Real.sqrt (a ^ 2 + (x - tau) ^ 2) := by
    rw [norm_mul, hn, hn]
  rw [norm_mul, norm_inv, hD]
  have hP : (0.13 * (1 + x ^ 2) / (1 + tau ^ 2)) ^ 2 ≤
      (a ^ 2 + (tau + x) ^ 2) * (a ^ 2 + (x - tau) ^ 2) := by
    have hP1 : (x ^ 2 - tau ^ 2) ^ 2 ≤ (a ^ 2 + (tau + x) ^ 2) * (a ^ 2 + (x - tau) ^ 2) := by
      nlinarith [sq_nonneg a, sq_nonneg (tau + x), sq_nonneg (x - tau), sq_nonneg (a * (tau + x)),
        sq_nonneg (a * (x - tau))]
    have hP2 : a ^ 4 ≤ (a ^ 2 + (tau + x) ^ 2) * (a ^ 2 + (x - tau) ^ 2) := by
      nlinarith [sq_nonneg (tau + x), sq_nonneg (x - tau), sq_nonneg a,
        mul_nonneg (sq_nonneg (tau + x)) (sq_nonneg (x - tau))]
    have ha2 : (0.2601 : ℝ) ≤ a ^ 2 := by nlinarith
    have ha4 : (0.0676 : ℝ) ≤ a ^ 4 := by
      have : a ^ 4 = (a ^ 2) ^ 2 := by ring
      rw [this]; nlinarith
    have hT : 0 < 1 + tau ^ 2 := by positivity
    rw [div_pow, div_le_iff₀ (by positivity)]
    by_cases hx : 2 * tau ^ 2 + 1 ≤ x ^ 2
    · have h1 : (1 + x ^ 2) / 2 ≤ x ^ 2 - tau ^ 2 := by linarith
      have h2 : ((1 + x ^ 2) / 2) ^ 2 ≤ (x ^ 2 - tau ^ 2) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) h1
      nlinarith [sq_nonneg tau, mul_le_mul_of_nonneg_left (by nlinarith : (1 : ℝ) ≤ (1 + tau ^ 2) ^ 2)
        (sq_nonneg (1 + x ^ 2))]
    · push Not at hx
      have h3 : (1 + x ^ 2) ^ 2 ≤ 4 * (1 + tau ^ 2) ^ 2 := by nlinarith
      nlinarith
  have hsqrt : 0.13 * (1 + x ^ 2) / (1 + tau ^ 2) ≤
      Real.sqrt (a ^ 2 + (tau + x) ^ 2) * Real.sqrt (a ^ 2 + (x - tau) ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.le_sqrt_of_sq_le hP
  have hpos : 0 < 0.13 * (1 + x ^ 2) / (1 + tau ^ 2) := by positivity
  have hnum : ‖-4 * I * (tau : ℂ)‖ = 4 * |tau| := by
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  rw [hnum]
  calc 4 * |tau| * (Real.sqrt (a ^ 2 + (tau + x) ^ 2) * Real.sqrt (a ^ 2 + (x - tau) ^ 2))⁻¹
      ≤ 4 * |tau| * (0.13 * (1 + x ^ 2) / (1 + tau ^ 2))⁻¹ := by
        gcongr
    _ ≤ 31 * |tau| * (1 + tau ^ 2) / (1 + x ^ 2) := by
        rw [inv_div, div_eq_mul_inv]
        have hx : 0 < 1 + x ^ 2 := by positivity
        field_simp
        nlinarith [abs_nonneg tau, sq_nonneg tau]

/-! ## The source trace on the cap line -/

theorem lowerCapPoint_mul_I (s x : ℝ) :
    1 / 2 + xiWardLowerCapPoint s x * I = ((1 / 2 + xiWardTransverseLevel s : ℝ) : ℂ) + x * I := by
  unfold xiWardLowerCapPoint
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- **The trace on the cap line.**  Off the zeros of `ζ`, `T(x − θ i) = i · ξ'/ξ(½ + θ + ix)`. -/
theorem continuedPrimeArchSourceRelativeTrace_capLine (s x : ℝ)
    (hzeta : riemannZeta (((1 / 2 + xiWardTransverseLevel s : ℝ) : ℂ) + x * I) ≠ 0) :
    continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) =
      I * logDeriv xi (((1 / 2 + xiWardTransverseLevel s : ℝ) : ℂ) + x * I) := by
  have hlev := xiWardTransverseLevel_mem_Ioo s
  set w : ℂ := ((1 / 2 + xiWardTransverseLevel s : ℝ) : ℂ) + x * I with hw
  have hre : w.re = 1 / 2 + xiWardTransverseLevel s := by simp [hw]
  have hspos : 0 < w.re := by rw [hre]; linarith [hlev.1]
  have hs1 : w ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre, Complex.one_re] at this; linarith [hlev.2]
  have hseam := seamFluxCochain_eq_continuedPrime_add_archimedean hspos hs1 hzeta
  rw [seamFluxCochain] at hseam
  unfold continuedPrimeArchSourceRelativeTrace
  rw [lowerCapPoint_mul_I, ← hw, ← hseam]
  ring

/-- The zeros of `ζ` on a vertical line inside the strip form a countable set of heights. -/
theorem countable_setOf_riemannZeta_line_eq_zero {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    {x : ℝ | riemannZeta ((σ : ℂ) + x * I) = 0}.Countable := by
  refine (Set.countable_range fun q : XiZeroCopy => (q.1 : ℂ).im).mono fun x hx => ?_
  set w : ℂ := (σ : ℂ) + x * I with hw
  have hre : w.re = σ := by simp [hw]
  have hw0 : w ≠ 0 := by intro h; have := congrArg Complex.re h; simp [hre] at this; linarith
  have hw1 : w ≠ 1 := by intro h; have := congrArg Complex.re h; simp [hre] at this; linarith
  have hxi : xi w = 0 := by
    rw [xi_eq_archFactor_mul_zeta hw0 hw1 (Gammaℝ_ne_zero_of_re_pos (by rw [hre]; exact h0))]
    rw [show riemannZeta w = 0 from hx, mul_zero]
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  refine ⟨q, ?_⟩
  show (q.1 : ℂ).im = x
  rw [hq]; simp [hw]

/-! ## Global integrability -/

/-- **The global Ward caps are absolutely integrable for almost every canonical level.** -/
theorem ae_forall_integrable_xiWardSchwarzCapFactor :
    ∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ tau : ℝ,
      Integrable fun x : ℝ => xiWardSchwarzCapDifference tau s x *
        continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x) := by
  set g : ℝ → ℝ → ℝ := fun σ x => ‖logDeriv xi ((σ : ℂ) + x * I)‖ / (1 + x ^ 2) with hg
  have h1 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (1 / 2 : ℝ) 1 → Integrable (g σ) :=
    ae_integrable_norm_logDeriv_xi_line
  have h2 : ∀ᵐ a ∂(volume : Measure ℝ), a ∈ Ioo (0 : ℝ) (1 / 2) → Integrable (g (1 / 2 + a)) := by
    have := (measurePreserving_add_right (volume : Measure ℝ) (1 / 2)).quasiMeasurePreserving.ae h1
    filter_upwards [this] with a ha hmem
    rw [add_comm]
    exact ha ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  filter_upwards [ae_comp_xiWardTransverseLevel h2] with s hs tau
  set σ : ℝ := 1 / 2 + xiWardTransverseLevel s with hσ
  have hlev := xiWardTransverseLevel_mem_Ioo s
  set K : ℝ := 31 * |tau| * (1 + tau ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the integrand agrees almost everywhere with a measurable function
  set F : ℝ → ℂ := fun x => xiWardSchwarzCapDifference tau s x * (I * logDeriv xi ((σ : ℂ) + x * I))
    with hF
  have hZ : (volume : Measure ℝ) {x : ℝ | riemannZeta ((σ : ℂ) + x * I) = 0} = 0 :=
    (countable_setOf_riemannZeta_line_eq_zero (σ := σ) (by rw [hσ]; linarith [hlev.1])
      (by rw [hσ]; linarith [hlev.2])).measure_zero _
  have hae : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), riemannZeta ((σ : ℂ) + (x : ℂ) * I) ≠ 0 := by
    rw [ae_iff]; simpa using hZ
  have heq : (fun x : ℝ => xiWardSchwarzCapDifference tau s x *
      continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x)) =ᵐ[volume] F := by
    filter_upwards [hae] with x hx
    simp only [hF]
    rw [continuedPrimeArchSourceRelativeTrace_capLine s x hx]
  have hFmeas : AEStronglyMeasurable F volume := by
    have hl : Measurable (logDeriv xi) := by
      have h1' : Measurable (deriv xi) := xi_differentiable.deriv.continuous.measurable
      have h2' : Measurable xi := xi_differentiable.continuous.measurable
      simpa [logDeriv] using h1'.div h2'
    have hp : Measurable fun x : ℝ => (σ : ℂ) + x * I := by fun_prop
    exact ((continuous_xiWardSchwarzCapDifference tau s).measurable.mul
      (measurable_const.mul (hl.comp hp))).aestronglyMeasurable
  refine (Integrable.mono' ((hs).const_mul K) hFmeas (Eventually.of_forall fun x => ?_)).congr
    heq.symm
  simp only [hF, norm_mul, Complex.norm_I, one_mul]
  have hk := norm_xiWardSchwarzCapDifference_le tau s x
  calc ‖xiWardSchwarzCapDifference tau s x‖ * ‖logDeriv xi ((σ : ℂ) + x * I)‖
      ≤ K / (1 + x ^ 2) * ‖logDeriv xi ((σ : ℂ) + x * I)‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg _)
    _ = K * g (1 / 2 + xiWardTransverseLevel s) x := by
        simp only [hg, hσ]; ring

/-- **The finite caps converge to the global cap.** -/
theorem ae_forall_tendsto_xiWardSchwarzCapFactorIntegral :
    ∀ᵐ s : ℝ ∂(volume : Measure ℝ), ∀ tau : ℝ,
      Tendsto (fun H => xiWardSchwarzCapFactorIntegral tau s H) atTop
        (nhds (∫ x : ℝ, xiWardSchwarzCapDifference tau s x *
          continuedPrimeArchSourceRelativeTrace (xiWardLowerCapPoint s x))) := by
  filter_upwards [ae_forall_integrable_xiWardSchwarzCapFactor] with s hs tau
  exact intervalIntegral_tendsto_integral (hs tau) tendsto_neg_atTop_atBot tendsto_id

end

end RHTower
