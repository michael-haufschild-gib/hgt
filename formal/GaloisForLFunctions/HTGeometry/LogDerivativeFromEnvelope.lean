import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic derivatives from two-sided envelopes

A quantity trapped between two multiples of `x^k e^{-b x}` has logarithmic slope `-b`; that much is
immediate.  Its logarithmic *derivative* need not converge — an envelope says nothing about
derivatives.  One extra structural fact repairs this: if the derivative is eventually monotone (in
either direction) then the envelope forces it to converge, and to the only value it can converge to.

The mechanism is the mean value theorem twice.  For fixed `b`, the slope of `f` over `[b, c]` tends to
the same limit `L = lim f x / x` as `c` grows, and monotonicity puts `deriv f b` on one side of every
such slope — so `deriv f` is bounded by `L`.  On the other side, the slope over `[c/2, c]` also tends
to `L` and is caught between the derivative's values at the two endpoints, which squeezes
`deriv f c` onto `L`.

This is the shape in which asymptotic envelopes of the "power times Gaussian" type — Fuchs-type
leakage scales, for instance — deliver the logarithmic derivative that endpoint-response identities
consume.
-/

noncomputable section

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

/-- The slope of `f` over `[b, c]`, for fixed `b`, has the same limit as `f x / x`. -/
theorem tendsto_slope_fixed_left {f : ℝ → ℝ} {L : ℝ} (b : ℝ)
    (hlim : Tendsto (fun x => f x / x) atTop (𝓝 L)) :
    Tendsto (fun c => (f c - f b) / (c - b)) atTop (𝓝 L) := by
  have hbc : Tendsto (fun c : ℝ => b / c) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hfb : Tendsto (fun c : ℝ => f b / c) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
  have hnum : Tendsto (fun c : ℝ => f c / c - f b / c) atTop (𝓝 (L - 0)) := hlim.sub hfb
  have hden : Tendsto (fun c : ℝ => 1 - b / c) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hbc
  have hquot : Tendsto (fun c : ℝ => (f c / c - f b / c) / (1 - b / c)) atTop (𝓝 ((L - 0) / (1 - 0))) :=
    hnum.div hden (by norm_num)
  have hval : (L - 0) / (1 - 0) = L := by norm_num
  rw [hval] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop b] with c hc0 hcb
  have hc : c ≠ 0 := ne_of_gt hc0
  have hcb' : c - b ≠ 0 := by
    intro h
    exact absurd (by linarith [sub_eq_zero.mp h] : c ≤ b) (not_le.mpr hcb)
  field_simp

/-- The slope of `f` over `[c/2, c]` has the same limit as `f x / x`. -/
theorem tendsto_slope_half {f : ℝ → ℝ} {L : ℝ}
    (hlim : Tendsto (fun x => f x / x) atTop (𝓝 L)) :
    Tendsto (fun c => (f c - f (c / 2)) / (c - c / 2)) atTop (𝓝 L) := by
  have hhalf : Tendsto (fun c : ℝ => c / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) tendsto_id
  have hcomp : Tendsto (fun c : ℝ => f (c / 2) / (c / 2)) atTop (𝓝 L) := hlim.comp hhalf
  have hcomb : Tendsto (fun c : ℝ => 2 * (f c / c) - f (c / 2) / (c / 2)) atTop
      (𝓝 (2 * L - L)) := (hlim.const_mul 2).sub hcomp
  have hval : 2 * L - L = L := by ring
  rw [hval] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
  have hc : c ≠ 0 := ne_of_gt hc0
  field_simp
  ring

/-- **An eventually monotone derivative is forced to converge by the slope.**  If `f x / x → L` and
`deriv f` is monotone beyond `a`, then `deriv f → L`. -/
theorem tendsto_deriv_of_monotoneOn_of_tendsto_div {f : ℝ → ℝ} {a L : ℝ}
    (hdiff : DifferentiableOn ℝ f (Ioi a))
    (hmono : MonotoneOn (deriv f) (Ioi a))
    (hlim : Tendsto (fun x => f x / x) atTop (𝓝 L)) :
    Tendsto (deriv f) atTop (𝓝 L) := by
  -- the mean value theorem on any interval beyond `a`
  have hMVT : ∀ u v : ℝ, a < u → u < v →
      ∃ ξ ∈ Ioo u v, deriv f ξ = (f v - f u) / (v - u) := by
    intro u v hau huv
    have hsubIcc : Icc u v ⊆ Ioi a := fun x hx => lt_of_lt_of_le hau hx.1
    have hsubIoo : Ioo u v ⊆ Ioi a := fun x hx => lt_trans hau hx.1
    exact exists_deriv_eq_slope f huv (hdiff.mono hsubIcc).continuousOn (hdiff.mono hsubIoo)
  -- the derivative is bounded above by `L`
  have hub : ∀ u : ℝ, a < u → deriv f u ≤ L := by
    intro u hau
    refine ge_of_tendsto (tendsto_slope_fixed_left u hlim) ?_
    filter_upwards [eventually_gt_atTop u] with v huv
    obtain ⟨ξ, hξ, hslope⟩ := hMVT u v hau huv
    rw [← hslope]
    exact hmono (mem_Ioi.mpr hau) (mem_Ioi.mpr (lt_trans hau hξ.1)) hξ.1.le
  -- and bounded below by the half-slope
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_slope_half hlim)
    (tendsto_const_nhds (x := L)) ?_ ?_
  · filter_upwards [eventually_gt_atTop (2 * max a 0 + 1)] with c hc
    have ha2 : a < c / 2 := by
      have : max a 0 ≤ max a 0 := le_rfl
      have h1 : a ≤ max a 0 := le_max_left _ _
      linarith
    have hcc : c / 2 < c := by
      have h0 : (0 : ℝ) < c := by
        have h1 : (0 : ℝ) ≤ max a 0 := le_max_right _ _
        linarith
      linarith
    obtain ⟨ξ, hξ, hslope⟩ := hMVT (c / 2) c ha2 hcc
    rw [← hslope]
    exact hmono (mem_Ioi.mpr (lt_trans ha2 hξ.1)) (mem_Ioi.mpr (lt_trans ha2 hcc)) hξ.2.le
  · filter_upwards [eventually_gt_atTop a] with c hc
    exact hub c hc

/-- The antitone companion: the same conclusion when `deriv f` decreases. -/
theorem tendsto_deriv_of_antitoneOn_of_tendsto_div {f : ℝ → ℝ} {a L : ℝ}
    (hdiff : DifferentiableOn ℝ f (Ioi a))
    (hanti : AntitoneOn (deriv f) (Ioi a))
    (hlim : Tendsto (fun x => f x / x) atTop (𝓝 L)) :
    Tendsto (deriv f) atTop (𝓝 L) := by
  have hderiv : deriv (fun x => -f x) = fun x => -deriv f x := by
    funext x
    exact deriv.neg
  have hdiff' : DifferentiableOn ℝ (fun x => -f x) (Ioi a) := hdiff.neg
  have hmono' : MonotoneOn (deriv (fun x => -f x)) (Ioi a) := by
    rw [hderiv]
    intro u hu v hv huv
    exact neg_le_neg (hanti hu hv huv)
  have hlim' : Tendsto (fun x => (-f x) / x) atTop (𝓝 (-L)) := by
    have h := hlim.neg
    refine h.congr' (Filter.Eventually.of_forall fun x => ?_)
    simp [neg_div]
  have h := tendsto_deriv_of_monotoneOn_of_tendsto_div hdiff' hmono' hlim'
  rw [hderiv] at h
  have h2 := h.neg
  simpa using h2

/-! ## Envelopes -/

/-- **A power-times-exponential envelope fixes the logarithmic slope.**  If
`c₁ x^k e^{-b x} ≤ D x ≤ c₂ x^k e^{-b x}` eventually, then `log (D x) / x → -b`. -/
theorem tendsto_log_div_of_envelope {D : ℝ → ℝ} {k₁ k₂ : ℕ} {b c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlow : ∀ᶠ x in atTop, c₁ * x ^ k₁ * Real.exp (-(b * x)) ≤ D x)
    (hup : ∀ᶠ x in atTop, D x ≤ c₂ * x ^ k₂ * Real.exp (-(b * x))) :
    Tendsto (fun x => Real.log (D x) / x) atTop (𝓝 (-b)) := by
  have hlogx : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hmodel : ∀ (k : ℕ) (c : ℝ), 0 < c →
      Tendsto (fun x : ℝ => Real.log (c * x ^ k * Real.exp (-(b * x))) / x) atTop (𝓝 (-b)) := by
    intro k c hc
    have hcomb : Tendsto (fun x : ℝ =>
        Real.log c / x + (k : ℝ) * (Real.log x / x) + (-b)) atTop (𝓝 (0 + (k : ℝ) * 0 + (-b))) := by
      refine ((Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id).add
        (hlogx.const_mul (k : ℝ))).add tendsto_const_nhds
    have hval : (0 : ℝ) + (k : ℝ) * 0 + (-b) = -b := by ring
    rw [hval] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hxk : (0 : ℝ) < x ^ k := pow_pos hx k
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_mul (ne_of_gt hc) (ne_of_gt hxk),
      Real.log_pow, Real.log_exp]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hmodel k₁ c₁ hc₁) (hmodel k₂ c₂ hc₂) ?_ ?_
  · filter_upwards [hlow, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    have hpos : (0 : ℝ) < c₁ * x ^ k₁ * Real.exp (-(b * x)) := by positivity
    gcongr
  · filter_upwards [hup, hlow, eventually_gt_atTop (0 : ℝ)] with x hx hxl hx0
    have hpos : (0 : ℝ) < c₁ * x ^ k₁ * Real.exp (-(b * x)) := by positivity
    gcongr
    exact lt_of_lt_of_le hpos hxl

/-- **The logarithmic derivative from an envelope plus monotonicity of the logarithmic derivative.**
The value is the exponential rate of the envelope. -/
theorem tendsto_logDeriv_of_envelope_of_antitoneOn {D : ℝ → ℝ} {k₁ k₂ : ℕ} {a b c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hDdiff : DifferentiableOn ℝ D (Ioi a)) (hDpos : ∀ x ∈ Ioi a, 0 < D x)
    (hanti : AntitoneOn (fun x => deriv D x / D x) (Ioi a))
    (hlow : ∀ᶠ x in atTop, c₁ * x ^ k₁ * Real.exp (-(b * x)) ≤ D x)
    (hup : ∀ᶠ x in atTop, D x ≤ c₂ * x ^ k₂ * Real.exp (-(b * x))) :
    Tendsto (fun x => deriv D x / D x) atTop (𝓝 (-b)) := by
  set f : ℝ → ℝ := fun x => Real.log (D x) with hf
  have hderiv : ∀ x ∈ Ioi a, deriv f x = deriv D x / D x := by
    intro x hx
    have hxd : DifferentiableAt ℝ D x := hDdiff.differentiableAt (isOpen_Ioi.mem_nhds hx)
    have h := (hxd.hasDerivAt.log (ne_of_gt (hDpos x hx)))
    exact h.deriv
  have hfdiff : DifferentiableOn ℝ f (Ioi a) := by
    intro x hx
    have hxd : DifferentiableAt ℝ D x := hDdiff.differentiableAt (isOpen_Ioi.mem_nhds hx)
    exact ((hxd.hasDerivAt.log (ne_of_gt (hDpos x hx))).differentiableAt).differentiableWithinAt
  have hfanti : AntitoneOn (deriv f) (Ioi a) := by
    intro u hu v hv huv
    rw [hderiv u hu, hderiv v hv]
    exact hanti hu hv huv
  have hflim : Tendsto (fun x => f x / x) atTop (𝓝 (-b)) :=
    tendsto_log_div_of_envelope hc₁ hc₂ hlow hup
  have h := tendsto_deriv_of_antitoneOn_of_tendsto_div hfdiff hfanti hflim
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop a] with x hx
  exact hderiv x hx

/-! ## The quadratic reparametrisation -/

/-- Under `x = beta l²`, a logarithmic derivative `-b` in the outer variable becomes the normalized
logarithmic derivative `-(2 beta b)` in the inner one. -/
theorem tendsto_scaled_logDeriv {D D' : ℝ → ℝ} {β b : ℝ} (hβ : 0 < β)
    (h : Tendsto (fun c => D' c / D c) atTop (𝓝 (-b))) :
    Tendsto (fun l => D' (β * l ^ 2) * (2 * β * l) / (l * D (β * l ^ 2))) atTop
      (𝓝 (-(2 * β * b))) := by
  have hinner : Tendsto (fun l : ℝ => β * l ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hβ (tendsto_pow_atTop two_ne_zero)
  have hcomp : Tendsto (fun l : ℝ => D' (β * l ^ 2) / D (β * l ^ 2)) atTop (𝓝 (-b)) :=
    h.comp hinner
  have hmul := hcomp.const_mul (2 * β)
  have hval : 2 * β * -b = -(2 * β * b) := by ring
  rw [hval] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
  have hlne : l ≠ 0 := ne_of_gt hl
  field_simp

/-- The chain rule for the quadratic reparametrisation, in the form the endpoint identity uses. -/
theorem hasDerivAt_comp_quadratic {D D' : ℝ → ℝ} {β : ℝ} (hD : ∀ c, HasDerivAt D (D' c) c)
    (l : ℝ) :
    HasDerivAt (fun t => D (β * t ^ 2)) (D' (β * l ^ 2) * (2 * β * l)) l := by
  have hinner : HasDerivAt (fun t : ℝ => β * t ^ 2) (2 * β * l) l := by
    have h := (hasDerivAt_pow 2 l).const_mul β
    refine h.congr_deriv ?_
    push_cast
    ring
  exact (hD (β * l ^ 2)).comp l hinner

end GaloisForLFunctions.HTGeometry

end
