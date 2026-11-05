import GaloisForLFunctions.FiniteFreeProbability.JensenSaddleError

/-!
# The saddle point of the Jensen polynomials of `Ξ`

For real `x` the saddle equation of `R_d(x)` is `a = a(d/(a − ix))`, with `a = G'/G` the slope of the Gamma factor. On the rectangle
`S = {L/5 ≤ Re a ≤ L/2, |Im a| ≤ 5}`, `L = log d`, the map `Ψ_x(a) = a(d/(a − ix))` is a self-map for `|x| ≤ X` (Stirling) and a `1/2`-contraction: with
`τ = d/(a − ix)`, `‖Ψ_x'(a)‖ = ‖a'(τ)‖ ‖τ‖ / ‖a − ix‖ ≤ 6/‖a − ix‖ ≤ 30/L`. So the saddle exists, is unique in `S`, depends continuously on `x`, and is real at `x = 0`.
Here `X` is restricted by `2000 (L²/4 + (X + 5)²) ≤ dL`, which forces `Re τ ≥ 400`: this is the range `X ≍ √(d log d)`.
-/

open Filter Topology Complex Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-- The rectangle of slopes. -/
def saddleRect (L : ℝ) : Set ℂ := {a | L / 5 ≤ a.re ∧ a.re ≤ L / 2 ∧ |a.im| ≤ 5}

theorem isClosed_saddleRect (L : ℝ) : IsClosed (saddleRect L) := by
  have h1 : IsClosed {a : ℂ | L / 5 ≤ a.re} := isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {a : ℂ | a.re ≤ L / 2} := isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {a : ℂ | |a.im| ≤ 5} :=
    isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter (h2.inter h3)

theorem convex_saddleRect (L : ℝ) : Convex ℝ (saddleRect L) := by
  have h1 : Convex ℝ {a : ℂ | L / 5 ≤ a.re} := convex_halfSpace_re_ge _
  have h2 : Convex ℝ {a : ℂ | a.re ≤ L / 2} := convex_halfSpace_re_le _
  have h3 : Convex ℝ {a : ℂ | |a.im| ≤ 5} := by
    have : {a : ℂ | |a.im| ≤ 5} = {a : ℂ | -5 ≤ a.im} ∩ {a : ℂ | a.im ≤ 5} := by
      ext a
      simp [abs_le]
    rw [this]
    exact (convex_halfSpace_im_ge _).inter (convex_halfSpace_im_le _)
  exact h1.inter (h2.inter h3)

/-- The standing assumptions on the degree and the range. -/
structure SaddleRange (d : ℕ) (X : ℝ) : Prop where
  hd : 0 < d
  hX : 0 ≤ X
  hL : 5 * Real.exp 14 ≤ Real.log d
  h1 : 2000 * ((Real.log d / 2) ^ 2 + (X + 5) ^ 2) ≤ d * Real.log d
  h2 : Real.log ((Real.log d / 2) ^ 2 + (X + 5) ^ 2) / 2 ≤ 3 / 5 * Real.log d - 14

variable {d : ℕ} {X : ℝ}

/-- The point `τ = d/(a − ix)`. -/
def saddleTau (d : ℕ) (a : ℂ) (x : ℝ) : ℂ := (d : ℂ) / (a - I * x)

theorem SaddleRange.L_pos (h : SaddleRange d X) : 0 < Real.log d :=
  lt_of_lt_of_le (by positivity) h.hL

theorem SaddleRange.L_ge (h : SaddleRange d X) : 40000 ≤ Real.log d := by
  have h14 : (8000 : ℝ) ≤ Real.exp 14 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h2 : Real.exp 14 = Real.exp 1 ^ 14 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h2]
    calc (8000 : ℝ) ≤ 2 ^ 14 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) h1 14
  have := h.hL
  linarith

theorem SaddleRange.d_pos (h : SaddleRange d X) : (0 : ℝ) < d := by exact_mod_cast h.hd

theorem le_norm_denom {a : ℂ} {x : ℝ} (ha : a ∈ saddleRect (Real.log d)) :
    Real.log d / 5 ≤ ‖a - I * x‖ := by
  refine ha.1.trans ?_
  have := Complex.re_le_norm (a - I * x)
  simpa using this

section Geometry

variable (h : SaddleRange d X) {a : ℂ} {x : ℝ}

include h

theorem SaddleRange.denom_ne (ha : a ∈ saddleRect (Real.log d)) : a - I * x ≠ 0 := fun h0 => by
  have h1 := congrArg Complex.re h0
  simp at h1
  have := h.L_pos
  have h2 := ha.1
  linarith

theorem SaddleRange.normSq_denom_le (ha : a ∈ saddleRect (Real.log d)) (hx : |x| ≤ X) :
    ‖a - I * x‖ ^ 2 ≤ (Real.log d / 2) ^ 2 + (X + 5) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, mul_re, I_re, ofReal_re, zero_mul, I_im, one_mul, ofReal_im, mul_zero, sub_zero,
    sub_im, mul_im, zero_add]
  have hre1 := ha.1
  have hre2 := ha.2.1
  have him := abs_le.1 ha.2.2
  have hx' := abs_le.1 hx
  have hL := h.L_pos
  have hXn := h.hX
  nlinarith [sq_nonneg (a.im - x), sq_abs (a.im - x), abs_le.2 (show -(X + 5) ≤ a.im - x ∧ a.im - x ≤ X + 5 by
    constructor <;> linarith [him.1, him.2, hx'.1, hx'.2])]

theorem SaddleRange.re_tau_ge (ha : a ∈ saddleRect (Real.log d)) (hx : |x| ≤ X) :
    400 ≤ (saddleTau d a x).re := by
  have hne := h.denom_ne (x := x) ha
  have hre : (saddleTau d a x).re = d * a.re / ‖a - I * x‖ ^ 2 := by
    rw [saddleTau, ← Complex.normSq_eq_norm_sq, Complex.div_re]
    simp only [natCast_re, natCast_im, zero_mul, zero_div, add_zero, sub_re, mul_re, I_re, ofReal_re,
      I_im, ofReal_im, mul_zero, sub_zero]
  rw [hre]
  have hsq := h.normSq_denom_le ha hx
  have hpos : 0 < ‖a - I * x‖ ^ 2 := by
    have := norm_pos_iff.2 hne
    positivity
  rw [le_div_iff₀ hpos]
  have h1 := h.h1
  have hdR := h.d_pos
  have h2 : (d : ℝ) * (Real.log d / 5) ≤ d * a.re := by
    gcongr
    exact ha.1
  nlinarith

theorem SaddleRange.norm_tau (ha : a ∈ saddleRect (Real.log d)) :
    ‖saddleTau d a x‖ * ‖a - I * x‖ = d := by
  have hne := h.denom_ne (x := x) ha
  rw [saddleTau, norm_div, Complex.norm_natCast]
  field_simp [norm_ne_zero_iff.2 hne]

theorem SaddleRange.saddle_identity (ha : a ∈ saddleRect (Real.log d)) :
    (a - I * x) * saddleTau d a x = d := by
  rw [saddleTau]
  field_simp [h.denom_ne (x := x) ha]

/-- `Ψ_x` maps the rectangle to itself. -/
theorem SaddleRange.mapsTo (ha : a ∈ saddleRect (Real.log d)) (hx : |x| ≤ X) :
    gammaSlope (saddleTau d a x) ∈ saddleRect (Real.log d) := by
  set τ := saddleTau d a x with hτ
  have hre := h.re_tau_ge ha hx
  have hre1 : 1 ≤ τ.re := by linarith
  have hst := abs_le.1 (abs_re_gammaSlope_sub_le hre1)
  have him := abs_im_gammaSlope_le hre1
  have hnid := h.norm_tau (x := x) ha
  have hd5 := le_norm_denom (x := x) ha
  have hL := h.L_pos
  have hdR := h.d_pos
  have hτpos : 0 < ‖τ‖ := lt_of_lt_of_le (by linarith) (Complex.re_le_norm τ)
  have hdenpos : 0 < ‖a - I * x‖ := lt_of_lt_of_le (by positivity) hd5
  have hlogeq : Real.log ‖τ‖ + Real.log ‖a - I * x‖ = Real.log d := by
    rw [← Real.log_mul hτpos.ne' hdenpos.ne', hnid]
  refine ⟨?_, ?_, him⟩
  · -- lower bound: `‖a − ix‖² ≤ L²/4 + (X + 5)²`
    have hsq := h.normSq_denom_le ha hx
    have hlogsq : 2 * Real.log ‖a - I * x‖ ≤ Real.log ((Real.log d / 2) ^ 2 + (X + 5) ^ 2) := by
      have h0 : Real.log (‖a - I * x‖ ^ 2) = 2 * Real.log ‖a - I * x‖ := by
        rw [Real.log_pow]
        norm_num
      rw [← h0]
      exact Real.log_le_log (by positivity) hsq
    have h2 := h.h2
    linarith [hst.1]
  · -- upper bound: `‖a − ix‖ ≥ L/5 ≥ e^{14}`
    have h14 : 14 ≤ Real.log ‖a - I * x‖ := by
      rw [Real.le_log_iff_exp_le hdenpos]
      have := h.hL
      linarith
    linarith [hst.2]

/-- The derivative of `Ψ_x`. -/
theorem SaddleRange.hasDerivAt_psi (ha : a ∈ saddleRect (Real.log d)) (hx : |x| ≤ X) :
    HasDerivAt (fun b => gammaSlope (saddleTau d b x))
      (gammaSlopeDeriv (saddleTau d a x) * (-(d : ℂ) / (a - I * x) ^ 2)) a := by
  have hne := h.denom_ne (x := x) ha
  have hre := h.re_tau_ge ha hx
  have hτ : HasDerivAt (fun b => saddleTau d b x) (-(d : ℂ) / (a - I * x) ^ 2) a := by
    have h1 := ((hasDerivAt_id a).sub_const (I * x)).inv hne
    have h2 := h1.const_mul (d : ℂ)
    simp only [saddleTau, div_eq_mul_inv]
    refine h2.congr_deriv ?_
    simp [id]
    ring
  have hτne : saddleTau d a x ≠ 1 / 2 := fun h0 => by
    rw [h0] at hre
    norm_num at hre
  exact (hasDerivAt_gammaSlope (by linarith) hτne).comp a hτ

theorem SaddleRange.norm_deriv_psi_le (ha : a ∈ saddleRect (Real.log d)) (hx : |x| ≤ X) :
    ‖gammaSlopeDeriv (saddleTau d a x) * (-(d : ℂ) / (a - I * x) ^ 2)‖ ≤ 1 / 2 := by
  have hre := h.re_tau_ge ha hx
  have hρ : 4 ≤ ‖saddleTau d a x‖ := by
    have := Complex.re_le_norm (saddleTau d a x)
    linarith
  have hb := norm_gammaSlopeDeriv_le (τ := saddleTau d a x) (by linarith) hρ
  have hnid := h.norm_tau (x := x) ha
  have hd5 := le_norm_denom (x := x) ha
  have hL := h.L_ge
  have hdenpos : 0 < ‖a - I * x‖ := lt_of_lt_of_le (by positivity) hd5
  have hτpos : 0 < ‖saddleTau d a x‖ := by linarith
  rw [norm_mul, norm_div, norm_neg, norm_pow, Complex.norm_natCast, ← hnid]
  calc _ ≤ 6 / ‖saddleTau d a x‖ * (‖saddleTau d a x‖ * ‖a - I * x‖ / ‖a - I * x‖ ^ 2) := by gcongr
    _ = 6 / ‖a - I * x‖ := by field_simp
    _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hdenpos (by norm_num)]
        linarith

/-- `Ψ_x` is a `1/2`-contraction on the rectangle. -/
theorem SaddleRange.contraction (hx : |x| ≤ X) {a b : ℂ} (ha : a ∈ saddleRect (Real.log d))
    (hb : b ∈ saddleRect (Real.log d)) :
    ‖gammaSlope (saddleTau d a x) - gammaSlope (saddleTau d b x)‖ ≤ 1 / 2 * ‖a - b‖ :=
  (convex_saddleRect _).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun c => gammaSlope (saddleTau d c x)) (C := 1 / 2)
    (fun _ hc => (h.hasDerivAt_psi hc hx).hasDerivWithinAt) (fun _ hc => h.norm_deriv_psi_le hc hx) hb ha

theorem SaddleRange.exists_fixedPoint (hx : |x| ≤ X) :
    ∃ a ∈ saddleRect (Real.log d), gammaSlope (saddleTau d a x) = a := by
  have hmem : ((Real.log d / 2 : ℝ) : ℂ) ∈ saddleRect (Real.log d) := by
    have hL := h.L_pos
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.ofReal_re]
      linarith
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      norm_num
  have hmaps : MapsTo (fun c => gammaSlope (saddleTau d c x)) (saddleRect (Real.log d))
      (saddleRect (Real.log d)) := fun c hc => h.mapsTo hc hx
  have hcontr : ContractingWith (1 / 2) (hmaps.restrict _ _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun c e => ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    have := h.contraction hx c.2 e.2
    simpa using this
  obtain ⟨a, ha, hfix, -, -⟩ := hcontr.exists_fixedPoint' (isClosed_saddleRect _).isComplete hmaps hmem
    (edist_ne_top _ _)
  exact ⟨a, ha, hfix⟩

end Geometry

/-- **The saddle exists**, continuously in `x`, and is real at `x = 0`. -/
theorem SaddleRange.exists_saddle (h : SaddleRange d X) :
    ∃ a : ℝ → ℂ, (∀ x ∈ Icc 0 X, a x ∈ saddleRect (Real.log d) ∧ gammaSlope (saddleTau d (a x) x) = a x) ∧
      ContinuousOn a (Icc 0 X) ∧ (a 0).im = 0 := by
  have habs : ∀ x ∈ Icc 0 X, |x| ≤ X := fun x hx => by
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have hex : ∀ x : ℝ, ∃ a : ℂ, x ∈ Icc 0 X → a ∈ saddleRect (Real.log d) ∧ gammaSlope (saddleTau d a x) = a := by
    intro x
    by_cases hx : x ∈ Icc 0 X
    · obtain ⟨a, ha, hfix⟩ := h.exists_fixedPoint (habs x hx)
      exact ⟨a, fun _ => ⟨ha, hfix⟩⟩
    · exact ⟨0, fun h' => absurd h' hx⟩
  choose a ha using hex
  refine ⟨a, ha, ?_, ?_⟩
  · intro x hx
    obtain ⟨hax, hfixx⟩ := ha x hx
    have hne := h.denom_ne (x := x) hax
    have hre := h.re_tau_ge hax (habs x hx)
    have hτne : saddleTau d (a x) x ≠ 1 / 2 := fun h0 => by
      rw [h0] at hre
      norm_num at hre
    have hslope : ContinuousAt gammaSlope (saddleTau d (a x) x) :=
      (hasDerivAt_gammaSlope (by linarith) hτne).continuousAt
    have hτc : ContinuousAt (fun y : ℝ => saddleTau d (a x) y) x := by
      unfold saddleTau
      refine ContinuousAt.div continuousAt_const (by fun_prop) hne
    have hδ : Tendsto (fun y : ℝ => ‖gammaSlope (saddleTau d (a x) y) - gammaSlope (saddleTau d (a x) x)‖)
        (𝓝[Icc 0 X] x) (𝓝 0) := by
      have h1 : ContinuousAt (fun y : ℝ => gammaSlope (saddleTau d (a x) y)) x :=
        ContinuousAt.comp (f := fun y : ℝ => saddleTau d (a x) y) hslope hτc
      have h2 := (h1.tendsto.sub_const (gammaSlope (saddleTau d (a x) x))).norm
      rw [sub_self, norm_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hdouble := hδ.const_mul 2
    rw [mul_zero] at hdouble
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdouble
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨hay, hfixy⟩ := ha y hy
    have hc := h.contraction (habs y hy) hay hax
    have e : a y - a x = (gammaSlope (saddleTau d (a y) y) - gammaSlope (saddleTau d (a x) y)) +
        (gammaSlope (saddleTau d (a x) y) - gammaSlope (saddleTau d (a x) x)) := by
      rw [hfixy, hfixx]
      ring
    have hle : ‖a y - a x‖ ≤ 1 / 2 * ‖a y - a x‖ +
        ‖gammaSlope (saddleTau d (a x) y) - gammaSlope (saddleTau d (a x) x)‖ := by
      conv_lhs => rw [e]
      exact (norm_add_le _ _).trans (add_le_add hc le_rfl)
    linarith
  · have h0 : (0 : ℝ) ∈ Icc 0 X := ⟨le_rfl, h.hX⟩
    obtain ⟨ha0, hfix0⟩ := ha 0 h0
    have hmem : (starRingEnd ℂ) (a 0) ∈ saddleRect (Real.log d) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa using ha0.1
      · simpa using ha0.2.1
      · simpa using ha0.2.2
    have htau : saddleTau d ((starRingEnd ℂ) (a 0)) 0 = (starRingEnd ℂ) (saddleTau d (a 0) 0) := by
      simp [saddleTau, map_div₀]
    have hfix' : gammaSlope (saddleTau d ((starRingEnd ℂ) (a 0)) 0) = (starRingEnd ℂ) (a 0) := by
      rw [htau, gammaSlope_conj, hfix0]
    have hc := h.contraction (x := 0) (by simpa using h.hX) hmem ha0
    rw [hfix', hfix0] at hc
    have hzero : ‖(starRingEnd ℂ) (a 0) - a 0‖ = 0 := by
      have := norm_nonneg ((starRingEnd ℂ) (a 0) - a 0)
      linarith
    have heq : (starRingEnd ℂ) (a 0) = a 0 := sub_eq_zero.1 (norm_eq_zero.1 hzero)
    exact Complex.conj_eq_iff_im.1 heq

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.SaddleRange.exists_saddle
