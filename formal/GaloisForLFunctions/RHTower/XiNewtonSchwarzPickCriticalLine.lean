import GaloisForLFunctions.RHTower.Reflection

/-!
# Newton–Schwarz–Pick geometry of the critical line

Geometric (hyperbolic) uniqueness mechanism for zeros on the critical line, with no positivity,
spectral or estimate input.

* `eqOn_id_of_two_fixedPoints`: Schwarz–Pick rigidity. A holomorphic self-map of a disc with two
  distinct fixed points is the identity on the disc (disc automorphisms `mob` plus the equality
  case of the Schwarz lemma).
* `newtonMap_lineReflect`, `re_newtonMap_of_re_eq_half`: for `f (1 - s̄) = conj (f s)` the Newton
  map commutes with the critical-line reflection, so the line is Newton-invariant.
  `re_eq_half_of_tendsto_newton_iterate`: Newton orbits started on the line can only converge to
  points of the line, so basins of off-line zeros never meet it.
* `eq_of_zeros_of_newton_mapsTo_ball`: a disc that the Newton map of an entire `f` maps
  holomorphically into itself contains at most one zero of `f`.
  `re_eq_half_of_newton_mapsTo_ball`: if the disc is centred on the critical line and `f` is
  line-symmetric, that zero lies on the line.
* `exists_ball_newton_invariant_of_zero`: every isolated zero, of any multiplicity, has a small
  Newton-invariant disc. Near a zero of order `n`, the Newton map is `z₀ + (z - z₀)·B z` with
  `B z₀ = 1 - 1/n`.
* `riemannHypothesis_iff_newton_invariant_critical_discs`: RH ⟺ every zero of `ξ` lies in a
  Newton-invariant disc centred on the critical line.
* `re_gt_of_mem_immediateNewtonBasin`: the immediate Newton basin of an off-line point stays in
  its open half-plane. `riemannHypothesis_iff_immediateNewtonBasin_meets_line`: RH ⟺ every
  immediate basin of a `ξ`-zero meets the critical line.

The last item is a receiver: certifying an invariant disc is a local zero-localization problem.
-/

open Complex Metric Set Filter Topology

namespace RHTower.XiNewtonCriticalLine

/-! ### Disc automorphisms -/

/-- The disc automorphism `w ↦ (w - a) / (1 - conj a * w)`. -/
noncomputable def mob (a w : ℂ) : ℂ := (w - a) / (1 - (starRingEnd ℂ) a * w)

lemma normSq_mob_identity (a w : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) a * w) - Complex.normSq (w - a)
      = (1 - Complex.normSq a) * (1 - Complex.normSq w) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

lemma mob_denom_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 - (starRingEnd ℂ) a * w ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * w = 1 := by linear_combination -h
  have h2 : ‖(starRingEnd ℂ) a * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact ha
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

lemma mob_mem_ball {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) : mob a w ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, mob, norm_div]
  have hD := mob_denom_ne_zero ha hw
  have hDpos : 0 < ‖1 - (starRingEnd ℂ) a * w‖ := norm_pos_iff.mpr hD
  rw [div_lt_one hDpos]
  have hid := normSq_mob_identity a w
  have ha2 : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hw2 : Complex.normSq w < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hprod : 0 < (1 - Complex.normSq a) * (1 - Complex.normSq w) :=
    mul_pos (by linarith) (by linarith)
  have hsq : ‖w - a‖ ^ 2 < ‖1 - (starRingEnd ℂ) a * w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

lemma mob_neg_mob {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) : mob (-a) (mob a w) = w := by
  have hD := mob_denom_ne_zero ha hw
  have haa : (1 : ℂ) - (starRingEnd ℂ) a * a ≠ 0 := mob_denom_ne_zero ha ha
  set D := 1 - (starRingEnd ℂ) a * w with hDdef
  unfold mob
  rw [map_neg, ← hDdef]
  have hu : (w - a) / D - -a = w * (1 - (starRingEnd ℂ) a * a) / D := by
    rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD, hDdef]
    ring
  have hv : 1 - -(starRingEnd ℂ) a * ((w - a) / D) = (1 - (starRingEnd ℂ) a * a) / D := by
    rw [eq_div_iff hD, sub_mul, neg_mul, neg_mul, mul_assoc, div_mul_cancel₀ _ hD, hDdef]
    ring
  rw [hu, hv, div_div_div_cancel_right₀ hD, mul_div_assoc, div_self haa, mul_one]

lemma mob_self (a : ℂ) : mob a a = 0 := by simp [mob]

lemma mob_neg_zero (a : ℂ) : mob (-a) 0 = a := by simp [mob]

lemma eq_of_mob_eq_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) (h : mob a w = 0) : w = a := by
  rw [mob, div_eq_zero_iff] at h
  rcases h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (mob_denom_ne_zero ha hw)

lemma differentiableOn_mob {a : ℂ} (ha : ‖a‖ < 1) : DifferentiableOn ℂ (mob a) (ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun w => (w - a) / (1 - (starRingEnd ℂ) a * w)) w
  exact (differentiableAt_id.sub_const a).div (by fun_prop) (mob_denom_ne_zero ha hw')

/-! ### Schwarz–Pick rigidity: two fixed points force the identity -/

/-- Schwarz lemma equality case in the unit disc with a fixed origin and one more fixed point. -/
lemma eqOn_id_of_fixed_zero {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h (ball 0 1))
    (hmaps : MapsTo h (ball 0 1) (ball 0 1)) (h0 : h 0 = 0) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) 1) (hb0 : b ≠ 0) (hbb : h b = b) : EqOn h id (ball 0 1) := by
  have hmaps' : MapsTo h (ball 0 1) (closedBall (h 0) 1) := by
    intro z hz
    rw [h0]
    exact ball_subset_closedBall (hmaps hz)
  have hslope : dslope h 0 b = 1 := by
    rw [dslope_of_ne _ hb0, slope_def_field, hbb, h0, sub_zero]
    exact div_self hb0
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd hmaps' hb
    (by rw [hslope, norm_one, div_one])
  intro z hz
  have := haff hz
  simpa [h0, hslope] using this

/-- **Schwarz–Pick rigidity on a disc.** A holomorphic self-map of a disc with two distinct
fixed points is the identity on that disc. -/
theorem eqOn_id_of_two_fixedPoints {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ g (ball c r)) (hmaps : MapsTo g (ball c r) (ball c r))
    {p q : ℂ} (hp : p ∈ ball c r) (hq : q ∈ ball c r) (hpq : p ≠ q)
    (hgp : g p = p) (hgq : g q = q) : EqOn g id (ball c r) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have scale_mem : ∀ w ∈ ball (0 : ℂ) 1, c + r * w ∈ ball c r := by
    intro w hw
    have hw' := mem_ball_zero_iff.mp hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    calc r * ‖w‖ < r * 1 := by gcongr
      _ = r := mul_one r
  have unscale_mem : ∀ z ∈ ball c r, (z - c) / r ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      div_lt_one hr]
    simpa [mem_ball, dist_eq_norm] using hz
  have scale_unscale : ∀ z, c + r * ((z - c) / r) = z := by
    intro z
    rw [mul_div_cancel₀ _ hrC]
    ring
  set G : ℂ → ℂ := fun w => (g (c + r * w) - c) / r with hG
  have G_maps : MapsTo G (ball 0 1) (ball 0 1) := by
    intro w hw
    exact unscale_mem _ (hmaps (scale_mem w hw))
  have G_diff : DifferentiableOn ℂ G (ball 0 1) := by
    intro w hw
    have hgz : DifferentiableAt ℂ g (c + r * w) :=
      hd.differentiableAt (isOpen_ball.mem_nhds (scale_mem w hw))
    apply DifferentiableAt.differentiableWithinAt
    have hlin : DifferentiableAt ℂ (fun w : ℂ => c + r * w) w := by fun_prop
    exact ((hgz.comp w hlin).sub_const c).div_const _
  set a := (p - c) / r with ha_def
  set a' := (q - c) / r with ha'_def
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.mp (unscale_mem p hp)
  have ha' : ‖a'‖ < 1 := mem_ball_zero_iff.mp (unscale_mem q hq)
  have hGa : G a = a := by
    simp only [G, ha_def, scale_unscale, hgp]
  have hGa' : G a' = a' := by
    simp only [G, ha'_def, scale_unscale, hgq]
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  set h : ℂ → ℂ := fun w => mob a (G (mob (-a) w)) with hh
  have h_maps : MapsTo h (ball 0 1) (ball 0 1) := by
    intro w hw
    have h1 := mob_mem_ball hna (mem_ball_zero_iff.mp hw)
    have h2 := G_maps h1
    exact mob_mem_ball ha (mem_ball_zero_iff.mp h2)
  have h_diff : DifferentiableOn ℂ h (ball 0 1) := by
    have h1 : DifferentiableOn ℂ (fun w => G (mob (-a) w)) (ball 0 1) :=
      G_diff.comp (differentiableOn_mob hna) (fun w hw =>
        mob_mem_ball hna (mem_ball_zero_iff.mp hw))
    exact (differentiableOn_mob ha).comp h1 (fun w hw =>
      G_maps (mob_mem_ball hna (mem_ball_zero_iff.mp hw)))
  have h0 : h 0 = 0 := by
    simp only [h, mob_neg_zero, hGa, mob_self]
  set b := mob a a' with hb_def
  have hb : b ∈ ball (0 : ℂ) 1 := mob_mem_ball ha ha'
  have hb0 : b ≠ 0 := by
    intro hb0
    have := eq_of_mob_eq_zero ha ha' hb0
    apply hpq
    have h2 : (p - c) / r = (q - c) / r := by rw [← ha_def, ← ha'_def, this]
    have h3 := congrArg (fun x => c + r * x) h2
    simpa [scale_unscale] using h3
  have hbb : h b = b := by
    simp only [h, hb_def, mob_neg_mob ha ha', hGa']
  have hid := eqOn_id_of_fixed_zero h_diff h_maps h0 hb hb0 hbb
  intro z hz
  set w := (z - c) / r with hw_def
  have hw : ‖w‖ < 1 := mem_ball_zero_iff.mp (unscale_mem z hz)
  have hv := mob_mem_ball ha hw
  have hfix := hid hv
  have hmv : mob (-a) (mob a w) = w := mob_neg_mob ha hw
  have e1 : mob a (G w) = mob a w := by
    have : h (mob a w) = mob a w := hfix
    simpa only [h, hmv] using this
  have hGw' : ‖G w‖ < 1 := mem_ball_zero_iff.mp (G_maps (mem_ball_zero_iff.mpr hw))
  have hGw : G w = w := by
    have := congrArg (mob (-a)) e1
    rwa [mob_neg_mob ha hGw', mob_neg_mob ha hw] at this
  have : g (c + r * w) = c + r * w := by
    have h4 := congrArg (fun x => c + r * x) hGw
    simp only [G] at h4
    rw [mul_div_cancel₀ _ hrC] at h4
    simpa using h4
  rw [hw_def, scale_unscale] at this
  simpa using this

/-! ### The Newton map of a critical-line-symmetric function -/

/-- The Newton map `s ↦ s - f s / f' s`. With Lean's convention `x / 0 = 0` every zero of `f`
is a fixed point. -/
noncomputable def newtonMap (f : ℂ → ℂ) (s : ℂ) : ℂ := s - f s / deriv f s

/-- Real symmetry with respect to the critical line: `f (1 - s̄) = conj (f s)`. -/
def LineSymmetric (f : ℂ → ℂ) : Prop :=
  ∀ s, f (1 - (starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)

lemma newtonMap_eq_self_of_eq_zero {f : ℂ → ℂ} {s : ℂ} (h : f s = 0) : newtonMap f s = s := by
  simp [newtonMap, h]

lemma deriv_lineReflect {f : ℂ → ℂ} (hsym : LineSymmetric f) (s : ℂ) :
    deriv f (1 - (starRingEnd ℂ) s) = -(starRingEnd ℂ) (deriv f s) := by
  have hf : f = (starRingEnd ℂ) ∘ (fun w => f (1 - w)) ∘ (starRingEnd ℂ) := by
    funext z
    simp only [Function.comp_apply]
    rw [hsym z, Complex.conj_conj]
  have hd : deriv f = (starRingEnd ℂ) ∘ deriv (fun w => f (1 - w)) ∘ (starRingEnd ℂ) := by
    conv_lhs => rw [hf]
    exact deriv_conj_conj
  have := congrFun hd (1 - (starRingEnd ℂ) s)
  simp only [Function.comp_apply, deriv_comp_const_sub, map_sub, map_one,
    Complex.conj_conj, sub_sub_cancel, map_neg] at this
  exact this

/-- The Newton map commutes with the reflection across the critical line. -/
theorem newtonMap_lineReflect {f : ℂ → ℂ} (hsym : LineSymmetric f) (s : ℂ) :
    newtonMap f (1 - (starRingEnd ℂ) s) = 1 - (starRingEnd ℂ) (newtonMap f s) := by
  simp only [newtonMap, hsym s, deriv_lineReflect hsym s, map_sub, map_div₀, div_neg]
  ring

lemma lineReflect_eq_self_iff (s : ℂ) : 1 - (starRingEnd ℂ) s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    apply Complex.ext <;> simp [h]; norm_num

/-- The critical line is invariant under the Newton map of a line-symmetric function. -/
theorem re_newtonMap_of_re_eq_half {f : ℂ → ℂ} (hsym : LineSymmetric f) {s : ℂ}
    (hs : s.re = 1 / 2) : (newtonMap f s).re = 1 / 2 := by
  have h1 : 1 - (starRingEnd ℂ) s = s := (lineReflect_eq_self_iff s).mpr hs
  have h2 := newtonMap_lineReflect hsym s
  rw [h1] at h2
  exact (lineReflect_eq_self_iff _).mp h2.symm

/-- Newton orbits started on the critical line stay on it; their limits lie on it. -/
theorem re_eq_half_of_tendsto_newton_iterate {f : ℂ → ℂ} (hsym : LineSymmetric f) {p ρ : ℂ}
    (hp : p.re = 1 / 2)
    (hlim : Tendsto (fun n : ℕ => (newtonMap f)^[n] p) atTop (𝓝 ρ)) : ρ.re = 1 / 2 := by
  have hall : ∀ n : ℕ, ((newtonMap f)^[n] p).re = 1 / 2 := by
    intro n
    induction n with
    | zero => simpa using hp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact re_newtonMap_of_re_eq_half hsym ih
  have hclosed : IsClosed {z : ℂ | z.re = 1 / 2} :=
    isClosed_eq Complex.continuous_re continuous_const
  exact hclosed.mem_of_tendsto hlim (Eventually.of_forall hall)

/-! ### Newton-invariant discs contain at most one zero -/

lemma eq_zero_on_ball_of_newton_eqOn_id {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {r : ℝ}
    (hid : EqOn (newtonMap f) id (ball c r)) {ρ : ℂ} (hρ : ρ ∈ ball c r) (hfρ : f ρ = 0) :
    ∀ z ∈ ball c r, f z = 0 := by
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨z₀, hz₀, hfz₀⟩ := hcon
  have hderiv_ev : deriv f =ᶠ[𝓝 z₀] 0 := by
    have h1 : ∀ᶠ z in 𝓝 z₀, z ∈ ball c r := isOpen_ball.mem_nhds hz₀
    have h2 : ∀ᶠ z in 𝓝 z₀, f z ≠ 0 :=
      (hf z₀).continuousAt.eventually_ne hfz₀
    filter_upwards [h1, h2] with z hz hfz
    have hN : newtonMap f z = z := hid hz
    simp only [newtonMap, sub_eq_self, div_eq_zero_iff] at hN
    rcases hN with h | h
    · exact absurd h hfz
    · simpa using h
  have hana : AnalyticOnNhd ℂ (deriv f) (ball c r) :=
    ((hf.differentiableOn.analyticOnNhd isOpen_univ).deriv).mono (subset_univ _)
  have hzero : EqOn (deriv f) 0 (ball c r) :=
    hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball c r).isPreconnected
      hz₀ hderiv_ev
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
    hf.differentiableOn hzero hz₀ hρ
  exact hfz₀ (hconst.trans hfρ)

/-- **Uniqueness in Newton-invariant discs.** If the Newton map of an entire function `f` is
holomorphic on a disc and maps it into itself, and `f` does not vanish identically there, then
the disc contains at most one zero of `f`. (Schwarz–Pick rigidity.) -/
theorem eq_of_zeros_of_newton_mapsTo_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hN : DifferentiableOn ℂ (newtonMap f) (ball c r))
    (hmaps : MapsTo (newtonMap f) (ball c r) (ball c r)) (hnz : ∃ z ∈ ball c r, f z ≠ 0)
    {ρ₁ ρ₂ : ℂ} (h₁ : ρ₁ ∈ ball c r) (h₂ : ρ₂ ∈ ball c r) (hf₁ : f ρ₁ = 0) (hf₂ : f ρ₂ = 0) :
    ρ₁ = ρ₂ := by
  by_contra hne
  have hid := eqOn_id_of_two_fixedPoints hr hN hmaps h₁ h₂ hne
    (newtonMap_eq_self_of_eq_zero hf₁) (newtonMap_eq_self_of_eq_zero hf₂)
  obtain ⟨z₀, hz₀, hfz₀⟩ := hnz
  exact hfz₀ (eq_zero_on_ball_of_newton_eqOn_id hf hid h₁ hf₁ z₀ hz₀)

lemma lineReflect_mem_ball {c ρ : ℂ} {r : ℝ} (hc : c.re = 1 / 2) (hρ : ρ ∈ ball c r) :
    1 - (starRingEnd ℂ) ρ ∈ ball c r := by
  have hc' : 1 - (starRingEnd ℂ) c = c := (lineReflect_eq_self_iff c).mpr hc
  rw [mem_ball, dist_eq_norm] at hρ ⊢
  have : 1 - (starRingEnd ℂ) ρ - c = -(starRingEnd ℂ) (ρ - c) := by
    conv_lhs => rw [← hc']
    simp only [map_sub]
    ring
  rw [this, norm_neg, Complex.norm_conj]
  exact hρ

/-- **Symmetric Newton–Schwarz–Pick certificate.** Let `f` be entire and symmetric with respect
to the critical line. If its Newton map is holomorphic on a disc centred on the critical line and
maps that disc into itself, then every zero of `f` in the disc lies on the critical line. -/
theorem re_eq_half_of_newton_mapsTo_ball {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hsym : LineSymmetric f) {c : ℂ} (hc : c.re = 1 / 2) {r : ℝ} (hr : 0 < r)
    (hN : DifferentiableOn ℂ (newtonMap f) (ball c r))
    (hmaps : MapsTo (newtonMap f) (ball c r) (ball c r)) (hnz : ∃ z ∈ ball c r, f z ≠ 0)
    {ρ : ℂ} (hρ : ρ ∈ ball c r) (hfρ : f ρ = 0) : ρ.re = 1 / 2 := by
  have hρ' := lineReflect_mem_ball hc hρ
  have hfρ' : f (1 - (starRingEnd ℂ) ρ) = 0 := by rw [hsym, hfρ, map_zero]
  have heq := eq_of_zeros_of_newton_mapsTo_ball hf hr hN hmaps hnz hρ hρ' hfρ hfρ'
  exact (lineReflect_eq_self_iff ρ).mp heq.symm

/-! ### Every isolated zero sits in a small Newton-invariant disc -/

/-- Near a zero `z₀` of multiplicity `n ≥ 1`, with `f = (z - z₀)^n g`, the Newton map is
`z₀ + (z - z₀) · B z` where `B z = 1 - g z / (n g z + (z - z₀) g' z)` and `B z₀ = 1 - 1/n`. -/
theorem exists_ball_newton_invariant_of_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hz₀ : f z₀ = 0) (hnt : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ δ > 0, DifferentiableOn ℂ (newtonMap f) (ball z₀ δ) ∧
      MapsTo (newtonMap f) (ball z₀ δ) (ball z₀ δ) := by
  obtain ⟨n, g, hg, hgz, hfg⟩ :=
    ((hf.analyticAt z₀).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hnt
  have hn : n ≠ 0 := by
    rintro rfl
    have := hfg.self_of_nhds
    simp only [pow_zero, one_smul] at this
    exact hgz (this ▸ hz₀)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn
  set B : ℂ → ℂ := fun z => 1 - g z / (((m + 1 : ℕ) : ℂ) * g z + (z - z₀) * deriv g z) with hB
  have hdg : AnalyticAt ℂ (deriv g) z₀ := hg.deriv
  have hden0 : ((m + 1 : ℕ) : ℂ) * g z₀ + (z₀ - z₀) * deriv g z₀ ≠ 0 := by
    rw [sub_self, zero_mul, add_zero]
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero m) hgz
  have hden_cont : ContinuousAt (fun z => ((m + 1 : ℕ) : ℂ) * g z + (z - z₀) * deriv g z) z₀ :=
    (continuousAt_const.mul hg.continuousAt).add
      ((continuousAt_id.sub continuousAt_const).mul hdg.continuousAt)
  have hB_cont : ContinuousAt B z₀ :=
    continuousAt_const.sub (hg.continuousAt.div hden_cont hden0)
  have hBz₀ : ‖B z₀‖ < 1 := by
    have hval : B z₀ = 1 - 1 / ((m + 1 : ℕ) : ℂ) := by
      simp only [hB, sub_self, zero_mul, add_zero]
      congr 1
      field_simp
    rw [hval]
    have hreal : (1 : ℂ) - 1 / ((m + 1 : ℕ) : ℂ) = ((1 - 1 / ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have h1 : 0 < 1 / ((m + 1 : ℕ) : ℝ) := by positivity
    have h2 : 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hpos]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- gather the local properties
  have hev_B : ∀ᶠ z in 𝓝 z₀, ‖B z‖ < 1 :=
    hB_cont.eventually (isOpen_lt continuous_norm continuous_const |>.mem_nhds hBz₀)
  have hev_den : ∀ᶠ z in 𝓝 z₀,
      ((m + 1 : ℕ) : ℂ) * g z + (z - z₀) * deriv g z ≠ 0 :=
    hden_cont.eventually_ne hden0
  have hev_an : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hg.eventually_analyticAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (((hfg.and hev_B).and hev_den).and hev_an)
  refine ⟨ε, hε, ?_⟩
  -- formula for the Newton map on the ball
  have hformula : ∀ z ∈ ball z₀ ε, newtonMap f z = z₀ + (z - z₀) * B z := by
    intro z hz
    obtain ⟨⟨⟨hfz, -⟩, hdenz⟩, hgan⟩ := hball z hz
    by_cases hzz : z = z₀
    · subst hzz
      rw [newtonMap_eq_self_of_eq_zero hz₀]
      ring
    have hloc : f =ᶠ[𝓝 z] fun w => (w - z₀) ^ (m + 1) * g w := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      simpa [smul_eq_mul] using (hball w hw).1.1.1
    have hderiv : deriv f z =
        ((m + 1 : ℕ) : ℂ) * (z - z₀) ^ m * g z + (z - z₀) ^ (m + 1) * deriv g z := by
      rw [hloc.deriv_eq]
      have h1 : HasDerivAt (fun w => (w - z₀) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (z - z₀) ^ m) z := by
        have := (hasDerivAt_pow (m + 1) (z - z₀)).comp z ((hasDerivAt_id z).sub_const z₀)
        simpa [Function.comp_def] using this
      exact (h1.mul hgan.differentiableAt.hasDerivAt).deriv
    have hfz' : f z = (z - z₀) ^ (m + 1) * g z := by simpa [smul_eq_mul] using hfz
    have hzne : z - z₀ ≠ 0 := sub_ne_zero.mpr hzz
    have hpm : (z - z₀) ^ m ≠ 0 := pow_ne_zero _ hzne
    simp only [newtonMap, hfz', hderiv, hB]
    have hsplit : ((m + 1 : ℕ) : ℂ) * (z - z₀) ^ m * g z + (z - z₀) ^ (m + 1) * deriv g z
        = (z - z₀) ^ m * (((m + 1 : ℕ) : ℂ) * g z + (z - z₀) * deriv g z) := by ring
    rw [hsplit, pow_succ, mul_assoc, mul_div_mul_left _ _ hpm]
    field_simp
    ring
  constructor
  · intro z hz
    obtain ⟨⟨⟨-, -⟩, hdenz⟩, hgan⟩ := hball z hz
    have hBd : DifferentiableAt ℂ B z := by
      have hgd : DifferentiableAt ℂ g z := hgan.differentiableAt
      have hdgd : DifferentiableAt ℂ (deriv g) z := hgan.deriv.differentiableAt
      exact (differentiableAt_const _).sub (hgd.div ((differentiableAt_const _).mul hgd |>.add
        ((differentiableAt_id.sub_const z₀).mul hdgd)) hdenz)
    have hev : (fun w => z₀ + (w - z₀) * B w) =ᶠ[𝓝 z] newtonMap f := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact (hformula w hw).symm
    exact (((differentiableAt_const _).add ((differentiableAt_id.sub_const z₀).mul hBd)).congr_of_eventuallyEq
      hev.symm).differentiableWithinAt
  · intro z hz
    obtain ⟨⟨⟨-, hBz⟩, -⟩, -⟩ := hball z hz
    rw [mem_ball, dist_eq_norm, hformula z hz, add_sub_cancel_left, norm_mul]
    have hz' : ‖z - z₀‖ < ε := by simpa [mem_ball, dist_eq_norm] using hz
    calc ‖z - z₀‖ * ‖B z‖ ≤ ‖z - z₀‖ * 1 := by gcongr
      _ < ε := by rw [mul_one]; exact hz'

/-! ### Application to the completed Riemann `ξ` -/

theorem xi_lineSymmetric : LineSymmetric xi := by
  intro s
  have h : (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) := by simp
  rw [h, xi_conj, xi_one_sub]

lemma xi_not_eventually_zero (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, xi w = 0 := by
  intro h
  have := xi_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z) h
  exact xi_two_ne_zero (this (mem_univ 2))

lemma xi_exists_ne_zero_ball (c : ℂ) {r : ℝ} (hr : 0 < r) : ∃ z ∈ ball c r, xi z ≠ 0 := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  apply xi_not_eventually_zero c
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with w hw using h w hw

lemma re_eq_half_of_xi_eq_zero_of_rh (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : xi ρ = 0) :
    ρ.re = 1 / 2 := by
  have hright := rh_iff_xi_ne_zero_right.mp hRH
  rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
  · exfalso
    have hmem : (1 : ℂ) - ρ ∈ rightHalf := by
      simp only [rightHalf, Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
      linarith
    exact hright _ hmem (by rw [xi_one_sub, hρ])
  · exact h
  · exfalso
    have hmem : ρ ∈ rightHalf := by
      simp only [rightHalf, Set.mem_setOf_eq]
      linarith
    exact hright _ hmem hρ

/-- **Newton–Schwarz–Pick receiver.** RH holds iff every zero of `ξ` lies in some disc centred
on the critical line on which the Newton map of `ξ` is holomorphic and which it maps into
itself. -/
theorem riemannHypothesis_iff_newton_invariant_critical_discs :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 → ∃ c : ℂ, c.re = 1 / 2 ∧ ∃ r > 0, ρ ∈ ball c r ∧
      DifferentiableOn ℂ (newtonMap xi) (ball c r) ∧
      MapsTo (newtonMap xi) (ball c r) (ball c r) := by
  constructor
  · intro hRH ρ hρ
    obtain ⟨δ, hδ, hd, hm⟩ :=
      exists_ball_newton_invariant_of_zero xi_differentiable hρ (xi_not_eventually_zero ρ)
    exact ⟨ρ, re_eq_half_of_xi_eq_zero_of_rh hRH hρ, δ, hδ, mem_ball_self hδ, hd, hm⟩
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hxs
    obtain ⟨c, hc, r, hr, hsb, hd, hm⟩ := h s hxs
    have hre := re_eq_half_of_newton_mapsTo_ball xi_differentiable xi_lineSymmetric hc hr hd hm
      (xi_exists_ne_zero_ball c hr) hsb hxs
    simp only [rightHalf, Set.mem_setOf_eq] at hs
    linarith

/-! ### Newton basins and half-plane confinement -/

/-- The Newton basin of `ρ`: starting points whose Newton orbit converges to `ρ`. -/
def newtonBasin (f : ℂ → ℂ) (ρ : ℂ) : Set ℂ :=
  {p | Tendsto (fun n : ℕ => (newtonMap f)^[n] p) atTop (𝓝 ρ)}

/-- The immediate Newton basin: the connected component of the basin containing `ρ`. -/
def immediateNewtonBasin (f : ℂ → ℂ) (ρ : ℂ) : Set ℂ :=
  connectedComponentIn (newtonBasin f ρ) ρ

lemma mem_newtonBasin_self_of_eq_zero {f : ℂ → ℂ} {ρ : ℂ} (hρ : f ρ = 0) :
    ρ ∈ newtonBasin f ρ := by
  have hfix : ∀ n : ℕ, (newtonMap f)^[n] ρ = ρ :=
    fun n => Function.iterate_fixed (newtonMap_eq_self_of_eq_zero hρ) n
  simp only [newtonBasin, Set.mem_setOf_eq, hfix]
  exact tendsto_const_nhds

/-- **Half-plane confinement.** The immediate Newton basin of a point strictly right of the
critical line lies strictly right of the line: it is connected, and a basin point on the line
would force the limit onto the line. -/
theorem re_gt_of_mem_immediateNewtonBasin {f : ℂ → ℂ} (hsym : LineSymmetric f) {ρ : ℂ}
    (hρ : 1 / 2 < ρ.re) {p : ℂ} (hp : p ∈ immediateNewtonBasin f ρ) : 1 / 2 < p.re := by
  by_contra hle
  push Not at hle
  have hconn : IsPreconnected (immediateNewtonBasin f ρ) :=
    isPreconnected_connectedComponentIn
  have hρmem : ρ ∈ immediateNewtonBasin f ρ := by
    apply mem_connectedComponentIn
    by_contra hρb
    exact absurd hp (by rw [immediateNewtonBasin, connectedComponentIn_eq_empty hρb]; simp)
  obtain ⟨q, hq, hqre⟩ := hconn.intermediate_value hp hρmem
    Complex.continuous_re.continuousOn ⟨hle, hρ.le⟩
  have hqb : q ∈ newtonBasin f ρ := connectedComponentIn_subset _ _ hq
  have := re_eq_half_of_tendsto_newton_iterate hsym hqre hqb
  linarith

/-- RH holds iff the immediate Newton basin of every zero of `ξ` meets the critical line. -/
theorem riemannHypothesis_iff_immediateNewtonBasin_meets_line :
    RiemannHypothesis ↔ ∀ ρ : ℂ, xi ρ = 0 →
      ∃ p ∈ immediateNewtonBasin xi ρ, p.re = 1 / 2 := by
  constructor
  · intro hRH ρ hρ
    exact ⟨ρ, mem_connectedComponentIn (mem_newtonBasin_self_of_eq_zero hρ),
      re_eq_half_of_xi_eq_zero_of_rh hRH hρ⟩
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hxs
    obtain ⟨p, hp, hpre⟩ := h s hxs
    have hpb : p ∈ newtonBasin xi s := connectedComponentIn_subset _ _ hp
    have := re_eq_half_of_tendsto_newton_iterate xi_lineSymmetric hpre hpb
    simp only [rightHalf, Set.mem_setOf_eq] at hs
    linarith

end RHTower.XiNewtonCriticalLine
