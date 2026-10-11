import GaloisForLFunctions.RHTower.XiRealPartDerivativeCurvesCriterion
import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointIndex

/-!
# Exceptional points are isolated

The exceptional points of the PTR producer are the points `s` with `Re ξ(s) = 0` and
`Im ξ'(s) = 0` (`riemannHypothesis_iff_re_xi_eq_zero_imp_im_deriv_xi_ne_zero`). At depth
`h = Re s − ½` they are the multiple real zeros of `cos(hD)Ξ`.

**Theorem** (`eventually_not_exceptional`). The set `{s : Re ξ(s) = 0, Im ξ'(s) = 0}` has no
accumulation point in `ℂ`. Equivalently, the curves `{Re ξ = 0}` and `{Im ξ' = 0}` meet in a
discrete set.

**Proof.** Suppose exceptional points accumulate at `s₀`.
* Write `ξ(s) = ξ(s₀) + ζ(s)^k` near `s₀`, with `ζ` biholomorphic and `ζ(s₀) = 0`
  (`exists_kthRoot_coordinate`), and let `Z` be its local inverse.
* At an exceptional point `s`, `ζ(s)^k = ξ(s) − ξ(s₀)` is purely imaginary. So the direction
  `ζ(s)/|ζ(s)|` lies in a finite set (`finite_directions`). One direction `ω` carries infinitely
  many of them, on the analytic arc `s(τ) = Z(ωτ)`, `τ` real, along which `Re ξ = 0`.
* `Im ξ'(s(τ))` vanishes at infinitely many `τ → 0`. By the identity theorem for
  `τ ↦ ξ'(Z(ωτ)) − conj ξ'(Z(ω τ̄))`, the value `ξ'(s(τ))` is real on the arc.
* Differentiating `ξ(Z(w)) = ξ(s₀) + w^k` gives `ξ'(s(τ))·s'(τ) = kω^kτ^{k−1} ∈ iℝ`. So
  `Re s'(τ) = 0`: the arc is a vertical segment.
* Then `cos(hD)Ξ` with `h = Re s₀ − ½` vanishes on an interval of real points, which is impossible.

**Consequence.** In the exceptional-point index law the alternative "infinitely many exceptional
depths" never occurs (`windowDefectCount_zero_le_exceptional_mass_finite`).
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- **A `k`-th root coordinate.** If `f − f(s₀)` has order `k ≥ 1` at `s₀`, then
`f = f(s₀) + ζ^k` near `s₀` for an analytic `ζ` with `ζ(s₀) = 0` and `ζ'(s₀) ≠ 0`. -/
theorem exists_kthRoot_coordinate {f : ℂ → ℂ} {s₀ : ℂ} (hf : AnalyticAt ℂ f s₀) {k : ℕ}
    (hk : k ≠ 0) (hord : analyticOrderAt (fun s => f s - f s₀) s₀ = k) :
    ∃ ζ : ℂ → ℂ, AnalyticAt ℂ ζ s₀ ∧ ζ s₀ = 0 ∧ deriv ζ s₀ ≠ 0 ∧
      ∀ᶠ s in 𝓝 s₀, f s = f s₀ + ζ s ^ k := by
  have hg : AnalyticAt ℂ (fun s => f s - f s₀) s₀ := hf.sub analyticAt_const
  obtain ⟨u, hu, hu0, hfac⟩ := (hg.analyticOrderAt_eq_natCast).mp hord
  set u₀ := u s₀ with hu₀
  set c : ℂ := u₀ ^ ((k : ℂ)⁻¹) with hc
  have hck : c ^ k = u₀ := Complex.cpow_nat_inv_pow u₀ hk
  have hc0 : c ≠ 0 := by
    intro h; rw [h, zero_pow hk] at hck; exact hu0 hck.symm
  -- a holomorphic `k`-th root of `u` near `s₀`
  set v : ℂ → ℂ := fun s => c * Complex.exp (Complex.log (u s / u₀) / k) with hv
  have hslit : u s₀ / u₀ ∈ slitPlane := by rw [← hu₀, div_self hu0]; simp [mem_slitPlane_iff]
  have hvan : AnalyticAt ℂ v s₀ := by
    have h1 : AnalyticAt ℂ (fun s => u s / u₀) s₀ := hu.div analyticAt_const hu0
    have h2 : AnalyticAt ℂ (fun s => Complex.log (u s / u₀)) s₀ :=
      (analyticAt_clog hslit).comp_of_eq h1 rfl
    exact analyticAt_const.mul ((h2.div analyticAt_const (by exact_mod_cast hk)).cexp)
  have hvk : ∀ᶠ s in 𝓝 s₀, v s ^ k = u s := by
    have hcont : ContinuousAt u s₀ := hu.continuousAt
    filter_upwards [hcont.eventually_ne hu0] with s hs
    simp only [hv, mul_pow, ← Complex.exp_nat_mul]
    rw [hck, mul_div_cancel₀ _ (by exact_mod_cast hk : (k : ℂ) ≠ 0),
      Complex.exp_log (div_ne_zero hs hu0)]
    field_simp
  have hv0 : v s₀ = c := by
    simp only [hv, ← hu₀, div_self hu0, Complex.log_one, zero_div, Complex.exp_zero, mul_one]
  set ζ : ℂ → ℂ := fun s => (s - s₀) * v s with hζ
  refine ⟨ζ, (analyticAt_id.sub analyticAt_const).mul hvan, by simp [hζ], ?_, ?_⟩
  · have hd : HasDerivAt ζ (1 * v s₀ + (s₀ - s₀) * deriv v s₀) s₀ :=
      ((hasDerivAt_id s₀).sub_const s₀).mul hvan.differentiableAt.hasDerivAt
    rw [hd.deriv, sub_self, zero_mul, add_zero, one_mul, hv0]; exact hc0
  · filter_upwards [hfac, hvk] with s h1 h2
    simp only [smul_eq_mul] at h1
    simp only [hζ, mul_pow, h2]
    rw [← h1]; ring

/-- The unit directions whose `k`-th power is purely imaginary are finitely many. -/
theorem finite_directions {k : ℕ} (hk : k ≠ 0) :
    {ω : ℂ | ‖ω‖ = 1 ∧ (ω ^ k).re = 0}.Finite := by
  have hp : (Polynomial.X ^ (4 * k) - Polynomial.C 1 : Polynomial ℂ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by omega) 1
  refine (Polynomial.finite_setOf_isRoot hp).subset ?_
  rintro ω ⟨hn, hre⟩
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  have hnk : ‖ω ^ k‖ = 1 := by rw [norm_pow, hn, one_pow]
  have hsq : (ω ^ k) ^ 2 = -1 := by
    have him : (ω ^ k).im ^ 2 = 1 := by
      have := Complex.sq_norm (ω ^ k)
      rw [hnk, Complex.normSq_apply, hre] at this
      nlinarith
    have hw : ω ^ k = ((ω ^ k).im : ℂ) * I := Complex.ext (by simp [hre]) (by simp)
    rw [hw, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, him]; simp
  calc ω ^ (4 * k) = ((ω ^ k) ^ 2) ^ 2 := by ring
    _ = 1 := by rw [hsq]; norm_num

/-- The exceptional-point predicate: `Re ξ(s) = 0` and `Im ξ'(s) = 0`. -/
def IsXiExceptional (s : ℂ) : Prop := (xi s).re = 0 ∧ (deriv xi s).im = 0

theorem isClosed_xiExceptional : IsClosed {s | IsXiExceptional s} := by
  have h1 : Continuous fun s => (xi s).re := Complex.continuous_re.comp xi_differentiable.continuous
  have hd : Continuous (deriv xi) := by
    have := (xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ).deriv
    rw [← continuousOn_univ]; exact this.continuousOn
  have h2 : Continuous fun s => (deriv xi s).im := Complex.continuous_im.comp hd
  exact (isClosed_eq h1 continuous_const).inter (isClosed_eq h2 continuous_const)

/-- `conj ∘ f ∘ conj` is analytic where `f` is analytic at the conjugate point. -/
theorem analyticAt_conj_comp_conj {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f ((starRingEnd ℂ) z)) :
    AnalyticAt ℂ (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) z := by
  obtain ⟨V, hV, hgV⟩ := hf.exists_mem_nhds_analyticOnNhd
  obtain ⟨U, hUV, hUo, hzU⟩ := _root_.mem_nhds_iff.mp hV
  have hcont : Continuous fun w : ℂ => (starRingEnd ℂ) w := Complex.continuous_conj
  refine DifferentiableOn.analyticAt (s := (fun w : ℂ => (starRingEnd ℂ) w) ⁻¹' U) ?_
    ((hUo.preimage hcont).mem_nhds (by simpa using hzU))
  intro w hw
  have hgw : DifferentiableAt ℂ f ((starRingEnd ℂ) w) := ((hgV.mono hUV) _ hw).differentiableAt
  have hd := hgw.hasDerivAt.conj_conj
  rw [Complex.conj_conj] at hd
  exact hd.differentiableAt.differentiableWithinAt

/-- **Exceptional points are isolated.** -/
theorem eventually_not_xiExceptional (s₀ : ℂ) : ∀ᶠ s in 𝓝[≠] s₀, ¬ IsXiExceptional s := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  simp only [not_not] at hcon
  have hxian : ∀ z, AnalyticAt ℂ xi z := fun z =>
    xi_differentiable.differentiableOn.analyticOnNhd isOpen_univ z (mem_univ _)
  -- `s₀` is exceptional
  have hs₀ : IsXiExceptional s₀ :=
    isClosed_xiExceptional.mem_of_frequently_of_tendsto (hcon.filter_mono nhdsWithin_le_nhds)
      tendsto_id
  -- the order of `ξ − ξ(s₀)` at `s₀`
  have hfan : AnalyticAt ℂ (fun s => xi s - xi s₀) s₀ := (hxian s₀).sub analyticAt_const
  have hentire : AnalyticOnNhd ℂ (fun s => xi s - xi s₀) univ := fun z _ =>
    (hxian z).sub analyticAt_const
  have hnz : ∃ z, (fun s => xi s - xi s₀) z ≠ 0 := by
    obtain ⟨a, -, -, -, -, hza, -⟩ := exists_two_distinct_positive_real_XiC_zeros
    by_cases h0 : xi s₀ = 0
    · exact ⟨2, by simp only [h0, sub_zero]; exact xi_ne_zero_of_one_le (by simp)⟩
    · refine ⟨1 / 2 + (a : ℂ) * I, ?_⟩
      have : xi (1 / 2 + (a : ℂ) * I) = 0 := by rw [← hza, XiC]
      simp only [this, zero_sub, neg_ne_zero]; exact h0
  have hordtop := analyticOrderAt_ne_top_of_entire_exists_ne_zero hentire hnz s₀
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hordtop
  have hk0 : k ≠ 0 := by
    rintro rfl
    have := (hfan.analyticOrderAt_eq_zero).mp (by rw [← hk]; rfl)
    simp at this
  obtain ⟨ζ, hζan, hζ0, hζ', hξζ⟩ := exists_kthRoot_coordinate (hxian s₀) hk0 hk.symm
  -- the local inverse of `ζ`
  have hstrict := hζan.hasStrictDerivAt
  set Z := hstrict.localInverse ζ (deriv ζ s₀) s₀ hζ' with hZ
  have hZan : AnalyticAt ℂ Z 0 := by
    have := hζan.analyticAt_localInverse hζ'
    rw [hζ0] at this; exact this
  have hleft : ∀ᶠ s in 𝓝 s₀, Z (ζ s) = s := hstrict.eventually_left_inverse hζ'
  have hright : ∀ᶠ w in 𝓝 (0 : ℂ), ζ (Z w) = w := by
    have := hstrict.eventually_right_inverse hζ'
    rw [hζ0] at this; exact this
  have hZ0 : Z 0 = s₀ := by
    have := HasStrictFDerivAt.localInverse_apply_image (hstrict.hasStrictFDerivAt_equiv hζ')
    rw [hζ0] at this; exact this
  have hZc : Tendsto Z (𝓝 0) (𝓝 s₀) := by
    have := hZan.continuousAt.tendsto; rwa [hZ0] at this
  -- `ξ ∘ Z = ξ(s₀) + w^k` near `0`
  have hξZ : ∀ᶠ w in 𝓝 (0 : ℂ), xi (Z w) = xi s₀ + w ^ k := by
    filter_upwards [hZc.eventually hξζ, hright] with w h1 h2
    rw [h1, h2]
  -- `ζ s ≠ 0` off `s₀`
  have hζne : ∀ᶠ s in 𝓝[≠] s₀, ζ s ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds hleft, self_mem_nhdsWithin] with s hs hne h0
    apply hne
    rw [← hs, h0, hZ0]; exact Set.mem_singleton _
  -- one direction carries infinitely many exceptional points
  have hD := finite_directions hk0
  obtain ⟨ω, hωD, hfreqω⟩ : ∃ ω ∈ {ω : ℂ | ‖ω‖ = 1 ∧ (ω ^ k).re = 0},
      ∃ᶠ s in 𝓝[≠] s₀, IsXiExceptional s ∧ ζ s ≠ 0 ∧ ζ s / (‖ζ s‖ : ℂ) = ω := by
    by_contra hall
    have hall2 : ∀ ω ∈ {ω : ℂ | ‖ω‖ = 1 ∧ (ω ^ k).re = 0}, ∀ᶠ s in 𝓝[≠] s₀,
        ¬ (IsXiExceptional s ∧ ζ s ≠ 0 ∧ ζ s / (‖ζ s‖ : ℂ) = ω) := by
      intro ω hω
      by_contra h
      exact hall ⟨ω, hω, (Filter.not_eventually.mp h).mono fun s hs => not_not.mp hs⟩
    have hev := (Filter.eventually_all_finite hD).mpr hall2
    have hcomb := hcon.and_eventually ((hev.and hζne).and (nhdsWithin_le_nhds hξζ))
    obtain ⟨s, hsE, ⟨hall', hsζ⟩, hsξ⟩ := hcomb.exists
    refine hall' (ζ s / (‖ζ s‖ : ℂ)) ⟨?_, ?_⟩ ⟨hsE, hsζ, rfl⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr hsζ)]
    · have hn : (0 : ℝ) < ‖ζ s‖ := norm_pos_iff.mpr hsζ
      rw [div_pow, ← Complex.ofReal_pow]
      have hre : (ζ s ^ k).re = 0 := by
        have h1 : ζ s ^ k = xi s - xi s₀ := by rw [hsξ]; ring
        rw [h1, Complex.sub_re, hsE.1, hs₀.1, sub_zero]
      rw [Complex.div_ofReal_re, hre, zero_div]
  obtain ⟨hωn, hωk⟩ := hωD
  -- the analytic arc and the identity theorem
  set Φ : ℂ → ℂ := fun τ => deriv xi (Z (ω * τ)) with hΦ
  have hlin : AnalyticAt ℂ (fun τ : ℂ => ω * τ) 0 := analyticAt_const.mul analyticAt_id
  have hΦan : ∀ τ₀ : ℂ, AnalyticAt ℂ Z (ω * τ₀) → AnalyticAt ℂ Φ τ₀ := by
    intro τ₀ hZτ
    have hd : AnalyticAt ℂ (deriv xi) (Z (ω * τ₀)) := (hxian _).deriv
    have hin : AnalyticAt ℂ (fun τ => Z (ω * τ)) τ₀ :=
      AnalyticAt.comp_of_eq (f := fun τ => ω * τ) hZτ (analyticAt_const.mul analyticAt_id) rfl
    exact AnalyticAt.comp_of_eq (f := fun τ => Z (ω * τ)) hd hin rfl
  have hZω0 : AnalyticAt ℂ Z (ω * 0) := by rw [mul_zero]; exact hZan
  set H : ℂ → ℂ := fun τ => Φ τ - (starRingEnd ℂ) (Φ ((starRingEnd ℂ) τ)) with hH
  have hHan : AnalyticAt ℂ H 0 := by
    refine (hΦan 0 hZω0).sub (analyticAt_conj_comp_conj ?_)
    rw [map_zero]; exact hΦan 0 hZω0
  have hτt : Tendsto (fun s => ((‖ζ s‖ : ℝ) : ℂ)) (𝓝[≠] s₀) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun s => ‖ζ s‖) (𝓝 s₀) (𝓝 ‖ζ s₀‖) := hζan.continuousAt.norm.tendsto
      rw [hζ0, norm_zero] at h1
      have h2 : Tendsto (fun s => ((‖ζ s‖ : ℝ) : ℂ)) (𝓝 s₀) (𝓝 0) := by
        have := (Complex.continuous_ofReal.tendsto 0).comp h1
        simpa [Function.comp_def] using this
      exact h2.mono_left nhdsWithin_le_nhds
    · filter_upwards [hζne] with s hs
      simpa using norm_ne_zero_iff.mpr hs
  have hHfreq : ∃ᶠ τ in 𝓝[≠] (0 : ℂ), H τ = 0 := by
    refine hτt.frequently ?_
    refine (hfreqω.and_eventually (nhdsWithin_le_nhds hleft)).mono ?_
    rintro s ⟨⟨hsE, hsζ, hdir⟩, hsl⟩
    have hωτ : ω * ((‖ζ s‖ : ℝ) : ℂ) = ζ s := by
      rw [← hdir]; field_simp [show ((‖ζ s‖ : ℝ) : ℂ) ≠ 0 by exact_mod_cast norm_ne_zero_iff.mpr hsζ]
    have hΦs : Φ ((‖ζ s‖ : ℝ) : ℂ) = deriv xi s := by simp only [hΦ]; rw [hωτ, hsl]
    simp only [hH, Complex.conj_ofReal, hΦs]
    have hd : deriv xi s = ((deriv xi s).re : ℂ) := Complex.ext (by simp) (by simp [hsE.2])
    rw [hd, Complex.conj_ofReal, sub_self]
  have hHzero : ∀ᶠ τ in 𝓝 (0 : ℂ), H τ = 0 := (hHan.frequently_zero_iff_eventually_zero).mp hHfreq
  -- `ξ'` is real on the real arc
  have hofR : Tendsto (fun τ : ℝ => (τ : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto (0 : ℝ))
  have hrealΦ : ∀ᶠ τ : ℝ in 𝓝 0, (Φ (τ : ℂ)).im = 0 := by
    filter_upwards [hofR.eventually hHzero] with τ hτ
    simp only [hH, Complex.conj_ofReal, sub_eq_zero] at hτ
    have := congrArg Complex.im hτ
    rw [Complex.conj_im] at this
    linarith
  -- the derivative identity `ξ'(Z w)·Z'(w) = k w^{k−1}`
  have hderivZ : ∀ᶠ w in 𝓝 (0 : ℂ), deriv xi (Z w) * deriv Z w = (k : ℂ) * w ^ (k - 1) := by
    obtain ⟨U, hU, hUo, h0U⟩ := _root_.eventually_nhds_iff.mp (hξZ.and hZan.eventually_analyticAt)
    filter_upwards [hUo.mem_nhds h0U] with w hw
    have heq : (fun w => xi (Z w)) =ᶠ[𝓝 w] fun w => xi s₀ + w ^ k :=
      Filter.eventually_of_mem (hUo.mem_nhds hw) fun y hy => (hU y hy).1
    have h1 : HasDerivAt (fun w => xi (Z w)) (deriv xi (Z w) * deriv Z w) w :=
      ((hxian (Z w)).differentiableAt.hasDerivAt).comp w ((hU w hw).2.differentiableAt.hasDerivAt)
    have h2 : HasDerivAt (fun w => xi s₀ + w ^ k) ((k : ℂ) * w ^ (k - 1)) w := by
      simpa using (hasDerivAt_pow k w).const_add (xi s₀)
    exact h1.unique (h2.congr_of_eventuallyEq heq)
  have hω0 : ω ≠ 0 := by intro h; rw [h, norm_zero] at hωn; norm_num at hωn
  have hlinR : Tendsto (fun τ : ℝ => ω * (τ : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ω)).mul hofR
  have hprod : ∀ᶠ τ : ℝ in 𝓝 0, Φ τ * (ω * deriv Z (ω * τ)) =
      (k : ℂ) * ω ^ k * ((τ : ℂ) ^ (k - 1)) := by
    filter_upwards [hlinR.eventually hderivZ] with τ hτ
    simp only [hΦ]
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)
    calc deriv xi (Z (ω * τ)) * (ω * deriv Z (ω * τ))
        = ω * (deriv xi (Z (ω * τ)) * deriv Z (ω * τ)) := by ring
      _ = ω * ((k : ℂ) * (ω * τ) ^ (k - 1)) := by rw [hτ]
      _ = (k : ℂ) * ω ^ (k - 1 + 1) * ((τ : ℂ) ^ (k - 1)) := by rw [mul_pow, pow_succ]; ring
      _ = (k : ℂ) * ω ^ k * ((τ : ℂ) ^ (k - 1)) := by rw [hk1]
  -- `ξ' ≠ 0` off `s₀`
  have hξ'ne : ∀ᶠ s in 𝓝[≠] s₀, deriv xi s ≠ 0 := by
    rcases ((hxian s₀).deriv).eventually_eq_zero_or_eventually_ne_zero with hz | hnz
    · exfalso
      obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hz
      have hconst : ∀ s ∈ ball s₀ ε, xi s = xi s₀ := fun s hs =>
        isOpen_ball.is_const_of_deriv_eq_zero (convex_ball s₀ ε).isPreconnected
          xi_differentiable.differentiableOn (fun y hy => hball y hy) hs (mem_ball_self hε)
      have : analyticOrderAt (fun s => xi s - xi s₀) s₀ = ⊤ := by
        rw [analyticOrderAt_eq_top]
        filter_upwards [Metric.ball_mem_nhds s₀ hε] with s hs
        rw [hconst s hs, sub_self]
      exact hordtop this
    · exact hnz
  have hgne : Tendsto (fun τ : ℝ => Z (ω * τ)) (𝓝[≠] 0) (𝓝[≠] s₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((hZc.comp hlinR).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [nhdsWithin_le_nhds (hlinR.eventually hright), self_mem_nhdsWithin]
      with τ hτ hτ0 heq
    have : ω * (τ : ℂ) = 0 := by rw [← hτ, heq, hζ0]
    exact hτ0 (by simpa [hω0] using this)
  have hΦne : ∀ᶠ τ : ℝ in 𝓝[≠] 0, Φ τ ≠ 0 := hgne.eventually hξ'ne
  -- the real arc `g` and its derivative
  set g : ℝ → ℂ := fun τ => Z (ω * τ) with hg
  have hgd : ∀ᶠ τ : ℝ in 𝓝 0, HasDerivAt g (ω * deriv Z (ω * τ)) τ := by
    filter_upwards [hlinR.eventually hZan.eventually_analyticAt] with τ hτ
    have hZd : HasDerivAt Z (deriv Z (ω * τ)) (ω * τ) := hτ.differentiableAt.hasDerivAt
    have hl : HasDerivAt (fun w : ℂ => ω * w) ω (τ : ℂ) := by
      simpa using (hasDerivAt_id (τ : ℂ)).const_mul ω
    have hG : HasDerivAt (fun w : ℂ => Z (ω * w)) (deriv Z (ω * τ) * ω) (τ : ℂ) :=
      hZd.comp (τ : ℂ) hl
    have := hG.comp_ofReal
    rw [mul_comm] at this
    exact this
  have hgre : ∀ᶠ τ : ℝ in 𝓝[≠] 0, (ω * deriv Z (ω * τ)).re = 0 := by
    filter_upwards [nhdsWithin_le_nhds hprod, nhdsWithin_le_nhds hrealΦ, hΦne] with τ h1 h2 h3
    have hre0 : ((k : ℂ) * ω ^ k * ((τ : ℂ) ^ (k - 1))).re = 0 := by
      have e : (k : ℂ) * ω ^ k * ((τ : ℂ) ^ (k - 1)) = (((k : ℝ) * τ ^ (k - 1) : ℝ) : ℂ) * ω ^ k := by
        push_cast; ring
      rw [e, Complex.re_ofReal_mul, hωk, mul_zero]
    have hΦre : (Φ τ).re ≠ 0 := fun h => h3 (Complex.ext h h2)
    rw [← h1, Complex.mul_re, h2, zero_mul, sub_zero] at hre0
    exact (mul_eq_zero.mp hre0).resolve_left hΦre
  -- `Re ξ = 0` along the arc
  have hreξ : ∀ᶠ τ : ℝ in 𝓝 0, (xi (g τ)).re = 0 := by
    filter_upwards [hlinR.eventually hξZ] with τ hτ
    simp only [hg]
    rw [hτ, Complex.add_re, hs₀.1, zero_add, mul_pow, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, hωk]
    ring
  -- choose a common radius
  obtain ⟨δ₁, hδ₁, hall₁⟩ := Metric.eventually_nhds_iff.mp (hgd.and hreξ)
  obtain ⟨δ₂, hδ₂, hall₂⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hgre)
  set δ := min δ₁ δ₂ with hδ
  have hδpos : 0 < δ := lt_min hδ₁ hδ₂
  have hIoo : ∀ τ ∈ Ioo (0 : ℝ) δ, HasDerivAt g (ω * deriv Z (ω * τ)) τ ∧ (xi (g τ)).re = 0 ∧
      (ω * deriv Z (ω * τ)).re = 0 := by
    intro τ hτ
    have hd1 : dist τ 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hτ.1]; exact hτ.2.trans_le (min_le_left _ _)
    have hd2 : dist τ 0 < δ₂ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hτ.1]; exact hτ.2.trans_le (min_le_right _ _)
    exact ⟨(hall₁ hd1).1, (hall₁ hd1).2, hall₂ hd2 (ne_of_gt hτ.1)⟩
  -- `Re g` is constant on `(0, δ)` and equals `Re s₀`
  have hconst : ∀ τ ∈ Ioo (0 : ℝ) δ, ∀ τ' ∈ Ioo (0 : ℝ) δ, (g τ).re = (g τ').re := by
    intro τ hτ τ' hτ'
    refine isOpen_Ioo.is_const_of_deriv_eq_zero (f := fun x => (g x).re) isPreconnected_Ioo ?_ ?_
      hτ hτ'
    · intro x hx
      have hd : HasDerivAt (fun x => (g x).re) (Complex.reCLM (ω * deriv Z (ω * x))) x :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hIoo x hx).1
      exact hd.differentiableAt.differentiableWithinAt
    · intro x hx
      have hd : HasDerivAt (fun x => (g x).re) (Complex.reCLM (ω * deriv Z (ω * x))) x :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hIoo x hx).1
      rw [hd.deriv, Pi.zero_apply, Complex.reCLM_apply]
      exact (hIoo x hx).2.2
  have hg0 : g 0 = s₀ := by simp only [hg, Complex.ofReal_zero, mul_zero]; exact hZ0
  have hgcont : Tendsto g (𝓝[>] 0) (𝓝 s₀) := (hZc.comp hlinR).mono_left nhdsWithin_le_nhds
  -- `Re g = Re s₀` on `(0, δ)`
  have hreEq : ∀ τ ∈ Ioo (0 : ℝ) δ, (g τ).re = s₀.re := by
    intro τ hτ
    have hlim : Tendsto (fun τ' => (g τ').re) (𝓝[>] 0) (𝓝 s₀.re) :=
      (Complex.continuous_re.tendsto s₀).comp hgcont
    have hev : ∀ᶠ τ' in 𝓝[>] (0 : ℝ), (g τ).re = (g τ').re := by
      filter_upwards [Ioo_mem_nhdsGT hδpos] with τ' hτ'
      exact hconst τ hτ τ' hτ'
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlim
  -- the arc avoids `s₀`
  obtain ⟨δ₃, hδ₃, hall₃⟩ := Metric.eventually_nhds_iff.mp (hlinR.eventually hright)
  set δ' := min δ δ₃ with hδ'
  have hδ'pos : 0 < δ' := lt_min hδpos hδ₃
  have hsub : ∀ τ ∈ Ioo (0 : ℝ) δ', τ ∈ Ioo (0 : ℝ) δ := fun τ hτ =>
    ⟨hτ.1, hτ.2.trans_le (min_le_left _ _)⟩
  set h₀ : ℝ := s₀.re - 1 / 2 with hh₀
  have hzero : ∀ τ ∈ Ioo (0 : ℝ) δ', cosProducer h₀ (((g τ).im : ℝ) : ℂ) = 0 := by
    intro τ hτ
    rw [cosProducer_ofReal]
    have e : (1 / 2 : ℂ) + (h₀ : ℂ) + (((g τ).im : ℝ) : ℂ) * I = g τ := by
      apply Complex.ext
      · simp [hh₀, hreEq τ (hsub τ hτ)]
      · simp
    rw [e, (hIoo τ (hsub τ hτ)).2.1]; simp
  have hne : ∀ τ ∈ Ioo (0 : ℝ) δ', (g τ).im ≠ s₀.im := by
    intro τ hτ heq
    have hgs : g τ = s₀ := Complex.ext (hreEq τ (hsub τ hτ)) heq
    have hd3 : dist τ 0 < δ₃ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hτ.1]; exact hτ.2.trans_le (min_le_right _ _)
    have hr := hall₃ hd3
    have : ω * (τ : ℂ) = 0 := by
      rw [← hr]; change ζ (g τ) = 0; rw [hgs, hζ0]
    rcases mul_eq_zero.mp this with h | h
    · exact hω0 h
    · exact (ne_of_gt hτ.1) (by exact_mod_cast h)
  have himT : Tendsto (fun τ => (((g τ).im : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] ((s₀.im : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto _).comp ((Complex.continuous_im.tendsto s₀).comp hgcont)
    · filter_upwards [Ioo_mem_nhdsGT hδ'pos] with τ hτ
      intro h
      exact hne τ hτ (by exact_mod_cast (Set.mem_singleton_iff.mp h))
  have hfr : ∃ᶠ z in 𝓝[≠] ((s₀.im : ℝ) : ℂ), cosProducer h₀ z = 0 :=
    himT.frequently (Filter.Eventually.frequently
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ'pos) hzero))
  have hzeroev := ((differentiable_cosProducer h₀).analyticAt _).frequently_zero_iff_eventually_zero.mp hfr
  exact analyticOrderAt_cosProducer_ne_top h₀ _ (analyticOrderAt_eq_top.mpr hzeroev)

/-- **Exceptional points are finite in compact sets.** -/
theorem finite_xiExceptional_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    {s ∈ K | IsXiExceptional s}.Finite := by
  have hc : IsCompact (K ∩ {s | IsXiExceptional s}) := hK.inter_right isClosed_xiExceptional
  have hfin := hc.finite (isDiscrete_iff_discreteTopology.mpr (by
    rw [discreteTopology_subtype_iff]
    intro x _
    rw [Filter.inf_principal_eq_bot]
    filter_upwards [eventually_not_xiExceptional x] with y hy hmem
    exact hy hmem.2))
  exact hfin

/-- The exceptional depths of a window are finitely many. -/
theorem finite_exceptionalDepths (T₁ T₂ : ℝ) :
    {h : ℝ | h ∈ Ioc 0 (1 / 2) ∧ windowEPMass T₁ T₂ h ≠ 0}.Finite := by
  classical
  have hK : IsCompact (Icc (1 / 2 : ℝ) 1 ×ℂ Icc T₁ T₂) := isCompact_Icc.reProdIm isCompact_Icc
  have hfin := finite_xiExceptional_of_isCompact hK
  refine (hfin.image (fun s => s.re - 1 / 2)).subset ?_
  rintro h ⟨hh, hM⟩
  -- a nonzero mass needs an exceptional point
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (windowEPSet_finite T₁ T₂ h).toFinset := by
    by_contra hnone
    push Not at hnone
    apply hM
    unfold windowEPMass
    rw [Finset.eq_empty_of_forall_notMem hnone, Finset.sum_empty]
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxI, hx0, hxd⟩ := hx
  refine ⟨1 / 2 + h + x * I, ⟨?_, ?_, ?_⟩, by simp⟩
  · rw [mem_reProdIm]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one]
    norm_num
    exact ⟨⟨by linarith [hh.1], by linarith [hh.2]⟩, hxI⟩
  · rw [cosProducer_ofReal] at hx0
    exact_mod_cast hx0
  · rw [deriv_cosProducer_ofReal] at hxd
    have := neg_eq_zero.mp hxd
    exact_mod_cast this

/-- **The exceptional-point index law, clean form.** In a window between shadow-free heights the
exceptional depths `0 < h ≤ ½` are finitely many, and their exceptional masses add up to at least
the number of non-real zeros of `Ξ` in the window. -/
theorem windowDefectCount_zero_le_exceptional_mass_finite {T₁ T₂ : ℝ} (hT : T₁ < T₂)
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2) :
    windowDefectCount T₁ T₂ 0 ≤
      ∑ h ∈ (finite_exceptionalDepths T₁ T₂).toFinset, windowEPMass T₁ T₂ h := by
  rcases windowDefectCount_zero_le_exceptional_mass hT hg₁ hg₂ with hinf | ⟨F, hF, hle⟩
  · exact absurd (finite_exceptionalDepths T₁ T₂) hinf
  · refine hle.trans (Finset.sum_le_sum_of_subset fun h hh => ?_)
    rw [Set.Finite.mem_toFinset]; exact hF h hh

end

end RHTower
