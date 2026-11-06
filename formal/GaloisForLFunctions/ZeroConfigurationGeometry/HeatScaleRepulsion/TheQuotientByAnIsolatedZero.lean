import GaloisForLFunctions.ZeroConfigurationGeometry.HeatScaleRepulsion.TheHalfGaussAtAPowerLevel

/-!
# `ξ` with an isolated deep zero divided out

Let `ρ = ½ + d + it` be a simple zero of `ζ` which is the only zero right of `½ + d − 13η + η/4` within height `2`, at a
height of level `T^E`. Then `Λ(s) = c (ξ(s) − ξ(ρ))/(s − ρ)`, `c = 3/2 − d`, has the same line model as `ξ` at a height of
depth `d − 13η` and level `T^{2E}` (`IsolatedZero.lineModel`). Dividing out the zero costs only a constant, since the
level is measured on discs which keep a fixed distance from `ρ`, and the maximum principle fills in the disc about `ρ`.

The reflection `‖Λ(½ − x + iX)‖ ≤ ‖Λ(½ + x + iX)‖` survives the division, since `ρ` lies to the right of the critical
line (`norm_lineFn_neg_le`).
-/

set_option autoImplicit false

open Complex Set Metric Filter Topology MeasureTheory
open _root_.RHTower _root_.RHTower.DeBruijn
open GaloisForLFunctions.ArithmeticHarmonicAnalysis

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The point of abscissa `½ + d` at height `t`. -/
def depthPoint (d t : ℝ) : ℂ := 1 / 2 + (d : ℂ) + I * t

theorem depthPoint_re (d t : ℝ) : (depthPoint d t).re = 1 / 2 + d := by
  unfold depthPoint
  rw [re_point, Complex.ofReal_re]

theorem depthPoint_im (d t : ℝ) : (depthPoint d t).im = t := by
  unfold depthPoint
  rw [im_point, Complex.ofReal_im, add_zero]

/-- **An isolated deep zero at level `T^E`.** The zero `½ + d + it` of `ζ` is simple and is the only zero right of
`½ + d − 13η + η/4` within height `2`, and `|ζ| ≤ T^E + 2` there. This is the absence of a crowd. -/
structure IsolatedZero (d η E T t : ℝ) : Prop where
  hd : 13 * η ≤ d
  hd2 : d ≤ 1 / 2
  mem : t ∈ Icc T (2 * T)
  zero : riemannZeta (depthPoint d t) = 0
  simple : deriv riemannZeta (depthPoint d t) ≠ 0
  ne_zero : ∀ {s : ℂ}, 1 / 2 + (d - 13 * η) + η / 4 ≤ s.re → |s.im - t| ≤ 2 → s ≠ depthPoint d t →
    riemannZeta s ≠ 0
  norm_le : ∀ {s : ℂ}, 1 / 2 ≤ s.re → |s.im - t| ≤ 2 → ‖riemannZeta s‖ ≤ T ^ E + 2

/-- `ζ` with the zero divided out, normalised to agree with `ζ` at `2 + it`. -/
def quotZeta (d t : ℝ) (s : ℂ) : ℂ :=
  ((3 / 2 - d : ℝ) : ℂ) * dslope riemannZeta (depthPoint d t) s

/-- `ξ` with the zero divided out, with the same normalisation. -/
def quotXi (d t : ℝ) (s : ℂ) : ℂ :=
  ((3 / 2 - d : ℝ) : ℂ) * dslope xi (depthPoint d t) s

theorem differentiable_dslope_xi (ρ : ℂ) : Differentiable ℂ (dslope xi ρ) := by
  have h := (Complex.differentiableOn_dslope (s := univ) (c := ρ) (f := xi) univ_mem).mpr
    xi_differentiable.differentiableOn
  exact differentiableOn_univ.mp h

theorem differentiable_quotXi (d t : ℝ) : Differentiable ℂ (quotXi d t) :=
  (differentiable_dslope_xi _).const_mul _

theorem differentiableAt_dslope_zeta {ρ s : ℂ} (hρ : ρ ≠ 1) (hs : s ≠ 1) :
    DifferentiableAt ℂ (dslope riemannZeta ρ) s := by
  have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hd : DifferentiableOn ℂ riemannZeta {z : ℂ | z ≠ 1} := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hd' := (Complex.differentiableOn_dslope (hopen.mem_nhds hρ)).mpr hd
  exact hd'.differentiableAt (hopen.mem_nhds hs)

namespace IsolatedZero

variable {d η E T t : ℝ}

theorem depthPoint_ne_one (h : IsolatedZero d η E T t) (hT : 8 ≤ T) : depthPoint d t ≠ 1 := by
  intro he
  have him := depthPoint_im d t
  rw [he, Complex.one_im] at him
  linarith only [him, h.mem.1, hT]

theorem xi_eq_zero (h : IsolatedZero d η E T t) (hT : 8 ≤ T) : xi (depthPoint d t) = 0 := by
  have him : (depthPoint d t).im ≠ 0 := by
    rw [depthPoint_im]
    linarith only [h.mem.1, hT] |> fun h => ne_of_gt h
  rw [xi_eq_archG_mul_zeta_offReal him, h.zero, mul_zero]

/-- `ξ(s) = (s − ρ) (ξ(s) − ξ(ρ))/(s − ρ)`. -/
theorem sub_mul_dslope (h : IsolatedZero d η E T t) (hT : 8 ≤ T) (s : ℂ) :
    (s - depthPoint d t) * dslope xi (depthPoint d t) s = xi s := by
  have he := sub_smul_dslope xi (depthPoint d t) s
  rwa [h.xi_eq_zero hT, sub_zero, smul_eq_mul] at he

/-- Dividing out the zero respects the factorization `ξ = G ζ`, also at the zero itself. -/
theorem dslope_xi_eq (h : IsolatedZero d η E T t) (hT : 8 ≤ T) {s : ℂ} (hre : 0 < s.re) (him : s.im ≠ 0) :
    dslope xi (depthPoint d t) s = archG s * dslope riemannZeta (depthPoint d t) s := by
  have hne1 : s ≠ 1 := fun he => him (by rw [he]; simp)
  by_cases hs : s = depthPoint d t
  · subst hs
    rw [dslope_same, dslope_same]
    have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const
    have hev : xi =ᶠ[𝓝 (depthPoint d t)] fun z => archG z * riemannZeta z := by
      filter_upwards [hopen.mem_nhds him] with z hz using xi_eq_archG_mul_zeta_offReal hz
    have hd : HasDerivAt (fun z => archG z * riemannZeta z)
        (deriv archG (depthPoint d t) * riemannZeta (depthPoint d t) +
          archG (depthPoint d t) * deriv riemannZeta (depthPoint d t)) (depthPoint d t) :=
      (differentiableAt_archG hre).hasDerivAt.mul (differentiableAt_riemannZeta hne1).hasDerivAt
    rw [hev.deriv_eq, hd.deriv, h.zero, mul_zero, zero_add]
  · rw [dslope_of_ne _ hs, dslope_of_ne _ hs, slope_def_field, slope_def_field, h.xi_eq_zero hT, h.zero,
      sub_zero, sub_zero, xi_eq_archG_mul_zeta_offReal him, mul_div_assoc]

theorem three_halves_sub_pos (h : IsolatedZero d η E T t) : 1 ≤ 3 / 2 - d := by
  linarith only [h.hd2]

/-- The size of `(ζ(s) − ζ(ρ))/(s − ρ)`: off the disc about `ρ` by division, on it by the maximum principle. -/
theorem norm_dslope_zeta_le (h : IsolatedZero d η E T t) (hη : 0 < η) (hη2 : η ≤ 2) (hT : 8 ≤ T) {s : ℂ}
    (hs1 : 1 / 2 ≤ s.re) (hs2 : |s.im - t| ≤ 2) :
    ‖dslope riemannZeta (depthPoint d t) s‖ ≤ (T ^ E + 2) / η := by
  have hρne := h.depthPoint_ne_one hT
  have hT0 : 0 < T := by linarith only [hT]
  have hM : 0 ≤ T ^ E + 2 := by
    have := Real.rpow_pos_of_pos hT0 E
    positivity
  have hoff : ∀ z : ℂ, η ≤ ‖z - depthPoint d t‖ → 1 / 2 ≤ z.re → |z.im - t| ≤ 2 →
      ‖dslope riemannZeta (depthPoint d t) z‖ ≤ (T ^ E + 2) / η := by
    intro z hz hz1 hz2
    have hne : z ≠ depthPoint d t := by
      intro he
      rw [he, sub_self, norm_zero] at hz
      linarith only [hz, hη]
    rw [dslope_of_ne _ hne, slope_def_field, h.zero, sub_zero, norm_div]
    exact div_le_div₀ hM (h.norm_le hz1 hz2) hη hz
  rcases le_or_gt η ‖s - depthPoint d t‖ with hfar | hnear
  · exact hoff s hfar hs1 hs2
  have hball : ∀ z ∈ closedBall (depthPoint d t) η, z ≠ 1 ∧ 1 / 2 ≤ z.re ∧ |z.im - t| ≤ 2 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans hz)
    have him := abs_le.mp ((Complex.abs_im_le_norm _).trans hz)
    rw [Complex.sub_re, depthPoint_re] at hre
    rw [Complex.sub_im, depthPoint_im] at him
    refine ⟨?_, by linarith only [hre.1, h.hd, hη], abs_le.mpr ⟨by linarith only [him.1, hη2],
      by linarith only [him.2, hη2]⟩⟩
    intro he
    rw [he, Complex.one_im] at him
    linarith only [him.1, hη2, h.mem.1, hT]
  have hdiff : DifferentiableOn ℂ (dslope riemannZeta (depthPoint d t)) (closedBall (depthPoint d t) η) :=
    fun z hz => (differentiableAt_dslope_zeta hρne (hball z hz).1).differentiableWithinAt
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hdiff.diffContOnCl_ball subset_rfl) (fun z hz => ?_)
    (subset_closure (mem_ball_iff_norm.mpr hnear))
  rw [frontier_ball _ hη.ne'] at hz
  have hzc := sphere_subset_closedBall hz
  rw [mem_sphere_iff_norm] at hz
  exact hoff z hz.ge (hball z hzc).2.1 (hball z hzc).2.2

/-- Dividing out the zero and doubling the level keeps the size under `T^{E} + 2`. -/
theorem norm_quotZeta_le (h : IsolatedZero d η (E / 2) T t) (hη : 0 < η) (hη2 : η ≤ 2) (hT : 8 ≤ T)
    (hA : 3 / η ≤ T ^ (E / 2)) {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : |s.im - t| ≤ 2) :
    ‖quotZeta d t s‖ ≤ T ^ E + 2 := by
  have hT0 : 0 < T := by linarith only [hT]
  obtain ⟨A, hAdef⟩ : ∃ A, A = T ^ (E / 2) := ⟨_, rfl⟩
  rw [← hAdef] at hA
  have hTE : T ^ E = A * A := by
    rw [hAdef, ← Real.rpow_add hT0]
    congr 1
    ring
  have hb := h.norm_dslope_zeta_le hη hη2 hT hs1 hs2
  rw [← hAdef] at hb
  have hc0 : 0 ≤ 3 / 2 - d := by linarith only [h.hd2, h.hd, hη]
  have hc : 3 / 2 - d ≤ 3 / 2 := by linarith only [h.hd, hη]
  have h3η : 3 / 2 ≤ 3 / η := by
    rw [div_le_div_iff₀ (by norm_num) hη]
    linarith only [hη2]
  have hA2 : 3 / 2 ≤ A := h3η.trans hA
  have hA0 : 0 ≤ A := by linarith only [hA2]
  unfold quotZeta
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0, hTE]
  have hbound : (3 / 2 - d) * ‖dslope riemannZeta (depthPoint d t) s‖ ≤ 3 / 2 * ((A + 2) / η) :=
    mul_le_mul hc hb (norm_nonneg _) (by norm_num)
  refine hbound.trans ?_
  have hid : 3 / 2 * ((A + 2) / η) = (3 / η) * ((A + 2) / 2) := by
    field_simp
  rw [hid]
  have hA3 : (A + 2) / 2 ≤ A + 1 := by linarith only [hA0]
  have hup : (3 / η) * ((A + 2) / 2) ≤ A * ((A + 2) / 2) :=
    mul_le_mul_of_nonneg_right hA (by positivity)
  nlinarith only [hup, hA2, hA0]

/-- **The pair of quotients at depth `d − 13η` and level `T^E`.** -/
theorem levelPair (h : IsolatedZero d η (E / 2) T t) (hη : 0 < η) (hη1 : η ≤ 1) (hT : 8 ≤ T) (hE : 0 ≤ E)
    (hA : 3 / η ≤ T ^ (E / 2)) :
    LevelPair (quotZeta d t) (quotXi d t) (d - 13 * η) η E T t := by
  have hρne := h.depthPoint_ne_one hT
  have hc0 : (((3 / 2 - d : ℝ) : ℂ)) ≠ 0 := by
    have := h.three_halves_sub_pos
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith only [this]))
  have hne1 : ∀ {s : ℂ}, |s.im - t| ≤ 2 → s ≠ 1 := by
    intro s hs he
    rw [he, Complex.one_im] at hs
    have := (abs_le.mp hs).1
    linarith only [this, h.mem.1, hT]
  have hlog := Real.log_nonneg (show 1 ≤ T by linarith only [hT])
  have hD : 108 ≤ 12 * (E * Real.log T + 9) / η := by
    rw [le_div_iff₀ hη]
    have := mul_nonneg hE hlog
    nlinarith only [this, hη, hη1]
  have hone : 1 ≤ 24 * (E * Real.log T + 9) / η ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_nonneg hE hlog
    nlinarith only [this, hη, hη1]
  refine
    { hd := by linarith only [h.hd]
      hd2 := by linarith only [h.hd2, hη]
      mem := h.mem
      entire := differentiable_quotXi d t
      factor := fun {s} hre him => ?_
      diff := fun {s} _ hst => (differentiableAt_dslope_zeta hρne (hne1 hst)).const_mul _
      ne_zero := fun {s} hs hst => mul_ne_zero hc0 ?_
      norm_le := fun hs hst => h.norm_quotZeta_le hη (by linarith only [hη1]) hT hA hs hst
      anchor := ?_
      far_logDeriv := fun {s} hs hst => ?_
      far_ge := fun {s} hs hs3 hst => ?_ }
  · unfold quotXi quotZeta
    rw [h.dslope_xi_eq hT hre him]
    ring
  · by_cases hsρ : s = depthPoint d t
    · rw [hsρ, dslope_same]
      exact h.simple
    · rw [dslope_of_ne _ hsρ, slope_def_field, h.zero, sub_zero]
      exact div_ne_zero (h.ne_zero hs hst hsρ) (sub_ne_zero.mpr hsρ)
  · -- At the anchor the normalisation cancels the distance to the zero.
    have hsub : (2 + (t : ℂ) * I) - depthPoint d t = ((3 / 2 - d : ℝ) : ℂ) := by
      unfold depthPoint
      push_cast
      ring
    have hne : (2 + (t : ℂ) * I) ≠ depthPoint d t := by
      intro he
      rw [he, sub_self] at hsub
      exact hc0 hsub.symm
    have hval : quotZeta d t (2 + (t : ℂ) * I) = riemannZeta (2 + (t : ℂ) * I) := by
      unfold quotZeta
      rw [dslope_of_ne _ hne, slope_def_field, h.zero, sub_zero, hsub, mul_comm, div_mul_cancel₀ _ hc0]
    rw [hval]
    exact (norm_riemannZeta_bounds_of_two_le_re (by simp)).1
  · -- Right of the abscissa `2`, the zero contributes at most `1` to the logarithmic derivative.
    have hne1' : s ≠ 1 := hne1 hst
    have hsρ : s ≠ depthPoint d t := by
      intro he
      rw [he, depthPoint_re] at hs
      linarith only [hs, h.hd2]
    have hdist : 1 ≤ ‖s - depthPoint d t‖ := by
      have := (Complex.abs_re_le_norm (s - depthPoint d t))
      rw [Complex.sub_re, depthPoint_re] at this
      have h2 := le_abs_self (s.re - (1 / 2 + d))
      linarith only [this, h2, hs, h.hd2]
    have hdne : DifferentiableAt ℂ (dslope riemannZeta (depthPoint d t)) s :=
      differentiableAt_dslope_zeta hρne hne1'
    have hzeta : riemannZeta s ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by linarith only [hs])
    have hdn : dslope riemannZeta (depthPoint d t) s ≠ 0 := by
      rw [dslope_of_ne _ hsρ, slope_def_field, h.zero, sub_zero]
      exact div_ne_zero hzeta (sub_ne_zero.mpr hsρ)
    have hev : riemannZeta =ᶠ[𝓝 s] fun z => (z - depthPoint d t) *
        dslope riemannZeta (depthPoint d t) z := by
      filter_upwards with z
      have he := sub_smul_dslope riemannZeta (depthPoint d t) z
      rw [h.zero, sub_zero, smul_eq_mul] at he
      exact he.symm
    have hlogz : logDeriv riemannZeta s = logDeriv (fun z => z - depthPoint d t) s +
        logDeriv (dslope riemannZeta (depthPoint d t)) s := by
      rw [← logDeriv_mul (f := fun z => z - depthPoint d t) (g := dslope riemannZeta (depthPoint d t)) s
        (sub_ne_zero.mpr hsρ) hdn (by fun_prop) hdne, logDeriv_apply, logDeriv_apply,
        hev.deriv_eq, hev.eq_of_nhds]
    have hlin : logDeriv (fun z => z - depthPoint d t) s = 1 / (s - depthPoint d t) := by
      rw [logDeriv_apply]
      congr 1
      exact (((hasDerivAt_id' s).sub_const _).deriv)
    have hquot : logDeriv (quotZeta d t) s = logDeriv riemannZeta s - 1 / (s - depthPoint d t) := by
      have hconst : logDeriv (quotZeta d t) s = logDeriv (dslope riemannZeta (depthPoint d t)) s :=
        logDeriv_const_mul s _ hc0
      rw [hconst, hlogz, hlin]
      ring
    rw [hquot]
    refine (norm_sub_le _ _).trans ?_
    have hb := norm_logDeriv_riemannZeta_le_inv_sub_one_add_two (show 1 < s.re by linarith only [hs]) s.im
    rw [Complex.re_add_im] at hb
    have hi : 1 / (s.re - 1) ≤ 1 := (div_le_one (by linarith only [hs])).mpr (by linarith only [hs])
    have hinv : ‖1 / (s - depthPoint d t)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact (div_le_one (by linarith only [hdist])).mpr hdist
    linarith only [hb, hi, hinv, hone]
  · -- Between the abscissae `2` and `3` the quotient is bounded below directly.
    have hsρ : s ≠ depthPoint d t := by
      intro he
      rw [he, depthPoint_re] at hs
      linarith only [hs, h.hd2]
    have hzeta := (norm_riemannZeta_bounds_of_two_le_re hs.le).1
    have hdist : ‖s - depthPoint d t‖ ≤ 9 / 2 := by
      have hn := Complex.norm_le_abs_re_add_abs_im (s - depthPoint d t)
      rw [Complex.sub_re, Complex.sub_im, depthPoint_re, depthPoint_im] at hn
      have h1 : |s.re - (1 / 2 + d)| ≤ 5 / 2 := abs_le.mpr ⟨by linarith only [hs, h.hd2],
        by linarith only [hs3, h.hd, hη]⟩
      linarith only [hn, h1, hst]
    have hpos : 0 < ‖s - depthPoint d t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hsρ)
    have hc1 := h.three_halves_sub_pos
    have hval : ‖quotZeta d t s‖ =
        (3 / 2 - d) * (‖riemannZeta s‖ / ‖s - depthPoint d t‖) := by
      unfold quotZeta
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hc1]), dslope_of_ne _ hsρ,
        slope_def_field, h.zero, sub_zero, norm_div]
    rw [hval]
    have hlow : (1 / 3) / (9 / 2) ≤ ‖riemannZeta s‖ / ‖s - depthPoint d t‖ :=
      div_le_div₀ (norm_nonneg _) hzeta hpos hdist
    have hprod : (1 / 3) / (9 / 2) ≤ (3 / 2 - d) * (‖riemannZeta s‖ / ‖s - depthPoint d t‖) := by
      have hq0 : 0 ≤ ‖riemannZeta s‖ / ‖s - depthPoint d t‖ := by positivity
      nlinarith only [hlow, hc1, hq0]
    have hexp : Real.exp (-(12 * (E * Real.log T + 9) / η)) ≤ 1 / 5 := by
      have hadd := Real.add_one_le_exp (12 * (E * Real.log T + 9) / η)
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hadd, hD])
    linarith only [hprod, hexp]

theorem exists_norm_dslope_le (h : IsolatedZero d η E T t) (hT : 8 ≤ T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, ‖dslope xi (depthPoint d t) s‖ ≤ M + ‖xi s‖ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (depthPoint d t) 1).exists_bound_of_continuousOn
    (differentiable_dslope_xi (depthPoint d t)).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s => ?_⟩
  have hx := norm_nonneg (xi s)
  by_cases hs : s ∈ closedBall (depthPoint d t) 1
  · have := (hC s hs).trans (le_max_left C 0)
    linarith only [this, hx]
  · rw [mem_closedBall, dist_eq_norm, not_le] at hs
    have hne : s ≠ depthPoint d t := by
      intro he
      rw [he, sub_self, norm_zero] at hs
      linarith only [hs]
    rw [dslope_of_ne _ hne, slope_def_field, h.xi_eq_zero hT, sub_zero, norm_div]
    have hle : ‖xi s‖ / ‖s - depthPoint d t‖ ≤ ‖xi s‖ := div_le_self hx hs.le
    linarith only [hle, le_max_right C 0]

/-- Off the zero, the quotient on a line is `ξ` divided by the distance to the zero. -/
theorem norm_lineFn_eq (h : IsolatedZero d η E T t) (hT : 8 ≤ T) {X v : ℝ}
    (hv : (1 / 2 + (v : ℂ) + I * X) ≠ depthPoint d t) :
    ‖lineFn (quotXi d t) X v‖ = (3 / 2 - d) * ‖xiLine X v‖ / ‖(1 / 2 + (v : ℂ) + I * X) - depthPoint d t‖ := by
  have hc1 := h.three_halves_sub_pos
  unfold lineFn quotXi
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hc1]), dslope_of_ne _ hv,
    slope_def_field, h.xi_eq_zero hT, sub_zero, norm_div, mul_div_assoc]
  rfl

/-- The distance to the zero, on a line. -/
theorem norm_line_sub_depthPoint (X v : ℝ) :
    ‖(1 / 2 + (v : ℂ) + I * X) - depthPoint d t‖ = Real.sqrt ((v - d) ^ 2 + (X - t) ^ 2) := by
  have he : (1 / 2 + (v : ℂ) + I * X) - depthPoint d t = ((v - d : ℝ) : ℂ) + ((X - t : ℝ) : ℂ) * I := by
    unfold depthPoint
    push_cast
    ring
  rw [he, Complex.norm_add_mul_I]

/-- Right of `9/2`, the quotient inherits every growth bound of `ξ`, since the distance to the zero increases. -/
theorem norm_lineFn_le_of_xi (h : IsolatedZero d η E T t) (hT : 8 ≤ T) {X W w F : ℝ} (hW : 9 / 2 ≤ W)
    (hw : W ≤ w) (hF : 0 ≤ F) (hx : ‖xiLine X w‖ ≤ ‖xiLine X W‖ * F) :
    ‖lineFn (quotXi d t) X w‖ ≤ ‖lineFn (quotXi d t) X W‖ * F := by
  have hne : ∀ v : ℝ, 9 / 2 ≤ v → (1 / 2 + (v : ℂ) + I * X) ≠ depthPoint d t := by
    intro v hv he
    have hre := congrArg Complex.re he
    rw [re_point, Complex.ofReal_re, depthPoint_re] at hre
    linarith only [hre, hv, h.hd2]
  have hc1 := h.three_halves_sub_pos
  have hpos : 0 < ‖(1 / 2 + (W : ℂ) + I * X) - depthPoint d t‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hne W hW))
  have hmono : ‖(1 / 2 + (W : ℂ) + I * X) - depthPoint d t‖ ≤ ‖(1 / 2 + (w : ℂ) + I * X) - depthPoint d t‖ := by
    rw [norm_line_sub_depthPoint, norm_line_sub_depthPoint]
    apply Real.sqrt_le_sqrt
    have h1 : 0 ≤ W - d := by linarith only [hW, h.hd2]
    have h2 : W - d ≤ w - d := by linarith only [hw]
    have := pow_le_pow_left₀ h1 h2 2
    linarith only [this]
  rw [h.norm_lineFn_eq hT (hne w (hW.trans hw)), h.norm_lineFn_eq hT (hne W hW)]
  have hm : (3 / 2 - d) * ‖xiLine X w‖ ≤ (3 / 2 - d) * (‖xiLine X W‖ * F) :=
    mul_le_mul_of_nonneg_left hx (by linarith only [hc1])
  have hN : 0 ≤ (3 / 2 - d) * (‖xiLine X W‖ * F) := by
    have := norm_nonneg (xiLine X W)
    have hc : 0 ≤ 3 / 2 - d := by linarith only [hc1]
    positivity
  calc
    _ ≤ (3 / 2 - d) * (‖xiLine X W‖ * F) / ‖(1 / 2 + (w : ℂ) + I * X) - depthPoint d t‖ :=
      div_le_div_of_nonneg_right hm (norm_nonneg _)
    _ ≤ (3 / 2 - d) * (‖xiLine X W‖ * F) / ‖(1 / 2 + (W : ℂ) + I * X) - depthPoint d t‖ :=
      div_le_div_of_nonneg_left hN hpos hmono
    _ = _ := by ring

/-- **The reflection survives the division.** -/
theorem norm_lineFn_neg_le (h : IsolatedZero d η E T t) (hη : 0 < η) (hT : 8 ≤ T) (X : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    ‖lineFn (quotXi d t) X (-x)‖ ≤ ‖lineFn (quotXi d t) X x‖ := by
  have hd : 0 < d := by linarith only [h.hd, hη]
  have hc1 := h.three_halves_sub_pos
  have hnm : (1 / 2 + ((-x : ℝ) : ℂ) + I * X) ≠ depthPoint d t := by
    intro he
    have hre := congrArg Complex.re he
    rw [re_point, Complex.ofReal_re, depthPoint_re] at hre
    linarith only [hre, hx, hd]
  have hrefl : ‖xiLine X (-x)‖ = ‖xiLine X x‖ := by
    have hc := xi_half_sub_eq_conj x X
    unfold xiLine
    rw [hc, Complex.norm_conj]
  rw [h.norm_lineFn_eq hT hnm, hrefl]
  by_cases hp : (1 / 2 + (x : ℂ) + I * X) = depthPoint d t
  · have hz : ‖xiLine X x‖ = 0 := by
      unfold xiLine
      rw [hp, h.xi_eq_zero hT, norm_zero]
    rw [hz, mul_zero, zero_div]
    exact norm_nonneg _
  · rw [h.norm_lineFn_eq hT hp]
    have hpos : 0 < ‖(1 / 2 + (x : ℂ) + I * X) - depthPoint d t‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hp)
    refine div_le_div_of_nonneg_left (mul_nonneg (by linarith only [hc1]) (norm_nonneg _)) hpos ?_
    rw [norm_line_sub_depthPoint, norm_line_sub_depthPoint]
    apply Real.sqrt_le_sqrt
    nlinarith only [mul_nonneg hx hd.le]

/-- **The line model of the quotient.** -/
theorem lineModel (h : IsolatedZero d η (E / 2) T t) (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hT : 8 ≤ T) (hE : 0 ≤ E)
    (hA : 3 / η ≤ T ^ (E / 2)) :
    LineModel (quotXi d t) (d - 13 * η) η (powerSlopeError E η T) (powerRatio E η T) t := by
  obtain ⟨M, hM0, hM⟩ := h.exists_norm_dslope_le hT
  have hc1 := h.three_halves_sub_pos
  refine (h.levelPair hη (by linarith only [hη2]) hT hE hA).lineModel hη hη2 hT hE ?_ ?_ ?_
  · intro τ X hτ
    have hb : 0 < 1 / (16 * τ) := by positivity
    have h1 := (integrable_exp_neg_mul_sq hb).const_mul ((3 / 2 - d) * M)
    have h2 := (integrable_exp_mul_norm_xiLine hτ X).const_mul (3 / 2 - d)
    refine (h1.add h2).mono' ?_ (Eventually.of_forall fun w => ?_)
    · have hc : Continuous fun w : ℝ => Real.exp (-(w ^ 2 / (16 * τ))) * ‖lineFn (quotXi d t) X w‖ :=
        (by fun_prop : Continuous fun w : ℝ => Real.exp (-(w ^ 2 / (16 * τ)))).mul
          ((differentiable_quotXi d t).continuous.comp (by fun_prop)).norm
      exact hc.aestronglyMeasurable
    · have hn : ‖lineFn (quotXi d t) X w‖ ≤ (3 / 2 - d) * (M + ‖xiLine X w‖) := by
        unfold lineFn quotXi
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hc1])]
        exact mul_le_mul_of_nonneg_left (hM _) (by linarith only [hc1])
      have he : Real.exp (-(1 / (16 * τ)) * w ^ 2) = Real.exp (-(w ^ 2 / (16 * τ))) := by
        congr 1
        field_simp
      have hpos := Real.exp_pos (-(w ^ 2 / (16 * τ)))
      rw [Real.norm_of_nonneg (by positivity)]
      simp only [Pi.add_apply]
      rw [he]
      calc
        _ ≤ Real.exp (-(w ^ 2 / (16 * τ))) * ((3 / 2 - d) * (M + ‖xiLine X w‖)) :=
          mul_le_mul_of_nonneg_left hn hpos.le
        _ = _ := by ring
  · intro X w hX hw hwX
    have hm := norm_xiLine_le_model hX (u := 9 / 2) (w := w) ⟨le_rfl, hw.trans hwX⟩ ⟨hw, hwX⟩
    rw [abs_of_nonneg (by linarith only [hw])] at hm
    have hl := h.norm_lineFn_le_of_xi hT (X := X) le_rfl hw
      (F := Real.exp ((w - 9 / 2) * (horizontalSlope X).re) * Real.exp (1 / 8 * (w - 9 / 2)))
      (by positivity) (by rw [← mul_assoc]; exact hm)
    rw [← mul_assoc] at hl
    exact hl
  · intro X W w hX hW hWw
    have hg := norm_xiLine_le_far hX hW hWw
    rw [← horizontalSlope_re] at hg
    exact h.norm_lineFn_le_of_xi hT hW hWw (Real.exp_pos _).le hg

end IsolatedZero

end

end GaloisForLFunctions.ZeroConfigurationGeometry
