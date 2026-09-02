import GaloisForLFunctions.RHTower.LevinsonEntirePhaseAdvance

/-!
# Hardy's `Z` as a real node amplitude times a polar factor

With the critical-line zeros of the entire detector divided out, `G♯ = Q·H` with `H` nonvanishing on
the segment.  On the line the node polynomial is `Q(½+iτ) = i^M ∏ (τ − τ_j)^{m_j}`: a fixed power of
`i` times a *real* amplitude.  Since the detector identity reads `Y·Z = 2 Re[e^{iθ}G]`, the real
amplitude factors straight out and

```text
Z(τ) = (∏_j (τ − τ_j)^{m_j}) · ρ(τ) · cos φ(τ),      ρ > 0, φ continuous,
```

with `φ` the phase of `i^M e^{iθ(τ)} H(½+iτ) · conj(½+iτ−1)²`.  The reflected quadratic factor
replaces the pole term `(s−1)^{-2}`, and its phase velocity `(¼+τ²)^{-1}` is positive, so the
advance of `φ` is at least the archimedean increment plus the argument variation of `H`.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

theorem linePt_sub_linePt (τ u : ℝ) : linePt τ - linePt u = ((τ - u : ℝ) : ℂ) * I := by
  unfold linePt
  push_cast
  ring

/-- On the critical line the node polynomial of a set of line nodes is a fixed power of `i` times a
real amplitude. -/
theorem lineProd_eq_pow_I_mul_amp {pts : Finset ℂ} (m : ℂ → ℕ)
    (hline : ∀ c ∈ pts, c.re = 1 / 2) (τ : ℝ) :
    (∏ c ∈ pts, (linePt τ - c) ^ (m c))
      = I ^ (∑ c ∈ pts, m c) * ((∏ c ∈ pts, (τ - c.im) ^ (m c) : ℝ) : ℂ) := by
  classical
  have hstep : ∀ c ∈ pts, (linePt τ - c) ^ (m c)
      = I ^ (m c) * (((τ - c.im) ^ (m c) : ℝ) : ℂ) := by
    intro c hc
    have hc' : linePt τ - c = ((τ - c.im : ℝ) : ℂ) * I := by
      apply Complex.ext
      · rw [Complex.sub_re, linePt_re, hline c hc]
        simp
      · rw [Complex.sub_im, linePt_im]
        simp
    rw [hc', mul_comm, mul_pow]
    push_cast
    ring
  rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  push_cast
  rfl

/-- The reflected linear factor `conj (s-1)` restricted to the critical line. -/
def lineConj (u : ℝ) : ℂ := ((-1 / 2 : ℝ) : ℂ) - (u : ℂ) * I

theorem lineConj_ne_zero (u : ℝ) : lineConj u ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [lineConj] at this

theorem hasDerivAt_lineConj (u : ℝ) : HasDerivAt lineConj (-I) u := by
  have h : HasDerivAt (fun x : ℝ => ((-1 / 2 : ℝ) : ℂ) - (x : ℂ) * I) (-(1 * I)) u :=
    ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const I).const_sub _
  rw [show (-I : ℂ) = -(1 * I) by ring]
  exact h

theorem continuous_lineConj : Continuous lineConj := by
  unfold lineConj
  exact continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)

theorem linePt_sub_one_inv_sq (u : ℝ) :
    ((linePt u - 1) ^ 2)⁻¹
      = ((((Complex.normSq (linePt u - 1))⁻¹ ^ 2 : ℝ)) : ℂ) * (lineConj u * lineConj u) := by
  have hne : linePt u - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [Complex.sub_re, linePt_re, Complex.one_re] at this
    norm_num at this
  have hconj : (starRingEnd ℂ) (linePt u - 1) = lineConj u := by
    apply Complex.ext
    · simp [lineConj, linePt, Complex.sub_re]
      norm_num
    · simp [lineConj, linePt, Complex.sub_im]
  have hinv : (linePt u - 1)⁻¹
      = lineConj u * (((Complex.normSq (linePt u - 1))⁻¹ : ℝ) : ℂ) := by
    rw [Complex.inv_def, hconj]
  rw [show ((linePt u - 1) ^ 2)⁻¹ = (linePt u - 1)⁻¹ * (linePt u - 1)⁻¹ by
    rw [sq, mul_inv], hinv]
  push_cast
  ring

/-- The imaginary part of the logarithmic derivative of the reflected quadratic factor. -/
theorem im_neg_two_I_div_lineConj (u : ℝ) :
    ((-2 * I) / lineConj u).im = 1 / (1 / 4 + u ^ 2) := by
  have hns : Complex.normSq (lineConj u) = 1 / 4 + u ^ 2 := by
    rw [Complex.normSq_apply]
    simp [lineConj]
    ring
  rw [Complex.div_im, hns]
  simp [lineConj]
  ring


/-- **The factored polar form of Hardy's `Z`.**  Once the critical-line zeros of the entire
detector have been divided out, `Z` is a real node amplitude times a genuine polar factor, and the
phase advance is bounded below by the archimedean increment plus the argument variation of the
cofactor. -/
theorem exists_factored_polar_hardyZ_advance_of_Y_pos {lam : ℝ}
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hY : ∀ u ∈ Icc T₁ T₂, (0 : ℝ) < (levinsonY (lam : ℂ) (linePt u)).re)
    {pts : Finset ℂ} {m : ℂ → ℕ} {H : ℂ → ℂ}
    (hline : ∀ c ∈ pts, c.re = 1 / 2)
    (hH : Differentiable ℂ H)
    (hfact : ∀ z, levinsonGEntire (lam : ℂ) z = (∏ c ∈ pts, (z - c) ^ (m c)) * H z)
    (hHne : ∀ τ ∈ Icc T₁ T₂, H (linePt τ) ≠ 0) :
    ∃ ρ φ : ℝ → ℝ, ContinuousOn φ (Icc T₁ T₂) ∧ (∀ τ ∈ Icc T₁ T₂, 0 < ρ τ) ∧
      (∀ τ ∈ Icc T₁ T₂,
        hardyZ τ = (∏ c ∈ pts, (τ - c.im) ^ (m c)) * (ρ τ * Real.cos (φ τ))) ∧
      (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ τ in T₁..T₂, (logDeriv H (linePt τ)).re) ≤ φ T₂ - φ T₁ := by
  classical
  set Mtot : ℕ := ∑ c ∈ pts, m c with hMtot
  have hHan : AnalyticOnNhd ℂ H Set.univ := hH.differentiableOn.analyticOnNhd isOpen_univ
  have hHc : Continuous fun u : ℝ => H (linePt u) := hH.continuous.comp continuous_linePt'
  have hH'c : Continuous fun u : ℝ => deriv H (linePt u) :=
    continuous_iff_continuousAt.mpr fun u =>
      ((hHan.deriv _ (Set.mem_univ _)).continuousAt).comp continuous_linePt'.continuousAt
  have hHderiv : ∀ u : ℝ, HasDerivAt (fun v : ℝ => H (linePt v)) (deriv H (linePt u) * I) u := by
    intro u
    have hpath : HasDerivAt linePt I u := by
      unfold linePt
      have h := ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const I).const_add
        (((1 / 2 : ℝ) : ℂ))
      simpa using h
    exact (hH (linePt u)).hasDerivAt.comp u hpath
  set A : ℝ → ℂ := fun u => Complex.exp (I * (gammaHardyTheta u : ℂ)) with hAdef
  have hAderiv : ∀ u : ℝ, HasDerivAt A (A u * (I * (gammaHardyPhaseRate u : ℂ))) u := by
    intro u
    have hθ : HasDerivAt (fun v : ℝ => I * (gammaHardyTheta v : ℂ))
        (I * (gammaHardyPhaseRate u : ℂ)) u :=
      ((hasDerivAt_gammaHardyTheta u).ofReal_comp).const_mul I
    simpa [hAdef, mul_comm] using hθ.cexp
  have hAne : ∀ u : ℝ, A u ≠ 0 := fun u => Complex.exp_ne_zero _
  have hAc : Continuous A := by
    refine Complex.continuous_exp.comp (continuous_const.mul ?_)
    exact Complex.continuous_ofReal.comp
      (continuous_iff_continuousAt.mpr fun u => (hasDerivAt_gammaHardyTheta u).continuousAt)
  set g : ℝ → ℂ :=
    fun u => (I ^ Mtot) * (A u * (H (linePt u) * (lineConj u * lineConj u))) with hgdef
  set g' : ℝ → ℂ := fun u => (I ^ Mtot) *
    ((A u * (I * (gammaHardyPhaseRate u : ℂ))) * (H (linePt u) * (lineConj u * lineConj u))
      + A u * ((deriv H (linePt u) * I) * (lineConj u * lineConj u)
        + H (linePt u) * (-I * lineConj u + lineConj u * (-I)))) with hg'def
  have hgderiv : ∀ u : ℝ, HasDerivAt g (g' u) u := by
    intro u
    have hsq : HasDerivAt (fun v : ℝ => lineConj v * lineConj v)
        (-I * lineConj u + lineConj u * (-I)) u :=
      (hasDerivAt_lineConj u).mul (hasDerivAt_lineConj u)
    have h1 := (hAderiv u).mul ((hHderiv u).mul hsq)
    have h2 := h1.const_mul (I ^ Mtot)
    exact h2
  have hgne : ∀ u ∈ Icc T₁ T₂, g u ≠ 0 := by
    intro u hu
    refine mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) ?_
    exact mul_ne_zero (hAne u)
      (mul_ne_zero (hHne u hu) (mul_ne_zero (lineConj_ne_zero u) (lineConj_ne_zero u)))
  have hgc : Continuous g := by
    rw [hgdef]
    exact continuous_const.mul
      (hAc.mul (hHc.mul (continuous_lineConj.mul continuous_lineConj)))
  have hg'c : Continuous g' := by
    rw [hg'def]
    refine continuous_const.mul (Continuous.add ?_ ?_)
    · exact (hAc.mul (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_gammaHardyPhaseRate))).mul
        (hHc.mul (continuous_lineConj.mul continuous_lineConj))
    · exact hAc.mul
        (((hH'c.mul continuous_const).mul (continuous_lineConj.mul continuous_lineConj)).add
          (hHc.mul ((continuous_const.mul continuous_lineConj).add
            (continuous_lineConj.mul continuous_const))))
  have hquot : ContinuousOn (fun u => g' u / g u) (Icc T₁ T₂) :=
    ContinuousOn.div hg'c.continuousOn hgc.continuousOn hgne
  obtain ⟨r, φ, hφc, hrpos, hpolar, hadv⟩ :=
    exists_continuousOn_polar_advance (f := g) (f' := g') hT
      (fun u _ => hgderiv u) hquot hgne
  -- the logarithmic derivative of the polar carrier
  have hquotEq : ∀ u ∈ Icc T₁ T₂, g' u / g u
      = I * (gammaHardyPhaseRate u : ℂ) + I * (deriv H (linePt u) / H (linePt u))
        + (-2 * I) / lineConj u := by
    intro u hu
    have hA0 := hAne u
    have hH0 := hHne u hu
    have hW0 := lineConj_ne_zero u
    have hI0 : (I : ℂ) ^ Mtot ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
    rw [hgdef, hg'def]
    field_simp
    ring
  have himEq : ∀ u ∈ Icc T₁ T₂, (g' u / g u).im
      = gammaHardyPhaseRate u + (logDeriv H (linePt u)).re + 1 / (1 / 4 + u ^ 2) := by
    intro u hu
    rw [hquotEq u hu, Complex.add_im, Complex.add_im, im_neg_two_I_div_lineConj, logDeriv_apply]
    simp [Complex.mul_im]
  have hHline_ne : ∀ u ∈ uIcc T₁ T₂, H (linePt u) ≠ 0 := by
    rw [uIcc_of_le hT]; exact hHne
  have hlogc : ContinuousOn (fun u : ℝ => (logDeriv H (linePt u)).re) (uIcc T₁ T₂) := by
    have : ContinuousOn (fun u : ℝ => deriv H (linePt u) / H (linePt u)) (uIcc T₁ T₂) :=
      ContinuousOn.div hH'c.continuousOn hHc.continuousOn hHline_ne
    simpa [logDeriv_apply, Function.comp_def] using Complex.continuous_re.comp_continuousOn this
  have hadvle : (gammaHardyTheta T₂ - gammaHardyTheta T₁)
      + (∫ τ in T₁..T₂, (logDeriv H (linePt τ)).re) ≤ φ T₂ - φ T₁ := by
    rw [hadv]
    have hcong : ∀ u ∈ uIcc T₁ T₂, (g' u / g u).im
        = gammaHardyPhaseRate u + (logDeriv H (linePt u)).re + 1 / (1 / 4 + u ^ 2) := by
      intro u hu
      rw [uIcc_of_le hT] at hu
      exact himEq u hu
    rw [intervalIntegral.integral_congr hcong]
    have hint₁ : IntervalIntegrable gammaHardyPhaseRate volume T₁ T₂ :=
      continuous_gammaHardyPhaseRate.intervalIntegrable T₁ T₂
    have hint₂ : IntervalIntegrable (fun u : ℝ => (logDeriv H (linePt u)).re) volume T₁ T₂ :=
      hlogc.intervalIntegrable
    have hint₃ : IntervalIntegrable (fun u : ℝ => 1 / (1 / 4 + u ^ 2)) volume T₁ T₂ := by
      refine Continuous.intervalIntegrable ?_ _ _
      fun_prop (disch := intro u; positivity)
    rw [intervalIntegral.integral_add (hint₁.add hint₂) hint₃,
      intervalIntegral.integral_add hint₁ hint₂, integral_gammaHardyPhaseRate]
    have hpos : (0 : ℝ) ≤ ∫ u in T₁..T₂, 1 / (1 / 4 + u ^ 2) :=
      intervalIntegral.integral_nonneg hT (fun u _ => by positivity)
    linarith
  -- the polar identity
  have hlineone : ∀ u : ℝ, linePt u - 1 ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    rw [Complex.sub_re, linePt_re, Complex.one_re] at this
    norm_num at this
  have hprodid : ∀ u : ℝ,
      Complex.exp (I * (gammaHardyTheta u : ℂ)) * levinsonG (lam : ℂ) (linePt u)
        = ((((∏ c ∈ pts, (u - c.im) ^ (m c))
              * ((Complex.normSq (linePt u - 1))⁻¹ ^ 2) : ℝ)) : ℂ) * g u := by
    intro u
    have hG : levinsonG (lam : ℂ) (linePt u)
        = levinsonGEntire (lam : ℂ) (linePt u) * ((linePt u - 1) ^ 2)⁻¹ := by
      rw [levinsonGEntire_eq (lam : ℂ) (linePt_ne_one u)]
      field_simp [hlineone u]
    rw [hG, hfact, lineProd_eq_pow_I_mul_amp m hline u, linePt_sub_one_inv_sq, hgdef, hAdef]
    push_cast
    ring
  have hns : ∀ u : ℝ, (0 : ℝ) < Complex.normSq (linePt u - 1) :=
    fun u => Complex.normSq_pos.mpr (hlineone u)
  refine ⟨fun u => 2 * ((Complex.normSq (linePt u - 1))⁻¹ ^ 2) * r u
      / (levinsonY (lam : ℂ) (linePt u)).re, φ, hφc, ?_, ?_, hadvle⟩
  · intro u hu
    have h1 := hrpos u hu
    have h2 := hY u hu
    have h3 := hns u
    positivity
  · intro u hu
    have h2 := hY u hu
    have hid : ((levinsonY (lam : ℂ) (linePt u)).re * hardyZ u : ℝ)
        = 2 * (Complex.exp (I * (gammaHardyTheta u : ℂ))
            * levinsonG (lam : ℂ) (linePt u)).re :=
      levinsonY_line_mul_hardyZ lam u
    rw [hprodid u, Complex.re_ofReal_mul, hpolar u hu] at hid
    refine mul_left_cancel₀ (ne_of_gt h2) ?_
    rw [hid]
    field_simp

/-- Legacy nonpositive-shift specialization of the factored polar theorem. -/
theorem exists_factored_polar_hardyZ_advance {lam : ℝ} (hlam : lam ≤ 0)
    {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ ≤ T₂)
    {pts : Finset ℂ} {m : ℂ → ℕ} {H : ℂ → ℂ}
    (hline : ∀ c ∈ pts, c.re = 1 / 2)
    (hH : Differentiable ℂ H)
    (hfact : ∀ z, levinsonGEntire (lam : ℂ) z = (∏ c ∈ pts, (z - c) ^ (m c)) * H z)
    (hHne : ∀ τ ∈ Icc T₁ T₂, H (linePt τ) ≠ 0) :
    ∃ ρ φ : ℝ → ℝ, ContinuousOn φ (Icc T₁ T₂) ∧ (∀ τ ∈ Icc T₁ T₂, 0 < ρ τ) ∧
      (∀ τ ∈ Icc T₁ T₂,
        hardyZ τ = (∏ c ∈ pts, (τ - c.im) ^ (m c)) * (ρ τ * Real.cos (φ τ))) ∧
      (gammaHardyTheta T₂ - gammaHardyTheta T₁)
          + (∫ τ in T₁..T₂, (logDeriv H (linePt τ)).re) ≤ φ T₂ - φ T₁ := by
  apply exists_factored_polar_hardyZ_advance_of_Y_pos (lam := lam) hT
  · intro u hu
    rw [levinsonY_line_eq, Complex.ofReal_re]
    have hd := log_pi_lt_re_digamma_quarter (le_trans h20 hu.1)
    have hmul : lam * ((Complex.digamma (((1 / 4 : ℝ) : ℂ)
        + ((u / 2 : ℝ) : ℂ) * Complex.I)).re - Real.log Real.pi) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hlam (sub_nonneg.mpr hd.le)
    linarith
  · exact hline
  · exact hH
  · exact hfact
  · exact hHne
