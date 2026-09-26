import GaloisForLFunctions.HTGeometry.ClockParametricHolomorphy
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Three-lines convexity of vertical mean squares

Let `F` be holomorphic on the open strip `l < Re z < u`, continuous and bounded on its closure. If
every vertical translate of a window `[A, B]` has mean square at most `S_L` on the left edge and at
most `S_R` on the right edge, then for `l ≤ σ ≤ u`

`∫_A^B ‖F(σ + it)‖² dt ≤ S_L^{1-λ} S_R^λ`,  `λ = (σ - l)/(u - l)`
(`integral_normSq_le_of_three_lines`).

The proof pairs `F` with its own conjugate on the line `Re z = σ`:
`Φ(z) = ∫_A^B F(z + it) · conj F(σ + it) dt` is holomorphic and bounded on the strip,
`Φ(σ) = I` is the mean square to be estimated, and Cauchy–Schwarz bounds `Φ` on the two edges by
`√(S_L I)` and `√(S_R I)`. Hadamard's three-line theorem then gives `I ≤ √I · √(S_L^{1-λ} S_R^λ)`.
-/

noncomputable section

open Complex Set Metric MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- Holomorphy of a compact parametric integral whose integrand is jointly continuous and
holomorphic in the parameter on an open set. -/
theorem differentiableOn_intervalIntegral_of_continuousOn_prod
    {a b : ℝ} {U : Set ℂ} (hU : IsOpen U) {F : ℝ → ℂ → ℂ}
    (hFc : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (univ ×ˢ U))
    (hFd : ∀ t : ℝ, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun w => ∫ t in a..b, F t w) U := by
  intro z hz
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.isOpen_iff.mp hU z hz
  let R : ℝ := ε / 2
  let r : ℝ := ε / 4
  have hRpos : 0 < R := by dsimp only [R]; linarith
  have hrpos : 0 < r := by dsimp only [r]; linarith
  have hbig : closedBall z R ⊆ U := by
    intro w hw
    apply hεsub
    rw [mem_ball]
    exact (mem_closedBall.mp hw).trans_lt (by dsimp only [R]; linarith)
  have hslice : ∀ t : ℝ, ContinuousOn (F t) U := fun t =>
    hFc.comp ((continuous_const.prodMk continuous_id).continuousOn)
      fun ζ hζ => ⟨mem_univ _, hζ⟩
  have hfixed : ∀ w ∈ U, Continuous fun t : ℝ => F t w := fun w hw =>
    hFc.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hw⟩
  obtain ⟨M, hM⟩ := ((isCompact_uIcc (a := a) (b := b)).prod
    (isCompact_closedBall z R)).exists_bound_of_continuousOn
      (hFc.mono fun q hq => ⟨mem_univ _, hbig hq.2⟩)
  have hnear : ∀ w ∈ ball z r, closedBall w r ⊆ closedBall z R := by
    intro w hw
    refine closedBall_subset_closedBall' ?_
    have hdist : dist w z < r := mem_ball.mp hw
    dsimp only [r] at hdist
    dsimp only [R, r]
    linarith
  have hdiffAt : ∀ (t : ℝ), ∀ ζ ∈ closedBall z R,
      DifferentiableAt ℂ (F t) ζ := by
    intro t ζ hζ
    exact (hFd t).differentiableAt (hU.mem_nhds (hbig hζ))
  have hbound : ∀ (t : ℝ), t ∈ uIcc a b → ∀ w ∈ ball z r,
      ‖deriv (F t) w‖ ≤ M / r := by
    intro t ht w hw
    have hsub := hnear w hw
    have hdc : DiffContOnCl ℂ (F t) (ball w r) := by
      refine ⟨fun ζ hζ =>
          (hdiffAt t ζ (hsub (ball_subset_closedBall hζ))).differentiableWithinAt, ?_⟩
      rw [closure_ball w hrpos.ne']
      exact (hslice t).mono fun ζ hζ => hbig (hsub hζ)
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdc fun ζ hζ => ?_
    exact hM (t, ζ) ⟨ht, hsub (sphere_subset_closedBall hζ)⟩
  have hderivCont : Continuous fun t : ℝ => deriv (F t) z := by
    refine GaloisForLFunctions.HTGeometry.continuous_deriv_parametric_on
      hRpos hFc hbig fun t ζ hζ => ?_
    exact hdiffAt t ζ (ball_subset_closedBall hζ)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball z r) (bound := fun _ => M / r) (F := fun w t => F t w)
    (F' := fun w t => deriv (F t) w) (ball_mem_nhds z hrpos)
    ?_ ?_ ?_ ?_ ?_ ?_).2.differentiableAt.differentiableWithinAt
  · refine Filter.eventually_of_mem (ball_mem_nhds z hrpos) fun w hw => ?_
    exact (hfixed w (hbig (hnear w hw (mem_closedBall_self hrpos.le)))).aestronglyMeasurable
  · exact (hfixed z hz).intervalIntegrable a b
  · exact hderivCont.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht w hw => ?_
    exact hbound t (uIoc_subset_uIcc ht) w hw
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ w hw => ?_
    exact (hdiffAt t w (hnear w hw (mem_closedBall_self hrpos.le))).hasDerivAt

/-- Retraction of `ℂ` onto the closed vertical strip `l ≤ Re z ≤ u`, clamping the real part. -/
def stripClampRe (l u : ℝ) (z : ℂ) : ℂ :=
  ((max l (min u z.re) : ℝ) : ℂ) + (z.im : ℂ) * I

theorem continuous_stripClampRe (l u : ℝ) : Continuous (stripClampRe l u) := by
  unfold stripClampRe
  fun_prop

theorem stripClampRe_mem {l u : ℝ} (hlu : l ≤ u) (z : ℂ) :
    stripClampRe l u z ∈ Complex.HadamardThreeLines.verticalClosedStrip l u := by
  show (stripClampRe l u z).re ∈ Icc l u
  simp only [stripClampRe, add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, I_im, mul_one,
    sub_self, add_zero]
  exact ⟨le_max_left _ _, max_le hlu (min_le_left _ _)⟩

theorem stripClampRe_of_mem {l u : ℝ} {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip l u) :
    stripClampRe l u z = z := by
  have hz' : z.re ∈ Icc l u := hz
  unfold stripClampRe
  rw [min_eq_right hz'.2, max_eq_right hz'.1]
  exact Complex.re_add_im z

theorem closure_verticalStrip {l u : ℝ} (hlu : l < u) :
    closure (Complex.HadamardThreeLines.verticalStrip l u) =
      Complex.HadamardThreeLines.verticalClosedStrip l u := by
  unfold Complex.HadamardThreeLines.verticalStrip Complex.HadamardThreeLines.verticalClosedStrip
  rw [Complex.closure_preimage_re, closure_Ioo hlu.ne]

/-- The elementary inequality behind Cauchy–Schwarz: if `X ≤ (κA + B/κ)/2` for every `κ > 0`, then
`X ≤ √(AB)`. -/
theorem le_sqrt_mul_of_forall_pos {X A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (h : ∀ κ : ℝ, 0 < κ → X ≤ (κ * A + B / κ) / 2) : X ≤ Real.sqrt (A * B) := by
  rcases hB.eq_or_lt with hB0 | hBpos
  · rw [← hB0, mul_zero, Real.sqrt_zero]
    by_contra hX
    push Not at hX
    have := h (X / A) (div_pos hX hA)
    rw [← hB0, zero_div, add_zero, div_mul_cancel₀ X hA.ne'] at this
    linarith
  · set κ : ℝ := Real.sqrt B / Real.sqrt A with hκ
    have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
    have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
    have hκpos : 0 < κ := div_pos hsB hsA
    have h1 := h κ hκpos
    have hA' : A = Real.sqrt A * Real.sqrt A := (Real.mul_self_sqrt hA.le).symm
    have hB' : B = Real.sqrt B * Real.sqrt B := (Real.mul_self_sqrt hBpos.le).symm
    have e1 : κ * A = Real.sqrt A * Real.sqrt B := by
      rw [hκ, div_mul_eq_mul_div, div_eq_iff hsA.ne']
      nth_rewrite 1 [hA']
      ring
    have e2 : B / κ = Real.sqrt A * Real.sqrt B := by
      rw [hκ, div_div_eq_mul_div, div_eq_iff hsB.ne']
      nth_rewrite 1 [hB']
      ring
    rw [e1, e2] at h1
    rw [Real.sqrt_mul hA.le]
    linarith

/-- Cauchy–Schwarz for interval integrals of continuous functions, in the form used by the
three-line argument. -/
theorem integral_norm_mul_le_sqrt_of_bound {f g : ℝ → ℂ} {A B SA : ℝ} (hAB : A ≤ B)
    (hf : Continuous f) (hg : Continuous g) (hSA : 0 < SA)
    (hfS : ∫ t in A..B, ‖f t‖ ^ 2 ≤ SA) :
    ∫ t in A..B, ‖f t‖ * ‖g t‖ ≤ Real.sqrt (SA * ∫ t in A..B, ‖g t‖ ^ 2) := by
  have hgS : 0 ≤ ∫ t in A..B, ‖g t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hAB fun t _ => by positivity
  refine le_sqrt_mul_of_forall_pos hSA hgS fun κ hκ => ?_
  have hint1 : IntervalIntegrable (fun t => ‖f t‖ * ‖g t‖) volume A B :=
    (hf.norm.mul hg.norm).intervalIntegrable A B
  have hint2 : IntervalIntegrable (fun t => (κ * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / κ) / 2) volume A B :=
    (((continuous_const.mul (hf.norm.pow 2)).add
      ((hg.norm.pow 2).div_const κ)).div_const 2).intervalIntegrable A B
  have hpt : ∀ t ∈ Icc A B, ‖f t‖ * ‖g t‖ ≤ (κ * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / κ) / 2 := by
    intro t _
    have hid : (κ * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / κ) / 2 - ‖f t‖ * ‖g t‖ =
        (κ * ‖f t‖ - ‖g t‖) ^ 2 / (2 * κ) := by
      field_simp
      ring
    have h0 : 0 ≤ (κ * ‖f t‖ - ‖g t‖) ^ 2 / (2 * κ) := by positivity
    linarith
  calc ∫ t in A..B, ‖f t‖ * ‖g t‖
      ≤ ∫ t in A..B, (κ * ‖f t‖ ^ 2 + ‖g t‖ ^ 2 / κ) / 2 :=
        intervalIntegral.integral_mono_on hAB hint1 hint2 hpt
    _ = (κ * ∫ t in A..B, ‖f t‖ ^ 2) / 2 + (∫ t in A..B, ‖g t‖ ^ 2) / κ / 2 := by
        have hc1 : IntervalIntegrable (fun t => κ * ‖f t‖ ^ 2) volume A B :=
          (continuous_const.mul (hf.norm.pow 2)).intervalIntegrable A B
        have hc2 : IntervalIntegrable (fun t => ‖g t‖ ^ 2 / κ) volume A B :=
          ((hg.norm.pow 2).div_const κ).intervalIntegrable A B
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add hc1 hc2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
        ring
    _ ≤ (κ * SA + (∫ t in A..B, ‖g t‖ ^ 2) / κ) / 2 := by
        have := mul_le_mul_of_nonneg_left hfS hκ.le
        linarith

/-- **Three-lines convexity of vertical mean squares.** -/
theorem integral_normSq_le_of_three_lines {F : ℂ → ℂ} {l u σ A B SL SR M : ℝ}
    (hlu : l < u) (hσl : l ≤ σ) (hσu : σ ≤ u) (hAB : A ≤ B)
    (hF : DiffContOnCl ℂ F (Complex.HadamardThreeLines.verticalStrip l u))
    (hM : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip l u, ‖F z‖ ≤ M)
    (hSL : 0 < SL) (hSR : 0 < SR)
    (hL : ∀ y : ℝ, ∫ t in A..B, ‖F ((l : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SL)
    (hR : ∀ y : ℝ, ∫ t in A..B, ‖F ((u : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ SR) :
    ∫ t in A..B, ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      SL ^ (1 - (σ - l) / (u - l)) * SR ^ ((σ - l) / (u - l)) := by
  set S := Complex.HadamardThreeLines.verticalClosedStrip l u with hS
  have hFc : ContinuousOn F S := by
    have := hF.continuousOn
    rwa [closure_verticalStrip hlu] at this
  have hmemLine : ∀ (x t : ℝ), x ∈ Icc l u → ((x : ℂ) + (t : ℂ) * I) ∈ S := by
    intro x t hx
    show ((x : ℂ) + (t : ℂ) * I).re ∈ Icc l u
    simpa using hx
  -- the clamped field is continuous everywhere
  set Fc : ℂ → ℂ := fun z => F (stripClampRe l u z) with hFcdef
  have hFcont : Continuous Fc :=
    hFc.comp_continuous (continuous_stripClampRe l u) (stripClampRe_mem hlu.le)
  have hFcEq : ∀ z ∈ S, Fc z = F z := fun z hz => by
    simp only [hFcdef, stripClampRe_of_mem hz]
  -- the center datum
  set c : ℝ → ℂ := fun t => (starRingEnd ℂ) (F ((σ : ℂ) + (t : ℂ) * I)) with hcdef
  have hlineσ : Continuous fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I) := by
    have h : Continuous fun t : ℝ => Fc ((σ : ℂ) + (t : ℂ) * I) := by
      exact hFcont.comp (by fun_prop)
    refine h.congr fun t => ?_
    exact hFcEq _ (hmemLine σ t ⟨hσl, hσu⟩)
  have hccont : Continuous c := (Complex.continuous_conj).comp hlineσ
  -- the scalar family
  set Φ : ℂ → ℂ := fun z => ∫ t in A..B, Fc (z + (t : ℂ) * I) * c t with hΦdef
  have hjoint : Continuous fun q : ℝ × ℂ => Fc (q.2 + (q.1 : ℂ) * I) * c q.1 :=
    (hFcont.comp (by fun_prop)).mul (hccont.comp continuous_fst)
  have hΦcont : Continuous Φ := by
    have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun (z : ℂ) (t : ℝ) => Fc (z + (t : ℂ) * I) * c t)
      (hjoint.comp continuous_swap) A B
    exact this
  have hstripOpen : IsOpen (Complex.HadamardThreeLines.verticalStrip l u) :=
    isOpen_Ioo.preimage Complex.continuous_re
  have hshift : ∀ (t : ℝ) (z : ℂ), z ∈ Complex.HadamardThreeLines.verticalStrip l u →
      z + (t : ℂ) * I ∈ Complex.HadamardThreeLines.verticalStrip l u := by
    intro t z hz
    show (z + (t : ℂ) * I).re ∈ Ioo l u
    have : (z + (t : ℂ) * I).re = z.re := by simp
    rw [this]
    exact hz
  have hopen_sub : Complex.HadamardThreeLines.verticalStrip l u ⊆ S :=
    fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hΦdiff : DifferentiableOn ℂ Φ (Complex.HadamardThreeLines.verticalStrip l u) := by
    refine differentiableOn_intervalIntegral_of_continuousOn_prod hstripOpen
      hjoint.continuousOn fun t => ?_
    have hdF : DifferentiableOn ℂ (fun z => F (z + (t : ℂ) * I) * c t)
        (Complex.HadamardThreeLines.verticalStrip l u) := by
      refine DifferentiableOn.mul_const ?_ _
      exact hF.differentiableOn.comp (differentiableOn_id.add_const _) fun z hz => hshift t z hz
    refine hdF.congr fun z hz => ?_
    simp only [hFcdef, stripClampRe_of_mem (hopen_sub (hshift t z hz))]
  have hΦd : DiffContOnCl ℂ Φ (Complex.HadamardThreeLines.verticalStrip l u) :=
    ⟨hΦdiff, hΦcont.continuousOn⟩
  -- boundedness
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM _ (hmemLine σ 0 ⟨hσl, hσu⟩))
  have hΦB : BddAbove ((norm ∘ Φ) '' S) := by
    refine ⟨M * M * |B - A|, ?_⟩
    rintro _ ⟨z, _, rfl⟩
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => ?_
    rw [norm_mul]
    have h1 : ‖Fc (z + (t : ℂ) * I)‖ ≤ M := hM _ (stripClampRe_mem hlu.le _)
    have h2 : ‖c t‖ ≤ M := by
      rw [hcdef, Complex.norm_conj]
      exact hM _ (hmemLine σ t ⟨hσl, hσu⟩)
    exact mul_le_mul h1 h2 (norm_nonneg _) hM0
  -- the center value
  set Icen : ℝ := ∫ t in A..B, ‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hIdef
  have hI0 : 0 ≤ Icen := intervalIntegral.integral_nonneg hAB fun t _ => by positivity
  have hΦσ : ‖Φ (σ : ℂ)‖ = Icen := by
    have hpt : ∀ t : ℝ, Fc ((σ : ℂ) + (t : ℂ) * I) * c t =
        ((‖F ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
      intro t
      rw [hFcEq _ (hmemLine σ t ⟨hσl, hσu⟩), hcdef, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
    simp only [hΦdef, hpt, intervalIntegral.integral_ofReal, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_of_nonneg hI0
  -- edge bounds
  have hedge : ∀ (x S' : ℝ), x ∈ Icc l u → 0 < S' →
      (∀ y : ℝ, ∫ t in A..B, ‖F ((x : ℂ) + ((y + t : ℝ) : ℂ) * I)‖ ^ 2 ≤ S') →
      ∀ z ∈ Complex.re ⁻¹' {x}, ‖Φ z‖ ≤ Real.sqrt (S' * Icen) := by
    intro x S' hx hS' hbound z hz
    have hzre : z.re = x := hz
    have hzeq : ∀ t : ℝ, z + (t : ℂ) * I = (x : ℂ) + ((z.im + t : ℝ) : ℂ) * I := by
      intro t
      apply Complex.ext <;> simp [hzre]
    have hfcont : Continuous fun t : ℝ => F ((x : ℂ) + ((z.im + t : ℝ) : ℂ) * I) := by
      have h : Continuous fun t : ℝ => Fc ((x : ℂ) + ((z.im + t : ℝ) : ℂ) * I) :=
        hFcont.comp (by fun_prop)
      refine h.congr fun t => ?_
      exact hFcEq _ (hmemLine x _ hx)
    calc ‖Φ z‖ ≤ ∫ t in A..B, ‖Fc (z + (t : ℂ) * I) * c t‖ :=
          intervalIntegral.norm_integral_le_integral_norm hAB
      _ = ∫ t in A..B, ‖F ((x : ℂ) + ((z.im + t : ℝ) : ℂ) * I)‖ *
            ‖F ((σ : ℂ) + (t : ℂ) * I)‖ := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [norm_mul, hzeq t, hFcEq _ (hmemLine x _ hx), hcdef, Complex.norm_conj]
      _ ≤ Real.sqrt (S' * Icen) :=
          integral_norm_mul_le_sqrt_of_bound hAB hfcont hlineσ hS' (hbound z.im)
  have hσS : (σ : ℂ) ∈ S := by
    show ((σ : ℂ)).re ∈ Icc l u
    simpa using (⟨hσl, hσu⟩ : σ ∈ Icc l u)
  have hthree := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := Φ) (z := (σ : ℂ)) (a := Real.sqrt (SL * Icen)) (b := Real.sqrt (SR * Icen))
    hlu hσS hΦd hΦB (hedge l SL ⟨le_rfl, hlu.le⟩ hSL hL) (hedge u SR ⟨hlu.le, le_rfl⟩ hSR hR)
  rw [hΦσ, Complex.ofReal_re] at hthree
  set lam : ℝ := (σ - l) / (u - l) with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one (by linarith)]
    linarith
  -- algebra: `√(SL I)^(1-λ) √(SR I)^λ = √I · √(SL^(1-λ) SR^λ)`
  set Q : ℝ := SL ^ (1 - lam) * SR ^ lam with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hfac : Real.sqrt (SL * Icen) ^ (1 - lam) * Real.sqrt (SR * Icen) ^ lam =
      Real.sqrt Icen * Real.sqrt Q := by
    rw [Real.sqrt_mul hSL.le, Real.sqrt_mul hSR.le,
      Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    have hI : Real.sqrt Icen ^ (1 - lam) * Real.sqrt Icen ^ lam = Real.sqrt Icen := by
      rcases (Real.sqrt_nonneg Icen).eq_or_lt with h0 | hpos
      · rw [← h0]
        rcases hlam0.eq_or_lt with hl0 | hlpos
        · rw [← hl0, sub_zero, Real.rpow_one, Real.rpow_zero, mul_one]
        · rw [Real.zero_rpow hlpos.ne', mul_zero]
      · rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
    have hQs : Real.sqrt Q = Real.sqrt SL ^ (1 - lam) * Real.sqrt SR ^ lam := by
      rw [hQ, Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
        Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hSL.le, ← Real.rpow_mul hSR.le,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), mul_comm (1 - lam),
        mul_comm lam]
    rw [hQs]
    calc Real.sqrt SL ^ (1 - lam) * Real.sqrt Icen ^ (1 - lam) *
          (Real.sqrt SR ^ lam * Real.sqrt Icen ^ lam)
        = (Real.sqrt Icen ^ (1 - lam) * Real.sqrt Icen ^ lam) *
          (Real.sqrt SL ^ (1 - lam) * Real.sqrt SR ^ lam) := by ring
      _ = _ := by rw [hI]
  rw [hfac] at hthree
  -- conclude
  rcases hI0.eq_or_lt with hI00 | hIpos
  · rw [← hI00]
    exact hQ0
  · have hsI : 0 < Real.sqrt Icen := Real.sqrt_pos.mpr hIpos
    have hsq : Real.sqrt Icen * Real.sqrt Icen ≤ Real.sqrt Icen * Real.sqrt Q := by
      rw [Real.mul_self_sqrt hI0]
      exact hthree
    have h2 : Real.sqrt Icen ≤ Real.sqrt Q := le_of_mul_le_mul_left hsq hsI
    exact (Real.sqrt_le_sqrt_iff hQ0).mp h2

end GaloisForLFunctions.HTGeometry
