import GaloisForLFunctions.RHTower.GaussianFormationUndampedLimit
import GaloisForLFunctions.RHTower.FormationAnchoredCubicSpecialization
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# The zero endpoint of the formation-anchored cubic homotopy

For a rectangle `D` compactly inside `1/2 < Re s < 1` (centered coordinate `s = 1/2 + z i`) with
`ξ ≠ 0` on its boundary, the anchored cubic defects `T_{D,x} = (R_{D,0} − R_{D,x})³`, `x > 0`, all
have trace equal to the number of enclosed Xi zero copies, and `x ↦ T_{D,x}` is trace-norm
continuous on `(0, ∞)`.  This file adds the endpoint `x → 0⁺`.

* **Endpoint** (`FormationRectangle.tendsto_traceNorm_anchoredCubicDefect_zero`).  If every zero of
  `ξ` has `Re ρ ≤ θ` with `θ` strictly left of `D`, then `‖T_{D,x}‖₁ → 0`.  The uniform undamped
  passage makes the Gaussian boundary log-derivatives converge uniformly to those of `ξ`, hence the
  boundary phases and their derivatives converge, hence the polarizations converge in
  Hilbert–Schmidt norm.
* **Sub-unit gate** (`FormationRectangle.card_le_traceNorm_anchoredCubicDefect`).  The enclosed
  multiplicity is at most `‖T_{D,x}‖₁` for every anchor, since `|Tr T| ≤ ‖T‖₁`.
* **Endpoint law** (`riemannHypothesis_iff_forall_tendsto_traceNorm_anchoredCubicDefect`,
  `riemannHypothesis_iff_forall_exists_traceNorm_anchoredCubicDefect_lt_one`).  RH holds iff every
  such rectangle's defects tend to `0` in trace norm, iff every such rectangle has one anchor with
  `‖T_{D,x}‖₁ < 1`.  Every off-line zero sits inside such a rectangle, because Xi zeros are isolated.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped Real

namespace RHTower

open XiAtlasFinitePart

/-- Anchors tending to `0⁺`. -/
def anchorZeroFilter : Filter (Ioi (0 : ℝ)) := Filter.comap Subtype.val (𝓝[>] (0 : ℝ))

instance anchorZeroFilter_neBot : anchorZeroFilter.NeBot := by
  refine Filter.comap_neBot fun t ht => ?_
  have hne : (𝓝[>] (0 : ℝ)).NeBot := inferInstance
  obtain ⟨x, hx⟩ := hne.nonempty_of_mem (inter_mem ht self_mem_nhdsWithin)
  exact ⟨⟨x, hx.2⟩, hx.1⟩

/-- The centered logarithmic derivative is the completed one rotated by `I`. -/
theorem logDeriv_XiC_eq_logDeriv_xi_mul_I (z : ℂ) :
    logDeriv XiC z = logDeriv xi (1 / 2 + z * I) * I := by
  have hinner : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I z := by
    simpa using ((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)
  have hXiC : HasDerivAt XiC (deriv xi (1 / 2 + z * I) * I) z :=
    ((xi_differentiable _).hasDerivAt).comp z hinner
  rw [logDeriv_apply, logDeriv_apply, hXiC.deriv, XiC]
  ring

private theorem eventually_xi_ne_zero_punctured (ρ : ℂ) : ∀ᶠ s in 𝓝[≠] ρ, xi s ≠ 0 := by
  rcases (xi_differentiable.analyticAt ρ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hxiA : AnalyticOnNhd ℂ xi univ := fun z _ => xi_differentiable.analyticAt z
    have hEq := hxiA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ ρ) (show xi =ᶠ[𝓝 ρ] 0 from h)
    exact xi_ne_zero_of_one_le_re (show (1 : ℝ) ≤ (2 : ℂ).re by norm_num) (hEq (mem_univ 2))
  · exact h

namespace FormationRectangle

variable (R : FormationRectangle)

/-- **Zero endpoint of the anchor homotopy.**  If every zero of `ξ` has `Re ρ ≤ θ` and `θ` lies
strictly left of the rectangle, the anchored cubic defects tend to `0` in trace norm as `x → 0⁺`. -/
theorem tendsto_traceNorm_anchoredCubicDefect_zero {θ : ℝ}
    (hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ θ) (hR : θ < 1 / 2 - R.z₂.im) :
    Tendsto (fun x => traceNorm CCMCircleL2 (R.anchoredCubicDefect x)) anchorZeroFilter
      (𝓝 0) := by
  set η : ℝ := min (min (1 / 2 - R.z₂.im - θ) (1 / 2)) 1 with hη
  have hη0 : 0 < η := lt_min (lt_min (by linarith) (by norm_num)) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηa : η ≤ 1 / 2 - R.z₂.im - θ := (min_le_left _ _).trans (min_le_left _ _)
  have hηb : η ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  set M : ℝ := 1 / 2 + (|R.z₁.re| + |R.z₂.re|) + 1 / 2 with hM
  set K : Set ℂ := Set.range (fun t : ℝ => 1 / 2 + rectangleBoundaryPath R.z₁ R.z₂ t * I)
    with hK
  have hKprop : ∀ s ∈ K, θ + η ≤ s.re ∧ η ≤ s.re ∧ s.re ≤ 2 - 1 ∧ ‖s‖ ≤ M := by
    rintro s ⟨t, rfl⟩
    have hmem := Complex.mem_reProdIm.1 (R.path_mem t)
    rw [uIcc_of_le R.re_lt.le, uIcc_of_le R.im_lt.le] at hmem
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hmem
    rw [re_half_add_mul_I]
    have hlo := R.im_lower
    have hup := R.im_upper
    refine ⟨by linarith, by linarith, by linarith, ?_⟩
    set z := rectangleBoundaryPath R.z₁ R.z₂ t
    have h1 : |z.re| ≤ |R.z₁.re| + |R.z₂.re| := by
      rw [abs_le]
      constructor
      · linarith [neg_abs_le R.z₁.re, abs_nonneg R.z₂.re]
      · linarith [le_abs_self R.z₂.re, abs_nonneg R.z₁.re]
    have h2 : |z.im| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    calc ‖1 / 2 + z * I‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z * I‖ := norm_add_le _ _
      _ = 1 / 2 + ‖z‖ := by rw [norm_mul, Complex.norm_I, mul_one]; norm_num
      _ ≤ 1 / 2 + (|z.re| + |z.im|) := by gcongr; exact Complex.norm_le_abs_re_add_abs_im z
      _ ≤ M := by rw [hM]; linarith
  have hconv : ∀ ε > 0, ∀ᶠ x in anchorZeroFilter, ∀ t,
      ‖logDeriv (R.gaussianDatum x).F (rectangleBoundaryPath R.completedDatum.z₁
          R.completedDatum.z₂ t) -
        logDeriv R.completedDatum.F (rectangleBoundaryPath R.completedDatum.z₁
          R.completedDatum.z₂ t)‖ ≤ ε := by
    intro ε hε
    have h := eventually_norm_logDeriv_gaussianFormation_sub_logDeriv_xi_le hθ hη0 hη1 one_pos hε
      hKprop
    filter_upwards [h.comap Subtype.val] with x hx t
    have hmem : rectangleBoundaryPath R.z₁ R.z₂ t ∈ centeredRightHalfPlane := R.path_im_lt t
    change ‖logDeriv (gaussianFormationCentered x.1) (rectangleBoundaryPath R.z₁ R.z₂ t) -
      logDeriv XiC (rectangleBoundaryPath R.z₁ R.z₂ t)‖ ≤ ε
    rw [logDeriv_gaussianFormationCentered x.2 hmem, logDeriv_XiC_eq_logDeriv_xi_mul_I, ← sub_mul,
      norm_mul, Complex.norm_I, mul_one]
    exact hx _ ⟨t, rfl⟩
  obtain ⟨hval, hder⟩ := R.completedDatum.phase_convergence (fun x => R.gaussianDatum x)
    (fun _ => rfl) (fun _ => rfl) hconv
  have h := R.completedPhase.tendsto_traceNorm_relativeCubicDefect R.completedPhase
    (fun x => R.gaussianPhase x) hval hder
  have hself : restrictedProjectionCubicDefect R.completedPhase.polarization
      R.completedPhase.polarization = 0 := by
    simp [restrictedProjectionCubicDefect, restrictedProjectionDisplacement]
  simpa [hself, anchoredCubicDefect] using h

/-- **Sub-unit gate.**  The enclosed Xi multiplicity is bounded by the trace norm of every anchored
cubic defect. -/
theorem card_le_traceNorm_anchoredCubicDefect (x : Ioi (0 : ℝ)) :
    ((xiZeroCopyClosedRectangle R.z₁ R.z₂).card : ℝ) ≤
      traceNorm CCMCircleL2 (R.anchoredCubicDefect x) := by
  have h := norm_opTrace_le_traceNorm (R.anchoredCubicDefect_memSchattenClass_one x)
  rw [R.opTrace_anchoredCubicDefect_eq x, R.opTrace_formationCubicDefect.2] at h
  simpa using h

theorem card_eq_zero_of_traceNorm_lt_one {x : Ioi (0 : ℝ)}
    (hx : traceNorm CCMCircleL2 (R.anchoredCubicDefect x) < 1) :
    (xiZeroCopyClosedRectangle R.z₁ R.z₂).card = 0 := by
  have h := (R.card_le_traceNorm_anchoredCubicDefect x).trans_lt hx
  exact Nat.lt_one_iff.1 (by exact_mod_cast h)

end FormationRectangle

/-- Every Xi zero right of the critical line is enclosed by a strict-right rectangle whose
boundary avoids the zeros. -/
theorem exists_formationRectangle_of_xi_eq_zero {ρ : ℂ} (hρ : xi ρ = 0) (hρre : 1 / 2 < ρ.re) :
    ∃ R : FormationRectangle, 0 < (xiZeroCopyClosedRectangle R.z₁ R.z₂).card := by
  have hρ1 : ρ.re < 1 := by
    by_contra h
    push Not at h
    exact xi_ne_zero_of_one_le_re h hρ
  obtain ⟨r, hr0, hr⟩ := Metric.mem_nhdsWithin_iff.1 (eventually_xi_ne_zero_punctured ρ)
  set w : ℂ := (ρ - 1 / 2) * (-I) with hw
  have hwρ : 1 / 2 + w * I = ρ := by
    rw [hw]; ring_nf; rw [Complex.I_sq]; ring
  have hw_re : w.re = ρ.im := by simp [hw]
  have hw_im : w.im = 1 / 2 - ρ.re := by simp [hw]
  set h : ℝ := min (r / 4) (min ((ρ.re - 1 / 2) / 2) ((1 - ρ.re) / 2)) with hh
  have hh0 : 0 < h := lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hhr : h ≤ r / 4 := min_le_left _ _
  have hh1 : h ≤ (ρ.re - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hh2 : h ≤ (1 - ρ.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set z₁ : ℂ := w - (h : ℂ) - (h : ℂ) * I with hz₁
  set z₂ : ℂ := w + (h : ℂ) + (h : ℂ) * I with hz₂
  have hz₁re : z₁.re = w.re - h := by simp [hz₁]
  have hz₁im : z₁.im = w.im - h := by simp [hz₁]
  have hz₂re : z₂.re = w.re + h := by simp [hz₂]
  have hz₂im : z₂.im = w.im + h := by simp [hz₂]
  let R : FormationRectangle :=
    { z₁ := z₁
      z₂ := z₂
      re_lt := by rw [hz₁re, hz₂re]; linarith
      im_lt := by rw [hz₁im, hz₂im]; linarith
      im_lower := by rw [hz₁im, hw_im]; linarith
      im_upper := by rw [hz₂im, hw_im]; linarith
      xi_ne_zero := by
        intro z hz hb
        have hmem := Complex.mem_reProdIm.1 hz
        rw [uIcc_of_le (by rw [hz₁re, hz₂re]; linarith),
          uIcc_of_le (by rw [hz₁im, hz₂im]; linarith)] at hmem
        obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hmem
        rw [hz₁re] at hr1
        rw [hz₂re] at hr2
        rw [hz₁im] at hi1
        rw [hz₂im] at hi2
        have hre_abs : |(z - w).re| ≤ h := by
          rw [Complex.sub_re, abs_le]; constructor <;> linarith
        have him_abs : |(z - w).im| ≤ h := by
          rw [Complex.sub_im, abs_le]; constructor <;> linarith
        have hdist : dist (1 / 2 + z * I) ρ < r := by
          rw [dist_eq_norm, ← hwρ, show 1 / 2 + z * I - (1 / 2 + w * I) = (z - w) * I by ring,
            norm_mul, Complex.norm_I, mul_one]
          calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
            _ ≤ h + h := add_le_add hre_abs him_abs
            _ < r := by linarith
        have hneq : 1 / 2 + z * I ∈ ({ρ} : Set ℂ)ᶜ := by
          rw [mem_compl_singleton_iff, ← hwρ]
          intro heq
          have hzw : z = w := by
            have : z * I = w * I := by linear_combination heq
            exact mul_right_cancel₀ Complex.I_ne_zero this
          rw [hzw] at hb
          rw [hz₁re, hz₂re, hz₁im, hz₂im] at hb
          rcases hb with hb | hb | hb | hb <;> linarith
        change xi (1 / 2 + z * I) ≠ 0
        exact hr ⟨Metric.mem_ball.2 hdist, hneq⟩ }
  have hXiw : XiC w = 0 := by
    change xi (1 / 2 + w * I) = 0
    rw [hwρ]; exact hρ
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy w).1 hXiw
  refine ⟨R, Finset.card_pos.2 ⟨q, ?_⟩⟩
  rw [mem_xiZeroCopyClosedRectangle, hq]
  change w ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im)
  rw [Complex.mem_reProdIm, hz₁re, hz₂re, hz₁im, hz₂im]
  constructor
  · rw [uIcc_of_le (by linarith)]; constructor <;> linarith
  · rw [uIcc_of_le (by linarith)]; constructor <;> linarith

/-- **TG endpoint law, sub-unit form.**  RH holds iff every strict-right rectangle has an anchor
`x > 0` whose formation-anchored cubic defect has trace norm below one. -/
theorem riemannHypothesis_iff_forall_exists_traceNorm_anchoredCubicDefect_lt_one :
    RiemannHypothesis ↔ ∀ R : FormationRectangle, ∃ x : Ioi (0 : ℝ),
      traceNorm CCMCircleL2 (R.anchoredCubicDefect x) < 1 := by
  constructor
  · intro hRH R
    have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := by
      intro ρ hρ
      by_contra h
      push Not at h
      exact (rh_iff_xi_ne_zero_right.mp hRH) ρ (mem_rightHalf.mpr h) hρ
    have hlim := R.tendsto_traceNorm_anchoredCubicDefect_zero hθ (by linarith [R.im_upper])
    exact (hlim.eventually (gt_mem_nhds one_pos)).exists
  · intro h
    rw [rh_iff_xi_ne_zero_right]
    intro s hs hzero
    obtain ⟨R, hR⟩ := exists_formationRectangle_of_xi_eq_zero hzero (mem_rightHalf.mp hs)
    obtain ⟨x, hx⟩ := h R
    have := R.card_eq_zero_of_traceNorm_lt_one hx
    omega

/-- **TG endpoint law, limit form.**  RH holds iff for every strict-right rectangle the
formation-anchored cubic defects tend to `0` in trace norm as the anchor tends to `0⁺`. -/
theorem riemannHypothesis_iff_forall_tendsto_traceNorm_anchoredCubicDefect :
    RiemannHypothesis ↔ ∀ R : FormationRectangle,
      Tendsto (fun x => traceNorm CCMCircleL2 (R.anchoredCubicDefect x)) anchorZeroFilter
        (𝓝 0) := by
  constructor
  · intro hRH R
    have hθ : ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ 1 / 2 := by
      intro ρ hρ
      by_contra h
      push Not at h
      exact (rh_iff_xi_ne_zero_right.mp hRH) ρ (mem_rightHalf.mpr h) hρ
    exact R.tendsto_traceNorm_anchoredCubicDefect_zero hθ (by linarith [R.im_upper])
  · intro h
    refine riemannHypothesis_iff_forall_exists_traceNorm_anchoredCubicDefect_lt_one.2 fun R => ?_
    exact ((h R).eventually (gt_mem_nhds one_pos)).exists

end RHTower
