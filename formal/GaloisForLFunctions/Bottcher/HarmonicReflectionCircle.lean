/-
# Harmonic Schwarz reflection across the unit circle

The circle counterpart of `harmonicAt_reflect_line` (`HarmonicReflection.lean`).  The Green potential
`u₀ = log‖β∘γ‖` of the exterior Böttcher map is harmonic on the outer side of a smooth Julia arc and
tends to `0` at the arc (Green boundary regularity).  Its **odd reflection across the unit circle**,

  `reflectCircle u₀ w = if 1 ≤ ‖w‖ then u₀ w else - u₀ (1 / conj w)`,

is harmonic on the whole ball around a circle point — this is exactly the harmonic-extension
hypothesis `hu` of `continuesAcross_of_greenPotential_harmonic_extension` (`BottcherArcExtension.lean`).

The reflection is proved by **transport to the real axis**: the entire map `Ψ(t) = exp(-i t)` carries
the real axis to the unit circle, the upper half-plane to the exterior `{‖w‖ > 1}`, and *intertwines
complex conjugation with the circle inversion* `σ(w) = 1/conj w`:  `Ψ(conj t) = σ(Ψ t)`.  Hence
`reflectCircle u₀ ∘ Ψ` is the odd reflection across the real axis of `u₀ ∘ Ψ`, and the line reflection
`harmonicAt_reflect_line` applies; pulling back by the analytic local inverse of `Ψ`
(`exists_localInverse_of_continuation`, no branch cut) transports harmonicity to the circle point.

Off the circle the reflection is harmonic directly: `= u₀` (outer) or `= -u₀ ∘ σ` with
`σ = conj ∘ inv`, via `harmonicAt_comp_conj` and `harmonicAt_comp_analytic`.  Continuity across the arc
is the `ContinuousOn.piecewise` gluing of the two closed half-plane pieces, agreeing on the axis where
`u₀` vanishes.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib
import GaloisForLFunctions.Bottcher.HarmonicReflection
import GaloisForLFunctions.Bottcher.InteriorModulusObstruction

open Complex Set Metric InnerProductSpace Topology Filter
open scoped Classical

namespace Bottcher

/-- **Circle inversion** `σ(w) = 1 / conj w = w / ‖w‖²`.  Fixes the unit circle, swaps interior and
exterior, and is an involution off `0`. -/
noncomputable def circleInv (w : ℂ) : ℂ := ((starRingEnd ℂ) w)⁻¹

theorem norm_circleInv (w : ℂ) : ‖circleInv w‖ = ‖w‖⁻¹ := by
  rw [circleInv, norm_inv, RCLike.norm_conj]

theorem circleInv_ne_zero {w : ℂ} (hw : w ≠ 0) : circleInv w ≠ 0 := by
  rw [circleInv]; exact inv_ne_zero (by simpa using hw)

theorem circleInv_circleInv (w : ℂ) : circleInv (circleInv w) = w := by
  rw [circleInv, circleInv, map_inv₀, Complex.conj_conj, inv_inv]

theorem circleInv_fixes {w : ℂ} (hw : ‖w‖ = 1) : circleInv w = w := by
  have hmul : (starRingEnd ℂ) w * w = 1 := by
    rw [mul_comm, Complex.mul_conj]; norm_cast
    rw [normSq_eq_norm_sq, hw]; norm_num
  rw [circleInv]; exact inv_eq_of_mul_eq_one_right hmul

/-- **Odd reflection of `u₀` across the unit circle.** -/
noncomputable def reflectCircle (u₀ : ℂ → ℝ) (w : ℂ) : ℝ :=
  if 1 ≤ ‖w‖ then u₀ w else - u₀ (circleInv w)

theorem reflectCircle_outer {u₀ : ℂ → ℝ} {w : ℂ} (hw : 1 ≤ ‖w‖) :
    reflectCircle u₀ w = u₀ w := if_pos hw

theorem reflectCircle_inner {u₀ : ℂ → ℝ} {w : ℂ} (hw : ‖w‖ < 1) :
    reflectCircle u₀ w = - u₀ (circleInv w) := if_neg (not_le.mpr hw)

/-- **Oddness of the circle reflection under inversion.**  `reflectCircle u₀ (σ w) = -reflectCircle u₀ w`
for `w ≠ 0`, provided `u₀` vanishes on the circle (needed only at `‖w‖ = 1`, where `σ` fixes `w`). -/
theorem reflectCircle_circleInv {u₀ : ℂ → ℝ} {w : ℂ} (hw : w ≠ 0)
    (hz : ‖w‖ = 1 → u₀ w = 0) :
    reflectCircle u₀ (circleInv w) = - reflectCircle u₀ w := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · have h1 : 1 < ‖circleInv w‖ := by rw [norm_circleInv]; exact (one_lt_inv₀ hpos).mpr hlt
    rw [reflectCircle_outer (le_of_lt h1), reflectCircle_inner hlt]; ring
  · rw [circleInv_fixes heq, reflectCircle_outer (le_of_eq heq.symm), hz heq]; ring
  · have h1 : ‖circleInv w‖ < 1 := by rw [norm_circleInv]; exact (inv_lt_one₀ hpos).mpr hgt
    rw [reflectCircle_inner h1, reflectCircle_outer (le_of_lt hgt), circleInv_circleInv w]

/-- **Off-circle harmonicity, exterior side.**  Where `1 < ‖w‖` and `u₀` is harmonic, so is the
reflection (there `reflectCircle u₀ = u₀`). -/
theorem harmonicAt_reflectCircle_outer {u₀ : ℂ → ℝ} {w : ℂ} (hw : 1 < ‖w‖)
    (h : HarmonicAt u₀ w) : HarmonicAt (reflectCircle u₀) w := by
  refine (harmonicAt_congr_nhds ?_).mpr h
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with z hz
  exact reflectCircle_outer (le_of_lt hz)

/-- **Off-circle harmonicity, interior side.**  Where `‖w‖ < 1` (and `w ≠ 0`) and `u₀` is harmonic at
the reflected point `σ w`, the reflection `= -u₀ ∘ σ` is harmonic.  `σ = conj ∘ (·)⁻¹`, so this is
`harmonicAt_comp_conj` followed by `harmonicAt_comp_analytic` with the analytic `z ↦ z⁻¹`. -/
theorem harmonicAt_reflectCircle_inner {u₀ : ℂ → ℝ} {w : ℂ} (hw : ‖w‖ < 1) (hwne : w ≠ 0)
    (hσ : HarmonicAt u₀ (circleInv w)) : HarmonicAt (reflectCircle u₀) w := by
  -- u₀ ∘ conj is harmonic at w⁻¹  (since conj (w⁻¹) = (conj w)⁻¹ = circleInv w)
  have hcc : HarmonicAt (fun z => u₀ ((starRingEnd ℂ) z)) (w⁻¹) := by
    apply harmonicAt_comp_conj
    rw [map_inv₀]; exact hσ
  have hinv : AnalyticAt ℂ (fun z : ℂ => z⁻¹) w := by
    simpa using (analyticAt_id (𝕜 := ℂ) (z := w)).inv hwne
  have hcomp := harmonicAt_comp_analytic hcc hinv
  have hneg := hcomp.neg
  refine (harmonicAt_congr_nhds ?_).mpr hneg
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hw] with z hz
  simp only [reflectCircle_inner hz, circleInv, Pi.neg_apply, map_inv₀]

/-! ### Transport map `Ψ(t) = exp(-i t)` -/

/-- The transport map `Ψ(t) = exp(-i·t)`: it carries the real axis to the unit circle, the upper
half-plane `{Im t > 0}` to the exterior `{‖w‖ > 1}`, and **intertwines complex conjugation with the
circle inversion** `σ = circleInv`:  `σ (Ψ t) = Ψ (conj t)`. -/
noncomputable def reflTransport (t : ℂ) : ℂ := Complex.exp (-(Complex.I * t))

theorem norm_reflTransport (t : ℂ) : ‖reflTransport t‖ = Real.exp t.im := by
  rw [reflTransport, Complex.norm_exp]
  congr 1
  simp only [neg_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  ring

theorem reflTransport_ne_zero (t : ℂ) : reflTransport t ≠ 0 := Complex.exp_ne_zero _

theorem analyticAt_reflTransport (t : ℂ) : AnalyticAt ℂ reflTransport t := by
  apply analyticAt_cexp.comp
  exact (analyticAt_const.mul analyticAt_id).neg

theorem hasDerivAt_reflTransport (t : ℂ) :
    HasDerivAt reflTransport (reflTransport t * (-Complex.I)) t := by
  have h1 : HasDerivAt (fun t : ℂ => -(Complex.I * t)) (-Complex.I) t := by
    simpa using ((hasDerivAt_id t).const_mul Complex.I).neg
  exact h1.cexp

theorem deriv_reflTransport_ne_zero (t : ℂ) : deriv reflTransport t ≠ 0 := by
  rw [(hasDerivAt_reflTransport t).deriv]
  exact mul_ne_zero (reflTransport_ne_zero t) (by simp [Complex.I_ne_zero])

/-- **The intertwining identity.**  `circleInv (Ψ t) = Ψ (conj t)`. -/
theorem circleInv_reflTransport (t : ℂ) :
    circleInv (reflTransport t) = reflTransport ((starRingEnd ℂ) t) := by
  simp only [circleInv, reflTransport]
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_I]
  ring

/-! ### The reflection across the arc -/

/-- **Harmonic reflection at a circle point (arc case).**  With `u₀` harmonic on the exterior part of
`ball w₀ R`, continuous up to the circle, and vanishing on the circle (Green boundary regularity), the
odd reflection `reflectCircle u₀` is harmonic at any circle point `w₁ ∈ ball w₀ R`.  Transport to the
real axis by `Ψ = reflTransport`: `reflectCircle u₀ ∘ Ψ` is the odd reflection across the real axis of
`u₀ ∘ Ψ`, so `harmonicAt_reflect_line` gives harmonicity at `t₁ = i·log w₁`; the analytic local inverse
of `Ψ` (`exists_localInverse_of_continuation`) transports it back to `w₁`. -/
theorem harmonicAt_reflectCircle_arc {u₀ : ℂ → ℝ} {w₀ w₁ : ℂ} {R : ℝ}
    (hR : 0 < R) (hw₁circ : ‖w₁‖ = 1) (hw₁ball : w₁ ∈ ball w₀ R)
    (hharm : ∀ w ∈ ball w₀ R, 1 < ‖w‖ → HarmonicAt u₀ w)
    (hcont : ContinuousOn u₀ ({w : ℂ | 1 ≤ ‖w‖} ∩ ball w₀ R))
    (hzero : ∀ w ∈ ball w₀ R, ‖w‖ = 1 → u₀ w = 0) :
    HarmonicAt (reflectCircle u₀) w₁ := by
  classical
  have hw₁ne : w₁ ≠ 0 := by rw [← norm_ne_zero_iff, hw₁circ]; norm_num
  set t₁ : ℂ := Complex.I * Complex.log w₁ with ht₁def
  have hPsit₁ : reflTransport t₁ = w₁ := by
    rw [reflTransport, ht₁def, show -(Complex.I * (Complex.I * Complex.log w₁)) = Complex.log w₁ by
      rw [← mul_assoc, Complex.I_mul_I]; ring]
    exact Complex.exp_log hw₁ne
  have ht₁im : t₁.im = 0 := by
    rw [ht₁def]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.log_re, hw₁circ, Real.log_one]
    ring
  obtain ⟨γ, hγAn, hγleft, hγright⟩ :=
    exists_localInverse_of_continuation (analyticAt_reflTransport t₁) (deriv_reflTransport_ne_zero t₁)
  rw [hPsit₁] at hγAn hγright
  have hγw₁ : γ w₁ = t₁ := by rw [← hPsit₁]; exact hγleft.self_of_nhds
  have hpre : reflTransport ⁻¹' (ball w₀ R) ∈ 𝓝 t₁ :=
    (analyticAt_reflTransport t₁).continuousAt.preimage_mem_nhds
      (by rw [hPsit₁]; exact Metric.isOpen_ball.mem_nhds hw₁ball)
  obtain ⟨ρ, hρ0, hρsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hPball : ∀ t ∈ ball t₁ ρ, reflTransport t ∈ ball w₀ R := fun t ht => hρsub ht
  have hsym : ∀ t ∈ ball t₁ ρ, (starRingEnd ℂ) t ∈ ball t₁ ρ := by
    intro t ht
    rw [mem_ball, dist_eq_norm] at ht ⊢
    have : (starRingEnd ℂ) t - t₁ = (starRingEnd ℂ) (t - t₁) := by
      rw [map_sub]; congr 1; exact (Complex.conj_eq_iff_im.mpr ht₁im).symm
    rw [this, RCLike.norm_conj]; exact ht
  have hΨcont : Continuous reflTransport := by
    show Continuous (fun t => Complex.exp (-(Complex.I * t))); fun_prop
  -- the reflection composed with Ψ is harmonic at t₁ (real-axis reflection)
  have key : HarmonicAt (fun t => reflectCircle u₀ (reflTransport t)) t₁ := by
    apply harmonicAt_reflect_line hρ0 ht₁im
    · -- harmonic off the axis
      intro t ht htim
      rcases lt_or_gt_of_ne htim with him | him
      · have hn : ‖reflTransport t‖ < 1 := by
          rw [norm_reflTransport]; exact Real.exp_lt_one_iff.mpr him
        have hσin : circleInv (reflTransport t) ∈ ball w₀ R := by
          rw [circleInv_reflTransport]; exact hPball _ (hsym t ht)
        have hσnorm : 1 < ‖circleInv (reflTransport t)‖ := by
          rw [norm_circleInv]
          exact (one_lt_inv₀ (by rw [norm_reflTransport]; exact Real.exp_pos _)).mpr hn
        exact harmonicAt_comp_analytic
          (harmonicAt_reflectCircle_inner hn (reflTransport_ne_zero t) (hharm _ hσin hσnorm))
          (analyticAt_reflTransport t)
      · have hn : 1 < ‖reflTransport t‖ := by
          rw [norm_reflTransport]; exact Real.one_lt_exp_iff.mpr him
        exact harmonicAt_comp_analytic
          (harmonicAt_reflectCircle_outer hn (hharm _ (hPball t ht) hn))
          (analyticAt_reflTransport t)
    · -- continuity across the axis, via `ContinuousOn.piecewise`
      have hup : ContinuousOn (fun t => u₀ (reflTransport t))
          (ball t₁ ρ ∩ {z : ℂ | 0 ≤ z.im}) := by
        apply hcont.comp hΨcont.continuousOn
        intro t ht
        exact ⟨by rw [mem_setOf_eq, norm_reflTransport]; exact Real.one_le_exp_iff.mpr ht.2,
          hPball t ht.1⟩
      have hlo : ContinuousOn (fun t => - u₀ (reflTransport ((starRingEnd ℂ) t)))
          (ball t₁ ρ ∩ {z : ℂ | z.im ≤ 0}) := by
        apply ContinuousOn.neg
        apply hcont.comp (hΨcont.comp Complex.continuous_conj).continuousOn
        intro t ht
        have h2 : t.im ≤ 0 := ht.2
        refine ⟨?_, hPball _ (hsym t ht.1)⟩
        rw [mem_setOf_eq, Function.comp_apply, norm_reflTransport]
        exact Real.one_le_exp_iff.mpr (by rw [Complex.conj_im]; linarith)
      have hpiece : ContinuousOn (Set.piecewise {z : ℂ | 0 ≤ z.im}
          (fun t => u₀ (reflTransport t)) (fun t => - u₀ (reflTransport ((starRingEnd ℂ) t))))
          (ball t₁ ρ) := by
        apply ContinuousOn.piecewise
        · intro a ha
          have haim : a.im = 0 := by
            have h1 : a ∈ closure {z : ℂ | 0 ≤ z.im} := frontier_subset_closure ha.2
            have h2 : a ∈ closure {z : ℂ | 0 ≤ z.im}ᶜ := by
              rw [← frontier_compl] at ha; exact frontier_subset_closure ha.2
            have hc : {z : ℂ | 0 ≤ z.im}ᶜ = {z : ℂ | z.im < 0} := by ext z; simp [not_le]
            rw [hc, closure_setOf_im_lt] at h2
            have hcl : closure {z : ℂ | 0 ≤ z.im} = {z : ℂ | 0 ≤ z.im} :=
              IsClosed.closure_eq (isClosed_le continuous_const continuous_im)
            rw [hcl] at h1; simp only [mem_setOf_eq] at h1 h2; linarith
          have hca : (starRingEnd ℂ) a = a := Complex.conj_eq_iff_im.mpr haim
          have hva : u₀ (reflTransport a) = 0 := by
            apply hzero _ (hPball a ha.1)
            rw [norm_reflTransport, haim, Real.exp_zero]
          show u₀ (reflTransport a) = - u₀ (reflTransport ((starRingEnd ℂ) a))
          rw [hca, hva]; ring
        · have hcl : closure {z : ℂ | 0 ≤ z.im} = {z : ℂ | 0 ≤ z.im} :=
            IsClosed.closure_eq (isClosed_le continuous_const continuous_im)
          rw [hcl]; exact hup
        · have hc : {z : ℂ | 0 ≤ z.im}ᶜ = {z : ℂ | z.im < 0} := by ext z; simp [not_le]
          rw [hc, closure_setOf_im_lt]; exact hlo
      apply hpiece.congr
      intro t ht
      show reflectCircle u₀ (reflTransport t) = _
      by_cases hn : 1 ≤ ‖reflTransport t‖
      · rw [reflectCircle_outer hn,
          Set.piecewise_eq_of_mem _ _ _
            (show t ∈ {z : ℂ | 0 ≤ z.im} by
              rw [mem_setOf_eq, ← Real.one_le_exp_iff, ← norm_reflTransport]; exact hn)]
      · rw [reflectCircle_inner (not_le.mp hn),
          Set.piecewise_eq_of_not_mem _ _ _
            (show t ∉ {z : ℂ | 0 ≤ z.im} by
              rw [mem_setOf_eq, not_le, ← Real.exp_lt_one_iff, ← norm_reflTransport]
              exact not_le.mp hn),
          circleInv_reflTransport]
    · -- oddness under conjugation
      intro t ht
      show reflectCircle u₀ (reflTransport ((starRingEnd ℂ) t)) = - reflectCircle u₀ (reflTransport t)
      rw [← circleInv_reflTransport t]
      exact reflectCircle_circleInv (reflTransport_ne_zero t)
        (fun hn1 => hzero _ (hPball t ht) hn1)
  -- transport back to `w₁`
  have hback := harmonicAt_comp_analytic (u := fun t => reflectCircle u₀ (reflTransport t)) (h := γ)
    (by rw [hγw₁]; exact key) hγAn
  refine (harmonicAt_congr_nhds ?_).mpr hback
  filter_upwards [hγright] with w hw
  show reflectCircle u₀ w = reflectCircle u₀ (reflTransport (γ w))
  rw [hw]

/-- **The harmonic reflection `hu`.**  The Green potential `u₀` (harmonic on the exterior of a smooth
Julia arc, continuous up to the arc, vanishing on it) reflects to a function `reflectCircle u₀`
harmonic on a whole ball `ball w₀ r₁` straddling the unit circle — the harmonic-extension hypothesis of
`continuesAcross_of_greenPotential_harmonic_extension`.  On the exterior side `reflectCircle u₀ = u₀`. -/
theorem harmonicOnNhd_reflectCircle {u₀ : ℂ → ℝ} {w₀ : ℂ} {R : ℝ}
    (hR : 0 < R) (hR1 : R ≤ 1/2) (hw₀ : ‖w₀‖ = 1)
    (hharm : ∀ w ∈ ball w₀ R, 1 < ‖w‖ → HarmonicAt u₀ w)
    (hcont : ContinuousOn u₀ ({w : ℂ | 1 ≤ ‖w‖} ∩ ball w₀ R))
    (hzero : ∀ w ∈ ball w₀ R, ‖w‖ = 1 → u₀ w = 0) :
    ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ R ∧ HarmonicOnNhd (reflectCircle u₀) (ball w₀ r₁) := by
  classical
  -- shrink so that `circleInv` maps `ball w₀ r₁` into `ball w₀ R`
  have hcInvCont : ContinuousAt circleInv w₀ := by
    have hw₀ne : w₀ ≠ 0 := by rw [← norm_ne_zero_iff, hw₀]; norm_num
    show ContinuousAt (fun w => ((starRingEnd ℂ) w)⁻¹) w₀
    exact (Complex.continuous_conj.continuousAt).inv₀ (by simpa using hw₀ne)
  have hcInvw₀ : circleInv w₀ = w₀ := circleInv_fixes hw₀
  have hpre : circleInv ⁻¹' (ball w₀ R) ∈ 𝓝 w₀ :=
    hcInvCont.preimage_mem_nhds (by rw [hcInvw₀]; exact ball_mem_nhds w₀ hR)
  have hpre2 : ball w₀ R ∩ circleInv ⁻¹' (ball w₀ R) ∈ 𝓝 w₀ :=
    Filter.inter_mem (ball_mem_nhds w₀ hR) hpre
  obtain ⟨r₁, hr₁0, hr₁sub⟩ := Metric.mem_nhds_iff.mp hpre2
  have hr₁ball : ball w₀ r₁ ⊆ ball w₀ R := fun w hw => (hr₁sub hw).1
  have hr₁R : r₁ ≤ R := by
    by_contra h
    push_neg at h
    have : w₀ + (((R + r₁) / 2 : ℝ) : ℂ) ∈ ball w₀ r₁ := by
      rw [mem_ball, dist_eq_norm, show w₀ + (((R + r₁) / 2 : ℝ) : ℂ) - w₀ = (((R + r₁) / 2 : ℝ) : ℂ) by ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have := (hr₁sub this).1
    rw [mem_ball, dist_eq_norm, show w₀ + (((R + r₁) / 2 : ℝ) : ℂ) - w₀ = (((R + r₁) / 2 : ℝ) : ℂ) by ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at this
    linarith
  refine ⟨r₁, hr₁0, hr₁R, ?_⟩
  intro w hw
  have hwR : w ∈ ball w₀ R := hr₁ball hw
  have hwne : w ≠ 0 := by
    have hd : dist w w₀ < r₁ := mem_ball.mp hw
    rw [Complex.dist_eq] at hd
    have : ‖w₀‖ - ‖w‖ ≤ ‖w - w₀‖ := by
      rw [← norm_neg (w - w₀), neg_sub]; exact norm_sub_norm_le w₀ w
    rw [hw₀] at this
    have : 0 < ‖w‖ := by nlinarith [norm_nonneg w, hr₁R]
    exact norm_pos_iff.mp this
  rcases lt_trichotomy ‖w‖ 1 with hlt | heq | hgt
  · have hσin : circleInv w ∈ ball w₀ R := (hr₁sub hw).2
    have hσnorm : 1 < ‖circleInv w‖ := by
      rw [norm_circleInv]; exact (one_lt_inv₀ (norm_pos_iff.mpr hwne)).mpr hlt
    exact harmonicAt_reflectCircle_inner hlt hwne (hharm _ hσin hσnorm)
  · exact harmonicAt_reflectCircle_arc hR heq hwR hharm hcont hzero
  · exact harmonicAt_reflectCircle_outer hgt (hharm _ hwR hgt)

end Bottcher
