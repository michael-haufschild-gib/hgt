import GaloisForLFunctions.RHTower.EntireArgumentVariationRectangle
import GaloisForLFunctions.Bottcher.SchwarzReflection
import GaloisForLFunctions.HTGeometry.SegmentArgumentBound
import Zeta23.FromPNTPlus.StrongPNTPrefix

/-!
# Local argument bounds on rectangles and horizontal segments

Three tools for functions holomorphic on an open set, not necessarily entire.

* `argument_variation_rectangle_le`: for `f` holomorphic on a connected open set containing a closed
  rectangle `[c, d] × [T₁, T₂]` and nonvanishing on its boundary,
  `∫ Re(f'/f)(c + it) dt ≤ ∫ Re(f'/f)(d + it) dt + ∫ Im(f'/f)(x + iT₁) dx − ∫ Im(f'/f)(x + iT₂) dx`.
  The defect is `2π` times the number of enclosed zeros.
* `differentiableOn_of_off_vertical_line`: a function continuous on an open set and holomorphic
  off a vertical line is holomorphic (Painlevé).
* `abs_integral_im_logDeriv_horizontal_le` (Backlund–Jensen): if `f` is holomorphic on a disc
  around `x₀ + iY`, bounded by `M` on a smaller disc of radius `R`, and `Re f(x₀ + iY) ≥ m > 0`,
  then along every zero-free horizontal segment `[a, x₀] + iY` with `x₀ − a ≤ r < R`,
  `|∫ Im(f'/f)| ≤ (log(M/m)/log(R/r) + 1)π`. The zeros of `Re f` on the segment are zeros of
  `(f(z + iY) + conj f(z̄ + iY))/2`, and Jensen counts them.
-/

open Complex Filter MeasureTheory intervalIntegral Set Topology Metric
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The argument principle on a rectangle, inequality form -/

/-- Zeros of a function holomorphic on a connected open set, not identically zero, are finite in
every closed rectangle inside the set. -/
theorem zeros_closedRectangle_finite_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hUc : IsConnected U) {x : ℂ} (hxU : x ∈ U) (hx : f x ≠ 0)
    {z₁ z₂ : ℂ} (hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U) :
    {z ∈ (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) | f z = 0}.Finite := by
  have hcod : (f ⁻¹' {0}ᶜ) ∈ codiscreteWithin U :=
    hf.preimage_zero_mem_codiscreteWithin hx hxU hUc
  have hcodK : (f ⁻¹' {0}ᶜ) ∈ codiscreteWithin (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) :=
    Filter.codiscreteWithin_mono hsub hcod
  refine ((isCompact_uIcc.reProdIm isCompact_uIcc).finite_sdiff_of_mem_codiscreteWithin
    hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

theorem analyticAt_logDeriv_of_ne_zero {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z)
    (hz : f z ≠ 0) : AnalyticAt ℂ (logDeriv f) z := by
  have h : AnalyticAt ℂ (fun w => deriv f w / f w) z := hf.deriv.div hf hz
  refine h.congr ?_
  filter_upwards with w
  rw [logDeriv_apply]

/-- **The argument principle on a rectangle, inequality form.** For `f` holomorphic on a connected
open set containing the closed rectangle `[c, d] × [T₁, T₂]`, not identically zero, and nonvanishing
on the boundary, the phase advance along the left edge is at most the advance along the other three
edges. The defect is `2π` times the number of enclosed zeros. -/
theorem argument_variation_rectangle_le {f : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsConnected U) (hf : AnalyticOnNhd ℂ f U) {x₀ : ℂ} (hx₀U : x₀ ∈ U) (hx₀ : f x₀ ≠ 0)
    {c d T₁ T₂ : ℝ} (hcd : c < d) (hT : T₁ < T₂) (hsub : (uIcc c d ×ℂ uIcc T₁ T₂) ⊆ U)
    (hbot : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₁ * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d, f ((x : ℂ) + T₂ * I) ≠ 0)
    (hright : ∀ t ∈ uIcc T₁ T₂, f ((d : ℂ) + t * I) ≠ 0)
    (hleft : ∀ t ∈ uIcc T₁ T₂, f ((c : ℂ) + t * I) ≠ 0) :
    (∫ t in T₁..T₂, (logDeriv f ((c : ℂ) + t * I)).re)
      ≤ (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + t * I)).re)
        + (∫ x in c..d, (logDeriv f ((x : ℂ) + T₁ * I)).im)
        - (∫ x in c..d, (logDeriv f ((x : ℂ) + T₂ * I)).im) := by
  classical
  set z₁ : ℂ := (c : ℂ) + T₁ * I with hz₁
  set z₂ : ℂ := (d : ℂ) + T₂ * I with hz₂
  have hz₁re : z₁.re = c := by simp [hz₁]
  have hz₁im : z₁.im = T₁ := by simp [hz₁]
  have hz₂re : z₂.re = d := by simp [hz₂]
  have hz₂im : z₂.im = T₂ := by simp [hz₂]
  have hsub' : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    rw [hz₁re, hz₁im, hz₂re, hz₂im]; exact hsub
  have hfinite := zeros_closedRectangle_finite_of_analyticOnNhd hf hUc hx₀U hx₀ hsub'
  set Z : Finset ℂ := hfinite.toFinset with hZ
  have hmem (z : ℂ) : z ∈ Z ↔ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂) ∧ f z = 0 := by
    rw [hZ, Set.Finite.mem_toFinset, Set.mem_sep_iff, hz₁re, hz₁im, hz₂re, hz₂im]
  have hord : ∀ w ∈ Z, analyticOrderAt f w ≠ ⊤ := by
    intro w hw
    have hwU : w ∈ U := hsub ((hmem w).mp hw).1
    refine hf.analyticOrderAt_ne_top_of_isPreconnected hUc.isPreconnected hx₀U hwU ?_
    rw [(hf x₀ hx₀U).analyticOrderAt_eq_zero.mpr hx₀]
    exact ENat.zero_ne_top
  obtain ⟨m, h, hhan, hm, hh0, hfact⟩ :=
    exists_finite_peel hUo hf Z (fun w hw => hsub ((hmem w).mp hw).1) hord
  have hhK : ∀ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂), h z ≠ 0 := by
    intro z hzK hhzero
    have hf0 : f z = 0 := by rw [hfact z (hsub hzK), hhzero, mul_zero]
    exact hh0 z ((hmem z).mpr ⟨hzK, hf0⟩) hhzero
  set V : Set ℂ := U ∩ h ⁻¹' {0}ᶜ with hV
  have hVopen : IsOpen V := hhan.continuousOn.isOpen_inter_preimage hUo isOpen_compl_singleton
  have hsubV : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ V := by
    rw [hz₁re, hz₁im, hz₂re, hz₂im]
    exact fun z hz => ⟨hsub hz, hhK z hz⟩
  have hin : ∀ w ∈ Z, z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
    intro w hw
    rw [hz₁re, hz₁im, hz₂re, hz₂im]
    obtain ⟨hwK, hwzero⟩ := (hmem w).mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    have hwreU := hwre
    have hwimU := hwim
    rw [uIcc_of_le hcd.le] at hwre
    rw [uIcc_of_le hT.le] at hwim
    refine ⟨lt_of_le_of_ne hwre.1 fun heq => ?_, lt_of_le_of_ne hwre.2 fun heq => ?_,
      lt_of_le_of_ne hwim.1 fun heq => ?_, lt_of_le_of_ne hwim.2 fun heq => ?_⟩
    · have hedge : (c : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [heq]
      exact hleft w.im hwimU (by rw [hedge]; exact hwzero)
    · have hedge : (d : ℂ) + w.im * I = w := by apply Complex.ext <;> simp [heq]
      exact hright w.im hwimU (by rw [hedge]; exact hwzero)
    · have hedge : (w.re : ℂ) + T₁ * I = w := by apply Complex.ext <;> simp [heq]
      exact hbot w.re hwreU (by rw [hedge]; exact hwzero)
    · have hedge : (w.re : ℂ) + T₂ * I = w := by apply Complex.ext <;> simp [heq]
      exact htop w.re hwreU (by rw [hedge]; exact hwzero)
  have hval : rectIntegral (logDeriv f) z₁ z₂ =
      2 * Real.pi * I * ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℂ) * (1 : ℂ) := by
    have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
      Z (fun w => w) m (f := f) (g := fun _ => (1 : ℂ)) (h := h)
      (z₁ := z₁) (z₂ := z₂) (U := V) hVopen (fun z _ => analyticAt_const) hin hsubV
      (hhan.mono (fun _ hz => hz.1)) (fun _ hz => hz.2) (fun z hz => hfact z hz.1)
    simp only [one_mul] at hres
    rw [hres]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hm w hw, mul_one]
  have hcontEdge : ∀ p : ℝ → ℂ, Continuous p → ∀ S : Set ℝ, (∀ t ∈ S, p t ∈ U) →
      (∀ t ∈ S, f (p t) ≠ 0) → ContinuousOn (fun t => logDeriv f (p t)) S := by
    intro p hp S hS hne t ht
    exact ((analyticAt_logDeriv_of_ne_zero (hf _ (hS t ht)) (hne t ht)).continuousAt.comp
      hp.continuousAt).continuousWithinAt
  have hbotU : ∀ x ∈ uIcc c d, (x : ℂ) + T₁ * I ∈ U := fun x hx =>
    hsub (Complex.mem_reProdIm.mpr ⟨by simpa using hx, by simp [left_mem_uIcc]⟩)
  have htopU : ∀ x ∈ uIcc c d, (x : ℂ) + T₂ * I ∈ U := fun x hx =>
    hsub (Complex.mem_reProdIm.mpr ⟨by simpa using hx, by simp [right_mem_uIcc]⟩)
  have hrightU : ∀ t ∈ uIcc T₁ T₂, (d : ℂ) + t * I ∈ U := fun t ht =>
    hsub (Complex.mem_reProdIm.mpr ⟨by simp [right_mem_uIcc], by simpa using ht⟩)
  have hleftU : ∀ t ∈ uIcc T₁ T₂, (c : ℂ) + t * I ∈ U := fun t ht =>
    hsub (Complex.mem_reProdIm.mpr ⟨by simp [left_mem_uIcc], by simpa using ht⟩)
  have hqbot := hcontEdge (fun x : ℝ => (x : ℂ) + T₁ * I) (by fun_prop) _ hbotU hbot
  have hqtop := hcontEdge (fun x : ℝ => (x : ℂ) + T₂ * I) (by fun_prop) _ htopU htop
  have hqright := hcontEdge (fun t : ℝ => (d : ℂ) + t * I) (by fun_prop) _ hrightU hright
  have hqleft := hcontEdge (fun t : ℝ => (c : ℂ) + t * I) (by fun_prop) _ hleftU hleft
  have hedges := two_pi_mul_weighted_re_sum_eq_edges
    (F := logDeriv f) (z₁ := z₁) (z₂ := z₂) (Z := Z)
    (m := fun w => (analyticOrderAt f w).toNat) (g := fun _ => (1 : ℂ)) hval
    (by rw [hz₁re, hz₂re, hz₁im]; exact hqbot.intervalIntegrable)
    (by rw [hz₁re, hz₂re, hz₂im]; exact hqtop.intervalIntegrable)
    (by rw [hz₂re, hz₁im, hz₂im]; exact hqright.intervalIntegrable)
    (by rw [hz₁re, hz₁im, hz₂im]; exact hqleft.intervalIntegrable)
  rw [hz₁re, hz₁im, hz₂re, hz₂im] at hedges
  have hN : 0 ≤ 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℝ) * (1 : ℂ).re :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun w _ => by simp)
  linarith

/-! ## Painlevé across a vertical line -/

/-- **Painlevé across a vertical line.** A function continuous on an open set and holomorphic off
the vertical line `Re z = a` is holomorphic on the whole set. -/
theorem differentiableOn_of_off_vertical_line {f : ℂ → ℂ} {U : Set ℂ} {a : ℝ} (hU : IsOpen U)
    (hcont : ContinuousOn f U) (hdiff : DifferentiableOn ℂ f (U ∩ {z : ℂ | z.re ≠ a})) :
    DifferentiableOn ℂ f U := by
  set U' : Set ℂ := (fun ζ : ℂ => I * ζ) ⁻¹' U with hU'
  have hU'o : IsOpen U' := hU.preimage (continuous_const.mul continuous_id)
  set g : ℂ → ℂ := fun ζ => f (I * ζ) with hg
  have hgc : ContinuousOn g U' :=
    hcont.comp (continuous_const.mul continuous_id).continuousOn (fun ζ hζ => hζ)
  have hgd : DifferentiableOn ℂ g (U' ∩ {ζ : ℂ | ζ.im ≠ -a}) := by
    intro ζ hζ
    have hre : (I * ζ).re ≠ a := by
      intro h; apply hζ.2; simp at h; linarith
    have hfd := (hdiff (I * ζ) ⟨hζ.1, hre⟩).differentiableAt
      ((hU.inter (isOpen_ne_fun Complex.continuous_re continuous_const)).mem_nhds ⟨hζ.1, hre⟩)
    exact (hfd.comp ζ ((differentiableAt_const _).mul differentiableAt_id)).differentiableWithinAt
  have hgD := Bottcher.differentiableOn_of_off_horizontal_line hU'o hgc hgd
  intro z hz
  have hz' : -I * z ∈ U' := by
    show I * (-I * z) ∈ U
    rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, I_mul_I, neg_neg], one_mul]; exact hz
  have hgz := (hgD _ hz').differentiableAt (hU'o.mem_nhds hz')
  have hcomp := hgz.comp z ((differentiableAt_const _).mul differentiableAt_id)
  have heq : (g ∘ fun w : ℂ => -I * w) = f := by
    funext w; simp only [hg, Function.comp_apply]
    rw [← mul_assoc, show I * -I = 1 by rw [mul_neg, I_mul_I, neg_neg], one_mul]
  rw [heq] at hcomp
  exact hcomp.differentiableWithinAt

/-! ## Backlund–Jensen on a horizontal segment -/

/-- The zeros of a function holomorphic on a ball, not identically zero, are finite in every
smaller closed ball. -/
theorem zeros_closedBall_finite_of_analyticOnNhd {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (ball c R)) {x : ℂ} (hxU : x ∈ ball c R) (hx : f x ≠ 0) :
    {z ∈ closedBall c r | f z = 0}.Finite := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (mem_ball.mp hxU)
  have hcod : (f ⁻¹' {0}ᶜ) ∈ codiscreteWithin (ball c R) :=
    hf.preimage_zero_mem_codiscreteWithin hx hxU ((convex_ball c R).isConnected
      (nonempty_ball.mpr hR))
  have hcodK : (f ⁻¹' {0}ᶜ) ∈ codiscreteWithin (closedBall c r) :=
    Filter.codiscreteWithin_mono (closedBall_subset_ball hrR) hcod
  refine ((isCompact_closedBall c r).finite_sdiff_of_mem_codiscreteWithin hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- The conjugate-symmetrized function `(f(z + iY) + conj f(z̄ + iY))/2`. On the real axis it is
`Re f(x + iY)`. -/
def horizontalRePart (f : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (f (z + Y * I) + conj (f (conj z + Y * I))) / 2

theorem horizontalRePart_ofReal (f : ℂ → ℂ) (Y x : ℝ) :
    horizontalRePart f Y x = (((f ((x : ℂ) + Y * I)).re : ℝ) : ℂ) := by
  rw [horizontalRePart, Complex.conj_ofReal, Complex.add_conj]
  push_cast
  ring

theorem differentiableOn_horizontalRePart {f : ℂ → ℂ} {x₀ Y R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball ((x₀ : ℂ) + Y * I) R)) :
    DifferentiableOn ℂ (horizontalRePart f Y) (ball (x₀ : ℂ) R) := by
  intro z hz
  have hmem : ∀ w : ℂ, w ∈ ball (x₀ : ℂ) R → w + Y * I ∈ ball ((x₀ : ℂ) + Y * I) R := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw ⊢
    rwa [show w + Y * I - ((x₀ : ℂ) + Y * I) = w - x₀ by ring]
  have hconj : conj z ∈ ball (x₀ : ℂ) R := by
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rwa [show conj z - (x₀ : ℂ) = conj (z - x₀) by simp, Complex.norm_conj]
  have h1 : DifferentiableAt ℂ (fun w => f (w + Y * I)) z := by
    have := (hf _ (hmem z hz)).differentiableAt.comp z
      (differentiableAt_id.add_const ((Y : ℂ) * I))
    simpa [Function.comp_def] using this
  have h2 : DifferentiableAt ℂ (fun w => f (w + Y * I)) (conj z) := by
    have := (hf _ (hmem _ hconj)).differentiableAt.comp (conj z)
      (differentiableAt_id.add_const ((Y : ℂ) * I))
    simpa [Function.comp_def] using this
  have h3 := h2.conj_conj
  rw [Complex.conj_conj] at h3
  exact ((h1.add h3).div_const 2).differentiableWithinAt

/-- **Backlund–Jensen bound on a horizontal segment.** Let `f` be holomorphic on the disc of radius
`R₂` around `x₀ + iY`, with `|f| ≤ M` on the closed disc of radius `R < R₂` and
`Re f(x₀ + iY) ≥ m > 0`. On every zero-free segment `[a, x₀] + iY` with `x₀ − a ≤ r < R`,
`|∫_a^{x₀} Im(f'/f)(x + iY) dx| ≤ (log(M/m)/log(R/r) + 1)π`. -/
theorem abs_integral_im_logDeriv_horizontal_le {f : ℂ → ℂ} {x₀ Y a r R R₂ M m : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRR₂ : R < R₂) (hm : 0 < m)
    (hf : AnalyticOnNhd ℂ f (ball ((x₀ : ℂ) + Y * I) R₂))
    (hM : ∀ z ∈ closedBall ((x₀ : ℂ) + Y * I) R, ‖f z‖ ≤ M)
    (hre : m ≤ (f ((x₀ : ℂ) + Y * I)).re) (ha : x₀ - r ≤ a) (hax : a ≤ x₀)
    (hne : ∀ x ∈ Icc a x₀, f ((x : ℂ) + Y * I) ≠ 0) :
    |∫ x in a..x₀, (logDeriv f ((x : ℂ) + Y * I)).im| ≤
      (Real.log (M / m) / Real.log (R / r) + 1) * Real.pi := by
  classical
  set c : ℂ := (x₀ : ℂ) + Y * I with hc
  set g := horizontalRePart f Y with hg
  have hgd := differentiableOn_horizontalRePart (R := R₂) hf
  have hgan : AnalyticOnNhd ℂ g (ball (x₀ : ℂ) R₂) := hgd.analyticOnNhd isOpen_ball
  have hR : 0 < R := hr.trans hrR
  have hg0 : g x₀ = (((f c).re : ℝ) : ℂ) := horizontalRePart_ofReal f Y x₀
  have hg0ne : g x₀ ≠ 0 := by
    rw [hg0]; exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hg0norm : m ≤ ‖g x₀‖ := by
    rw [hg0, Complex.norm_real, Real.norm_eq_abs]; exact hre.trans (le_abs_self _)
  -- the bound for `g` on the closed disc of radius `R`
  have hgM : ∀ z ∈ closedBall (x₀ : ℂ) R, ‖g z‖ ≤ M := by
    intro z hz
    have hmem : ∀ w : ℂ, w ∈ closedBall (x₀ : ℂ) R → w + Y * I ∈ closedBall c R := by
      intro w hw
      rw [mem_closedBall, dist_eq_norm] at hw ⊢
      rwa [show w + Y * I - c = w - x₀ by rw [hc]; ring]
    have hconj : conj z ∈ closedBall (x₀ : ℂ) R := by
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      rwa [show conj z - (x₀ : ℂ) = conj (z - x₀) by simp, Complex.norm_conj]
    have h1 := hM _ (hmem z hz)
    have h2 := hM _ (hmem _ hconj)
    rw [hg, horizontalRePart, norm_div, Complex.norm_two]
    calc ‖f (z + Y * I) + conj (f (conj z + Y * I))‖ / 2
        ≤ (‖f (z + Y * I)‖ + ‖conj (f (conj z + Y * I))‖) / 2 := by
          gcongr; exact norm_add_le _ _
      _ ≤ M := by rw [Complex.norm_conj]; linarith
  -- normalize to the unit disc
  set κ : ℝ := (R + R₂) / 2 with hκ
  have hκR : R < κ := by rw [hκ]; linarith
  have hκR₂ : κ < R₂ := by rw [hκ]; linarith
  have hκ0 : 0 < κ := hR.trans hκR
  set G : ℂ → ℂ := fun w => g (x₀ + κ * w) / g x₀ with hG
  have hmapball : ∀ w : ℂ, ‖w‖ < R₂ / κ → (x₀ : ℂ) + κ * w ∈ ball (x₀ : ℂ) R₂ := by
    intro w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hκ0]
    rwa [lt_div_iff₀ hκ0, mul_comm] at hw
  have hGan : AnalyticOnNhd ℂ G (ball 0 (R₂ / κ)) := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    have hin : AnalyticAt ℂ (fun w : ℂ => (x₀ : ℂ) + κ * w) w := by fun_prop
    exact ((hgan _ (hmapball w hw)).comp_of_eq hin rfl).div analyticAt_const hg0ne
  have h1lt : 1 < R₂ / κ := by rw [lt_div_iff₀ hκ0, one_mul]; exact hκR₂
  have hGan1 : AnalyticOnNhd ℂ G (closedBall 0 1) := fun w hw =>
    hGan w (closedBall_subset_ball h1lt hw)
  have hG0 : G 0 = 1 := by simp [hG, div_self hg0ne]
  have hfinG : (SetOfZeros 1 G).Finite := by
    have h := zeros_closedBall_finite_of_analyticOnNhd h1lt hGan (x := 0)
      (by rw [mem_ball, dist_self]; linarith) (by rw [hG0]; exact one_ne_zero)
    refine h.subset ?_
    rintro w ⟨hw1, hw0⟩
    exact ⟨by rwa [mem_closedBall, dist_zero_right], hw0⟩
  have hr1 : r / κ < 1 := by rw [div_lt_one hκ0]; linarith
  have hR1 : R / κ < 1 := by rw [div_lt_one hκ0]; exact hκR
  have hrR' : r / κ < R / κ := div_lt_div_of_pos_right hrR hκ0
  have hGM : ∀ w : ℂ, ‖w‖ ≤ R / κ → ‖G w‖ ≤ M / m := by
    intro w hw
    have hz : (x₀ : ℂ) + κ * w ∈ closedBall (x₀ : ℂ) R := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hκ0]
      rwa [le_div_iff₀ hκ0, mul_comm] at hw
    rw [hG, norm_div]
    have hgx := hgM _ hz
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hgx
    calc ‖g ((x₀ : ℂ) + κ * w)‖ / ‖g x₀‖ ≤ M / ‖g x₀‖ := by gcongr
      _ ≤ M / m := div_le_div_of_nonneg_left hM0 hm hg0norm
  have hZB := ZerosBound (div_pos hr hκ0) hr1 hrR' hR1 hGan1 hG0 hfinG hGM
  have hratio : R / κ / (r / κ) = R / r := by field_simp
  rw [hratio] at hZB
  set Zr : Finset ℂ := (finiteSetOfZeros_mono hr1 hfinG).toFinset with hZr
  -- the real zeros of `Re f` on the segment inject into the zeros of `G`
  set S : Set ℝ := {x ∈ Icc a x₀ | (f ((x : ℂ) + Y * I)).re = 0} with hS
  set φ : ℝ → ℂ := fun x => (((x - x₀) / κ : ℝ) : ℂ) with hφ
  have hφinj : Set.InjOn φ S := by
    intro p _ q _ h
    have h' := Complex.ofReal_injective h
    rw [div_left_inj' hκ0.ne'] at h'
    linarith
  have hφmem : ∀ x ∈ S, φ x ∈ Zr := by
    intro x hx
    obtain ⟨⟨hxa, hxb⟩, hx0⟩ := hx
    rw [hZr, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · show ‖φ x‖ ≤ r / κ
      rw [hφ, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hκ0,
        abs_of_nonpos (by linarith)]
      exact div_le_div_of_nonneg_right (by linarith) hκ0.le
    · show g ((x₀ : ℂ) + κ * φ x) / g x₀ = 0
      have hfix : (x₀ : ℂ) + κ * φ x = (x : ℂ) := by
        rw [hφ, ← Complex.ofReal_mul, mul_div_cancel₀ _ hκ0.ne', ← Complex.ofReal_add]
        congr 1; ring
      rw [hfix, hg, horizontalRePart_ofReal, hx0, Complex.ofReal_zero, zero_div]
  have hSfin : S.Finite :=
    Set.Finite.of_finite_image ((Zr.finite_toSet).subset (by
      rintro _ ⟨x, hx, rfl⟩; exact hφmem x hx)) hφinj
  have hord : ∀ ρ ∈ Zr, 1 ≤ analyticOrderNatAt G ρ := by
    intro ρ hρ
    rw [hZr, Set.Finite.mem_toFinset] at hρ
    obtain ⟨hρr, hρ0⟩ := hρ
    have hρball : ρ ∈ ball (0 : ℂ) (R₂ / κ) := by
      rw [mem_ball, dist_zero_right]; exact lt_of_le_of_lt hρr (hr1.trans h1lt)
    have han : AnalyticAt ℂ G ρ := hGan ρ hρball
    have hne0 : analyticOrderAt G ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr hρ0
    have hnetop : analyticOrderAt G ρ ≠ ⊤ := by
      refine hGan.analyticOrderAt_ne_top_of_isPreconnected (convex_ball _ _).isPreconnected
        (x := 0) (by rw [mem_ball, dist_self]; linarith) hρball ?_
      rw [(hGan 0 (by rw [mem_ball, dist_self]; linarith)).analyticOrderAt_eq_zero.mpr
        (by rw [hG0]; exact one_ne_zero)]
      exact ENat.zero_ne_top
    unfold analyticOrderNatAt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hn] at hne0 ⊢
    simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
    omega
  have hcard : (hSfin.toFinset.card : ℝ) ≤ Real.log (M / m) / Real.log (R / r) := by
    have h1 : hSfin.toFinset.card ≤ Zr.card := by
      rw [← Set.ncard_eq_toFinset_card S hSfin]
      calc S.ncard = (φ '' S).ncard := (hφinj.ncard_image).symm
        _ ≤ (↑Zr : Set ℂ).ncard := Set.ncard_le_ncard (by
            rintro _ ⟨x, hx, rfl⟩; exact hφmem x hx) Zr.finite_toSet
        _ = Zr.card := Set.ncard_coe_finset Zr
    have h2 : (Zr.card : ℝ) ≤ ((∑ ρ ∈ Zr, analyticOrderNatAt G ρ : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_eq_sum_ones Zr).le.trans (Finset.sum_le_sum hord)
    calc (hSfin.toFinset.card : ℝ) ≤ Zr.card := by exact_mod_cast h1
      _ ≤ _ := h2
      _ ≤ 1 / Real.log (R / r) * Real.log (M / m) := by exact_mod_cast hZB
      _ = Real.log (M / m) / Real.log (R / r) := by ring
  -- Backlund's step
  have hpath : ∀ x ∈ Icc a x₀, HasDerivAt (fun t : ℝ => f ((t : ℂ) + Y * I))
      (deriv f ((x : ℂ) + Y * I)) x := by
    intro x hx
    have hxball : (x : ℂ) + Y * I ∈ ball c R₂ := by
      rw [mem_ball, dist_eq_norm, show (x : ℂ) + Y * I - c = ((x - x₀ : ℝ) : ℂ) by
        rw [hc]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.1]
    have hd : HasDerivAt (fun w : ℂ => f (w + Y * I)) (deriv f ((x : ℂ) + Y * I)) (x : ℂ) :=
      HasDerivAt.comp_add_const (x : ℂ) ((Y : ℂ) * I) (hf _ hxball).differentiableAt.hasDerivAt
    exact hd.comp_ofReal
  have hcont : ContinuousOn (fun t : ℝ => deriv f ((t : ℂ) + Y * I) / f ((t : ℂ) + Y * I))
      (Icc a x₀) := by
    intro x hx
    have hxball : (x : ℂ) + Y * I ∈ ball c R₂ := by
      rw [mem_ball, dist_eq_norm, show (x : ℂ) + Y * I - c = ((x - x₀ : ℝ) : ℂ) by
        rw [hc]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [hx.2])]
      linarith [hx.1]
    have han := analyticAt_logDeriv_of_ne_zero (hf _ hxball) (hne x hx)
    have hc' := han.continuousAt.comp (f := fun t : ℝ => (t : ℂ) + Y * I) (by fun_prop)
    refine (hc'.congr (Eventually.of_forall fun t => ?_)).continuousWithinAt
    simp [logDeriv_apply]
  have hB := abs_integral_im_logDeriv_le_of_finite_re_zeros hax hpath hcont hne hSfin.toFinset
    (fun t ht h0 => by
      rw [Set.Finite.mem_toFinset]; exact ⟨Ioo_subset_Icc_self ht, h0⟩)
  have hfilt : ((hSfin.toFinset.filter (fun z => z ∈ Ioo a x₀)).card : ℝ) ≤
      hSfin.toFinset.card := by exact_mod_cast Finset.card_filter_le _ _
  have hint : (∫ x in a..x₀, (logDeriv f ((x : ℂ) + Y * I)).im) =
      ∫ x in a..x₀, (deriv f ((x : ℂ) + Y * I) / f ((x : ℂ) + Y * I)).im := by
    simp only [logDeriv_apply]
  rw [hint]
  refine hB.trans ?_
  have hpi := Real.pi_pos
  nlinarith

end

end RHTower
