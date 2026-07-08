/-
The canonical branch datum: a member symmetric under reflection across a vertical
line canonically pairs any right-chart square root with its Schwarz reflection on
the left chart, and the deck class of the canonical pair is an OBSERVABLE — the
product of the signs of the (real) member values at the two reflection-fixed
ports.  An odd hole parity is exactly a sign change of the member across the hole
along the symmetry line.

Geometry: the reflection `z ↦ 2μ − conj z` fixes every point of `Re = μ`, fixes an
annulus centered on the line, swaps the two slit charts, and fixes the two
vertical basepoints.  A line-symmetric member is real at fixed ports, its chart
root takes real or purely imaginary values there according to the member's sign,
and the double conjugation ratio in the deck class reads that dichotomy off.

For the completed symmetrized member on a critical-line-centered annulus, the
sign observable replaces the deck-class hypothesis of the selection weld: a sign
change of the member between the two ports yields, beyond any bound, a prime set
that drives every sweep selection into strict reading reversal while no sweep
stage admits a global square root.
-/
import GaloisForLFunctions.RHTower.SweepSelection
import GaloisForLFunctions.RHTower.DiscWindow

noncomputable section

namespace RHTower

open Complex Metric Set

/-! ### §1 The vertical-line reflection and its chart action -/

/-- Reflection across the vertical line `Re = μ`. -/
def lineReflection (μ : ℝ) (z : ℂ) : ℂ := ((2 * μ : ℝ) : ℂ) - (starRingEnd ℂ) z

/-- Reflection across the critical line `Re = 1/2` in closed form: `2·(1/2) = 1`. -/
theorem lineReflection_half (z : ℂ) :
    lineReflection (1 / 2) z = 1 - (starRingEnd ℂ) z := by
  rw [lineReflection]; norm_num

theorem lineReflection_re (μ : ℝ) (z : ℂ) :
    (lineReflection μ z).re = 2 * μ - z.re := by
  rw [lineReflection]
  simp

theorem lineReflection_im (μ : ℝ) (z : ℂ) : (lineReflection μ z).im = z.im := by
  rw [lineReflection]
  simp

theorem lineReflection_involutive (μ : ℝ) (z : ℂ) :
    lineReflection μ (lineReflection μ z) = z := by
  rw [lineReflection, lineReflection, map_sub, Complex.conj_ofReal,
    Complex.conj_conj]
  ring

/-- Points on the symmetry line are fixed. -/
theorem lineReflection_eq_self {μ : ℝ} {z : ℂ} (hz : z.re = μ) :
    lineReflection μ z = z := by
  apply Complex.ext
  · rw [lineReflection_re, hz]
    ring
  · rw [lineReflection_im]

/-- The reflected offset from a center on the line is the negated conjugate
offset. -/
theorem lineReflection_sub_center {μ : ℝ} {a : ℂ} (ha : a.re = μ) (z : ℂ) :
    lineReflection μ z - a = -((starRingEnd ℂ) (z - a)) := by
  have hca : (starRingEnd ℂ) a = ((2 * μ : ℝ) : ℂ) - a := by
    apply Complex.ext
    · rw [Complex.conj_re, Complex.sub_re, Complex.ofReal_re, ha]
      ring
    · rw [Complex.conj_im, Complex.sub_im, Complex.ofReal_im]
      ring
  rw [lineReflection, map_sub, hca]
  ring

theorem norm_lineReflection_sub_center {μ : ℝ} {a : ℂ} (ha : a.re = μ) (z : ℂ) :
    ‖lineReflection μ z - a‖ = ‖z - a‖ := by
  rw [lineReflection_sub_center ha, norm_neg, norm_conj]

/-- The reflection fixes a line-centered annulus. -/
theorem lineReflection_mem_annulus {μ : ℝ} {a : ℂ} {r₀ R : ℝ} (ha : a.re = μ)
    {z : ℂ} (hz : z ∈ ball a R \ closedBall a r₀) :
    lineReflection μ z ∈ ball a R \ closedBall a r₀ := by
  obtain ⟨hzB, hzC⟩ := hz
  constructor
  · rw [mem_ball, dist_eq_norm, norm_lineReflection_sub_center ha]
    rwa [mem_ball, dist_eq_norm] at hzB
  · intro hmem
    apply hzC
    rw [mem_closedBall, dist_eq_norm] at hmem ⊢
    rwa [norm_lineReflection_sub_center ha] at hmem

/-- Conjugation preserves the slit plane. -/
theorem conj_mem_slitPlane {w : ℂ} (hw : w ∈ Complex.slitPlane) :
    (starRingEnd ℂ) w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff] at hw ⊢
  rcases hw with h | h
  · left
    rwa [Complex.conj_re]
  · right
    rw [Complex.conj_im]
    exact neg_ne_zero.mpr h

/-- The reflection carries the left slit chart into the right slit chart. -/
theorem lineReflection_mem_chartRA {μ : ℝ} {a : ℂ} {r₀ R : ℝ} (ha : a.re = μ)
    {z : ℂ} (hz : z ∈ chartLA a r₀ R) : lineReflection μ z ∈ chartRA a r₀ R := by
  obtain ⟨hslit, hann⟩ := hz
  have hslit' : a - z ∈ Complex.slitPlane := hslit
  refine ⟨?_, lineReflection_mem_annulus ha hann⟩
  show lineReflection μ z - a ∈ Complex.slitPlane
  rw [lineReflection_sub_center ha,
    show -((starRingEnd ℂ) (z - a)) = (starRingEnd ℂ) (a - z) by
      rw [map_sub, map_sub]; ring]
  exact conj_mem_slitPlane hslit'

/-- The reflection carries the right slit chart into the left slit chart. -/
theorem lineReflection_mem_chartLA {μ : ℝ} {a : ℂ} {r₀ R : ℝ} (ha : a.re = μ)
    {z : ℂ} (hz : z ∈ chartRA a r₀ R) : lineReflection μ z ∈ chartLA a r₀ R := by
  obtain ⟨hslit, hann⟩ := hz
  have hslit' : z - a ∈ Complex.slitPlane := hslit
  refine ⟨?_, lineReflection_mem_annulus ha hann⟩
  show a - lineReflection μ z ∈ Complex.slitPlane
  rw [show a - lineReflection μ z = -(lineReflection μ z - a) by ring,
    lineReflection_sub_center ha, neg_neg]
  exact conj_mem_slitPlane hslit'

/-! ### §2 Schwarz reflection and the canonical reflected root -/

/-- Schwarz reflection preserves analyticity: if `H` is analytic at `conj w`,
its conjugate-reflected function is analytic at `w`. -/
theorem analyticAt_conj_comp_conj {H : ℂ → ℂ} {w : ℂ}
    (hH : AnalyticAt ℂ H ((starRingEnd ℂ) w)) :
    AnalyticAt ℂ (fun z => (starRingEnd ℂ) (H ((starRingEnd ℂ) z))) w := by
  rw [analyticAt_iff_eventually_differentiableAt]
  have hpull : ∀ᶠ z in nhds w, DifferentiableAt ℂ H ((starRingEnd ℂ) z) :=
    (Complex.continuous_conj.tendsto w).eventually
      (analyticAt_iff_eventually_differentiableAt.mp hH)
  filter_upwards [hpull] with z hz
  have h := hz.conj_conj
  rwa [Complex.conj_conj] at h

/-- The canonical reflected root: the Schwarz reflection of a chart root across
the vertical symmetry line. -/
def reflectedRoot (μ : ℝ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun z => (starRingEnd ℂ) (G (lineReflection μ z))

/-- At reflection-fixed points the reflected root reads the conjugate of the
generating root. -/
theorem reflectedRoot_apply_fixed {μ : ℝ} (G : ℂ → ℂ) {p : ℂ} (hp : p.re = μ) :
    reflectedRoot μ G p = (starRingEnd ℂ) (G p) := by
  show (starRingEnd ℂ) (G (lineReflection μ p)) = _
  rw [lineReflection_eq_self hp]

theorem reflectedRoot_analyticAt {μ : ℝ} {G : ℂ → ℂ} {z : ℂ}
    (hG : AnalyticAt ℂ G (lineReflection μ z)) :
    AnalyticAt ℂ (reflectedRoot μ G) z := by
  have haff : AnalyticAt ℂ (fun w : ℂ => ((2 * μ : ℝ) : ℂ) - w)
      ((starRingEnd ℂ) z) := analyticAt_const.sub analyticAt_id
  have hG' : AnalyticAt ℂ G
      ((fun w : ℂ => ((2 * μ : ℝ) : ℂ) - w) ((starRingEnd ℂ) z)) := hG
  exact analyticAt_conj_comp_conj
    (H := G ∘ fun w : ℂ => ((2 * μ : ℝ) : ℂ) - w) (hG'.comp haff)

/-- The reflected root is analytic on the left chart when the generating root is
analytic on the right chart. -/
theorem reflectedRoot_analyticOnNhd {μ : ℝ} {a : ℂ} {r₀ R : ℝ} (ha : a.re = μ)
    {G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G (chartRA a r₀ R)) :
    AnalyticOnNhd ℂ (reflectedRoot μ G) (chartLA a r₀ R) := fun _ hz =>
  reflectedRoot_analyticAt (hG _ (lineReflection_mem_chartRA ha hz))

/-- The reflected root is a left-chart square root of a line-symmetric member. -/
theorem reflectedRoot_sq {μ : ℝ} {a : ℂ} {r₀ R : ℝ} (ha : a.re = μ)
    {f G : ℂ → ℂ}
    (hsym : ∀ z ∈ ball a R \ closedBall a r₀,
      f (lineReflection μ z) = (starRingEnd ℂ) (f z))
    (hpG : ∀ z ∈ chartRA a r₀ R, G z ^ 2 = f z) :
    ∀ z ∈ chartLA a r₀ R, reflectedRoot μ G z ^ 2 = f z := by
  intro z hz
  show ((starRingEnd ℂ) (G (lineReflection μ z))) ^ 2 = f z
  rw [← map_pow, hpG _ (lineReflection_mem_chartRA ha hz), hsym z hz.2,
    Complex.conj_conj]

/-! ### §3 The sign dichotomy for roots of real values -/

/-- A square root of a positive real is fixed by conjugation. -/
theorem conj_eq_self_of_sq_pos {w v : ℂ} (hw : w ^ 2 = v) (hIm : v.im = 0)
    (hpos : 0 < v.re) : (starRingEnd ℂ) w = w := by
  have hsq : ((starRingEnd ℂ) w) ^ 2 = w ^ 2 := by
    rw [← map_pow, hw, Complex.conj_eq_iff_im.mpr hIm, ← hw]
  have hfac : ((starRingEnd ℂ) w - w) * ((starRingEnd ℂ) w + w) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hre : w.re = 0 := by
      have hc := congrArg Complex.re (eq_neg_of_add_eq_zero_left h)
      rw [Complex.conj_re, Complex.neg_re] at hc
      linarith
    have hv : v.re = w.re * w.re - w.im * w.im := by
      rw [← hw, sq, Complex.mul_re]
    rw [hre] at hv
    nlinarith [mul_self_nonneg w.im]

/-- A square root of a negative real is negated by conjugation. -/
theorem conj_eq_neg_of_sq_neg {w v : ℂ} (hw : w ^ 2 = v) (hIm : v.im = 0)
    (hneg : v.re < 0) : (starRingEnd ℂ) w = -w := by
  have hsq : ((starRingEnd ℂ) w) ^ 2 = w ^ 2 := by
    rw [← map_pow, hw, Complex.conj_eq_iff_im.mpr hIm, ← hw]
  have hfac : ((starRingEnd ℂ) w - w) * ((starRingEnd ℂ) w + w) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso
    have him : w.im = 0 := Complex.conj_eq_iff_im.mp (sub_eq_zero.mp h)
    have hv : v.re = w.re * w.re - w.im * w.im := by
      rw [← hw, sq, Complex.mul_re]
    rw [him] at hv
    nlinarith [mul_self_nonneg w.re]
  · exact eq_neg_of_add_eq_zero_left h

/-- The conjugation ratio of a root of a positive real is `1`. -/
theorem div_conj_self_of_sq_pos {w v : ℂ} (hw : w ^ 2 = v) (hIm : v.im = 0)
    (hpos : 0 < v.re) : w / (starRingEnd ℂ) w = 1 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    rw [← hw] at hpos
    norm_num at hpos
  rw [conj_eq_self_of_sq_pos hw hIm hpos, div_self hw0]

/-- The conjugation ratio of a root of a negative real is `-1`. -/
theorem div_conj_self_of_sq_neg {w v : ℂ} (hw : w ^ 2 = v) (hIm : v.im = 0)
    (hneg : v.re < 0) : w / (starRingEnd ℂ) w = -1 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    rw [← hw] at hneg
    norm_num at hneg
  rw [conj_eq_neg_of_sq_neg hw hIm hneg, div_neg, div_self hw0]

/-- A line-symmetric member is real at reflection-fixed points. -/
theorem im_eq_zero_of_lineSymmetric_fixed {f : ℂ → ℂ} {μ : ℝ} {p : ℂ}
    (hp : p.re = μ)
    (hsymp : f (lineReflection μ p) = (starRingEnd ℂ) (f p)) :
    (f p).im = 0 := by
  rw [lineReflection_eq_self hp] at hsymp
  exact Complex.conj_eq_iff_im.mp hsymp.symm

/-! ### §4 The canonical deck class is the sign observable -/

/-- The deck class of the canonical pair at reflection-fixed ports is the double
conjugation ratio of the generating root. -/
theorem deckClass_reflectedRoot {μ : ℝ} (G : ℂ → ℂ) {pP pM : ℂ}
    (hpP : pP.re = μ) (hpM : pM.re = μ) :
    deckClass G (reflectedRoot μ G) pP pM
      = (G pP / (starRingEnd ℂ) (G pP)) / (G pM / (starRingEnd ℂ) (G pM)) := by
  rw [deckClass, reflectedRoot_apply_fixed G hpP, reflectedRoot_apply_fixed G hpM]

/-- **Same sign, even parity**: when the (real) member values at the two fixed
ports have positive product, the canonical pair's deck class is `1`. -/
theorem deckClass_reflectedRoot_one_of_sign_pos {μ : ℝ} {a : ℂ} {r₀ R : ℝ}
    {f G : ℂ → ℂ}
    (hsym : ∀ z ∈ ball a R \ closedBall a r₀,
      f (lineReflection μ z) = (starRingEnd ℂ) (f z))
    {pP pM : ℂ} (hpP : pP.re = μ) (hpM : pM.re = μ)
    (hPmem : pP ∈ ball a R \ closedBall a r₀)
    (hMmem : pM ∈ ball a R \ closedBall a r₀)
    (hGP : G pP ^ 2 = f pP) (hGM : G pM ^ 2 = f pM)
    (hsign : 0 < (f pP).re * (f pM).re) :
    deckClass G (reflectedRoot μ G) pP pM = 1 := by
  have hImP : (f pP).im = 0 :=
    im_eq_zero_of_lineSymmetric_fixed hpP (hsym pP hPmem)
  have hImM : (f pM).im = 0 :=
    im_eq_zero_of_lineSymmetric_fixed hpM (hsym pM hMmem)
  rw [deckClass_reflectedRoot G hpP hpM]
  rcases mul_pos_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [div_conj_self_of_sq_pos hGP hImP h1,
      div_conj_self_of_sq_pos hGM hImM h2]
    norm_num
  · rw [div_conj_self_of_sq_neg hGP hImP h1,
      div_conj_self_of_sq_neg hGM hImM h2]
    norm_num

/-- **Sign change, odd parity**: when the (real) member values at the two fixed
ports have negative product, the canonical pair's deck class is `-1` — the hole
parity IS the sign change of the member across the hole along the symmetry
line. -/
theorem deckClass_reflectedRoot_neg_one_of_sign_change {μ : ℝ} {a : ℂ}
    {r₀ R : ℝ} {f G : ℂ → ℂ}
    (hsym : ∀ z ∈ ball a R \ closedBall a r₀,
      f (lineReflection μ z) = (starRingEnd ℂ) (f z))
    {pP pM : ℂ} (hpP : pP.re = μ) (hpM : pM.re = μ)
    (hPmem : pP ∈ ball a R \ closedBall a r₀)
    (hMmem : pM ∈ ball a R \ closedBall a r₀)
    (hGP : G pP ^ 2 = f pP) (hGM : G pM ^ 2 = f pM)
    (hsign : (f pP).re * (f pM).re < 0) :
    deckClass G (reflectedRoot μ G) pP pM = -1 := by
  have hImP : (f pP).im = 0 :=
    im_eq_zero_of_lineSymmetric_fixed hpP (hsym pP hPmem)
  have hImM : (f pM).im = 0 :=
    im_eq_zero_of_lineSymmetric_fixed hpM (hsym pM hMmem)
  rw [deckClass_reflectedRoot G hpP hpM]
  rcases mul_neg_iff.mp hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [div_conj_self_of_sq_pos hGP hImP h1,
      div_conj_self_of_sq_neg hGM hImM h2]
    norm_num
  · rw [div_conj_self_of_sq_neg hGP hImP h1,
      div_conj_self_of_sq_pos hGM hImM h2]
    norm_num

/-- **The parity is exactly the sign observable**: for nonvanishing real port
values, the canonical deck class is nontrivial iff the member changes sign
between the two ports. -/
theorem deckClass_reflectedRoot_ne_one_iff {μ : ℝ} {a : ℂ} {r₀ R : ℝ}
    {f G : ℂ → ℂ}
    (hsym : ∀ z ∈ ball a R \ closedBall a r₀,
      f (lineReflection μ z) = (starRingEnd ℂ) (f z))
    {pP pM : ℂ} (hpP : pP.re = μ) (hpM : pM.re = μ)
    (hPmem : pP ∈ ball a R \ closedBall a r₀)
    (hMmem : pM ∈ ball a R \ closedBall a r₀)
    (hGP : G pP ^ 2 = f pP) (hGM : G pM ^ 2 = f pM)
    (hne : (f pP).re * (f pM).re ≠ 0) :
    deckClass G (reflectedRoot μ G) pP pM ≠ 1
      ↔ (f pP).re * (f pM).re < 0 := by
  constructor
  · intro hdeck
    rcases lt_or_gt_of_ne hne with h | h
    · exact h
    · exact absurd (deckClass_reflectedRoot_one_of_sign_pos hsym hpP hpM
        hPmem hMmem hGP hGM h) hdeck
  · intro hsign
    rw [deckClass_reflectedRoot_neg_one_of_sign_change hsym hpP hpM
      hPmem hMmem hGP hGM hsign]
    norm_num

/-! ### §5 The canonical selection: the datum supplies the initial signs -/

/-- **The canonical sweep selection**: the symmetric member's own port readings —
the generating root at the top port, the reflected root at the bottom port —
serve as initial readings of a sweep selection for every anchor.  The canonical
branch datum supplies exactly the sign pair the selection interface leaves
free. -/
theorem exists_canonical_sweepSelection (P : Finset ℕ) {μ : ℝ} {f G : ℂ → ℂ}
    {pP pM : ℂ} (hpM : pM.re = μ)
    (hGP : G pP ^ 2 = f pP) (hGM : G pM ^ 2 = f pM)
    (hImM : (f pM).im = 0) :
    ∃ F₁ F₂ : ℝ → ℂ, SweepSelection P pP pM (f pP) (f pM) F₁ F₂ ∧
      F₁ 0 = G pP ∧ F₂ 0 = reflectedRoot μ G pM := by
  refine ⟨fun t => Complex.exp ((t : ℂ) * anchorLog P pP / 2) * G pP,
    fun t => Complex.exp ((t : ℂ) * anchorLog P pM / 2) * reflectedRoot μ G pM,
    ⟨?_, ?_, fun t => ?_, fun t => ?_⟩, ?_, ?_⟩
  · exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.mul continuous_const).div_const 2)).mul
      continuous_const
  · exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.mul continuous_const).div_const 2)).mul
      continuous_const
  · rw [mul_pow, ← Complex.exp_nat_mul, hGP, anchorSweep,
      show ((2 : ℕ) : ℂ) * ((t : ℂ) * anchorLog P pP / 2)
        = (t : ℂ) * anchorLog P pP by push_cast; ring]
  · rw [mul_pow, ← Complex.exp_nat_mul,
      reflectedRoot_apply_fixed G hpM, ← map_pow, hGM,
      Complex.conj_eq_iff_im.mpr hImM, anchorSweep,
      show ((2 : ℕ) : ℂ) * ((t : ℂ) * anchorLog P pM / 2)
        = (t : ℂ) * anchorLog P pM by push_cast; ring]
  · simp
  · simp

/-! ### §6 The completed symmetrized member: the weld from the sign change -/

/-- Strip containment for a critical-line-centered annulus of radius at most
`1/2`. -/
theorem annulus_strip_of_center_half {a : ℂ} {r₀ R : ℝ} (ha : a.re = 1 / 2)
    (hR : R ≤ 1 / 2) {z : ℂ} (hz : z ∈ ball a R \ closedBall a r₀) :
    0 < z.re ∧ z.re < 1 := by
  have hb : ‖z - a‖ < R := by
    have := hz.1
    rwa [mem_ball, dist_eq_norm] at this
  have habs : |z.re - a.re| ≤ ‖z - a‖ := by
    have h := Complex.abs_re_le_norm (z - a)
    rwa [Complex.sub_re] at h
  rw [ha] at habs
  rw [abs_le] at habs
  constructor <;> [linarith [habs.1]; linarith [habs.2]]

/-- The completed symmetrized member is line-symmetric on every
critical-line-centered annulus inside the strip. -/
theorem completedSEM_lineSymmetric_on_annulus {N : ℕ} {a : ℂ} {r₀ R : ℝ}
    (ha : a.re = 1 / 2) (hR : R ≤ 1 / 2) :
    ∀ z ∈ ball a R \ closedBall a r₀,
      completedSEM N (lineReflection (1 / 2) z)
        = (starRingEnd ℂ) (completedSEM N z) := by
  intro z hz
  obtain ⟨h0, h1⟩ := annulus_strip_of_center_half ha hR hz
  rw [lineReflection_half]
  exact completedSEM_lineReflection h0 h1

/-- **The weld with the parity as an observable**: on a critical-line-centered
annulus, any right-chart root of the completed symmetrized member generates the
canonical pair, and a sign change of the (real) member between the two
critical-line ports IS the odd hole parity.  With steering admissibility, one
prime set beyond any bound then drives every sweep selection into strict
reading reversal while no sweep stage admits a global square root on the
annulus: the deck-class hypothesis of the selection weld is replaced by the
observable sign change. -/
theorem completedSEM_selection_weld_of_sign_change {N : ℕ} {a : ℂ} {r₀ R : ℝ}
    (ha : a.re = 1 / 2) (h0 : 0 ≤ r₀) (hrR : r₀ < R) (hR : R ≤ 1 / 2)
    (hcτ : (r₀ + R) / 2 < a.im)
    (hnarrow : 9 * (2 * ((r₀ + R) / 2)) ≤ a.im + (r₀ + R) / 2)
    (hcap : (a.im + (r₀ + R) / 2) * (4 * Real.log 2) < Real.pi)
    {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (chartRA a r₀ R))
    (hpG : ∀ z ∈ chartRA a r₀ R, G z ^ 2 = completedSEM N z)
    (hsign : (completedSEM N (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re
      * (completedSEM N (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re < 0) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      (∀ vP vM : ℂ, vP ≠ 0 → vM ≠ 0 → ∀ F₁ F₂ : ℝ → ℂ,
        SweepSelection P (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) vP vM F₁ F₂ →
          (F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)).re < 0) ∧
      ∀ t : ℝ, ¬∃ F : ℂ → ℂ,
        AnalyticOnNhd ℂ F (ball a R \ closedBall a r₀) ∧
        ∀ z ∈ ball a R \ closedBall a r₀,
          F z ^ 2 = anchorSweep P t z * completedSEM N z := by
  have hre0 : 0 < a.re := by rw [ha]; norm_num
  have hre1 : a.re < 1 := by rw [ha]; norm_num
  have hsym := completedSEM_lineSymmetric_on_annulus (N := N) (r₀ := r₀) ha hR
  have hre : ∀ z ∈ ball a R \ closedBall a r₀, 0 < z.re := fun z hz =>
    (annulus_strip_of_center_half ha hR hz).1
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  have hpPre : (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I).re = 1 / 2 := by
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, ha]
    ring
  have hpMre : (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I).re = 1 / 2 := by
    rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, ha]
    ring
  have hfP : completedSEM N (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    rw [h] at hsign
    simp at hsign
  have hfM : completedSEM N (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h
    rw [h] at hsign
    simp at hsign
  have hGP : G (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ^ 2
      = completedSEM N (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) :=
    hpG _ hPmem.1
  have hGM : G (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ^ 2
      = completedSEM N (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) :=
    hpG _ hMmem.1
  have hdeck : deckClass G (reflectedRoot (1 / 2) G)
      (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 1 := by
    rw [deckClass_reflectedRoot_neg_one_of_sign_change (a := a) (r₀ := r₀)
      (R := R) hsym hpPre hpMre hPmem.1.2 hMmem.1.2 hGP hGM hsign]
    norm_num
  exact selection_principle_weld hre0 hre1 h0 hrR hcτ hnarrow hcap hre
    hG (reflectedRoot_analyticOnNhd ha hG) hpG
    (reflectedRoot_sq ha hsym hpG) hfP hfM hdeck Q

/-! ### §7 The generating root exists: the datum is unconditional -/

/-- A member analytic and nonvanishing on the right slit chart carries an
analytic square root there: the chart is simply connected. -/
theorem exists_chartRA_sqrt {f : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 < r₀)
    (hrR : r₀ < R)
    (hf : AnalyticOnNhd ℂ f (chartRA a r₀ R))
    (hf0 : ∀ z ∈ chartRA a r₀ R, f z ≠ 0) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (chartRA a r₀ R) ∧
      ∀ z ∈ chartRA a r₀ R, G z ^ 2 = f z := by
  obtain ⟨χ, hχan, -, hχpow⟩ := U0KummerBranch.exists_analyticOnNhd_pow_eq
    (isOpen_chartRA a r₀ R) (isSimplyConnected_chartRA a h0 hrR) hf hf0
    (by norm_num : (2 : ℕ) ≠ 0)
  exact ⟨χ, hχan, hχpow⟩

/-- **The unconditional canonical weld**: for the completed symmetrized member,
nonvanishing on a critical-line-centered annulus plus a sign change of the
(real) member between the two critical-line ports already yields the full
selection weld — the generating chart root exists on the simply connected slit
chart, its Schwarz reflection completes the canonical pair with odd deck class,
and one prime set beyond any bound drives every sweep selection into strict
reading reversal while no sweep stage admits a global square root on the
annulus. -/
theorem completedSEM_selection_weld_of_sign_change_nonvanishing {N : ℕ}
    (hN : 1 ≤ N) {a : ℂ} {r₀ R : ℝ}
    (ha : a.re = 1 / 2) (h0 : 0 < r₀) (hrR : r₀ < R) (hR : R ≤ 1 / 2)
    (hcτ : (r₀ + R) / 2 < a.im)
    (hnarrow : 9 * (2 * ((r₀ + R) / 2)) ≤ a.im + (r₀ + R) / 2)
    (hcap : (a.im + (r₀ + R) / 2) * (4 * Real.log 2) < Real.pi)
    (hf0 : ∀ z ∈ ball a R \ closedBall a r₀, completedSEM N z ≠ 0)
    (hsign : (completedSEM N (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re
      * (completedSEM N (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).re < 0) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      (∀ vP vM : ℂ, vP ≠ 0 → vM ≠ 0 → ∀ F₁ F₂ : ℝ → ℂ,
        SweepSelection P (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) vP vM F₁ F₂ →
          (F₁ 1 / F₂ 1 / (F₁ 0 / F₂ 0)).re < 0) ∧
      ∀ t : ℝ, ¬∃ F : ℂ → ℂ,
        AnalyticOnNhd ℂ F (ball a R \ closedBall a r₀) ∧
        ∀ z ∈ ball a R \ closedBall a r₀,
          F z ^ 2 = anchorSweep P t z * completedSEM N z := by
  have hfan : AnalyticOnNhd ℂ (completedSEM N) (chartRA a r₀ R) := fun z hz =>
    completedSEM_analyticOnNhd_strip hN z (annulus_strip_of_center_half ha hR hz.2)
  obtain ⟨G, hG, hpG⟩ := exists_chartRA_sqrt h0 hrR hfan
    (fun z hz => hf0 z hz.2)
  exact completedSEM_selection_weld_of_sign_change ha (le_of_lt h0) hrR hR hcτ
    hnarrow hcap hG hpG hsign Q

end RHTower
