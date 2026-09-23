import GaloisForLFunctions.RHTower.ZetaFarRightDecay
import GaloisForLFunctions.RHTower.LevinsonEntireDetector
import GaloisForLFunctions.HTGeometry.SegmentArgumentBound

/-!
# The right edge of a Levinson rectangle

At abscissa `4` the two elementary bounds `‖ζ-1‖ ≤ 3/16` and `‖ζ'‖ ≤ 3/8` give
`‖G - 1‖ ≤ 9/16 < 1` for every `‖λ‖ ≤ 1`, so `Re G > 0` on the whole vertical line.  A function
with positive real part has argument variation at most `π`, so the right edge of the rectangle
contributes `O(1)`, and passing to the entire detector `G♯ = (s-1)^(2 : ℕ) G` only adds the explicit
rational term `2/(s-1)`.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

theorem norm_levinsonG_sub_one_le_of_four_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {s : ℂ}
    (hs : 4 ≤ s.re) : ‖levinsonG lam s - 1‖ ≤ 9 / 16 := by
  have h1 := norm_riemannZeta_sub_one_le_of_four_le hs
  have h2 := norm_deriv_riemannZeta_le_of_four_le hs
  have hsplit : levinsonG lam s - 1 = (riemannZeta s - 1) + lam * deriv riemannZeta s := by
    rw [levinsonG]; ring
  have hmul : ‖lam * deriv riemannZeta s‖ ≤ 3 / 8 := by
    rw [norm_mul]
    calc ‖lam‖ * ‖deriv riemannZeta s‖ ≤ 1 * (3 / 8) :=
          mul_le_mul hlam h2 (norm_nonneg _) (by norm_num)
      _ = 3 / 8 := by norm_num
  rw [hsplit]
  calc ‖(riemannZeta s - 1) + lam * deriv riemannZeta s‖
      ≤ ‖riemannZeta s - 1‖ + ‖lam * deriv riemannZeta s‖ := norm_add_le _ _
    _ ≤ 3 / 16 + 3 / 8 := add_le_add h1 hmul
    _ = 9 / 16 := by norm_num

/-- **The detector has positive real part far to the right.** -/
theorem re_levinsonG_pos_of_four_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {s : ℂ} (hs : 4 ≤ s.re) :
    0 < (levinsonG lam s).re := by
  have h := norm_levinsonG_sub_one_le_of_four_le hlam hs
  have hre : |(levinsonG lam s - 1).re| ≤ 9 / 16 := le_trans (Complex.abs_re_le_norm _) h
  rw [Complex.sub_re, Complex.one_re, abs_le] at hre
  linarith [hre.1]

theorem levinsonG_ne_zero_of_four_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {s : ℂ} (hs : 4 ≤ s.re) :
    levinsonG lam s ≠ 0 := by
  intro h
  have := re_levinsonG_pos_of_four_le hlam hs
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

theorem levinsonGEntire_ne_zero_of_four_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1) {s : ℂ} (hs : 4 ≤ s.re) :
    levinsonGEntire lam s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    norm_num at hs
  rw [Ne, levinsonGEntire_eq_zero_iff lam hs1]
  exact levinsonG_ne_zero_of_four_le hlam hs

/-! ## The argument variation on the right edge -/

theorem vertEdge_re {d t : ℝ} : (((d : ℂ) + t * I)).re = d := by simp

theorem continuous_vertEdge (d : ℝ) : Continuous fun u : ℝ => (d : ℂ) + u * I := by
  exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)

theorem continuous_levinsonG_vertEdge (lam : ℂ) {d : ℝ}
    (hne : ∀ u : ℝ, ((d : ℂ) + u * I) ≠ 1) :
    Continuous fun u : ℝ => levinsonG lam ((d : ℂ) + u * I) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have h1 : ContinuousAt (fun v : ℝ => (d : ℂ) + v * I) u := (continuous_vertEdge d).continuousAt
  have h2 : ContinuousAt (levinsonG lam) ((d : ℂ) + u * I) :=
    (analyticAt_levinsonG lam (hne u)).continuousAt
  have hc : ContinuousAt ((levinsonG lam) ∘ (fun v : ℝ => (d : ℂ) + v * I)) u :=
    ContinuousAt.comp h2 h1
  simpa [Function.comp_def] using hc

theorem continuous_deriv_levinsonG_vertEdge (lam : ℂ) {d : ℝ}
    (hne : ∀ u : ℝ, ((d : ℂ) + u * I) ≠ 1) :
    Continuous fun u : ℝ => deriv (levinsonG lam) ((d : ℂ) + u * I) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have h1 : ContinuousAt (fun v : ℝ => (d : ℂ) + v * I) u := (continuous_vertEdge d).continuousAt
  have h2 : ContinuousAt (deriv (levinsonG lam)) ((d : ℂ) + u * I) :=
    ((analyticAt_levinsonG lam (hne u)).deriv).continuousAt
  have hc : ContinuousAt ((deriv (levinsonG lam)) ∘ (fun v : ℝ => (d : ℂ) + v * I)) u :=
    ContinuousAt.comp h2 h1
  simpa [Function.comp_def] using hc

theorem hasDerivAt_levinsonG_vertEdge (lam : ℂ) {d : ℝ} (hd : 4 ≤ d) (t : ℝ) :
    HasDerivAt (fun u : ℝ => levinsonG lam ((d : ℂ) + u * I))
      (deriv (levinsonG lam) ((d : ℂ) + t * I) * I) t := by
  have hne : ((d : ℂ) + t * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [vertEdge_re, Complex.one_re] at this
    linarith
  have hpath : HasDerivAt (fun u : ℝ => (d : ℂ) + u * I) I t := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add ((d : ℝ) : ℂ)
    simpa using h
  exact ((analyticAt_levinsonG lam hne).differentiableAt.hasDerivAt).comp t hpath

/-- **The right edge contributes at most one half-turn.** -/
theorem abs_integral_re_logDeriv_levinsonG_right_le {lam : ℂ} (hlam : ‖lam‖ ≤ 1)
    {d T₁ T₂ : ℝ} (hd : 4 ≤ d) (hT : T₁ ≤ T₂) :
    |∫ t in T₁..T₂, (logDeriv (levinsonG lam) ((d : ℂ) + t * I)).re| ≤ Real.pi := by
  classical
  set f : ℝ → ℂ := fun u => levinsonG lam ((d : ℂ) + u * I) with hfdef
  set f' : ℝ → ℂ := fun u => deriv (levinsonG lam) ((d : ℂ) + u * I) * I with hf'def
  have hd4 : ∀ u : ℝ, (4 : ℝ) ≤ (((d : ℂ) + u * I)).re := by
    intro u; rw [vertEdge_re]; exact hd
  have hne : ∀ u : ℝ, f u ≠ 0 := fun u => levinsonG_ne_zero_of_four_le hlam (hd4 u)
  have hpathne : ∀ u : ℝ, ((d : ℂ) + u * I) ≠ 1 := by
    intro u h
    have := congrArg Complex.re h
    rw [vertEdge_re, Complex.one_re] at this
    linarith
  have hfc : Continuous f := continuous_levinsonG_vertEdge lam hpathne
  have hf'c : Continuous f' :=
    (continuous_deriv_levinsonG_vertEdge lam hpathne).mul continuous_const
  have hquot : ContinuousOn (fun u => f' u / f u) (Icc T₁ T₂) :=
    ContinuousOn.div hf'c.continuousOn hfc.continuousOn (fun u _ => hne u)
  have hZ : ∀ t ∈ Ioo T₁ T₂, (f t).re = 0 → t ∈ (∅ : Finset ℝ) := by
    intro t _ hzero
    exact absurd hzero (ne_of_gt (re_levinsonG_pos_of_four_le hlam (hd4 t)))
  have hbound := abs_integral_im_logDeriv_le_of_finite_re_zeros hT
    (f := f) (f' := f') (fun u _ => hasDerivAt_levinsonG_vertEdge lam hd u) hquot
    (fun u _ => hne u) ∅ hZ
  have hcongr : ∀ u ∈ Set.uIcc T₁ T₂,
      (f' u / f u).im = (logDeriv (levinsonG lam) ((d : ℂ) + u * I)).re := by
    intro u _
    rw [hf'def, hfdef, logDeriv_apply]
    simp only
    rw [mul_comm, mul_div_assoc, Complex.mul_im]
    simp
  rw [intervalIntegral.integral_congr hcongr] at hbound
  simpa using hbound

end RHTower

end
