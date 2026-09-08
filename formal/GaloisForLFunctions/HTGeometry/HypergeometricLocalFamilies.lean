import GaloisForLFunctions.HTGeometry.HypergeometricParameterHolomorphy

/-! Local holomorphic Gauss families with literal denominator separation. -/
namespace GaloisForLFunctions.HTGeometry
open Complex Filter Topology Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private theorem local_family {a b c : ℂ → ℂ} {w z : ℂ}
    (ha : AnalyticAt ℂ a w) (hb : AnalyticAt ℂ b w) (hc : AnalyticAt ℂ c w)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ᶠ u in 𝓝 w, ∀ j : ℕ, δ ≤ ‖c u+j‖)
    (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun u => ordinaryHypergeometric (a u) (b u) (c u) z) w := by
  let B := ‖a w‖+‖b w‖+‖c w‖+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hs : ContinuousAt (fun u => ‖a u‖+‖b u‖+‖c u‖) w :=
    (ha.continuousAt.norm.add hb.continuousAt.norm).add hc.continuousAt.norm
  have he : ∀ᶠ u in 𝓝 w, ‖a u‖+‖b u‖+‖c u‖ < B :=
    hs.eventually_lt_const (by dsimp [B]; linarith)
  obtain ⟨R,hR,hall⟩ := Metric.eventually_nhds_iff.mp
    (he.and (hsep.and ((Complex.analyticAt_iff_eventually_differentiableAt.mp ha).and
      ((Complex.analyticAt_iff_eventually_differentiableAt.mp hb).and
        (Complex.analyticAt_iff_eventually_differentiableAt.mp hc)))))
  apply hypergeometric_family_differentiableAt a b c w z R B δ hR hB hδ
  · intro u hu; exact (hall (Metric.mem_ball.mp hu)).2.2.1
  · intro u hu; exact (hall (Metric.mem_ball.mp hu)).2.2.2.1
  · intro u hu; exact (hall (Metric.mem_ball.mp hu)).2.2.2.2
  · intro u hu
    have h := (hall (Metric.mem_ball.mp hu)).1
    have hna := norm_nonneg (a u)
    have hnb := norm_nonneg (b u)
    have hnc := norm_nonneg (c u)
    exact ⟨by linarith,by linarith,by linarith⟩
  · intro u hu; exact (hall (Metric.mem_ball.mp hu)).2.1
  · exact hz

/-- Holomorphic parameters with nonreal denominator retain holomorphy of the original Gauss sum. -/
theorem hypergeometric_family_of_im_ne_zero {a b c : ℂ → ℂ} {w z : ℂ}
    (ha : AnalyticAt ℂ a w) (hb : AnalyticAt ℂ b w) (hc : AnalyticAt ℂ c w)
    (hci : (c w).im ≠ 0) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun u => ordinaryHypergeometric (a u) (b u) (c u) z) w := by
  have hδ : 0 < |(c w).im|/2 := by positivity
  apply local_family ha hb hc hδ ?_ hz
  have he : ∀ᶠ u in 𝓝 w, |(c w).im|/2 < |(c u).im| :=
    (Complex.continuous_im.continuousAt.comp hc.continuousAt).abs.eventually_const_lt (by dsimp; linarith)
  filter_upwards [he] with u hu
  intro j
  have hn := Complex.abs_im_le_norm (c u+j)
  simp only [Complex.add_im,Complex.natCast_im,add_zero] at hn
  exact hu.le.trans hn

/-- Positive denominator real part supplies local uniform pole separation. -/
theorem hypergeometric_family_of_re_pos {a b c : ℂ → ℂ} {w z : ℂ}
    (ha : AnalyticAt ℂ a w) (hb : AnalyticAt ℂ b w) (hc : AnalyticAt ℂ c w)
    (hcr : 0 < (c w).re) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun u => ordinaryHypergeometric (a u) (b u) (c u) z) w := by
  have hδ : 0 < (c w).re/2 := half_pos hcr
  apply local_family ha hb hc hδ ?_ hz
  have he : ∀ᶠ u in 𝓝 w, (c w).re/2 < (c u).re :=
    (Complex.continuous_re.continuousAt.comp hc.continuousAt).eventually_const_lt (by dsimp; linarith)
  filter_upwards [he] with u hu
  intro j
  have hn := Complex.re_le_norm (c u+j)
  simp only [Complex.add_re,Complex.natCast_re] at hn
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  linarith

end
end GaloisForLFunctions.HTGeometry
