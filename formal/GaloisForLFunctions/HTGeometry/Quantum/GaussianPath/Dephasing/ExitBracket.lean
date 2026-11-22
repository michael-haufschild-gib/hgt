import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ChordSlope
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ExitInfimum
import GaloisForLFunctions.HTGeometry.ArcsineSeries

/-! # Stability of the first physical scalar exit on a spectral semicircle -/
open Real Set
namespace GaloisForLFunctions.HTGeometry.Dephasing
noncomputable section

/-- Uniform error η in the empty-circuit distance profile displaces
the first exit by at most 4η/W, where W is the spectral width. -/
theorem scalar_exit_bracket (f : ℝ→ℝ) {W η : ℝ} (hW : 0 < W) (hη : 0 ≤ η) (hsmall : η ≤ 1/4)
    (hf : ∀ u∈Icc (0:ℝ) (π/W), |f u-2*sin (u*W/4)| ≤ η) :
    |sInf {u : ℝ | 0 ≤ u ∧ 1/10 < f u}-4*arcsin (1/20)/W| ≤ 4*η/W := by
  let θ := arcsin (1/20)
  let b := 4*θ/W
  let d := 4*η/W
  have ht : 0 ≤ θ := arcsin_nonneg.mpr (by norm_num)
  have hs : sin θ=1/20 := sin_arcsin (by norm_num) (by norm_num)
  have hθ := GaloisForLFunctions.arcsin_le_pi_half_mul (1/20) (by norm_num) (by norm_num)
  have hl : θ ≤ π/4 := by dsimp only [θ]; linarith only [hθ,pi_pos]
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hbW : b*W=4*θ := div_mul_cancel₀ _ hW.ne'
  have hdW : d*W=4*η := div_mul_cancel₀ _ hW.ne'
  have hT : b+d < π/W := by
    apply (lt_div_iff₀ hW).mpr
    rw [add_mul,hbW,hdW]
    dsimp only [θ]
    linarith only [hθ,hsmall,pi_gt_three]
  have hlo (u : ℝ) (hu : u∈Icc 0 (b-d)) : f u ≤ 1/10 := by
    have hut : u ≤ π/W := hu.2.trans ((by linarith only [hd] : b-d ≤ b+d).trans hT.le)
    have hw : u*W ≤ 4*θ-4*η := by simpa only [sub_mul,hbW,hdW] using mul_le_mul_of_nonneg_right hu.2 hW.le
    have hbot := FirstAscent.sine_chord_floor (div_nonneg (mul_nonneg hu.1 hW.le) (by norm_num : (0:ℝ) ≤ 4))
      (show u*W/4 ≤ θ by linarith only [hw,hη]) hl
    rw [hs] at hbot
    linarith only [hbot,(abs_le.mp (hf u ⟨hu.1,hut⟩)).2,hw]
  have hhi (u : ℝ) (hu : u∈Icc 0 (π/W)) (hc : f u ≤ 1/10) : u ≤ b+d := by
    apply (mul_le_mul_iff_left₀ hW).mp
    rw [add_mul,hbW,hdW]
    rcases le_total (u*W/4) θ with hh|hh
    · linarith only [hh,hη]
    · have hup : u*W/4 ≤ π/4 := div_le_div_of_nonneg_right ((le_div_iff₀ hW).mp hu.2) (by norm_num)
      have hchord := FirstAscent.sine_chord_floor ht hh hup
      rw [hs] at hchord
      linarith only [hchord,(abs_le.mp (hf u hu)).1,hc]
  have h := FirstAscent.first_exit_bracket (fun u => f u ≤ 1/10) (add_nonneg hb hd) hT hlo hhi
  simp only [not_le] at h
  exact abs_le.mpr ⟨by linarith only [h.1],by linarith only [h.2]⟩

#print axioms scalar_exit_bracket
end
end GaloisForLFunctions.HTGeometry.Dephasing
