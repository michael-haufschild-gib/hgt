import GaloisForLFunctions.RHTower.ZetaNotchDualOscillationBound
import GaloisForLFunctions.Bottcher.IntervalLogDerivFTC

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

/-- Actual chi logarithmic transport along the compact shift segment. -/
def zetaChiSegmentLog (s : ℂ) (t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, (s - (1 / 2 : ℂ)) *
    logDeriv zetaChi (linePt t + (u : ℂ) * (s - (1 / 2 : ℂ)))

/-- Exact segment transport of the original chi factor. Its nonvanishing
follows from the Gamma factors on the strict strip. -/
theorem zetaChi_shift_div_line_eq_exp_segmentLog {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    zetaChi (s + (t : ℂ) * I) / zetaChi (linePt t) =
      Complex.exp (zetaChiSegmentLog s t) := by
  let δ : ℂ := s - (1 / 2 : ℂ)
  let z : ℝ → ℂ := fun u => linePt t + (u : ℂ) * δ
  let p : ℝ → ℝ := fun u => 1 / 2 + u * δ.re
  let U : Set ℝ := p ⁻¹' Ioo 0 1
  let g : ℝ → ℂ := fun u => zetaChi (z u)
  let g' : ℝ → ℂ := fun u => δ * g u * logDeriv zetaChi (z u)
  have hzC : Continuous z := by dsimp [z]; fun_prop
  have hpC : Continuous p := by dsimp [p]; fun_prop
  have hre (u : ℝ) : (z u).re = p u := by
    simp [z, p, linePt]
  have hU : IsOpen U := isOpen_Ioo.preimage hpC
  have hUc : Convex ℝ U := by
    intro x hx y hy r q hr hq hrq
    have hb := (convex_Ioo (0 : ℝ) 1) hx hy hr hq hrq
    have he : p (r • x + q • y) = r • p x + q • p y := by
      dsimp only [p]
      simp only [smul_eq_mul]
      nlinarith
    change p (r • x + q • y) ∈ Ioo 0 1
    rw [he]
    exact hb
  have hsub : uIcc (0 : ℝ) 1 ⊆ U := by
    intro u hu
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hb := (convex_Ioo (0 : ℝ) 1)
      (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num) ⟨hs0, hs1⟩
      (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (show 1 - u + u = 1 by ring)
    change p u ∈ Ioo 0 1
    have he : p u = (1 - u) * (1 / 2) + u * s.re := by
      simp [p, δ]
      ring
    rw [he]
    simpa only [smul_eq_mul] using hb
  have hz0 (u : ℝ) (hu : u ∈ U) : 0 < (z u).re := by
    rw [hre]
    exact hu.1
  have hz1 (u : ℝ) (hu : u ∈ U) : (z u).re < 1 := by
    rw [hre]
    exact hu.2
  have hG (u : ℝ) (hu : u ∈ U) : Gammaℝ (1 - z u) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simpa using sub_pos.mpr (hz1 u hu))
  have hn (u : ℝ) (hu : u ∈ U) : g u ≠ 0 :=
    zetaChi_ne_zero_of_mem_openStrip (hz0 u hu) (hz1 u hu)
  have hd (u : ℝ) (hu : u ∈ U) : HasDerivAt g (g' u) u := by
    have hzD : HasDerivAt z δ u := by
      simpa [z] using
        (((hasDerivAt_id u).ofReal_comp).mul_const δ).const_add (linePt t)
    have hb := ((zetaChi_analyticAt (hG u hu)).differentiableAt.hasDerivAt).scomp u hzD
    change HasDerivAt g (δ • deriv zetaChi (z u)) u at hb
    apply hb.congr_deriv
    dsimp only [g']
    rw [smul_eq_mul, logDeriv_apply]
    dsimp only [g] at hn ⊢
    field_simp [hn u hu]
  have hgC : ContinuousOn g U := fun u hu => (hd u hu).continuousAt.continuousWithinAt
  have hlogC : ContinuousOn (fun u => logDeriv zetaChi (z u)) U := by
    intro u hu
    exact ((ZetaNotch.continuousAt_logDeriv_zetaChi (hG u hu) (hn u hu)).comp hzC.continuousAt).continuousWithinAt
  have hg'C : ContinuousOn g' U := (continuousOn_const.mul hgC).mul hlogC
  have hb := exp_integral_logDeriv_interval hU hUc hsub hd hn hg'C
  have hi : (∫ u in (0 : ℝ)..1, g' u / g u) = zetaChiSegmentLog s t := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only [g', zetaChiSegmentLog]
    change δ * g u * logDeriv zetaChi (z u) / g u = δ * logDeriv zetaChi (z u)
    field_simp [hn u (hsub hu)]
  rw [hi] at hb
  have hzA : z 0 = linePt t := by simp [z]
  have hzB : z 1 = s + (t : ℂ) * I := by dsimp [z, δ, linePt]; push_cast; ring
  dsimp only [g] at hb
  rw [hzA, hzB] at hb
  exact hb.symm

/-- The normalized actual chi ratio is the exponential of its exact
conductor-subtracted segment error. -/
theorem zetaChi_normalized_shift_eq_exp {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (t : ℝ) :
    (zetaChi (s + (t : ℂ) * I) / zetaChi (linePt t)) *
      Complex.exp ((s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)) =
      Complex.exp (zetaChiSegmentLog s t +
        (s - (1 / 2 : ℂ)) * (Real.log (t / (2 * Real.pi)) : ℂ)) := by
  rw [Complex.exp_add, zetaChi_shift_div_line_eq_exp_segmentLog hs0 hs1]

end RHTower
