/-
# The disconnected half of all-nonexceptional U0--Bottcher independence

For a disconnected quadratic parameter the critical point is an escaping, nondegenerate saddle
of the Green function.  The first lemma below records the outward side of that saddle: every
neighbourhood of the critical point contains points at strictly larger Green level.  In particular
the connected critical superlevel has a point strictly inside the unit circle.
-/
import GaloisForLFunctions.U0.U0AllNonexceptionalConnected
import GaloisForLFunctions.Bottcher.FigureEight
import GaloisForLFunctions.Bottcher.GreenSuperlevel
import GaloisForLFunctions.Bottcher.SectionInverse
import GaloisForLFunctions.Bottcher.BottcherTowerData

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0NaturalBoundary U0MeroCarrier U0WindowNormalization U0PhiLargeCapstone

namespace U0AllNonexceptional

/-- A disconnected critical point is not a local maximum of the Green function.  More precisely,
there is a point in the open unit disk whose Green value is strictly larger than the critical
value.  This is the outward pair of sectors in the nondegenerate holomorphic saddle model. -/
theorem exists_unitDisk_green_gt_critical {c : ℂ} (hc : Disconnected c) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ greenFunctionDyn c 0 < greenFunctionDyn c z := by
  have h0basin : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  obtain ⟨R₀, F, hR₀, hFan₀, hFre₀, _hF'0⟩ := exists_holomorphic_completion_critical hc
  obtain ⟨Rb, hRb, hRbsub⟩ :=
    Metric.mem_nhds_iff.mp ((isClosed_filledJulia c).isOpen_compl.mem_nhds h0basin)
  let R : ℝ := min (min R₀ Rb) (1 / 2)
  have hR : 0 < R := lt_min (lt_min hR₀ hRb) (by norm_num)
  have hRR₀ : R ≤ R₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRRb : R ≤ Rb := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRhalf : R ≤ 1 / 2 := min_le_right _ _
  have hbasin : ball (0 : ℂ) R ⊆ (filledJulia c)ᶜ :=
    (ball_subset_ball hRRb).trans hRbsub
  have hFan : AnalyticOnNhd ℂ F (ball (0 : ℂ) R) :=
    hFan₀.mono (ball_subset_ball hRR₀)
  have hFre : EqOn (fun z => (F z).re) (greenLimit c) (ball (0 : ℂ) R) :=
    hFre₀.mono (ball_subset_ball hRR₀)
  have hF'' : deriv (deriv F) 0 ≠ 0 :=
    deriv2_completion_critical_ne_zero hc hR hbasin hFan hFre
  have hFopen : IsOpen (F '' ball (0 : ℂ) R) := by
    rcases hFan.is_constant_or_isOpen (convex_ball (0 : ℂ) R).isPreconnected with hconst | hopen
    · exfalso
      obtain ⟨v, hv⟩ := hconst
      have hderiv_zero : (fun z => deriv F z) =ᶠ[nhds (0 : ℂ)] (fun _ => 0) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with z hz
        have hev : F =ᶠ[nhds z] (fun _ => v) := by
          filter_upwards [isOpen_ball.mem_nhds hz] with w hw
          exact hv w hw
        simpa using hev.deriv_eq
      exact hF'' (by simpa using hderiv_zero.deriv_eq)
    · exact hopen _ (Set.Subset.refl _) isOpen_ball
  have hF0mem : F 0 ∈ F '' ball (0 : ℂ) R :=
    ⟨0, Metric.mem_ball_self hR, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hFopen (F 0) hF0mem
  have htarget : F 0 + ((ε / 2 : ℝ) : ℂ) ∈ F '' ball (0 : ℂ) R := by
    apply hεsub
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  obtain ⟨z, hzR, hzF⟩ := htarget
  have hzbasin : z ∉ filledJulia c := hbasin hzR
  have h0G : greenFunctionDyn c 0 = greenLimit c 0 := by
    unfold greenFunctionDyn
    rw [if_neg h0basin]
  have hzG : greenFunctionDyn c z = greenLimit c z := by
    unfold greenFunctionDyn
    rw [if_neg hzbasin]
  refine ⟨z, ?_, ?_⟩
  · have hzR' : ‖z‖ < R := by simpa [mem_ball_zero_iff] using hzR
    linarith
  · rw [h0G, hzG, ← hFre (Metric.mem_ball_self hR), ← hFre hzR, hzF]
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith

end U0AllNonexceptional
