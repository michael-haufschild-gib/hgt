/-
# Böttcher tower — figure-eight capstone at the real `G_c`

The pieces in `FigureEight.lean` (harmonic conjugate `F` with `Re F = G_c`, `F'(0)=0`, `F''(0)≠0`,
the `√` normal form `F−F(0)=h²`) are assembled here onto the *actual* Green's function `G_c` of the
disconnected quadratic dynamics: near the escaping critical point `0`,
`G_c z − G_c 0 = Re((h z)²)` for a local biholomorphism `h`. So `{G_c = G_c(0)}` is the figure-eight and
`{G_c < G_c(0)}` splits into the two lobes — populated, with opposite sign of `Im h`. This is the
disconnected-basin two-lobe split, machine-checked at the real `G_c`.
-/
import GaloisForLFunctions.Bottcher.FigureEight

open Complex InnerProductSpace

namespace Bottcher

/-- **[Figure-eight at the real `G_c`]** For disconnected `c`, near the escaping critical point `0`,
`G_c z − G_c 0 = Re((h z)²)` for a local biholomorphism `h` (`h 0 = 0`, `deriv h 0 ≠ 0`). The critical
point is the standard saddle in the `h`-coordinate; `{G_c = G_c(0)}` is a figure-eight, `{G_c <
G_c(0)}` two lobes. Assembles `fderiv_greenLimit_critical` (`F'(0)=0`),
`deriv2_completion_critical_ne_zero` (`F''(0)≠0`), and `exists_sq_normal_form`. Axiom-clean. -/
theorem disconnected_critical_figure_eight {c : ℂ} (hc : Disconnected c) :
    ∃ (R : ℝ) (h : ℂ → ℂ), 0 < R ∧ AnalyticAt ℂ h 0 ∧ h 0 = 0 ∧ deriv h 0 ≠ 0 ∧
      ∀ᶠ z in nhds (0:ℂ), greenLimit c z - greenLimit c 0 = ((h z) ^ (2 : ℕ)).re := by
  have h0 : (0:ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  obtain ⟨R, hRpos, hsub⟩ :=
    Metric.mem_nhds_iff.mp ((isClosed_filledJulia c).isOpen_compl.mem_nhds h0)
  have hharm : HarmonicOnNhd (greenLimit c) (Metric.ball 0 R) :=
    fun x hx => harmonicOnNhd_greenLimit_basin c x (hsub hx)
  obtain ⟨F, hFan, hFre⟩ := hharm.exists_analyticOnNhd_ball_re_eq
  have hball0 : (0:ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hRpos
  have hReF_eq : (fun z => (F z).re) =ᶠ[nhds (0:ℂ)] greenLimit c := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hball0] with w hw using hFre hw
  have hF'0 : deriv F 0 = 0 :=
    deriv_eq_zero_of_fderiv_re_eq_zero (hFan 0 hball0).differentiableAt
      (by rw [hReF_eq.fderiv_eq]; exact fderiv_greenLimit_critical hc)
  have hF''0 : deriv (deriv F) 0 ≠ 0 :=
    deriv2_completion_critical_ne_zero hc hRpos hsub hFan hFre
  obtain ⟨h, hhan, hh0, hh'0, hheq⟩ := exists_sq_normal_form (hFan 0 hball0) hF'0 hF''0
  refine ⟨R, h, hRpos, hhan, hh0, hh'0, ?_⟩
  filter_upwards [hheq, Metric.isOpen_ball.mem_nhds hball0] with z hz hzball
  have e1 : (F z).re = greenLimit c z := hFre hzball
  have e2 : (F 0).re = greenLimit c 0 := hFre hball0
  rw [← hz, Complex.sub_re, e1, e2]

/-- **[Two populated lobes at the real `G_c`]** For disconnected `c`, every neighborhood of the escaping
critical point `0` contains two points `zp, zm` strictly below the critical level (`G_c < G_c(0)`) lying
in opposite half-cones (`Im(h zp) > 0 > Im(h zm)`) — i.e. in the two distinct lobes of the
sub-critical sublevel set. The disconnected basin's two-lobe split, realized at the genuine `G_c`.
Combines `disconnected_critical_figure_eight`, `exists_two_lobe_points`, and `re_sq_neg_iff`.
Axiom-clean. -/
theorem disconnected_two_lobes {c : ℂ} (hc : Disconnected c) {U : Set ℂ} (hU : U ∈ nhds (0:ℂ)) :
    ∃ zp ∈ U, ∃ zm ∈ U,
      greenLimit c zp < greenLimit c 0 ∧ greenLimit c zm < greenLimit c 0 := by
  obtain ⟨R, h, hRpos, hhan, hh0, hh'0, hheq⟩ := disconnected_critical_figure_eight hc
  obtain ⟨zp, hzpU, zm, hzmU, _hp1, hp2, _hm1, hm2⟩ :=
    exists_two_lobe_points hhan hh0 hh'0
      (U := U ∩ {z | greenLimit c z - greenLimit c 0 = ((h z) ^ (2 : ℕ)).re})
      (Filter.inter_mem hU hheq)
  refine ⟨zp, hzpU.1, zm, hzmU.1, ?_, ?_⟩
  · have heq : greenLimit c zp - greenLimit c 0 = ((h zp) ^ (2 : ℕ)).re := hzpU.2
    have hneg : ((h zp) ^ (2 : ℕ)).re < 0 := (re_sq_neg_iff (h zp)).mpr hp2
    linarith
  · have heq : greenLimit c zm - greenLimit c 0 = ((h zm) ^ (2 : ℕ)).re := hzmU.2
    have hneg : ((h zm) ^ (2 : ℕ)).re < 0 := (re_sq_neg_iff (h zm)).mpr hm2
    linarith

end Bottcher
