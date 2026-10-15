import GaloisForLFunctions.RHTower.XiHurwitzAnchorZeroGraph
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.HTGeometry.PuncturedPowerRoot

/-!
# Fixed-width Hurwitz root tubes pinch at critical-line zeros

Every neighbourhood of the anchor shift contains simple Hurwitz shift zeros
whose exponent lies strictly in the right half-strip. Consequently no fixed
positive shift disk over that half-strip carries holomorphic roots of any
fixed degree greater than one. The source of these branch points is an
unconditional critical-line Xi zero, not a hypothetical off-line zero.
-/

open Complex Filter Metric Set HurwitzZetaContinuation
open scoped Topology

namespace RHTower

/-- Critical-line Xi zeros force simple Hurwitz shift zeros inside every fixed anchor tube. -/
theorem exists_simple_hurwitz_shift_zero_near_critical_anchor
    {rho : ℂ} (hzero : xi rho = 0) (hline : rho.re = 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s a : ℂ, (1 / 2 < s.re ∧ s.re < 1) ∧ ‖a - 1‖ < ε ∧
      AnalyticAt ℂ (continuedHzeta s) a ∧ continuedHzeta s a = 0 ∧
      analyticOrderAt (continuedHzeta s) a = 1 := by
  obtain ⟨A, hA, hAa, hgraph, horder⟩ := exists_analytic_hurwitz_zero_graph hzero
  have hlim : Tendsto (fun s => (s, A s)) (𝓝 rho) (𝓝 (rho, 1)) := by
    simpa only [hA, id_eq] using (continuousAt_id.prodMk hAa.continuousAt).tendsto
  have hlimA : Tendsto A (𝓝 rho) (𝓝 (1 : ℂ)) := by
    simpa only [hA] using hAa.continuousAt.tendsto
  have htube : ∀ᶠ s in 𝓝 rho, ‖A s - 1‖ < min ε (1 / 2 : ℝ) := by
    simpa only [mem_ball, dist_eq_norm] using
      hlimA.eventually (ball_mem_nhds (1 : ℂ) (lt_min hε (by norm_num)))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (htube.and (horder.and (hlim.eventually hgraph)))
  let t : ℝ := min δ (1 / 2 : ℝ) / 2
  have ht : 0 < t := half_pos (lt_min hδ (by norm_num))
  have htδ : t < δ := by
    have := min_le_left δ (1 / 2 : ℝ)
    dsimp [t]
    linarith
  have hthalf : t < (1 / 2 : ℝ) := by
    have := min_le_right δ (1 / 2 : ℝ)
    dsimp [t]
    linarith
  let s : ℂ := rho + (t : ℂ)
  have hsd : dist s rho < δ := by
    simpa [s, dist_eq_norm, abs_of_pos ht] using htδ
  have hs := hball hsd
  have hsre : s.re = 1 / 2 + t := by simp [s, hline]
  have hsstrip : 1 / 2 < s.re ∧ s.re < 1 := by constructor <;> linarith
  have hspos : 0 < s.re := by linarith [hsstrip.1]
  have hs1 : s ≠ 1 := by
    intro heq
    have := hsstrip.2
    simp [heq] at this
  refine ⟨s, A s, hsstrip, (lt_min_iff.mp hs.1).1, ?_, hs.2.2.mpr rfl, hs.2.1⟩
  exact continuedHzeta_analyticAt_shift hspos hs1 (lt_min_iff.mp hs.1).2

/-- Unconditional branch points in every fixed-width Hurwitz tube over the right half-strip. -/
theorem exists_simple_hurwitz_shift_zero_in_right_half_strip
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s a : ℂ, (1 / 2 < s.re ∧ s.re < 1) ∧ ‖a - 1‖ < ε ∧
      AnalyticAt ℂ (continuedHzeta s) a ∧ continuedHzeta s a = 0 ∧
      analyticOrderAt (continuedHzeta s) a = 1 := by
  obtain ⟨t, _, ht⟩ := exists_Xi_zero_gt 0
  have hre : (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by simp
  have hz : xi (1 / 2 + (t : ℂ) * I) = 0 := by
    apply Complex.ext
    · rw [Complex.zero_re]
      exact ht
    · rw [xi_im_eq_zero_on_line hre, Complex.zero_im]
  exact exists_simple_hurwitz_shift_zero_near_critical_anchor hz hre hε

/-- No fixed shift disk admits holomorphic power roots throughout the right half-strip. -/
theorem not_forall_exists_hurwitz_shift_disk_power_root
    {d : ℕ} (hd : 1 < d) {ε : ℝ} (hε : 0 < ε) :
    ¬ ∀ s : ℂ, (1 / 2 < s.re ∧ s.re < 1) → ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball (1 : ℂ) ε) ∧
        ∀ a ∈ ball (1 : ℂ) ε, g a ^ d = continuedHzeta s a := by
  intro hroot
  obtain ⟨s, a, hs, ha, han, hz, hord⟩ :=
    exists_simple_hurwitz_shift_zero_in_right_half_strip hε
  obtain ⟨g, hg, hpow⟩ := hroot s hs
  have hamem : a ∈ ball (1 : ℂ) ε := by simpa only [mem_ball, dist_eq_norm] using ha
  have hga := hg a hamem
  have hmem : ∀ᶠ z in 𝓝 a, z ∈ ball (1 : ℂ) ε := isOpen_ball.mem_nhds hamem
  have hp : ∀ᶠ z in 𝓝[≠] a, g z ^ d = continuedHzeta s z := by
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with z hz'
    exact hpow z hz'
  have hgd : ∀ᶠ z in 𝓝[≠] a, DifferentiableAt ℂ g z :=
    (hga.eventually_analyticAt.mono fun z hz' => hz'.differentiableAt).filter_mono
      nhdsWithin_le_nhds
  have hdiv := GaloisForLFunctions.HTGeometry.dvd_analyticOrderNatAt_of_pow_eq_on_punctured_nhds
    (by omega : 0 < d) han hz hgd hp
  have hd1 : d ∣ 1 := by simpa only [analyticOrderNatAt, hord, ENat.toNat_one] using hdiv
  have := Nat.dvd_one.mp hd1
  omega

end RHTower
