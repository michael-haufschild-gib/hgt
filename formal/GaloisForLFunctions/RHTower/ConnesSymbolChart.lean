import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Connes' symbol chart

Formalization of the smoothness claim of §V (28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

In the proof of Theorem V.3 (the local trace formula) Connes computes the symbol of the scaling
operator `U(h) = ∫ h(λ) U(λ) d*λ` and finds

  `σ(x,ξ) = ρ^{-1} ĝ(x ξ)`,   `g(λ) = h((λ+1)^{-1}) |λ+1|^{-1}`,

then remarks: *"Since `h` is smooth with compact support on `K^*` the function `g` belongs to
`C_c^∞(K)`."*  That remark is exactly what makes the Fourier tail estimate §V (32) available, and it
is proved here for `K = ℝ` without extra hypotheses.

The chart factors as `g = H ∘ (λ ↦ (λ+1)^{-1})` with `H(u) = h(u)|u|`; `H` is smooth because `h`
vanishes near `0`, and `g` is smooth at `λ = -1` because `H` has compact support and `(λ+1)^{-1}`
escapes every compact set there.

* `contDiff_connesSymbolChart` - `g ∈ C^∞(ℝ)`.
* `hasCompactSupport_connesSymbolChart` - `g` has compact support (in `closedBall (-1) c^{-1}`,
  where `c` is any inner radius avoiding `supp h`).
-/

namespace GaloisForLFunctions.RHTower
noncomputable section
open Function Set Metric

/-- **§V (28).**  Connes' symbol chart: the change of variable `λ ↦ λ - 1` that turns the scaling
symbol `h(λ⁻¹)` on `K^*` into a compactly supported smooth function on `K`. -/
def connesSymbolChart (h : ℝ → ℂ) (lam : ℝ) : ℂ := h ((lam + 1)⁻¹) * ((|lam + 1| : ℝ) : ℂ)⁻¹

/-- The auxiliary weight `H(u) = h(u)|u|`. -/
def connesChartWeight (h : ℝ → ℂ) (u : ℝ) : ℂ := h u * ((|u| : ℝ) : ℂ)

theorem connesSymbolChart_eq_comp (h : ℝ → ℂ) (lam : ℝ) :
    connesSymbolChart h lam = connesChartWeight h ((lam + 1)⁻¹) := by
  simp [connesSymbolChart, connesChartWeight, abs_inv]

section
variable {h : ℝ → ℂ}

/-- A smooth function whose support avoids the origin vanishes on a ball around the origin. -/
theorem exists_inner_radius (h0 : (0:ℝ) ∉ tsupport h) :
    ∃ c > 0, ∀ u : ℝ, |u| < c → h u = 0 := by
  have hopen : IsOpen (tsupport h)ᶜ := (isClosed_tsupport h).isOpen_compl
  obtain ⟨c, hc, hball⟩ := Metric.isOpen_iff.mp hopen 0 h0
  refine ⟨c, hc, fun u hu => ?_⟩
  refine image_eq_zero_of_notMem_tsupport (hball ?_)
  simpa [Real.dist_eq] using hu

/-- A compactly supported function vanishes outside a large ball. -/
theorem exists_outer_radius (hcs : HasCompactSupport h) :
    ∃ C > 0, ∀ u : ℝ, C < |u| → h u = 0 := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max R 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun u hu => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
  have := hR hmem
  rw [mem_closedBall, Real.dist_eq, sub_zero] at this
  exact absurd this (not_le.2 (lt_of_le_of_lt (le_max_left R 1) hu))

theorem contDiff_connesChartWeight (hh : ContDiff ℝ (⊤ : ℕ∞) h) (h0 : (0:ℝ) ∉ tsupport h) :
    ContDiff ℝ (⊤ : ℕ∞) (connesChartWeight h) := by
  obtain ⟨c, hc, hzero⟩ := exists_inner_radius h0
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases eq_or_ne u 0 with rfl | hu
  · refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0:ℂ))) ?_
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hc] with v hv
    have : |v| < c := by simpa [Real.dist_eq] using hv
    simp [connesChartWeight, hzero v this]
  · have habs : ContDiffAt ℝ (⊤ : ℕ∞) (fun v : ℝ => ((|v| : ℝ) : ℂ)) u := by
      have hofReal : ContDiff ℝ (⊤ : ℕ∞) (fun v : ℝ => ((v : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff
      rcases lt_or_gt_of_ne hu with hneg | hpos
      · refine ContDiffAt.congr_of_eventuallyEq
          (f := fun v : ℝ => ((-v : ℝ) : ℂ))
          ((hofReal.comp contDiff_neg).contDiffAt) ?_
        filter_upwards [Iio_mem_nhds hneg] with v hv
        rw [abs_of_neg hv]
      · refine ContDiffAt.congr_of_eventuallyEq
          (f := fun v : ℝ => ((v : ℝ) : ℂ)) hofReal.contDiffAt ?_
        filter_upwards [Ioi_mem_nhds hpos] with v hv
        rw [abs_of_pos hv]
    exact (hh.contDiffAt).mul habs

theorem connesChartWeight_eq_zero_of_lt (h0 : (0:ℝ) ∉ tsupport h) :
    ∃ c > 0, ∀ u : ℝ, |u| < c → connesChartWeight h u = 0 := by
  obtain ⟨c, hc, hzero⟩ := exists_inner_radius h0
  exact ⟨c, hc, fun u hu => by simp [connesChartWeight, hzero u hu]⟩

theorem connesChartWeight_eq_zero_of_gt (hcs : HasCompactSupport h) :
    ∃ C > 0, ∀ u : ℝ, C < |u| → connesChartWeight h u = 0 := by
  obtain ⟨C, hC, hzero⟩ := exists_outer_radius hcs
  exact ⟨C, hC, fun u hu => by simp [connesChartWeight, hzero u hu]⟩

/-- **§V (28), smoothness.**  If `h` is smooth with compact support inside `K^* = ℝ ∖ {0}`, then
the chart `g(λ) = h((λ+1)⁻¹)|λ+1|⁻¹` is smooth on all of `K = ℝ`. -/
theorem contDiff_connesSymbolChart (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hcs : HasCompactSupport h) (h0 : (0:ℝ) ∉ tsupport h) :
    ContDiff ℝ (⊤ : ℕ∞) (connesSymbolChart h) := by
  obtain ⟨C, hC, hout⟩ := connesChartWeight_eq_zero_of_gt hcs
  have hW := contDiff_connesChartWeight hh h0
  rw [contDiff_iff_contDiffAt]
  intro lam
  rcases eq_or_ne (lam + 1) 0 with hlam | hlam
  · have hlam' : lam = -1 := by linarith [hlam]
    subst hlam'
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0:ℂ))) ?_
    filter_upwards [Metric.ball_mem_nhds (-1 : ℝ) (inv_pos.mpr hC)] with v hv
    have hv' : |v + 1| < C⁻¹ := by
      have : |v - (-1)| < C⁻¹ := by simpa [Real.dist_eq] using hv
      simpa [sub_neg_eq_add] using this
    rw [connesSymbolChart_eq_comp]
    rcases eq_or_ne (v + 1) 0 with h1 | h1
    · obtain ⟨c, hc, hin⟩ := connesChartWeight_eq_zero_of_lt h0
      rw [h1]; simpa using hin 0 (by simpa using hc)
    · refine hout _ ?_
      rw [abs_inv]
      rw [lt_inv_comm₀ hC (abs_pos.mpr h1)]
      exact hv'
  · have hchart : connesSymbolChart h = connesChartWeight h ∘ (fun v : ℝ => (v + 1)⁻¹) := by
      funext v; exact connesSymbolChart_eq_comp h v
    rw [hchart]
    refine ContDiffAt.comp _ (hW.contDiffAt) ?_
    exact ContDiffAt.inv (by fun_prop) hlam

/-- **§V (28), compact support.**  The chart has compact support. -/
theorem hasCompactSupport_connesSymbolChart (h0 : (0:ℝ) ∉ tsupport h) :
    HasCompactSupport (connesSymbolChart h) := by
  obtain ⟨c, hc, hin⟩ := connesChartWeight_eq_zero_of_lt h0
  refine HasCompactSupport.intro (K := Metric.closedBall (-1 : ℝ) c⁻¹) (isCompact_closedBall _ _) ?_
  intro lam hlam
  have hdist : c⁻¹ < |lam + 1| := by
    have : ¬ (|lam - (-1)| ≤ c⁻¹) := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hlam
    have h' : c⁻¹ < |lam - (-1)| := not_le.mp this
    simpa [sub_neg_eq_add] using h'
  have hne : lam + 1 ≠ 0 := by
    intro h1
    rw [h1, abs_zero] at hdist
    exact absurd hdist (not_lt.2 (le_of_lt (inv_pos.mpr hc)))
  rw [connesSymbolChart_eq_comp]
  refine hin _ ?_
  rw [abs_inv, inv_lt_comm₀ (abs_pos.mpr hne) hc]
  exact hdist

end
end
end GaloisForLFunctions.RHTower
