import GaloisForLFunctions.RHTower.AnalyticDominatedL2Sections
import GaloisForLFunctions.HTGeometry.L2CauchyHolomorphy
import GaloisForLFunctions.HTGeometry.LinearJet
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Order

/-!
# Actual derivatives of locally dominated L² sections

Cauchy estimates keep the pointwise derivative family locally dominated in
the same measure. Iterating this fact identifies every Hilbert-valued jet
with the L² class of the actual pointwise jet.
-/

open MeasureTheory Set Metric Filter Topology

namespace RHTower.DominatedL2Sections

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Cauchy estimates provide the derivative family in the same L² carrier. -/
def Family.derivativeFamily (F : Family μ) : Family μ where
  domain := F.domain
  isOpen_domain := F.isOpen_domain
  value z a := deriv (fun w => F.value w a) z
  measurable z hz := by
    obtain ⟨R, hR, hsub, B, hB, hbound⟩ := F.local_bound z hz
    exact aestronglyMeasurable_deriv_param_complex hR
      (fun w hw => F.measurable w (hsub hw))
      (fun a => (F.holomorphic a).differentiableAt (F.isOpen_domain.mem_nhds hz))
  holomorphic a := (F.holomorphic a).deriv F.isOpen_domain
  local_bound z hz := by
    obtain ⟨R, hR, hsub, B, hB, hbound⟩ := F.local_bound z hz
    refine ⟨R / 2, by positivity,
      (ball_subset_ball (by linarith : R / 2 ≤ R)).trans hsub,
      (fun a => (2 / R) * B a), hB.const_mul (2 / R), ?_⟩
    intro a w hw
    have h := Bottcher.norm_deriv_le_of_bounded_on_ball hR
      ((F.holomorphic a).mono hsub) (hbound a) w hw
    convert h using 1
    ring

theorem Family.section_eq_l2Family (F : Family μ) {z : ℂ} (hz : z ∈ F.domain) :
    F.section z = l2Family μ F.value z := by
  rw [l2Family_eq_toLp μ F.value z (F.memLp hz)]
  simp only [Family.section, dif_pos hz]

/-- Differentiation commutes with passage to the actual L² quotient. -/
theorem Family.hasDerivAt_section (F : Family μ) {z : ℂ} (hz : z ∈ F.domain) :
    HasDerivAt F.section (F.derivativeFamily.section z) z := by
  obtain ⟨R, hR, hsub, B, hB, hbound⟩ := F.local_bound z hz
  have h : HasDerivAt (l2Family μ F.value)
      (l2Family μ F.derivativeFamily.value z) z :=
    hasDerivAt_l2Family_of_cauchy_dominated μ F.value z R hR B hB
      (fun w hw => F.measurable w (hsub hw))
      (fun a => (F.holomorphic a).mono hsub) hbound
  rw [← F.derivativeFamily.section_eq_l2Family hz] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [F.isOpen_domain.mem_nhds hz] with w hw
  exact F.section_eq_l2Family hw

theorem Family.differentiableOn_section (F : Family μ) :
    DifferentiableOn ℂ F.section F.domain :=
  fun _ hz => (F.hasDerivAt_section hz).differentiableAt.differentiableWithinAt

theorem Family.analytic_section (F : Family μ) :
    AnalyticOnNhd ℂ F.section F.domain :=
  F.differentiableOn_section.analyticOnNhd F.isOpen_domain

/-- The locally dominated family of actual pointwise jets of order `n`. -/
def Family.jetFamily (F : Family μ) : ℕ → Family μ
  | 0 => F
  | n + 1 => (F.jetFamily n).derivativeFamily

theorem Family.jetFamily_domain (F : Family μ) (n : ℕ) :
    (F.jetFamily n).domain = F.domain := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem Family.jetFamily_value (F : Family μ) (n : ℕ) (z : ℂ) (a : α) :
    (F.jetFamily n).value z a = iteratedDeriv n (fun w => F.value w a) z := by
  induction n generalizing z a with
  | zero => rfl
  | succ n ih =>
    change deriv (fun w => (F.jetFamily n).value w a) z =
      iteratedDeriv (n + 1) (fun w => F.value w a) z
    rw [iteratedDeriv_succ]
    congr 1
    funext w
    exact ih w a

/-- Every genuine Hilbert jet is represented by the corresponding pointwise jet family. -/
theorem Family.iteratedDeriv_section (F : Family μ) (n : ℕ) :
    EqOn (iteratedDeriv n F.section) (fun z => (F.jetFamily n).section z) F.domain := by
  induction n with
  | zero => intro z _; rfl
  | succ n ih =>
    intro z hz
    have he : iteratedDeriv n F.section =ᶠ[𝓝 z] fun w => (F.jetFamily n).section w :=
      Filter.eventuallyEq_of_mem (F.isOpen_domain.mem_nhds hz) ih
    have hj : z ∈ (F.jetFamily n).domain := by rw [F.jetFamily_domain n]; exact hz
    rw [iteratedDeriv_succ, he.deriv_eq, ((F.jetFamily n).hasDerivAt_section hj).deriv]
    rfl

theorem Family.memLp_iteratedDeriv (F : Family μ) (n : ℕ) {z : ℂ} (hz : z ∈ F.domain) :
    MemLp (fun a => iteratedDeriv n (fun w => F.value w a) z) 2 μ := by
  have hj : z ∈ (F.jetFamily n).domain := by rw [F.jetFamily_domain n]; exact hz
  have he : (F.jetFamily n).value z =
      (fun a => iteratedDeriv n (fun w => F.value w a) z) := by
    funext a
    exact F.jetFamily_value n z a
  rw [← he]
  exact (F.jetFamily n).memLp hj

/-- This identifies representatives, rather than defining the generators as abstract orbit jets. -/
theorem Family.coe_iteratedDeriv_section (F : Family μ) (n : ℕ) {z : ℂ}
    (hz : z ∈ F.domain) :
    ((iteratedDeriv n F.section z : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
      (fun a => iteratedDeriv n (fun w => F.value w a) z) := by
  rw [F.iteratedDeriv_section n hz]
  have hj : z ∈ (F.jetFamily n).domain := by rw [F.jetFamily_domain n]; exact hz
  filter_upwards [(F.jetFamily n).section_coe hj] with a ha
  exact ha.trans (F.jetFamily_value n z a)

/-- Connected holomorphic sections lie in the closed span of their genuine jets at any base point. -/
theorem Family.section_mem_closed_span_jets (F : Family μ)
    (hconn : IsPreconnected F.domain) {z₀ z : ℂ}
    (hz₀ : z₀ ∈ F.domain) (hz : z ∈ F.domain) :
    F.section z ∈ (Submodule.span ℂ
      (range fun n : ℕ => iteratedDeriv n F.section z₀)).topologicalClosure := by
  rw [RHTower.mem_topologicalClosure_span_iff_forall_dual]
  intro L hL
  let g : ℂ → ℂ := fun w => L (F.section w)
  have hg : AnalyticOnNhd ℂ g F.domain := by
    apply DifferentiableOn.analyticOnNhd _ F.isOpen_domain
    intro w hw
    exact (L.hasFDerivAt.comp_hasDerivAt w
      (F.hasDerivAt_section hw)).differentiableAt.differentiableWithinAt
  have hzero : ∀ n : ℕ, iteratedDeriv n g z₀ = 0 := by
    intro n
    change iteratedDeriv n (fun w => L (F.section w)) z₀ = 0
    rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_clm_comp_eqOn
      F.isOpen_domain L F.differentiableOn_section n hz₀]
    exact hL n
  have horder : analyticOrderAt g z₀ = ⊤ := ENat.eq_top_iff_forall_ge.mpr (fun n =>
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hg z₀ hz₀)).mpr
      (fun i _ => hzero i))
  exact hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀
    (analyticOrderAt_eq_top.mp horder) hz

end

end RHTower.DominatedL2Sections
