import GaloisForLFunctions.HTGeometry.AnalyticBallZeroSet
import Mathlib.Analysis.Meromorphic.FactorizedRational

/-!
# Extracting the zeros of an analytic function on a ball

An analytic function on a ball that is nonzero somewhere factors as a polynomial carrying its zeros
times a zero-free analytic function.  Mathlib's `MeromorphicOn.extract_zeros_poles` supplies the
factorisation up to equality on a codiscrete subset; on a ball, where both sides are analytic, the
identity theorem upgrades that to equality everywhere.

The upgrade needs only that the codiscrete filter of a nonempty ball is not the bottom filter, which
is the statement that a point of `ℂ` is not isolated.
-/

namespace HTGeometry

open Metric Filter Topology

/-- The order of a somewhere-nonzero analytic function on a ball is finite at every point. -/
theorem meromorphicOrderAt_ne_top_of_analytic_ball {f : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball c R)) (hz₀ : z₀ ∈ ball c R) (hfz₀ : f z₀ ≠ 0) :
    ∀ u : ball c R, meromorphicOrderAt f (u : ℂ) ≠ ⊤ := by
  rintro ⟨u, hu⟩
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf u hu).meromorphicAt).mpr
    (eventually_ne_zero_of_analyticOnNhd_ball hf hz₀ hfz₀ hu)

/-- The codiscrete filter of a nonempty ball is not the bottom filter. -/
theorem codiscreteWithin_ball_ne_bot {c z₀ : ℂ} {R : ℝ} (hz₀ : z₀ ∈ ball c R) :
    codiscreteWithin (ball c R) ≠ ⊥ := by
  intro hbot
  have hmem : (∅ : Set ℂ) ∈ codiscreteWithin (ball c R) := by
    rw [hbot]
    exact Filter.mem_bot
  rw [mem_codiscreteWithin] at hmem
  have hd := hmem z₀ hz₀
  rw [Set.sdiff_empty] at hd
  have hle : (𝓝[≠] z₀ : Filter ℂ) ≤ Filter.principal (ball c R) :=
    le_trans nhdsWithin_le_nhds (Filter.le_principal_iff.mpr (isOpen_ball.mem_nhds hz₀))
  exact (inferInstance : (𝓝[≠] z₀ : Filter ℂ).NeBot).ne (hd.eq_bot_of_le hle)

/-- **Identity theorem, codiscrete form.**  Two analytic functions on a ball agreeing on a
codiscrete subset agree everywhere on the ball. -/
theorem eqOn_of_codiscreteWithin_ball {F G : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hF : AnalyticOnNhd ℂ F (ball c R)) (hG : AnalyticOnNhd ℂ G (ball c R))
    (hz₀ : z₀ ∈ ball c R) (h : F =ᶠ[codiscreteWithin (ball c R)] G) :
    Set.EqOn F G (ball c R) := by
  rcases hF.eqOn_or_eventually_ne_of_preconnected hG isPreconnected_ball with heq | hne
  · exact heq
  · exact absurd (Filter.eventually_false_iff_eq_bot.mp
      ((h.and hne).mono fun x hx => hx.2 hx.1)) (codiscreteWithin_ball_ne_bot hz₀)

/-- The divisor of an analytic function is nonnegative. -/
theorem divisor_nonneg_of_analytic_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball c R)) (z : ℂ) :
    0 ≤ MeromorphicOn.divisor f (ball c R) z := by
  have h := hf.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mpr hf
  exact h z

/-- **Extraction of the zeros.**  An analytic function on a closed ball, nonzero somewhere on the
open ball, is the factorised rational function of its divisor times a zero-free analytic factor. -/
theorem exists_zeroFree_factor {f : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hz₀ : z₀ ∈ ball c R) (hfz₀ : f z₀ ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball c R) ∧ (∀ z ∈ ball c R, g z ≠ 0) ∧
      Set.EqOn f
        (fun z => (∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f (ball c R) u)) * g z)
        (ball c R) := by
  have hfb : AnalyticOnNhd ℂ f (ball c R) := fun z hz => hf z (ball_subset_closedBall hz)
  have hord := meromorphicOrderAt_ne_top_of_analytic_ball hfb hz₀ hfz₀
  have hfin : (MeromorphicOn.divisor f (ball c R)).support.Finite :=
    hf.meromorphicOn.divisor_ball_support_finite
  obtain ⟨g, hg, hgne, heq⟩ := hfb.meromorphicOn.extract_zeros_poles hord hfin
  refine ⟨g, hg, fun z hz => hgne ⟨z, hz⟩, ?_⟩
  have hfun : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f (ball c R) u))
      = fun x : ℂ => ∏ᶠ u, (x - u) ^ (MeromorphicOn.divisor f (ball c R) u) :=
    Function.FactorizedRational.finprod_eq_fun hfin
  have hPanalytic : AnalyticOnNhd ℂ
      (fun z : ℂ => ∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f (ball c R) u)) (ball c R) := by
    intro z hz
    have hA := Function.FactorizedRational.analyticAt
      (d := fun u => MeromorphicOn.divisor f (ball c R) u) (x := z)
      (divisor_nonneg_of_analytic_ball hfb z)
    rwa [hfun] at hA
  have hRHS : AnalyticOnNhd ℂ
      (fun z : ℂ => (∏ᶠ u, (z - u) ^ (MeromorphicOn.divisor f (ball c R) u)) * g z)
      (ball c R) := fun z hz => (hPanalytic z hz).mul (hg z hz)
  refine eqOn_of_codiscreteWithin_ball hfb hRHS hz₀ ?_
  filter_upwards [heq] with z hz
  simp only [Pi.smul_apply', smul_eq_mul] at hz
  rw [congrFun hfun z] at hz
  exact hz

end HTGeometry
