import GaloisForLFunctions.HTGeometry.PolydiscWeierstrass
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Locally uniform limits in finite complex dimension

This file supplies the Weierstrass closure step needed in a multivariable Vitali argument.
For a sequence of functions on an open subset of `ℂ^n`, local uniform convergence and
holomorphy of every term imply holomorphy of the limit.

This is deliberately not a normal-family or full Vitali theorem: deriving a locally uniformly
convergent subsequence from local boundedness remains a separate proof obligation. The file does
identify any such limit from convergence on a nonempty open subset.
-/

open Filter Set
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A locally uniform limit of holomorphic `ℂ^n`-valued-domain functions is holomorphic.

At each point, local uniform convergence becomes uniform convergence on every compact closed ball
strictly inside a surrounding open ball. `differentiableOn_of_tendstoUniformlyOn` then supplies the
local Cauchy-integral argument. -/
theorem differentiableOn_of_tendstoLocallyUniformlyOn
    {F : ℕ → (Fin n → ℂ) → E} {g : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hconv : TendstoLocallyUniformlyOn F g atTop U) : DifferentiableOn ℂ g U := by
  intro z hz
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU z hz
  have hFball : ∀ k, DifferentiableOn ℂ (F k) (Metric.ball z R) := fun k =>
    (hF k).mono hball
  have hFcont : ∀ k, ContinuousOn (F k) (Metric.ball z R) := fun k =>
    (hFball k).continuousOn
  have hgcont : ContinuousOn g (Metric.ball z R) :=
    (hconv.continuousOn (Eventually.of_forall fun k => (hF k).continuousOn).frequently).mono hball
  have huni : ∀ ρ : ℝ, 0 ≤ ρ → ρ < R →
      TendstoUniformlyOn F g atTop (Metric.closedBall z ρ) := by
    intro ρ _ hρR
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv
      (Metric.closedBall z ρ) ((Metric.closedBall_subset_ball hρR).trans hball)
      (isCompact_closedBall z ρ)
  obtain ⟨g', hg'⟩ := (differentiableOn_of_tendstoUniformlyOn hR hFcont hFball hgcont huni) z
    (Metric.mem_ball_self hR)
  have hderivAt : DifferentiableAt ℂ g z :=
    (hg'.hasFDerivAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))).differentiableAt
  exact hderivAt.differentiableWithinAt

/-- The locally uniform limit theorem in analytic form. -/
theorem analyticOnNhd_of_tendstoLocallyUniformlyOn
    {F : ℕ → (Fin n → ℂ) → E} {g : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hconv : TendstoLocallyUniformlyOn F g atTop U) : AnalyticOnNhd ℂ g U :=
  fun z hz => analyticAt_of_differentiableOn (z := z) hU
    (differentiableOn_of_tendstoLocallyUniformlyOn hU hF hconv) hz

/-- A locally uniform subsequential limit is determined globally by convergence on a nonempty
open part of a preconnected domain.

This is the uniqueness half of the multivariable Vitali pattern. It does not produce a locally
uniformly convergent subsequence; that normal-family step requires independent compactness input. -/
theorem eqOn_of_tendstoLocallyUniformlyOn_of_tendstoOn_open
    {F : ℕ → (Fin n → ℂ) → E} {g h : (Fin n → ℂ) → E}
    {U V : Set (Fin n → ℂ)} (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hhconv : TendstoLocallyUniformlyOn F h atTop U) (hg : AnalyticOnNhd ℂ g U)
    (hVopen : IsOpen V) (hVU : V ⊆ U) (hVnonempty : V.Nonempty)
    (hpoint : ∀ z ∈ V, Tendsto (fun k => F k z) atTop (𝓝 (g z))) : EqOn h g U := by
  obtain ⟨z₀, hz₀⟩ := hVnonempty
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_of_tendstoLocallyUniformlyOn hU hF hhconv) hg hUconn (hVU hz₀) ?_
  filter_upwards [hVopen.mem_nhds hz₀] with z hz
  exact tendsto_nhds_unique (hhconv.tendsto_at (hVU hz)) (hpoint z hz)

end GaloisForLFunctions.HTGeometry
