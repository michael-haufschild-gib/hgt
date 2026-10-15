import GaloisForLFunctions.Hurwitz.AnchorLevelGraph
import GaloisForLFunctions.RHTower.XiHurwitzAnchorTransversality

/-!
# Local Hurwitz zero graphs through every Xi zero

Every Xi zero gives an analytic graph of simple shift zeros of the actual
Hurwitz family. The Xi zero itself may have arbitrary multiplicity in the
exponent variable. This theorem does not assert RH or a zero-free strip.
-/

open Complex Filter Metric Set HurwitzZetaContinuation
open scoped Topology

namespace RHTower

/-- Every Xi zero lies on an analytic graph of transverse zeros of the actual Hurwitz source. -/
theorem exists_analytic_hurwitz_zero_graph {rho : ℂ} (hzero : xi rho = 0) :
    ∃ A : ℂ → ℂ, A rho = 1 ∧ AnalyticAt ℂ A rho ∧
      (∀ᶠ p : ℂ × ℂ in 𝓝 (rho, 1), continuedHzeta p.1 p.2 = 0 ↔ p.2 = A p.1) ∧
      ∀ᶠ s in 𝓝 rho, analyticOrderAt (continuedHzeta s) (A s) = 1 := by
  have hrho := xi_zero_re_pos hzero
  have hrho1 : rho ≠ 1 := by
    intro h
    have := xi_zero_re_lt_one hzero
    simp [h] at this
  have hzeta : riemannZeta rho = 0 := (xi_eq_zero_iff hrho hrho1).mp hzero
  obtain ⟨A, hA, hAa, hgraph⟩ := exists_analytic_anchor_level_graph hrho hrho1
  have hgraph0 : ∀ᶠ p : ℂ × ℂ in 𝓝 (rho, 1),
      continuedHzeta p.1 p.2 = 0 ↔ p.2 = A p.1 := by
    simpa only [hzeta] using hgraph
  refine ⟨A, hA, hAa, hgraph0, ?_⟩
  have hlim : Tendsto (fun s => (s, A s)) (𝓝 rho) (𝓝 (rho, 1)) := by
    simpa only [hA, id_eq] using (continuousAt_id.prodMk hAa.continuousAt).tendsto
  have hlimA : Tendsto A (𝓝 rho) (𝓝 (1 : ℂ)) := by
    simpa only [hA] using hAa.continuousAt.tendsto
  have hne := (continuousAt_deriv_continuedHzeta_shift_joint hrho hrho1
      (a := 1) (by norm_num)).eventually_ne
    (continuedHzeta_xiZero_deriv_at_one_ne_zero hrho)
  filter_upwards [hlim.eventually hgraph0, hlim.eventually hne,
    hlimA.eventually (ball_mem_nhds (1 : ℂ) (by norm_num : 0 < (1 / 2 : ℝ))),
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hrho,
    isOpen_ne.mem_nhds hrho1] with s hsgraph hsne hsa hspos hs1
  have ha : ‖A s - 1‖ < (1 / 2 : ℝ) := by
    simpa only [mem_ball, dist_eq_norm] using hsa
  exact (continuedHzeta_analyticAt_shift hspos hs1 ha).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (hsgraph.mpr rfl) hsne

end RHTower
