import GaloisForLFunctions.RHTower.XiHurwitzAnchorZeroGraph
import GaloisForLFunctions.Hurwitz.AnchorGraphContact
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# Xi multiplicity is the contact order of the actual Hurwitz zero graph

The smooth joint Hurwitz divisor does not erase the multiplicity of the
anchor slice. Its analytic graph meets `a = 1` with exactly the Xi order.
-/

open Complex Filter Metric Set HurwitzZetaContinuation
open scoped Topology

namespace RHTower

/-- Exact source graph and contact law, with no simplicity assumption on the Xi zero. -/
theorem exists_analytic_hurwitz_zero_graph_with_contact_order
    {rho : ℂ} (hzero : xi rho = 0) :
    ∃ A : ℂ → ℂ, A rho = 1 ∧ AnalyticAt ℂ A rho ∧
      (∀ᶠ p : ℂ × ℂ in 𝓝 (rho, 1), continuedHzeta p.1 p.2 = 0 ↔ p.2 = A p.1) ∧
      (∀ᶠ s in 𝓝 rho, analyticOrderAt (continuedHzeta s) (A s) = 1) ∧
      analyticOrderAt (fun s => A s - 1) rho = analyticOrderAt riemannZeta rho ∧
      analyticOrderAt (fun s => A s - 1) rho = analyticOrderAt xi rho := by
  obtain ⟨A, hA, hAa, hgraph, horder⟩ := exists_analytic_hurwitz_zero_graph hzero
  have hrho := xi_zero_re_pos hzero
  have hrho1 : rho ≠ 1 := by
    intro h
    have := xi_zero_re_lt_one hzero
    simp [h] at this
  have hlim : Tendsto (fun s => (s, A s)) (𝓝 rho) (𝓝 (rho, 1)) := by
    simpa only [hA, id_eq] using (continuousAt_id.prodMk hAa.continuousAt).tendsto
  have hzgraph : ∀ᶠ s in 𝓝 rho, continuedHzeta s (A s) = 0 := by
    filter_upwards [hlim.eventually hgraph] with s hs
    exact hs.mpr rfl
  have hc := analyticOrderAt_anchor_zero_graph_contact hrho hrho1 hA hAa hzgraph
  have hneg : (fun s => A s - 1) = -(fun s => 1 - A s) := by
    funext s
    simp
  have hc' : analyticOrderAt (fun s => A s - 1) rho = analyticOrderAt riemannZeta rho := by
    rw [hneg, analyticOrderAt_neg]
    exact hc
  refine ⟨A, hA, hAa, hgraph, horder, hc', hc'.trans ?_⟩
  exact (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
    ⟨hrho, xi_zero_re_lt_one hzero⟩).symm

end RHTower
