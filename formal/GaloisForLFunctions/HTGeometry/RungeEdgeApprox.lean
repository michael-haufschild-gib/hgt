import GaloisForLFunctions.HTGeometry.RungeApproxClass
import GaloisForLFunctions.HTGeometry.RungeEdgeRiemann

/-!
# Edge integrals are approximable by the differentially algebraic class

Each Cauchy kernel appearing in the Riemann sum of an edge integral has its pole on the edge.  If
every such pole can be pushed — either to a point outside `Ω`, or to infinity — then the whole edge
integral is uniformly approximable on a compact set by functions analytic and differentially
algebraic on `Ω`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

variable {Ω K : Set ℂ}

/-- A pole absorbed by a nearby point outside `Ω`. -/
theorem approxOn_cauchyKernel_of_nearOutside (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hΩne : Ω.Nonempty) (hΩinf : Ω.Infinite) {w b : ℂ} (hb : b ∉ Ω) {r d : ℝ}
    (hr0 : 0 ≤ r) (hrd : r < d) (hwb : ‖w - b‖ ≤ r) (hK : ∀ z ∈ K, d ≤ ‖z - b‖) :
    ApproxOn K (RungeDA Ω) (fun z => (z - w)⁻¹) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_polePush_small (K := K) hr0 hrd hwb hK hε
  exact ⟨fun z => polePushSum w b N z, rungeDA_polePushSum hΩo hΩc hΩne hΩinf hb N, hN⟩

/-- A far pole absorbed by a polynomial. -/
theorem approxOn_cauchyKernel_of_far {w : ℂ} {R : ℝ} (hR : 0 < R)
    (hK : ∀ z ∈ K, ‖z‖ ≤ R) (hw : 2 * R ≤ ‖w‖) :
    ApproxOn K (RungeDA Ω) (fun z => (z - w)⁻¹) := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_infPush_small (K := K) hR hK hw hε
  exact ⟨fun z => infPushSum w N z, rungeDA_infPushSum N, hN⟩

/-- **Edge integrals are approximable.** -/
theorem approxOn_edgeCauchyIntegral (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hΩne : Ω.Nonempty) (hΩinf : Ω.Infinite) (hKc : IsCompact K)
    {F : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hFc : ContinuousOn F (γ '' Icc a b))
    (hne : ∀ x ∈ Icc a b, ∀ z ∈ K, γ x ≠ z)
    (hpole : ∀ x ∈ Icc a b, ApproxOn K (RungeDA Ω) (fun z => (z - γ x)⁻¹)) :
    ApproxOn K (RungeDA Ω) (fun z => edgeCauchyIntegral F γ a b z) := by
  classical
  refine approxOn_of_approxOn ?_
  intro ε hε
  obtain ⟨N, hNpos, hN⟩ := exists_edgeCauchyRiemann_approx hab hKc hγ hFc hne hε
  refine ⟨fun z => edgeCauchyRiemann F γ a b N z, ?_, hN⟩
  have hterm : ∀ i ∈ Finset.range N,
      ApproxOn K (RungeDA Ω)
        (fun z => (((b - a) / N : ℝ)) • (F (γ (uniformNode a b N i)) *
          (γ (uniformNode a b N i) - z)⁻¹)) := by
    intro i hi
    have hnode : uniformNode a b N i ∈ Icc a b :=
      uniformNode_mem_Icc hab hNpos (le_of_lt (Finset.mem_range.1 hi))
    have hbase := hpole _ hnode
    have hfun : (fun z => (((b - a) / N : ℝ)) • (F (γ (uniformNode a b N i)) *
        (γ (uniformNode a b N i) - z)⁻¹))
        = fun z => (-(((b - a) / N : ℝ) : ℂ) * F (γ (uniformNode a b N i))) *
            (z - γ (uniformNode a b N i))⁻¹ := by
      funext z
      have hinv : (γ (uniformNode a b N i) - z)⁻¹ = -((z - γ (uniformNode a b N i))⁻¹) := by
        rw [show γ (uniformNode a b N i) - z = -(z - γ (uniformNode a b N i)) by ring, inv_neg]
      rw [hinv, Complex.real_smul]
      ring
    rw [hfun]
    exact approxOn_smul (rungeDA_smul hΩo hΩc hΩne hΩinf) _ hbase
  have hsum := approxOn_finsetSum (K := K) (C := RungeDA Ω) rungeDA_zero
    (rungeDA_add hΩo hΩc hΩne hΩinf) (Finset.range N) hterm
  have hfun : (fun z => edgeCauchyRiemann F γ a b N z)
      = fun z => ∑ i ∈ Finset.range N, (((b - a) / N : ℝ)) • (F (γ (uniformNode a b N i)) *
          (γ (uniformNode a b N i) - z)⁻¹) := by
    funext z
    rfl
  rw [hfun]
  exact hsum

end

end GaloisForLFunctions.HTGeometry
