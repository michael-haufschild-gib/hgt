import GaloisForLFunctions.HTGeometry.NevanlinnaControlSurjective
import GaloisForLFunctions.HTGeometry.CenteredJetOffsetGenericity

/-!
# Genericity of full expanded rank for the Nevanlinna packet family

Closing the genericity chain.  The Nevanlinna jet control map is surjective at distinct noncritical
upper packet nodes, the packet jet index matches the matrix coordinates by a constructed bijection,
and a constant centering offset is absorbed.

So the bounded densities whose Nevanlinna packet jets give the expanded evaluation matrix full
column rank are open, dense and residual.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **Full expanded rank is generic among bounded densities for the Nevanlinna packet family.**
No transversality, differentiability, reachability or Baire hypothesis appears: the analytic input
is surjectivity of the jet control map, which holds at distinct noncritical upper packet nodes over
a projective pushforward of a finite measure of infinite support. -/
theorem exists_nodes_residual_expandedMatrix_nevanlinnaPacket
    {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (deg : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i : ι, Fin (orders i))) →₀ ℕ))
    (hexp : Function.Injective exponent)
    (offset :
      ((κ × Fin (deg + 1)) × Fin (Fintype.card (Σ i : ι, Fin (orders i)))) → ℂ)
    (am qf : ℂ → ℂ)
    {ν : Measure ℝ} [IsFiniteMeasure ν] (hsupp : ν.support.Infinite)
    (zz : (κ × Fin (deg + 1)) × ι → ℂ)
    (hz : zz ∈ nevanlinnaUpperPacketSet qf)
    (hx : Function.Injective fun p => qf (zz p))
    (ha : ∀ p, am (zz p) ≠ 0) (hq : ∀ p, deriv qf (zz p) ≠ 0) :
    ∃ z : κ × Fin (deg + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : Lp ℝ ⊤ (ν.map (OnePoint.some)) | Function.Injective
        (expandedDifferentialEvaluationMatrix deg
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (offset + funLeftCLM (packetJetIndexEquiv (row := κ × Fin (deg + 1)) orders)
            (projectiveNevanlinnaJetExpansionSmoothControl am qf
              (fun p : (κ × Fin (deg + 1)) × ι => orders p.2)
              (ν.map (OnePoint.some)) zz u))).mulVec} ∧
      Dense {u : Lp ℝ ⊤ (ν.map (OnePoint.some)) | Function.Injective
        (expandedDifferentialEvaluationMatrix deg
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (offset + funLeftCLM (packetJetIndexEquiv (row := κ × Fin (deg + 1)) orders)
            (projectiveNevanlinnaJetExpansionSmoothControl am qf
              (fun p : (κ × Fin (deg + 1)) × ι => orders p.2)
              (ν.map (OnePoint.some)) zz u))).mulVec} ∧
      {u : Lp ℝ ⊤ (ν.map (OnePoint.some)) | Function.Injective
        (expandedDifferentialEvaluationMatrix deg
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (offset + funLeftCLM (packetJetIndexEquiv (row := κ × Fin (deg + 1)) orders)
            (projectiveNevanlinnaJetExpansionSmoothControl am qf
              (fun p : (κ × Fin (deg + 1)) × ι => orders p.2)
              (ν.map (OnePoint.some)) zz u))).mulVec}
        ∈ residual (Lp ℝ ⊤ (ν.map (OnePoint.some))) := by
  classical
  haveI : IsFiniteMeasure (ν.map (OnePoint.some)) :=
    Measure.isFiniteMeasure_map ν (OnePoint.some)
  exact exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset deg
    (Fintype.card (Σ i : ι, Fin (orders i))) exponent hexp offset
    (projectiveNevanlinnaJetExpansionSmoothControl am qf
      (fun p : (κ × Fin (deg + 1)) × ι => orders p.2) (ν.map (OnePoint.some)) zz)
    (surjective_projectiveNevanlinnaJetExpansionSmoothControl hsupp am qf
      (fun p : (κ × Fin (deg + 1)) × ι => orders p.2) zz hz hx ha hq)
    (packetJetIndexEquiv (row := κ × Fin (deg + 1)) orders)

end

end GaloisForLFunctions.HTGeometry
