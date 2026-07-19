import GaloisForLFunctions.HTGeometry.WeightedJetControlFullRankGenericity

/-!
# The packet jet index, constructed rather than assumed

The genericity statement for reweightings matches jet coordinates to matrix coordinates through a
bijection.  For a row packet over a shift family that bijection is not an extra assumption: the
combined jet index of the packet is a sigma type over rows and shifts, which splits as rows times
the single-row jet index, and the latter is a finite type of the required cardinality.

Composing the split with the canonical enumeration of a finite type produces the bijection outright,
so the genericity conclusion for packet jets carries no index hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The packet jet index bijection: rows times flattened single-row jets, matched to the combined
jet index of the packet. -/
def packetJetIndexEquiv {ι row : Type*} [Fintype ι] (orders : ι → ℕ) :
    (row × Fin (Fintype.card (Σ i : ι, Fin (orders i)))) ≃
      jetIndex (fun p : row × ι => orders p.2) :=
  (Equiv.prodCongr (Equiv.refl row)
      (Fintype.equivFin (Σ i : ι, Fin (orders i))).symm).trans
    (jetIndexProdEquiv (row := row) orders).symm

/-- **Genericity of full expanded rank for packet jets.**  Over a base measure of infinite support
with a strictly positive integrable density, the bounded reweightings whose packet jets give the
expanded evaluation matrix full column rank are open, dense and residual.

The jet index bijection is constructed, so the only hypotheses are the measure ones and injectivity
of the exponent enumeration and of the combined nodes. -/
theorem exists_nodes_residual_expandedMatrix_packetJets
    {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i : ι, Fin (orders i))) →₀ ℕ))
    (hexp : Function.Injective exponent)
    (μ : Measure ℝ) (hsupp : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (x : (κ × Fin (q + 1)) × ι → ℂ) (hx : Function.Injective x)
    (hupper : ∀ p, 0 < (x p).im) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (funLeftCLM (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)
            (weightedJetControl μ w hw x (fun p => ne_of_gt (hupper p))
              (fun p : (κ × Fin (q + 1)) × ι => orders p.2) u))).mulVec} ∧
      Dense {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (funLeftCLM (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)
            (weightedJetControl μ w hw x (fun p => ne_of_gt (hupper p))
              (fun p : (κ × Fin (q + 1)) × ι => orders p.2) u))).mulVec} ∧
      {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (funLeftCLM (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)
            (weightedJetControl μ w hw x (fun p => ne_of_gt (hupper p))
              (fun p : (κ × Fin (q + 1)) × ι => orders p.2) u))).mulVec}
        ∈ residual (Lp ℝ ⊤ μ) :=
  exists_nodes_residual_expandedMatrix_weightedJetControl q
    (Fintype.card (Σ i : ι, Fin (orders i))) exponent hexp μ hsupp w hw hwpos x hx hupper
    (fun p : (κ × Fin (q + 1)) × ι => orders p.2)
    (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)

end

end GaloisForLFunctions.HTGeometry
