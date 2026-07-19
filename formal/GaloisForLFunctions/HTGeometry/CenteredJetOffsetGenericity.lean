import GaloisForLFunctions.HTGeometry.PacketJetIndexGenericity

/-!
# Genericity with a centered jet offset

The packet values of the carrier are not the jets of the reweighting alone: each carries an additive
term coming from the centering function, constant in the density.

A constant offset of the jets changes nothing in the genericity argument.  The chart is still the
identity on the density space, and the displacement identity still holds exactly, because a constant
cancels in the difference.  So full expanded rank remains open, dense and residual, and the offset
is carried through the statement rather than assumed away.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- **Genericity with a constant jet offset.**  A constant additive term in the jets leaves the
genericity conclusion untouched: surjectivity of the jet map is still the only hypothesis. -/
theorem exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset
    {κ D J' : Type} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
    (q n : ℕ) (exponent : κ → (Fin n →₀ ℕ)) (hexp : Function.Injective exponent)
    (c : ((κ × Fin (q + 1)) × Fin n) → ℂ)
    (J : D →L[ℝ] (J' → ℂ)) (hJ : Function.Surjective J)
    (e : ((κ × Fin (q + 1)) × Fin n) ≃ J') :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : D | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (c + funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J') (J u))).mulVec} ∧
      Dense {u : D | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (c + funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J') (J u))).mulVec} ∧
      {u : D | Function.Injective
        (expandedDifferentialEvaluationMatrix q n z exponent
          (c + funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J') (J u))).mulVec}
        ∈ residual D := by
  classical
  set K : D →L[ℝ] (((κ × Fin (q + 1)) × Fin n) → ℂ) :=
    (funLeftCLM (e : ((κ × Fin (q + 1)) × Fin n) → J')).comp J with hK
  have hKsurj : Function.Surjective K := surjective_funLeftCLM_comp e J hJ
  refine exists_nodes_residual_expandedMatrix_mulVec_injective q n exponent hexp
    (fun u => c + K u) (continuous_const.add K.continuous) ?_
  intro u₀ ε hε
  refine ⟨ε, hε, K, hKsurj, ?_⟩
  intro h hh
  refine ⟨u₀ + h, ?_, ?_⟩
  · simpa [dist_eq_norm] using hh
  · show c + K (u₀ + h) = (c + K u₀) + K h
    rw [map_add, ← add_assoc]

/-- **Genericity for centered packet jets.**  The carrier's packet values are a constant centering
term plus the jets of a bounded reweighting; over a base measure of infinite support with a strictly
positive integrable density, the reweightings giving full expanded column rank are open, dense and
residual.  Neither the index bijection nor the centering term is assumed away. -/
theorem exists_nodes_residual_expandedMatrix_centeredPacketJets
    {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (q : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i : ι, Fin (orders i))) →₀ ℕ))
    (hexp : Function.Injective exponent)
    (c : ((κ × Fin (q + 1)) × Fin (Fintype.card (Σ i : ι, Fin (orders i)))) → ℂ)
    (μ : Measure ℝ) (hsupp : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (x : (κ × Fin (q + 1)) × ι → ℂ) (hx : Function.Injective x)
    (hupper : ∀ p, 0 < (x p).im) :
    ∃ z : κ × Fin (q + 1) → ℂ,
      Function.Injective z ∧
      IsOpen {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (c + funLeftCLM (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)
            (weightedJetControl μ w hw x (fun p => ne_of_gt (hupper p))
              (fun p : (κ × Fin (q + 1)) × ι => orders p.2) u))).mulVec} ∧
      Dense {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (c + funLeftCLM (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)
            (weightedJetControl μ w hw x (fun p => ne_of_gt (hupper p))
              (fun p : (κ × Fin (q + 1)) × ι => orders p.2) u))).mulVec} ∧
      {u : Lp ℝ ⊤ μ | Function.Injective
        (expandedDifferentialEvaluationMatrix q
          (Fintype.card (Σ i : ι, Fin (orders i))) z exponent
          (c + funLeftCLM (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)
            (weightedJetControl μ w hw x (fun p => ne_of_gt (hupper p))
              (fun p : (κ × Fin (q + 1)) × ι => orders p.2) u))).mulVec}
        ∈ residual (Lp ℝ ⊤ μ) :=
  exists_nodes_residual_expandedMatrix_of_surjective_jetMap_offset q
    (Fintype.card (Σ i : ι, Fin (orders i))) exponent hexp c
    (weightedJetControl μ w hw x (fun p => ne_of_gt (hupper p))
      (fun p : (κ × Fin (q + 1)) × ι => orders p.2))
    (surjective_weightedJetControl μ hsupp w hw hwpos x hx hupper
      (fun p : (κ × Fin (q + 1)) × ι => orders p.2))
    (packetJetIndexEquiv (row := κ × Fin (q + 1)) orders)

end

end GaloisForLFunctions.HTGeometry
