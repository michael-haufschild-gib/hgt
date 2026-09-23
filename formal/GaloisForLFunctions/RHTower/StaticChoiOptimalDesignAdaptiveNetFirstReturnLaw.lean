import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignFirstReturnLaw

/-!
# Adaptive target classes from one finite projective net

An arbitrary target class, with no finiteness or measurable structure, is reduced to a finite
projective net.  Combining the triangle inequality with the intrinsic-rank optimal-design law
excludes first return to the complete target class.  Only the net's occupied replica span enters;
neither the cardinality nor measurability of the original class appears.
-/

open Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- **Adaptive-net intrinsic-rank first-return law.**  Every target in `C` is resolved by one member
of the finite net `W`.  A narrow hit on the original class would therefore be a wider hit on the
net, which the optimal-design spectral budget excludes. -/
theorem no_forward_adaptivePureChoiCircuitReturn_of_gaussianReplicaCrowdingNet
    {d : ℕ} (hd : 0 < d)
    {C W : Type*} [Fintype W] [Nonempty W] [DecidableEq W]
    {energy : Fin d → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (selectedTarget : C → EuclideanSpace ℂ (Fin d × Fin d))
    (hselectedTarget : ∀ c, ‖selectedTarget c‖ = 1)
    (netTarget : W → EuclideanSpace ℂ (Fin d × Fin d))
    (hnetTarget : ∀ w, ‖netTarget w‖ = 1)
    (netIndex : C → W)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hnet : ∀ c, pureStateTraceDistance
      (selectedTarget c) (netTarget (netIndex c)) ≤ eta)
    {r : ℕ} {T δ epsn epsw : ℝ}
    (hTpos : 0 < T) (hδ : 0 < δ)
    (hepsn : 0 ≤ epsn) (hgap : epsn + eta < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun w => (netTarget w).ofLp)) : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          (replicaActionCrowdingDegree energy r δ : ℝ) *
            ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r) +
          Real.exp (-((T * δ) ^ (2 : ℕ)) / 2)) <
        gaussianFloorTwo *
          ((epsw - (epsn + eta)) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ (2 : ℕ)) ^ r) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - (epsn + eta)) / staticChoiSpeed energy) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (selectedTarget c) ≤ epsn := by
  have hfinite := no_forward_pureChoiCircuitReturn_of_gaussianReplicaCrowding
    hd hmax netTarget hnetTarget hTpos hδ
    (add_nonneg hepsn heta) hgap hepswOne hT hbudget
  intro hhit
  apply hfinite
  obtain ⟨t, ht, c, hc⟩ := hhit
  refine ⟨t, ht, netIndex c, ?_⟩
  exact (pureStateTraceDistance_triangle
    (staticSpectralChoiVector d t energy)
    (selectedTarget c) (netTarget (netIndex c))
    (staticSpectralChoiVector_norm hd t energy)
    (hselectedTarget c) (hnetTarget (netIndex c))).trans
      (add_le_add hc (hnet c))

end RHTower
