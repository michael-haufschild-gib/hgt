import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingMetric
import GaloisForLFunctions.HTGeometry.DifferentialVariationalOreModule

/-!
# Isometry of the projective interleaving metric

Completed-skew linear equivalences and differential coefficient automorphisms preserve the least
orbit-interleaving radius.  Therefore every literal semilinear projective action, including the
canonical action built from the variational Ore module in any finite basis, is an isometry of the
projective interleaving metric.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DiffOp

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Completed-skew linear transport preserves orbit interleaving exactly. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_leftOrbitInterleavedAt_iff
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    (mapCompletedPseudoDiffOpLatticeLinear e L).LeftOrbitInterleavedAt n
        (mapCompletedPseudoDiffOpLatticeLinear e M) ↔
      L.LeftOrbitInterleavedAt n M := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← mapCompletedPseudoDiffOpLatticeLinear_leftScale] at ha
    exact (mapCompletedPseudoDiffOpLatticeLinear_interleavedAt_iff e L
      (leftScaleCompletedPseudoDiffOpLattice a M) n).1 ha
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [← mapCompletedPseudoDiffOpLatticeLinear_leftScale]
    exact (mapCompletedPseudoDiffOpLatticeLinear_interleavedAt_iff e L
      (leftScaleCompletedPseudoDiffOpLattice a M) n).2 ha

/-- Completed-skew linear transport preserves orbit-interleaving distance. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_mapLinear
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance
        (mapCompletedPseudoDiffOpLatticeLinear e L)
        (mapCompletedPseudoDiffOpLatticeLinear e M) =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff,
      mapCompletedPseudoDiffOpLatticeLinear_leftOrbitInterleavedAt_iff]
    exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M
  · rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
    exact (mapCompletedPseudoDiffOpLatticeLinear_leftOrbitInterleavedAt_iff e L M _).1
      (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec
        (mapCompletedPseudoDiffOpLatticeLinear e L)
        (mapCompletedPseudoDiffOpLatticeLinear e M))

/-- The induced projective action of a completed-skew linear equivalence is an isometry. -/
theorem differentialVariationalProjectiveInterleavingDistance_mapLinear
    (e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (ι → CompletedPseudoDiffOp K))
    (x y : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveInterleavingDistance
        (mapDifferentialVariationalProjectiveBuildingCarrier e x)
        (mapDifferentialVariationalProjectiveBuildingCarrier e y) =
      differentialVariationalProjectiveInterleavingDistance x y := by
  induction x using Quotient.inductionOn with
  | _ L =>
      induction y using Quotient.inductionOn with
      | _ M => exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_mapLinear e L M

omit [Fintype ι] in
/-- Differential coefficient transport carries orbit interleaving forward. -/
theorem mapCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    {L M : CompletedPseudoDiffOpLattice K ι} {n : ℕ}
    (h : L.LeftOrbitInterleavedAt n M) :
    (mapCompletedPseudoDiffOpLattice σ hσ L).LeftOrbitInterleavedAt n
      (mapCompletedPseudoDiffOpLattice σ hσ M) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨mapCompletedPseudoDiffOpUnit σ hσ a, ?_⟩
  rw [← mapCompletedPseudoDiffOpLattice_leftScale]
  exact (mapCompletedPseudoDiffOpLattice_interleavedAt_iff σ hσ L
    (leftScaleCompletedPseudoDiffOpLattice a M) n).2 ha

/-- Differential coefficient transport cannot increase orbit-interleaving distance. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_mapCoefficients_le
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M) ≤
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M := by
  rw [completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff]
  exact mapCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt σ hσ
    (completedPseudoDiffOpLatticeOrbitInterleavingDistance_spec L M)

/-- Differential coefficient transport preserves orbit-interleaving distance exactly. -/
theorem completedPseudoDiffOpLatticeOrbitInterleavingDistance_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeOrbitInterleavingDistance
        (mapCompletedPseudoDiffOpLattice σ hσ L)
        (mapCompletedPseudoDiffOpLattice σ hσ M) =
      completedPseudoDiffOpLatticeOrbitInterleavingDistance L M := by
  apply le_antisymm
  · exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_mapCoefficients_le
      σ hσ L M
  · let hσinv := symm_deriv_comm hσ
    have hle := completedPseudoDiffOpLatticeOrbitInterleavingDistance_mapCoefficients_le
      σ.symm hσinv
      (mapCompletedPseudoDiffOpLattice σ hσ L)
      (mapCompletedPseudoDiffOpLattice σ hσ M)
    have hcancel (P : CompletedPseudoDiffOpLattice K ι) :
        mapCompletedPseudoDiffOpLattice σ.symm hσinv
          (mapCompletedPseudoDiffOpLattice σ hσ P) = P := by
      calc
        mapCompletedPseudoDiffOpLattice σ.symm hσinv
            (mapCompletedPseudoDiffOpLattice σ hσ P) =
          mapCompletedPseudoDiffOpLattice (σ.trans σ.symm)
            (trans_deriv_comm σ σ.symm hσ hσinv) P :=
          mapCompletedPseudoDiffOpLattice_trans σ σ.symm hσ hσinv P
        _ = mapCompletedPseudoDiffOpLattice (RingEquiv.refl K)
            refl_deriv_comm P := by
          congr 2
          exact RingEquiv.self_trans_symm σ
        _ = P := mapCompletedPseudoDiffOpLattice_refl P
    simpa only [hcancel] using hle

/-- The induced projective coefficient action is an isometry. -/
theorem differentialVariationalProjectiveInterleavingDistance_mapCoefficients
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    (x y : DifferentialVariationalProjectiveBuildingCarrier K ι) :
    differentialVariationalProjectiveInterleavingDistance
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ x)
        (mapDifferentialVariationalProjectiveBuildingCarrierCoefficients σ hσ y) =
      differentialVariationalProjectiveInterleavingDistance x y := by
  induction x using Quotient.inductionOn with
  | _ L =>
      induction y using Quotient.inductionOn with
      | _ M =>
          exact completedPseudoDiffOpLatticeOrbitInterleavingDistance_mapCoefficients σ hσ L M

/-- Every literal semilinear projective action is a projective-interleaving isometry. -/
theorem differentialVariationalProjectiveInterleavingDistance_semilinearAction
    (σ : K ≃+* K) (hσ : ∀ a : K, σ (a′) = (σ a)′)
    {r : ℕ} (A : (Matrix (Fin r) (Fin r) (CompletedPseudoDiffOp K))ˣ)
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveInterleavingDistance
        (differentialVariationalProjectiveSemilinearAction σ hσ A x)
        (differentialVariationalProjectiveSemilinearAction σ hσ A y) =
      differentialVariationalProjectiveInterleavingDistance x y := by
  simp only [differentialVariationalProjectiveSemilinearAction,
    mapDifferentialVariationalProjectiveBuildingCarrierMatrix]
  rw [differentialVariationalProjectiveInterleavingDistance_mapLinear,
    differentialVariationalProjectiveInterleavingDistance_mapCoefficients]

end DiffOp

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- The canonical variational Ore action in every finite basis is an isometry of the unconditional
projective interleaving metric. -/
theorem DifferentialFieldAut.projectiveBuildingAction_interleavingDistance
    (σ : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    DiffOp.differentialVariationalProjectiveInterleavingDistance
        (σ.projectiveBuildingAction b x) (σ.projectiveBuildingAction b y) =
      DiffOp.differentialVariationalProjectiveInterleavingDistance x y := by
  exact DiffOp.differentialVariationalProjectiveInterleavingDistance_semilinearAction
    σ.toRingEquiv σ.deriv_comm (variationalOreCompletedMatrixUnit σ.fixes σ.deriv_comm b) x y

end


end GaloisForLFunctions.HTGeometry
