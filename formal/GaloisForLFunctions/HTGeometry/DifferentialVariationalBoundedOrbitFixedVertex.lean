import GaloisForLFunctions.HTGeometry.DifferentialOperatorCompletedCartanBalanceEveryLattice
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpIntegerNoetherian
import GaloisForLFunctions.HTGeometry.DifferentialVariationalRankOnePhase

/-!
# Bounded variational orbits fix projective lattice vertices

A balanced Euclidean bound controls every raw Cartan coordinate, hence uniformly interleaves every
literal orbit lattice with the base lattice.  Passing from nonnegative to integer iterates gives a
shift-invariant family inside one fixed enlarged lattice.  The completed valuation ring is left
Noetherian, so the supremum of this family is again a finite full lattice.  Integer-index shift
invariance makes that lattice literally fixed by the canonical variational action.
-/

open scoped BigOperators Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Literal action on a completed valuation lattice. -/
noncomputable def DifferentialFieldAut.latticeBuildingAction
    (tau : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    DiffOp.CompletedPseudoDiffOpLattice K (Fin r) :=
  DiffOp.differentialVariationalLatticeSemilinearAction
    tau.toRingEquiv tau.deriv_comm
    (variationalOreCompletedMatrixUnit tau.fixes tau.deriv_comm b) L

@[simp] theorem DifferentialFieldAut.projectiveBuildingAction_mk
    (tau : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    tau.projectiveBuildingAction b (Quotient.mk _ L) =
      Quotient.mk _ (tau.latticeBuildingAction b L) :=
  rfl

@[simp] theorem DifferentialFieldAut.latticeBuildingAction_one
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    (1 : DifferentialFieldAut C K).latticeBuildingAction b L = L := by
  unfold DifferentialFieldAut.latticeBuildingAction
  unfold DiffOp.differentialVariationalLatticeSemilinearAction
  rw [variationalOreCompletedMatrixUnit_refl,
    DiffOp.completedPseudoDiffOpMatrixLinearEquiv_one]
  change DiffOp.mapCompletedPseudoDiffOpLatticeLinear
      (LinearEquiv.refl (DiffOp.CompletedPseudoDiffOp K) _)
      (DiffOp.mapCompletedPseudoDiffOpLattice (RingEquiv.refl K)
        DiffOp.refl_deriv_comm L) = L
  rw [DiffOp.mapCompletedPseudoDiffOpLattice_refl,
    DiffOp.mapCompletedPseudoDiffOpLatticeLinear_refl]

theorem DifferentialFieldAut.latticeBuildingAction_mul
    (sigma tau : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    (sigma * tau).latticeBuildingAction b L =
      tau.latticeBuildingAction b (sigma.latticeBuildingAction b L) := by
  unfold DifferentialFieldAut.latticeBuildingAction
  unfold DiffOp.differentialVariationalLatticeSemilinearAction
  rw [DiffOp.mapCompletedPseudoDiffOpLattice_matrix]
  rw [DiffOp.mapCompletedPseudoDiffOpLatticeLinear_trans]
  rw [DiffOp.mapCompletedPseudoDiffOpLattice_trans]
  rw [DiffOp.completedPseudoDiffOpMatrixLinearEquiv_mul]
  rw [← variationalOreCompletedMatrixUnit_trans]
  congr 1

theorem DifferentialFieldAut.latticeBuildingAction_zpow_shift
    (sigma : DifferentialFieldAut C K) (z : ℤ)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (L : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) :
    sigma.latticeBuildingAction b ((sigma ^ z).latticeBuildingAction b L) =
      (sigma ^ (z + 1)).latticeBuildingAction b L := by
  rw [← DifferentialFieldAut.latticeBuildingAction_mul, ← zpow_add_one]

/-- A balanced Euclidean displacement bound gives literal uniformizer interleaving of its
representatives. -/
theorem DiffOp.completedPseudoDiffOpLattice_interleavedAt_of_balanced_euclidean_le
    {r : ℕ} (L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)) (N : ℕ)
    (hbalance : ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L M i = 0)
    (hdist : DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
      (Quotient.mk _ L) (Quotient.mk _ M) ≤ (N : ℝ)) :
    L.InterleavedAt N M := by
  let d := DiffOp.completedPseudoDiffOpDominantCartanData L M
  apply (DiffOp.mapCompletedPseudoDiffOpLatticeLinear_interleavedAt_iff
    d.frame L M N).1
  rw [d.map_left, d.map_right,
    ← DiffOp.standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  apply (DiffOp.standardCompletedPseudoDiffOpLattice_interleavedAt_iff
    (fun _ : Fin r => 0) d.coweight N).2
  intro i
  have hcenter : DiffOp.centeredCoweight d.coweight i = (d.coweight i : ℝ) := by
    simp only [DiffOp.centeredCoweight]
    have hbalance' : ∑ j, d.coweight j = 0 := hbalance
    rw [← Int.cast_sum, hbalance']
    simp
  have habsReal : |(d.coweight i : ℝ)| ≤ (N : ℝ) := by
    rw [← hcenter]
    exact (DiffOp.abs_apply_le_euclideanNorm
      (DiffOp.centeredCoweight d.coweight) i).trans hdist
  have habsInt : |d.coweight i| ≤ (N : ℤ) := by
    exact_mod_cast habsReal
  have hb := (abs_le.mp habsInt)
  omega

/-- The upper half of an interleaving places the second lattice inside the inverse uniformizer
scale of the first. -/
theorem DiffOp.CompletedPseudoDiffOpLattice.carrier_le_inverseScale_of_interleavedAt
    {r : ℕ} {L M : DiffOp.CompletedPseudoDiffOpLattice K (Fin r)} {N : ℕ}
    (h : L.InterleavedAt N M) :
    M.carrier ≤
      (DiffOp.leftScaleCompletedPseudoDiffOpLattice
        (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(N : ℤ))) L).carrier := by
  have hscaled := DiffOp.leftScaleCompletedPseudoDiffOpLattice_carrier_mono
    (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(N : ℤ))) h.2
  rw [DiffOp.leftScaleCompletedPseudoDiffOpLattice_mul] at hscaled
  have hunit :
      DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(N : ℤ)) *
          DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (N : ℤ) = 1 := by
    rw [← zpow_add]
    simp
  rw [hunit, DiffOp.leftScaleCompletedPseudoDiffOpLattice_one] at hscaled
  exact hscaled

/-- Forward and inverse displacements of an isometry have the same base-point distance. -/
theorem differentialVariationalEuclideanVertexDistance_inverseAction
    (tau : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
        (tau⁻¹.projectiveBuildingAction b x) =
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
        (tau.projectiveBuildingAction b x) := by
  calc
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
        (tau⁻¹.projectiveBuildingAction b x) =
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (tau.projectiveBuildingAction b x)
        (tau.projectiveBuildingAction b (tau⁻¹.projectiveBuildingAction b x)) :=
      (tau.projectiveBuildingAction_euclideanVertexDistance b x
        (tau⁻¹.projectiveBuildingAction b x)).symm
    _ = DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
        (tau.projectiveBuildingAction b x) x := by
      rw [← DifferentialFieldAut.projectiveBuildingAction_mul, inv_mul_cancel,
        DifferentialFieldAut.projectiveBuildingAction_one]
    _ = DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
        (tau.projectiveBuildingAction b x) :=
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance_comm _ _

/-- A bound for all nonnegative iterates automatically bounds every integer iterate. -/
theorem differentialVariationalEuclideanVertexDistance_zpow_le_of_pow_le
    (sigma : DifferentialFieldAut C K)
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (B : ℝ)
    (hB : ∀ n : ℕ,
      DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
        ((sigma ^ n).projectiveBuildingAction b x) ≤ B) (z : ℤ) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x
      ((sigma ^ z).projectiveBuildingAction b x) ≤ B := by
  cases z with
  | ofNat n => simpa using hB n
  | negSucc n =>
      rw [zpow_negSucc,
        differentialVariationalEuclideanVertexDistance_inverseAction]
      exact hB (n + 1)

/-- Every bounded Euclidean orbit of the canonical variational action fixes a projective
completed-lattice vertex. -/
theorem differentialVariationalEuclideanOrbitBounded_implies_hasFixedVertex
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (sigma : DifferentialFieldAut C K)
    (hbounded : DifferentialVariationalEuclideanOrbitBounded b x sigma) :
    DifferentialVariationalHasFixedVertex b sigma := by
  induction x using Quotient.inductionOn with
  | _ L =>
      obtain ⟨B, hB⟩ := hbounded
      obtain ⟨N, hBN⟩ := exists_nat_ge B
      let orbit : ℤ → DiffOp.CompletedPseudoDiffOpLattice K (Fin r) :=
        fun z => (sigma ^ z).latticeBuildingAction b L
      let upper : DiffOp.CompletedPseudoDiffOpLattice K (Fin r) :=
        DiffOp.leftScaleCompletedPseudoDiffOpLattice
          (DiffOp.completedPseudoDiffOpUniformizerUnit (K := K) ^ (-(N : ℤ))) L
      have horbit_le (z : ℤ) : (orbit z).carrier ≤ upper.carrier := by
        have hzdist :
            DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
                (Quotient.mk _ L) (Quotient.mk _ (orbit z)) ≤ (N : ℝ) := by
          calc
            DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
                (Quotient.mk _ L) (Quotient.mk _ (orbit z)) ≤ B := by
              simpa only [orbit, DifferentialFieldAut.projectiveBuildingAction_mk] using
                differentialVariationalEuclideanVertexDistance_zpow_le_of_pow_le
                  sigma b (Quotient.mk _ L) B hB z
            _ ≤ (N : ℝ) := hBN
        have hzbalance :
            ∑ i, DiffOp.completedPseudoDiffOpDominantRelativePosition L (orbit z) i = 0 := by
          simpa only [orbit, DifferentialFieldAut.latticeBuildingAction] using
            (sigma ^ z).variationalOreCartanBalance_everyLattice b L
        have hinter : L.InterleavedAt N (orbit z) :=
          DiffOp.completedPseudoDiffOpLattice_interleavedAt_of_balanced_euclidean_le
            L (orbit z) N hzbalance hzdist
        exact
          DiffOp.CompletedPseudoDiffOpLattice.carrier_le_inverseScale_of_interleavedAt
            hinter
      let S : Submodule (DiffOp.CompletedPseudoDiffOpInteger (K := K))
          (Fin r → DiffOp.CompletedPseudoDiffOp K) :=
        ⨆ z : ℤ, (orbit z).carrier
      have hSle : S ≤ upper.carrier := by
        exact iSup_le horbit_le
      have hSfg : S.FG := upper.fg.of_le hSle
      have hLle : L.carrier ≤ S := by
        have hzero := le_iSup (fun z : ℤ => (orbit z).carrier) 0
        simpa only [S, orbit, zpow_zero,
          DifferentialFieldAut.latticeBuildingAction_one] using hzero
      have hSfull : Submodule.span (DiffOp.CompletedPseudoDiffOp K)
          (S : Set (Fin r → DiffOp.CompletedPseudoDiffOp K)) = ⊤ := by
        apply le_antisymm le_top
        rw [← L.full]
        exact Submodule.span_mono hLle
      let fixedLattice : DiffOp.CompletedPseudoDiffOpLattice K (Fin r) :=
        { carrier := S
          fg := hSfg
          full := hSfull }
      have hcarrier : (sigma.latticeBuildingAction b fixedLattice).carrier = S := by
        let eO := DiffOp.mapCompletedPseudoIntegerEquiv sigma.toRingEquiv sigma.deriv_comm
        letI : RingHomSurjective eO.toRingHom := ⟨eO.surjective⟩
        change Submodule.map
            (DiffOp.restrictCompletedPseudoVecLinearEquiv
              (DiffOp.completedPseudoDiffOpMatrixLinearEquiv
                (variationalOreCompletedMatrixUnit sigma.fixes sigma.deriv_comm b))).toLinearMap
            (Submodule.map
              (DiffOp.mapCompletedPseudoIntegerVecLinearMap
                (ι := Fin r) sigma.toRingEquiv sigma.deriv_comm) S) = S
        rw [show S = ⨆ z : ℤ, (orbit z).carrier by rfl]
        rw [Submodule.map_iSup, Submodule.map_iSup]
        change (⨆ z : ℤ, (sigma.latticeBuildingAction b (orbit z)).carrier) =
          ⨆ z : ℤ, (orbit z).carrier
        apply le_antisymm
        · apply iSup_le
          intro z
          apply le_iSup_of_le (z + 1)
          exact le_of_eq (by
            simpa only [orbit] using congrArg
              DiffOp.CompletedPseudoDiffOpLattice.carrier
              (sigma.latticeBuildingAction_zpow_shift z b L))
        · apply iSup_le
          intro z
          apply le_iSup_of_le (z - 1)
          have hshift := sigma.latticeBuildingAction_zpow_shift (z - 1) b L
          have hz : z - 1 + 1 = z := by omega
          rw [hz] at hshift
          exact le_of_eq (by
            simpa only [orbit] using congrArg
              DiffOp.CompletedPseudoDiffOpLattice.carrier hshift.symm)
      have hfixedLattice : sigma.latticeBuildingAction b fixedLattice = fixedLattice := by
        apply DiffOp.CompletedPseudoDiffOpLattice.ext
        exact hcarrier
      refine ⟨Quotient.mk _ fixedLattice, ?_⟩
      rw [DifferentialFieldAut.projectiveBuildingAction_mk, hfixedLattice]

end

end GaloisForLFunctions.HTGeometry
