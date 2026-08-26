import GaloisForLFunctions.RHTower.UnitaryReplicaOptimalDesignTransportLaw
import GaloisForLFunctions.RHTower.ReturnExcisedGrowingReplicaPseudodeterminantLaw
import GaloisForLFunctions.RHTower.AutonomousReturnReflection
import GaloisForLFunctions.HTGeometry.ReplicaProjectionIncidenceLaw

/-!
# Residual replica optimal-design transport

Determinant designs require positive occupied dimension, not endpoint
normalization. This permits one pre-draw design on unnormalized
return-orthogonal residuals and transports it through every spectral basis.
-/

open scoped BigOperators Matrix ComplexConjugate
open Matrix
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Determinant design does not require normalized targets once positive
occupied replica dimension is supplied explicitly. -/
theorem exists_replicaTarget_optimalDesign_pointwise_of_finrank_pos
    {C alpha : Type*} [Fintype C] [Nonempty C] [DecidableEq C] [Fintype alpha]
    (r : ℕ) (target : C → alpha → ℂ)
    (hpos : 0 < Module.finrank ℂ (replicaTargetSpan r target)) :
    ∃ w ∈ stdSimplex ℝ C,
      ∀ (psi : alpha → ℂ) (c : C),
        finitePureStateFidelity psi (target c) ^ r ≤
          (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
            ∑ j, w j * finitePureStateFidelity psi (target j) ^ r := by
  classical
  have hspan := span_replicaTargetCoordinateVector_eq_top r target
  have key : ∀ (m : ℕ) (T : C → Fin m → ℂ), 0 < m →
      Submodule.span ℂ (Set.range T) = ⊤ →
      ∃ w ∈ stdSimplex ℝ C, ∀ (u : Fin m → ℂ) (c : C),
        ‖finiteComplexInner u (T c)‖ ^ 2 ≤
          (m : ℝ) * ∑ j, w j * ‖finiteComplexInner u (T j)‖ ^ 2 := by
    rintro (_ | m) T hm hspanT
    · exact absurd hm (lt_irrefl 0)
    · simpa using exists_finiteOptimalDesign_pointwise T hspanT
  obtain ⟨w, hw, hdesign⟩ := key _
    (fun c ↦ replicaTargetCoordinateVector r target c) hpos hspan
  refine ⟨w, hw, ?_⟩
  intro psi c
  have hbound := hdesign (replicaTargetCoordinate r target psi) c
  simp_rw [replicaTargetCoordinateVector_eq_coordinate] at hbound
  simp_rw [finiteComplexInner_replicaTargetCoordinate_endpoint] at hbound
  simp_rw [← finitePureStateFidelity_pow_eq_replica_inner_norm_sq] at hbound
  exact hbound

/-- Any supplied determinant design transports through a common unitary;
normalization is irrelevant. -/
theorem replicaTargetDesign_pointwise_unitaryTransport
    {C alpha : Type*} [Fintype C] [Fintype alpha] [DecidableEq alpha]
    (r : ℕ) (target : C → alpha → ℂ) (w : C → ℝ)
    (hdesign : ∀ (psi : alpha → ℂ) (c : C),
      finitePureStateFidelity psi (target c) ^ r ≤
        (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
          ∑ j, w j * finitePureStateFidelity psi (target j) ^ r)
    (U : Matrix.unitaryGroup alpha ℂ)
    (psi : alpha → ℂ) (c : C) :
    finitePureStateFidelity psi (unitaryTransportTarget U target c) ^ r ≤
      (Module.finrank ℂ
        (replicaTargetSpan r (unitaryTransportTarget U target)) : ℝ) *
        ∑ j, w j * finitePureStateFidelity psi
          (unitaryTransportTarget U target j) ^ r := by
  have hbase := hdesign ((U : Matrix alpha alpha ℂ)ᴴ *ᵥ psi) c
  rw [finrank_replicaTargetSpan_unitaryTransportTarget r U target]
  change finitePureStateFidelity psi
        ((U : Matrix alpha alpha ℂ) *ᵥ target c) ^ r ≤
      (Module.finrank ℂ (replicaTargetSpan r target) : ℝ) *
        ∑ j, w j * finitePureStateFidelity psi
          ((U : Matrix alpha alpha ℂ) *ᵥ target j) ^ r
  simpa only [finitePureStateFidelity_unitary_pull U] using hbase

def physicalUnitaryChoiResidual
    {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  staticChoiAnchorResidual (fun _ => 0) 0
    (GaloisForLFunctions.RHTower.choiVector
      (U : Matrix (Fin d) (Fin d) ℂ))

theorem pureConjugationUnitary_mulVec_physicalUnitaryChoiResidual
    {d : ℕ} (hd : 0 < d)
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ((pureConjugationUnitary (star hH.eigenvectorUnitary) :
        Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) *ᵥ
      (physicalUnitaryChoiResidual U).ofLp) =
      (staticChoiAnchorResidual hH.eigenvalues 0
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U :
            Matrix (Fin d) (Fin d) ℂ))).ofLp := by
  let Kstar : Matrix.unitaryGroup (Fin d) ℂ := star hH.eigenvectorUnitary
  have hphysical : physicalUnitaryChoiResidual U =
      GaloisForLFunctions.RHTower.choiVector
          (U : Matrix (Fin d) (Fin d) ℂ) -
        (Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ) / (d : ℂ)) •
          GaloisForLFunctions.RHTower.choiVector
            (1 : Matrix (Fin d) (Fin d) ℂ) := by
    unfold physicalUnitaryChoiResidual staticChoiAnchorResidual
    rw [staticChoiAnchorComponent_zero_choiVector_eq_normalizedTrace hd]
    rw [← choiVector_one_eq_staticSpectralChoiVector_zero_general hd (fun _ => 0)]
  have hspectral :
      staticChoiAnchorResidual hH.eigenvalues 0
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U :
            Matrix (Fin d) (Fin d) ℂ)) =
      GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U :
            Matrix (Fin d) (Fin d) ℂ) -
        (Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ) / (d : ℂ)) •
          GaloisForLFunctions.RHTower.choiVector
            (1 : Matrix (Fin d) (Fin d) ℂ) := by
    unfold staticChoiAnchorResidual
    rw [staticChoiAnchorComponent_zero_choiVector_eq_normalizedTrace hd]
    rw [← choiVector_one_eq_staticSpectralChoiVector_zero_general hd hH.eigenvalues]
    congr 2
    change Matrix.trace
      (star (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        (U : Matrix (Fin d) (Fin d) ℂ) *
          (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) / (d : ℂ) = _
    rw [GaloisForLFunctions.HTGeometry.trace_unitaryConjugate]
  rw [hphysical, hspectral]
  change (pureConjugationChannel (Kstar : Matrix (Fin d) (Fin d) ℂ)) *ᵥ
      ((GaloisForLFunctions.RHTower.choiVector
          (U : Matrix (Fin d) (Fin d) ℂ)).ofLp -
        (Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ) / (d : ℂ)) •
          (GaloisForLFunctions.RHTower.choiVector
            (1 : Matrix (Fin d) (Fin d) ℂ)).ofLp) =
      (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH U :
            Matrix (Fin d) (Fin d) ℂ)).ofLp -
        (Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ) / (d : ℂ)) •
          (GaloisForLFunctions.RHTower.choiVector
            (1 : Matrix (Fin d) (Fin d) ℂ)).ofLp
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  rw [pureConjugationChannel_mulVec_choiVector]
  rw [pureConjugationChannel_mulVec_choiVector]
  have hKid :
      (Kstar : Matrix (Fin d) (Fin d) ℂ) *
          (1 : Matrix (Fin d) (Fin d) ℂ) *
          (Kstar : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    simpa only [Matrix.mul_one, Matrix.star_eq_conjTranspose] using Kstar.property.2
  rw [hKid]
  congr 2
  dsimp [Kstar, hermitianSpectralEndpoint]
  rw [← Matrix.star_eq_conjTranspose, star_star]

def physicalUnitaryChoiResidualTarget
    {d : ℕ} {C : Type*}
    (U : C → Matrix.unitaryGroup (Fin d) ℂ) : C → (Fin d × Fin d) → ℂ :=
  fun c => (physicalUnitaryChoiResidual (U c)).ofLp

theorem unitaryTransportTarget_physicalUnitaryChoiResidualTarget
    {d : ℕ} (hd : 0 < d) {C : Type*}
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (U : C → Matrix.unitaryGroup (Fin d) ℂ) :
    unitaryTransportTarget (pureConjugationUnitary (star hH.eigenvectorUnitary))
        (physicalUnitaryChoiResidualTarget U) =
      fun c => (staticChoiAnchorResidual hH.eigenvalues 0
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH (U c) :
            Matrix (Fin d) (Fin d) ℂ))).ofLp := by
  funext c
  exact pureConjugationUnitary_mulVec_physicalUnitaryChoiResidual
    hd hH (U c)

/-- One residual design selected in the physical basis controls every
Hermitian spectral basis without post-draw reselection. -/
theorem exists_physicalUnitaryChoiResidual_optimalDesign_allSpectralBases
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Fin d) ℂ)
    (hpos : 0 < Module.finrank ℂ
      (replicaTargetSpan r (physicalUnitaryChoiResidualTarget U))) :
    ∃ w ∈ stdSimplex ℝ C,
      ∀ (H : Matrix (Fin d) (Fin d) ℂ) (hH : H.IsHermitian)
        (psi : (Fin d × Fin d) → ℂ) (c : C),
        finitePureStateFidelity psi
            (staticChoiAnchorResidual hH.eigenvalues 0
              (GaloisForLFunctions.RHTower.choiVector
                (hermitianSpectralEndpoint hH (U c) :
                  Matrix (Fin d) (Fin d) ℂ))).ofLp ^ r ≤
          (Module.finrank ℂ (replicaTargetSpan r (fun j =>
            (staticChoiAnchorResidual hH.eigenvalues 0
              (GaloisForLFunctions.RHTower.choiVector
                (hermitianSpectralEndpoint hH (U j) :
                  Matrix (Fin d) (Fin d) ℂ))).ofLp)) : ℝ) *
            ∑ j, w j * finitePureStateFidelity psi
              (staticChoiAnchorResidual hH.eigenvalues 0
                (GaloisForLFunctions.RHTower.choiVector
                  (hermitianSpectralEndpoint hH (U j) :
                    Matrix (Fin d) (Fin d) ℂ))).ofLp ^ r := by
  obtain ⟨w, hw, hdesign⟩ :=
    exists_replicaTarget_optimalDesign_pointwise_of_finrank_pos
      r (physicalUnitaryChoiResidualTarget U) hpos
  refine ⟨w, hw, ?_⟩
  intro H hH psi c
  let V := pureConjugationUnitary (star hH.eigenvectorUnitary)
  have htransport := replicaTargetDesign_pointwise_unitaryTransport
    r (physicalUnitaryChoiResidualTarget U) w hdesign V psi c
  have hfamily := unitaryTransportTarget_physicalUnitaryChoiResidualTarget
    hd hH U
  rw [hfamily] at htransport
  exact htransport

/-- One normalized member already forces positive occupied replica rank; no
normalization condition is needed on the rest of the target family. -/
theorem replicaTargetSpan_finrank_pos_of_exists_normalized
    {C alpha : Type*} [Fintype alpha]
    (r : ℕ) (target : C → alpha → ℂ) (c : C)
    (htarget : finiteComplexInner (target c) (target c) = 1) :
    0 < Module.finrank ℂ (replicaTargetSpan r target) := by
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨replicaTargetVectorInSpan r target c, ?_⟩
  intro hz
  have hval := congrArg (fun z : replicaTargetSpan r target =>
    ‖(z : EuclideanSpace ℂ (Fin r → alpha))‖) hz
  have hnorm := norm_finitePureTensorPowerEuclidean_eq_one
    r (target c) htarget
  simp [replicaTargetVectorInSpan, hnorm] at hval

/-- A trace-zero unitary has no scalar Choi component, so return excision
leaves its normalized Choi vector unchanged. -/
theorem physicalUnitaryChoiResidual_eq_choiVector_of_trace_zero
    {d : ℕ} (hd : 0 < d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (htrace : Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ) = 0) :
    physicalUnitaryChoiResidual U =
      GaloisForLFunctions.RHTower.choiVector
        (U : Matrix (Fin d) (Fin d) ℂ) := by
  unfold physicalUnitaryChoiResidual staticChoiAnchorResidual
  rw [staticChoiAnchorComponent_zero_choiVector_eq_normalizedTrace hd]
  rw [← choiVector_one_eq_staticSpectralChoiVector_zero_general hd (fun _ => 0)]
  rw [htrace, zero_div, zero_smul, sub_zero]

/-- The trace-zero physical residual has unit Hilbert norm. -/
theorem finiteComplexInner_physicalUnitaryChoiResidual_eq_one_of_trace_zero
    {d : ℕ} (hd : 0 < d) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (htrace : Matrix.trace (U : Matrix (Fin d) (Fin d) ℂ) = 0) :
    finiteComplexInner (physicalUnitaryChoiResidual U).ofLp
      (physicalUnitaryChoiResidual U).ofLp = 1 := by
  rw [physicalUnitaryChoiResidual_eq_choiVector_of_trace_zero hd U htrace]
  rw [← inner_toLp_eq_finiteComplexInner]
  rw [inner_self_eq_norm_sq_to_K]
  have hnorm := GaloisForLFunctions.RHTower.norm_choiVector_eq_one
    (show 0 < Fintype.card (Fin d) by simpa using hd)
      (Unitary.coe_star_mul_self U)
  have hnorm' :
      ‖WithLp.toLp 2
        (GaloisForLFunctions.RHTower.choiVector
          (U : Matrix (Fin d) (Fin d) ℂ)).ofLp‖ = 1 := by
    simpa using hnorm
  rw [hnorm']
  norm_num

/-- A single traceless unitary endpoint discharges the positive-rank premise
for the entire physical residual dictionary at every replica order. -/
theorem physicalUnitaryChoiResidualTarget_finrank_pos_of_exists_trace_zero
    {d : ℕ} (hd : 0 < d) {C : Type*}
    (r : ℕ) (U : C → Matrix.unitaryGroup (Fin d) ℂ) (c : C)
    (htrace : Matrix.trace (U c : Matrix (Fin d) (Fin d) ℂ) = 0) :
    0 < Module.finrank ℂ
      (replicaTargetSpan r (physicalUnitaryChoiResidualTarget U)) := by
  exact replicaTargetSpan_finrank_pos_of_exists_normalized
    r (physicalUnitaryChoiResidualTarget U) c
      (finiteComplexInner_physicalUnitaryChoiResidual_eq_one_of_trace_zero
        hd (U c) htrace)

/-- The scalar-return excision is one fixed complex-linear projector. -/
def staticChoiTracelessResidualLinearMap
    {d : ℕ} (energy : Fin d → ℝ) :
    EuclideanSpace ℂ (Fin d × Fin d) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin d × Fin d) where
  toFun := staticChoiTracelessResidual energy
  map_add' x y := by
    simp only [staticChoiTracelessResidual, staticChoiScalarComponent,
      inner_add_right, add_smul]
    module
  map_smul' c x := by
    simp only [staticChoiTracelessResidual, staticChoiScalarComponent,
      inner_smul_right, RingHom.id_apply]
    module

@[simp] theorem staticChoiTracelessResidualLinearMap_apply
    {d : ℕ} (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    staticChoiTracelessResidualLinearMap energy target =
      staticChoiTracelessResidual energy target := rfl

/-- Return excision cannot increase occupied replica rank. -/
theorem finrank_replicaTargetSpan_staticChoiTracelessResidual_le
    {C : Type*} {d : ℕ} (r : ℕ) (energy : Fin d → ℝ)
    (target : C → (Fin d × Fin d) → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r (fun c x =>
        (staticChoiTracelessResidual energy
          (WithLp.toLp 2 (target c))).ofLp x)) ≤
      Module.finrank ℂ (replicaTargetSpan r target) := by
  convert finrank_projectedReplicaTargetSpan_le r
      (staticChoiTracelessResidualLinearMap energy) target using 1
  congr 2

/-- Physical unitary residual dictionaries inherit every full-Choi replica-rank bound. -/
theorem finrank_physicalUnitaryChoiResidualTarget_le_choi
    {C : Type*} {d : ℕ} (r : ℕ)
    (U : C → Matrix.unitaryGroup (Fin d) ℂ) :
    Module.finrank ℂ
        (replicaTargetSpan r (physicalUnitaryChoiResidualTarget U)) ≤
      Module.finrank ℂ (replicaTargetSpan r (fun c =>
        (GaloisForLFunctions.RHTower.choiVector
          (U c : Matrix (Fin d) (Fin d) ℂ)).ofLp)) := by
  let target := fun c =>
    (GaloisForLFunctions.RHTower.choiVector
      (U c : Matrix (Fin d) (Fin d) ℂ)).ofLp
  have h := finrank_replicaTargetSpan_staticChoiTracelessResidual_le
    r (fun _ : Fin d => 0) target
  change Module.finrank ℂ (replicaTargetSpan r (fun c x =>
      (staticChoiTracelessResidual (fun _ : Fin d => 0)
        (GaloisForLFunctions.RHTower.choiVector
          (U c : Matrix (Fin d) (Fin d) ℂ))).ofLp x)) ≤ _
  simpa only [target] using h

end

end RHTower
