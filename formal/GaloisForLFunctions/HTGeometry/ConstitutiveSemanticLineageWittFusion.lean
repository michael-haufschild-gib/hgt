import GaloisForLFunctions.HTGeometry.WittFormationMechanics

/-!
# Semantic--lineage formation and Witt-ghost neutrality

A finite family of invertible certificate maps generates two canonical packets.  The semantic
packet sums transported history, while the lineage packet applies inverse transport in every
coordinate.  Their composite is exactly cardinality times the identity.  Consequently the formed
history carrier is a scaled idempotent and every recovery ghost is independent of the certificate
family.

This formalizes the algebraic core of ULF-FFM-1.  It is a formation-factorization theorem, not an RH
statement.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]

/-- Sum a finite history after transport by its certificate family. -/
noncomputable def certificateSemanticPacket (A : ι → V ≃ₗ[K] V) :
    (ι → V) →ₗ[K] V := by
  classical
  exact
    { toFun := fun x => ∑ i, A i (x i)
      map_add' := fun x y => by simp [map_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [map_smul, Finset.smul_sum] }

/-- Place one recovered vector in every history coordinate using inverse certificate transport. -/
def certificateLineagePacket (A : ι → V ≃ₗ[K] V) : V →ₗ[K] (ι → V) where
  toFun v i := (A i).symm v
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

/-- History carrier formed by lineage after semantic recovery. -/
noncomputable def certificateFormedCarrier (A : ι → V ≃ₗ[K] V) :
    (ι → V) →ₗ[K] (ι → V) :=
  (certificateLineagePacket A).comp (certificateSemanticPacket A)

/-- **Exact common recovery.**  Every certificate cancels its inverse, so the recovered packet is
cardinality times the original vector. -/
theorem certificateSemantic_comp_lineage (A : ι → V ≃ₗ[K] V) :
    (certificateSemanticPacket A).comp (certificateLineagePacket A) =
      (Fintype.card ι : K) • LinearMap.id := by
  classical
  ext v
  simpa [certificateSemanticPacket, certificateLineagePacket] using
    (Nat.cast_smul_eq_nsmul K (Fintype.card ι) v).symm

/-- **Scaled idempotence.**  Formation followed twice equals cardinality times formation once. -/
theorem certificateFormedCarrier_comp_self (A : ι → V ≃ₗ[K] V) :
    (certificateFormedCarrier A).comp (certificateFormedCarrier A) =
      (Fintype.card ι : K) • certificateFormedCarrier A := by
  classical
  apply LinearMap.ext
  intro x
  funext i
  have h := LinearMap.congr_fun (certificateSemantic_comp_lineage A)
    (certificateSemanticPacket A x)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_coe, id_eq] at h
  change (certificateLineagePacket A)
      ((certificateSemanticPacket A)
        ((certificateLineagePacket A) ((certificateSemanticPacket A) x))) i = _
  rw [h]
  simp [certificateFormedCarrier, certificateLineagePacket]

/-- Every positive iterate of the formed carrier is a scalar multiple of its first iterate. -/
theorem certificateFormedCarrier_pow (A : ι → V ≃ₗ[K] V) (n : ℕ) :
    (certificateFormedCarrier A) ^ (n + 1) =
      (Fintype.card ι : K) ^ n • certificateFormedCarrier A := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih]
      apply LinearMap.ext
      intro x
      change (Fintype.card ι : K) ^ n •
          (certificateFormedCarrier A) ((certificateFormedCarrier A) x) = _
      have h := LinearMap.congr_fun (certificateFormedCarrier_comp_self A) x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
      rw [h, smul_smul]
      change ((Fintype.card ι : K) ^ n * (Fintype.card ι : K)) •
        (certificateFormedCarrier A) x =
          (Fintype.card ι : K) ^ (n + 1) • (certificateFormedCarrier A) x
      rw [pow_succ]

/-- Pointwise certificate transport is the canonical change of history frame. -/
def certificatePointwiseGauge (A : ι → V ≃ₗ[K] V) : (ι → V) ≃ₗ[K] (ι → V) :=
  LinearEquiv.piCongrRight A

/-- **Carrier conjugacy.**  Every certificate carrier is conjugate to the identity-certificate
carrier. -/
theorem certificatePointwiseGauge_formedCarrier (A : ι → V ≃ₗ[K] V) (x : ι → V) :
    certificatePointwiseGauge A (certificateFormedCarrier A x) =
      certificateFormedCarrier (fun _ => LinearEquiv.refl K V)
        (certificatePointwiseGauge A x) := by
  classical
  funext i
  simp [certificatePointwiseGauge, certificateFormedCarrier, certificateSemanticPacket,
    certificateLineagePacket]

/-- Recovery ghost obtained by inserting `n` formed-carrier iterates between semantic and lineage
packets. -/
noncomputable def certificateRecoveryGhost (A : ι → V ≃ₗ[K] V) (n : ℕ) : V →ₗ[K] V :=
  (certificateSemanticPacket A).comp
    (((certificateFormedCarrier A) ^ n).comp (certificateLineagePacket A))

/-- **Ghost neutrality.**  Every recovery ghost depends only on finite history cardinality, not on
the certificate maps. -/
theorem certificateRecoveryGhost_eq (A : ι → V ≃ₗ[K] V) (n : ℕ) :
    certificateRecoveryGhost A n =
      (Fintype.card ι : K) ^ (n + 1) • LinearMap.id := by
  classical
  apply LinearMap.ext
  intro v
  cases n with
  | zero =>
      have h := LinearMap.congr_fun (certificateSemantic_comp_lineage A) v
      simpa [certificateRecoveryGhost] using h
  | succ n =>
      have hp := LinearMap.congr_fun (certificateFormedCarrier_pow A n)
        ((certificateLineagePacket A) v)
      have hf := LinearMap.congr_fun (certificateSemantic_comp_lineage A) v
      have hpq : certificateFormedCarrier A ((certificateLineagePacket A) v) =
          (Fintype.card ι : K) • (certificateLineagePacket A) v := by
        change (certificateLineagePacket A)
          ((certificateSemanticPacket A) ((certificateLineagePacket A) v)) = _
        rw [show (certificateSemanticPacket A) ((certificateLineagePacket A) v) =
          (Fintype.card ι : K) • v by simpa using hf]
        simp
      change (certificateSemanticPacket A)
        (((certificateFormedCarrier A) ^ (n + 1)) ((certificateLineagePacket A) v)) = _
      rw [hp]
      simp only [map_smul, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hpq]
      simp only [map_smul]
      rw [show (certificateSemanticPacket A) ((certificateLineagePacket A) v) =
          (Fintype.card ι : K) • v by simpa using hf]
      rw [smul_smul, smul_smul]
      change ((Fintype.card ι : K) ^ n * (Fintype.card ι : K) *
        (Fintype.card ι : K)) • v =
          (Fintype.card ι : K) ^ (n + 1 + 1) • v
      rw [pow_succ, pow_succ]

/-- Recovery ghosts obey a first-order constant recurrence. -/
theorem certificateRecoveryGhost_succ (A : ι → V ≃ₗ[K] V) (n : ℕ) :
    certificateRecoveryGhost A (n + 1) =
      (Fintype.card ι : K) • certificateRecoveryGhost A n := by
  classical
  rw [certificateRecoveryGhost_eq, certificateRecoveryGhost_eq, pow_succ]
  ext v
  simp [smul_smul, mul_comm]

/-- Any two certificate histories have exactly the same complete recovery-ghost packet. -/
theorem certificateRecoveryGhost_certificate_independent
    (A A' : ι → V ≃ₗ[K] V) (n : ℕ) :
    certificateRecoveryGhost A n = certificateRecoveryGhost A' n := by
  classical
  rw [certificateRecoveryGhost_eq, certificateRecoveryGhost_eq]

section Complex

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- The operator recovery ghost is the lift of the one-mode Witt ghost with mode equal to history
cardinality. -/
theorem certificateRecoveryGhost_eq_oneModeWitt
    (A : ι → W ≃ₗ[ℂ] W) (n : ℕ) (v : W) :
    certificateRecoveryGhost A n v =
      wittGhost (fun _ : Fin 1 => (Fintype.card ι : ℂ)) (n + 1) • v := by
  classical
  rw [LinearMap.congr_fun (certificateRecoveryGhost_eq A n) v]
  simp [wittGhost]

end Complex

/-- Capstone: exact recovery, scaled-idempotent formation, and complete ghost neutrality hold for
every finite invertible certificate family. -/
theorem semanticLineageWittFusion_unconditional (A : ι → V ≃ₗ[K] V) :
    ((certificateSemanticPacket A).comp (certificateLineagePacket A) =
      (Fintype.card ι : K) • LinearMap.id) ∧
    ((certificateFormedCarrier A).comp (certificateFormedCarrier A) =
      (Fintype.card ι : K) • certificateFormedCarrier A) ∧
    (∀ n, certificateRecoveryGhost A n =
      (Fintype.card ι : K) ^ (n + 1) • LinearMap.id) ∧
    (∀ (A' : ι → V ≃ₗ[K] V) n,
      certificateRecoveryGhost A n = certificateRecoveryGhost A' n) := by
  exact ⟨certificateSemantic_comp_lineage A, certificateFormedCarrier_comp_self A,
    certificateRecoveryGhost_eq A, certificateRecoveryGhost_certificate_independent A⟩

end

end GaloisForLFunctions.HTGeometry
