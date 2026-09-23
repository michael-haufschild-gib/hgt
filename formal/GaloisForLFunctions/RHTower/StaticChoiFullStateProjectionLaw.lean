import GaloisForLFunctions.RHTower.StaticChoiSyndeticComplexityLaw

/-!
# Full-state bridge for the static Choi complexity law

The phase-torus entropy theorem is naturally expressed on the spectral
diagonal subspace of the Choi Hilbert space.  Circuit targets, however, are
arbitrary states in the full tensor-square space.  This file closes that
semantic gap.

Restricting a full density matrix to diagonal--diagonal spectral coordinates
is Hilbert--Schmidt contractive.  The restriction of the actual diagonal
unitary Choi density is exactly `uniformPhaseDensity`.  Therefore separation
from the projected circuit targets implies separation from the original full
targets, with no dimension factor or loss of radius.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Restrict a full Choi density matrix to the block indexed by the spectral
diagonal vectors `(i,i)`. -/
def diagonalDensityRestriction (d : ℕ)
    (ρ : EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d))) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun ij ↦ ρ ((ij.1, ij.1), (ij.2, ij.2))

/-- Diagonal block restriction is contractive in Hilbert--Schmidt norm. -/
theorem norm_diagonalDensityRestriction_le (d : ℕ)
    (ρ : EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d))) :
    ‖diagonalDensityRestriction d ρ‖ ≤ ‖ρ‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  let f : (Fin d × Fin d) → ((Fin d × Fin d) × (Fin d × Fin d)) :=
    fun ij ↦ ((ij.1, ij.1), (ij.2, ij.2))
  have hf : Function.Injective f := by
    intro a b h
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x ↦ x.1.1.val) h
    · apply Fin.ext
      exact congrArg (fun x ↦ x.2.1.val) h
  change (∑ ij, ‖ρ (f ij)‖ ^ (2 : ℕ)) ≤ ∑ pq, ‖ρ pq‖ ^ (2 : ℕ)
  rw [← Finset.sum_image (s := Finset.univ) (g := f)
    (f := fun pq ↦ ‖ρ pq‖ ^ (2 : ℕ)) hf.injOn]
  exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _

theorem diagonalDensityRestriction_sub (d : ℕ)
    (ρ σ : EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d))) :
    diagonalDensityRestriction d (ρ - σ) =
      diagonalDensityRestriction d ρ - diagonalDensityRestriction d σ := by
  ext ij
  rfl

/-- Metric form of diagonal-block contractivity. -/
theorem dist_diagonalDensityRestriction_le (d : ℕ)
    (ρ σ : EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d))) :
    dist (diagonalDensityRestriction d ρ)
        (diagonalDensityRestriction d σ) ≤ dist ρ σ := by
  rw [dist_eq_norm, dist_eq_norm, ← diagonalDensityRestriction_sub]
  exact norm_diagonalDensityRestriction_le d (ρ - σ)

/-- Full density matrix of the normalized Choi state of a diagonal unitary.
Only the spectral diagonal vectors `(i,i)` carry amplitude. -/
def fullUniformPhaseChoiDensity (d : ℕ)
    (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d)) :=
  WithLp.toLp 2 fun pq ↦
    if pq.1.1 = pq.1.2 ∧ pq.2.1 = pq.2.2 then
      ((d : ℝ)⁻¹ : ℂ) * fourier 1 (x pq.1.1) *
        starRingEnd ℂ (fourier 1 (x pq.2.1))
    else 0

/-- The diagonal restriction of the full Choi density is exactly the phase
density used by the entropy theorem. -/
@[simp] theorem diagonalDensityRestriction_fullUniformPhaseChoiDensity
    (d : ℕ) (x : Fin d → UnitAddCircle) :
    diagonalDensityRestriction d (fullUniformPhaseChoiDensity d x) =
      uniformPhaseDensity d x := by
  ext ij
  simp [diagonalDensityRestriction, fullUniformPhaseChoiDensity,
    uniformPhaseDensity]

/-- Projected-target distance is bounded by the true full-state distance. -/
theorem dist_uniformPhaseDensity_projectedTarget_le_full
    (d : ℕ) (x : Fin d → UnitAddCircle)
    (c : EuclideanSpace ℂ ((Fin d × Fin d) × (Fin d × Fin d))) :
    dist (uniformPhaseDensity d x) (diagonalDensityRestriction d c) ≤
      dist (fullUniformPhaseChoiDensity d x) c := by
  rw [← diagonalDensityRestriction_fullUniformPhaseChoiDensity]
  exact dist_diagonalDensityRestriction_le d _ _

/-- **Full-state syndetic Choi complexity law.** For every full circuit-target
dictionary in the actual tensor-square Choi space, the explicit entropy
budget below one forces one full-state hard endpoint in every interval of a
fixed finite length.

The theorem loses neither radius nor a dimension factor when passing from the
spectral phase geometry to arbitrary circuit targets. -/
theorem maximallyProjective_fullChoiCircuitTargets_syndetic
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (hmax : GaloisForLFunctions.HTGeometry.MaximallyProjectiveEnergy energy)
    {gate : Type*} [Fintype gate] (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ
        ((Fin (d + 1) × Fin (d + 1)) ×
          (Fin (d + 1) × Fin (d + 1))))
    {δ : ℝ} (hδ : 0 < δ)
    (hentropy :
      (Fintype.card gate : ℝ) ^ (s + 1) *
          (((d + 1 : ℕ) : ℝ) * Real.exp (((d + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * δ ^ (2 : ℕ)) / 2) ^
              ((d + 1 : ℕ) - 1)) < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ, ∃ t ∈ Set.Icc a (a + L),
      ∀ w : PaddedCircuitWord gate s,
        δ < dist
          (fullUniformPhaseChoiDensity (d + 1)
            (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t)))
          (target w) := by
  obtain ⟨L, hL, hhits⟩ :=
    maximallyProjective_paddedCircuitHardTimes_syndetic
      energy hmax s (fun w ↦ diagonalDensityRestriction (d + 1) (target w))
      hδ hentropy
  refine ⟨L, hL, fun a ↦ ?_⟩
  obtain ⟨t, ht, hhard⟩ := hhits a
  refine ⟨t, ht, fun w ↦ ?_⟩
  exact (hhard w).trans_le
    (dist_uniformPhaseDensity_projectedTarget_le_full
      (d + 1)
      (zeroAnchoredPhase d (projectivePhysicalPhaseFlow energy t))
      (target w))

end RHTower
