import GaloisForLFunctions.HTGeometry.StaticShortcutRecurrenceEnergyLaw
import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw

/-!
# Replica-projector frame energy for static shortcut histories

The abstract observer--spectral reciprocity law uses a real Hilbert target family with nonnegative
collisions.  This module supplies the exact pure-state quantum realization.  Vectorizing the
rank-one projector of an `r`-fold tensor power turns its real Hilbert--Schmidt inner product with a
second projector into the `r`th power of pure-state fidelity.  Nonnegativity is automatic.

Consequently the preparation frame energy in the static shortcut law is exactly the complete
average replica fidelity of the target family.  This is an aggregate pair invariant; it requires no
minimum endpoint separation and retains every target-pair multiplicity.
-/

open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α : Type*} [Fintype α]

/-- Coordinate vectorization of the rank-one projector `|ψ><ψ|`. -/
def finitePureProjectorCoordinate (ψ : α → ℂ) : α × α → ℂ :=
  fun p => ψ p.1 * conj (ψ p.2)

/-- Rank-one projector in finite Hilbert--Schmidt coordinates. -/
def finitePureProjectorEuclidean (ψ : α → ℂ) :
    EuclideanSpace ℂ (α × α) :=
  WithLp.toLp 2 (finitePureProjectorCoordinate ψ)

/-- Hilbert--Schmidt overlap of two pure-state projectors is their fidelity. -/
theorem inner_finitePureProjectorEuclidean (ψ φ : α → ℂ) :
    inner ℂ (finitePureProjectorEuclidean ψ)
        (finitePureProjectorEuclidean φ) =
      (finitePureStateFidelity ψ φ : ℂ) := by
  rw [inner_toLp_eq_finiteComplexInner]
  simp only [finitePureProjectorCoordinate, finitePureProjectorEuclidean,
    finiteComplexInner, finitePureStateFidelity, map_mul,
    starRingEnd_apply, star_star]
  let z : ℂ := ∑ x, star (ψ x) * φ x
  have hfactor :
      (∑ x : α × α,
          star (ψ x.1) * ψ x.2 * (φ x.1 * star (φ x.2))) =
        z * star z := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ i, ∑ j, star (ψ i) * ψ j * (φ i * star (φ j))) =
          ∑ i, ∑ j,
            (star (ψ i) * φ i) * (ψ j * star (φ j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i, (star (ψ i) * φ i) *
          ∑ j, (ψ j * star (φ j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = z * ∑ j, (ψ j * star (φ j)) := by
        rw [Finset.sum_mul]
      _ = z * star z := by
        congr 1
        simp only [z, star_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [star_mul, star_star]
        ring
  rw [hfactor]
  have hnorm : ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) = star z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    rfl
  rw [hnorm]
  ring

/-- Replica-projector Hilbert--Schmidt overlap is exactly replica fidelity. -/
theorem inner_finitePureProjectorEuclidean_tensorPower
    (r : ℕ) (ψ φ : α → ℂ) :
    inner ℂ
        (finitePureProjectorEuclidean (finitePureTensorPower r ψ))
        (finitePureProjectorEuclidean (finitePureTensorPower r φ)) =
      (finitePureStateFidelity ψ φ ^ r : ℂ) := by
  rw [inner_finitePureProjectorEuclidean,
    finitePureStateFidelity_tensorPower]
  norm_cast

/-- The replica-projector identity in the underlying real Hilbert space used by the static
shortcut law. -/
theorem real_inner_finitePureProjectorEuclidean_tensorPower
    (r : ℕ) (ψ φ : α → ℂ) :
    inner ℝ
        (finitePureProjectorEuclidean (finitePureTensorPower r ψ))
        (finitePureProjectorEuclidean (finitePureTensorPower r φ)) =
      finitePureStateFidelity ψ φ ^ r := by
  have hreal (u v : EuclideanSpace ℂ ((Fin r → α) × (Fin r → α))) :
      inner ℝ u v = (inner ℂ u v).re := by
    simp [PiLp.inner_apply, Complex.inner]
  rw [hreal]
  rw [inner_finitePureProjectorEuclidean_tensorPower]
  norm_cast

/-- Uniform observer frame energy of replica projectors is the complete average replica
fidelity, with all target-pair multiplicities retained. -/
theorem finitePreparationFrameEnergy_replicaProjector_eq_averageFidelity
    {C : Type*} [Fintype C] (r : ℕ) (target : C → α → ℂ) :
    finitePreparationFrameEnergy
        (fun c => finitePureProjectorEuclidean
          (finitePureTensorPower r (target c))) =
      ∑ c, ∑ d,
        (Fintype.card C : ℝ)⁻¹ * (Fintype.card C : ℝ)⁻¹ *
          finitePureStateFidelity (target c) (target d) ^ r := by
  rw [finitePreparationFrameEnergy_eq_pairAverage]
  simp_rw [real_inner_finitePureProjectorEuclidean_tensorPower]

/-- Physical replica-projector collisions are nonnegative without an extra sign premise. -/
theorem real_inner_finitePureProjectorEuclidean_tensorPower_nonneg
    (r : ℕ) (ψ φ : α → ℂ) :
    0 ≤ inner ℝ
      (finitePureProjectorEuclidean (finitePureTensorPower r ψ))
      (finitePureProjectorEuclidean (finitePureTensorPower r φ)) := by
  rw [real_inner_finitePureProjectorEuclidean_tensorPower]
  exact pow_nonneg (sq_nonneg ‖finiteComplexInner ψ φ‖) r

end

end GaloisForLFunctions.HTGeometry
