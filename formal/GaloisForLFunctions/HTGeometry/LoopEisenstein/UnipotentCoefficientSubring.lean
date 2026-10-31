import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientMap
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentTriangularMultiplication

/-!
# Subring descent for completed unipotent coefficients

The free stream detects membership of every matrix coefficient in a
subring. Decoding over the subring proves this without an additional
inverse calculation. Triangular corrections commute with ring maps and
therefore preserve every subring.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
noncomputable section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Completed unipotent matrices descending to the given coefficient subring. -/
def unipotentCoefficientSubring (A : Subring R) : Subgroup (unipotentCoefficientGroup R) :=
  (unipotentCoefficientMap A.subtype).range

/-- Descent to a subring is detected exactly by the free stream. -/
theorem mem_unipotentCoefficientSubring (A : Subring R) (g : unipotentCoefficientGroup R) :
    g ∈ unipotentCoefficientSubring A ↔ ∀ n, unipotentCoefficientStreamEquiv R g n ∈ A := by
  constructor
  · rintro ⟨u, rfl⟩ n
    rw [unipotentStream_map]
    exact (unipotentCoefficientStreamEquiv A u n).property
  · intro h
    let x : ℕ → A := fun n => ⟨unipotentCoefficientStreamEquiv R g n, h n⟩
    refine ⟨(unipotentCoefficientStreamEquiv A).symm x, ?_⟩
    apply (unipotentCoefficientStreamEquiv R).injective
    funext n
    rw [unipotentStream_map, Equiv.apply_symm_apply]
    rfl

/-- Integrality of the free stream is equivalent to integrality of all four matrix entries. -/
theorem unipotentStream_mem_subring_iff (A : Subring R) (g : unipotentCoefficientGroup R) :
    (∀ n, unipotentCoefficientStreamEquiv R g n ∈ A) ↔
      ∀ i j n, PowerSeries.coeff n (g.1 i j) ∈ A := by
  constructor
  · intro h
    let x : ℕ → A := fun n => ⟨unipotentCoefficientStreamEquiv R g n, h n⟩
    let u := (unipotentCoefficientStreamEquiv A).symm x
    have he : unipotentCoefficientMap A.subtype u = g := by
      apply (unipotentCoefficientStreamEquiv R).injective
      funext n
      rw [unipotentStream_map]
      change A.subtype (unipotentCoefficientStreamEquiv A
        ((unipotentCoefficientStreamEquiv A).symm x) n) = _
      rw [Equiv.apply_symm_apply]
      rfl
    intro i j n
    rw [← he, unipotentCoefficientMap_apply, PowerSeries.coeff_map]
    exact (PowerSeries.coeff n (u.1 i j)).property
  · intro h n
    change unipotentCoordinatesToStream R (unipotentCoefficientToCoordinates R g) n ∈ A
    unfold unipotentCoordinatesToStream
    split_ifs
    · exact h 0 1 (n / 3)
    · exact h 1 0 (n / 3 + 1)
    · exact h 0 0 (n / 3 + 1)

/-- Completing a stream prefix with zeros commutes with coefficient-ring maps. -/
theorem unipotentPrefixCompletion_map (f : R →+* S) (n : ℕ) (x : Fin n → R) :
    unipotentCoefficientMap f (unipotentPrefixCompletion x) =
      unipotentPrefixCompletion (fun i => f (x i)) := by
  apply (unipotentCoefficientStreamEquiv S).injective
  funext k
  rw [unipotentStream_map]
  simp only [unipotentPrefixCompletion, Equiv.apply_symm_apply]
  split_ifs
  · rfl
  · exact map_zero f

/-- Every nonlinear triangular correction is natural in the coefficient ring. -/
theorem unipotentTriangularCorrection_map (f : R →+* S) (n : ℕ) (x y : Fin n → R) :
    f (unipotentTriangularCorrection n x y) =
      unipotentTriangularCorrection n (fun i => f (x i)) (fun i => f (y i)) := by
  unfold unipotentTriangularCorrection
  rw [← unipotentPrefixCompletion_map f n x, ← unipotentPrefixCompletion_map f n y]
  simp only [unipotentStreamDefect, ← map_mul, unipotentStream_map, map_sub]

/-- A triangular correction of two subring-valued prefixes remains in that subring. -/
theorem unipotentTriangularCorrection_mem_subring (A : Subring R) (n : ℕ) (x y : Fin n → R)
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A) :
    unipotentTriangularCorrection n x y ∈ A := by
  let xA : Fin n → A := fun i => ⟨x i, hx i⟩
  let yA : Fin n → A := fun i => ⟨y i, hy i⟩
  have he := unipotentTriangularCorrection_map A.subtype n xA yA
  change ((unipotentTriangularCorrection n xA yA : A) : R) =
    unipotentTriangularCorrection n x y at he
  rw [← he]
  exact (unipotentTriangularCorrection n xA yA).property

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentStream_mem_subring_iff
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentTriangularCorrection_map
#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.unipotentTriangularCorrection_mem_subring
