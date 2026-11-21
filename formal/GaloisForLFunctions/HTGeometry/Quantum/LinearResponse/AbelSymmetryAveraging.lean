import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelCornerSelection
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelResponsePerturbation
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelBohrPolynomials

/-!
# Fixed points and symmetry-averaged measurements

A symmetry fixing the Hamiltonian commutes with its response. Averaging
the observed output makes invariant probes insensitive to the choice
of Hamiltonian within its symmetry orbit.
-/

open Matrix Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι κ G : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Group G] {H : Matrix ι ι ℂ}

/-- The probe's supported frequencies are intrinsic under star-algebra transport. -/
theorem abelProbeBohrGaps_map (e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ)
    (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    abelProbeBohrGaps (isHermitian_map_starAlgEquiv e hH) (e X) = abelProbeBohrGaps hH X := by
  ext g
  rw [mem_abelProbeBohrGaps_iff_gapComponent_ne_zero,
    mem_abelProbeBohrGaps_iff_gapComponent_ne_zero, ← map_hamiltonianGapComponent e hH]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hn h
    apply hn
    rw [h, map_zero]
  · intro hn h
    apply hn
    exact e.injective (h.trans (map_zero e).symm)

variable (A : G →* (Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ))

/-- Matrices fixed by every element of the symmetry representation. -/
def matrixSymmetryFixed : Submodule ℂ (Matrix ι ι ℂ) where
  carrier := {X | ∀ g, A g X = X}
  zero_mem' := fun g => map_zero (A g)
  add_mem' hx hy := fun g => by rw [map_add, hx g, hy g]
  smul_mem' c _ hx := fun g => by rw [map_smul, hx g]

theorem hamiltonianDampedGapResponse_mem_symmetryFixed_iff (hH : H.IsHermitian)
    (hfix : H ∈ matrixSymmetryFixed A) (μ : ℝ) (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    hamiltonianDampedGapResponse hH μ ε X ∈ matrixSymmetryFixed A ↔
      X ∈ matrixSymmetryFixed A := by
  change (∀ g, A g (hamiltonianDampedGapResponse hH μ ε X) =
    hamiltonianDampedGapResponse hH μ ε X) ↔ ∀ g, A g X = X
  have hcov (g : G) := map_hamiltonianDampedGapResponse_of_eq (A g) hH hH
    (hfix g) μ ε X
  exact ⟨fun h g => hamiltonianDampedGapResponse_injective hH μ ε
    ((hcov g).symm.trans (h g)),
    fun h g => (hcov g).trans (congrArg (hamiltonianDampedGapResponse hH μ ε) (h g))⟩

/-- The zero-centered response is a linear equivalence on the fixed submodule. -/
def abelResponseFixedLinearEquiv (hH : H.IsHermitian) (hfix : H ∈ matrixSymmetryFixed A)
    (ε : Ioi (0 : ℝ)) : matrixSymmetryFixed A ≃ₗ[ℂ] matrixSymmetryFixed A where
  toFun X := ⟨hamiltonianDampedGapResponse hH 0 ε X,
    (hamiltonianDampedGapResponse_mem_symmetryFixed_iff A hH hfix 0 ε X).mpr X.property⟩
  invFun X := ⟨hamiltonianAbelInverse H ε X, fun g => by
    change A g (hamiltonianAbelInverse H ε (X : Matrix ι ι ℂ)) =
      hamiltonianAbelInverse H ε (X : Matrix ι ι ℂ)
    simp only [hamiltonianAbelInverse_eq_sub, map_sub, map_mul, map_smul, hfix g, X.property g]⟩
  left_inv X := Subtype.ext (hamiltonianAbelInverse_leftInverse hH ε X)
  right_inv X := Subtype.ext (hamiltonianAbelInverse_rightInverse hH ε X)
  map_add' X Y := Subtype.ext ((abelResponseLinearEquiv hH ε).map_add
    (X : Matrix ι ι ℂ) (Y : Matrix ι ι ℂ))
  map_smul' c X := Subtype.ext ((abelResponseLinearEquiv hH ε).map_smul c (X : Matrix ι ι ℂ))

section Finite

variable [Fintype G]

/-- The finite Reynolds projection on matrix data. -/
def matrixSymmetryAverage : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (A g).toAlgEquiv.toLinearEquiv.toLinearMap

theorem matrixSymmetryAverage_apply (X : Matrix ι ι ℂ) :
    matrixSymmetryAverage A X = (Fintype.card G : ℂ)⁻¹ • ∑ g, A g X := by
  rw [matrixSymmetryAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

theorem matrixSymmetryAverage_mem_fixed (X : Matrix ι ι ℂ) :
    matrixSymmetryAverage A X ∈ matrixSymmetryFixed A := by
  intro h
  change A h (matrixSymmetryAverage A X) = matrixSymmetryAverage A X
  rw [matrixSymmetryAverage_apply, map_smul, map_sum]
  congr 1
  exact Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _
    (fun g => by rw [map_mul, StarAlgEquiv.mul_apply])

theorem matrixSymmetryAverage_action (X : Matrix ι ι ℂ) (h : G) :
    matrixSymmetryAverage A (A h X) = matrixSymmetryAverage A X := by
  rw [matrixSymmetryAverage_apply, matrixSymmetryAverage_apply]
  congr 1
  exact Fintype.sum_bijective (fun g => g * h) (Group.mulRight_bijective h) _ _
    (fun g => by rw [map_mul, StarAlgEquiv.mul_apply])

theorem matrixSymmetryAverage_eq_self_iff (X : Matrix ι ι ℂ) :
    matrixSymmetryAverage A X = X ↔ X ∈ matrixSymmetryFixed A := by
  constructor
  · intro h
    exact h ▸ matrixSymmetryAverage_mem_fixed A X
  · intro hx
    have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [matrixSymmetryAverage_apply, Finset.sum_congr rfl (fun g _ => hx g), Finset.sum_const,
      Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Projection of a reading at a fixed Hamiltonian equals response to
the projected probe. -/
theorem matrixSymmetryAverage_abelResponse (hH : H.IsHermitian) (hfix : H ∈ matrixSymmetryFixed A)
    (ε : Ioi (0 : ℝ)) (X : Matrix ι ι ℂ) :
    matrixSymmetryAverage A (hamiltonianDampedGapResponse hH 0 ε X) =
      hamiltonianDampedGapResponse hH 0 ε (matrixSymmetryAverage A X) := by
  let R := abelResponseLinearEquiv hH ε
  change matrixSymmetryAverage A (R X) = R (matrixSymmetryAverage A X)
  rw [matrixSymmetryAverage_apply, matrixSymmetryAverage_apply, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun g _ =>
    map_hamiltonianDampedGapResponse_of_eq (A g) hH hH (hfix g) 0 ε X

/-- An invariant probe with averaged output identifies the Hamiltonian
at most up to its finite symmetry orbit. -/
theorem matrixSymmetryAverage_response_orbit (hH : H.IsHermitian)
    (μ : ℝ) (ε : Ioi (0 : ℝ)) {X : Matrix ι ι ℂ} (hX : X ∈ matrixSymmetryFixed A) (g : G) :
    matrixSymmetryAverage A
        (hamiltonianDampedGapResponse (isHermitian_map_starAlgEquiv (A g) hH) μ ε X) =
      matrixSymmetryAverage A (hamiltonianDampedGapResponse hH μ ε X) := by
  have hc := map_hamiltonianDampedGapResponse (A g) hH μ ε X
  rw [hX g] at hc
  rw [← hc, matrixSymmetryAverage_action]

/-- Averaging the first variation with an invariant probe retains
exactly the contribution from the averaged Hamiltonian direction. -/
theorem matrixSymmetryAverage_abelVariation (hH : H.IsHermitian)
    (hfix : H ∈ matrixSymmetryFixed A) (ε : Ioi (0 : ℝ))
    (T : Matrix ι ι ℂ) {X : Matrix ι ι ℂ} (hX : X ∈ matrixSymmetryFixed A) :
    matrixSymmetryAverage A (abelResponseVariation hH ε T X) =
      abelResponseVariation hH ε (matrixSymmetryAverage A T) X := by
  let Y := hamiltonianDampedGapResponse hH 0 ε X
  let L := abelResponseVariationLinear hH ε X
  have hY (g : G) : A g Y = Y :=
    (hamiltonianDampedGapResponse_mem_symmetryFixed_iff A hH hfix 0 ε X).mpr hX g
  have hc (g : G) : A g (L T) = L (A g T) := by
    change A g (abelResponseVariation hH ε T X) = abelResponseVariation hH ε (A g T) X
    rw [abelResponseVariation, abelResponseVariation,
      map_hamiltonianDampedGapResponse_of_eq (A g) hH hH (hfix g)]
    congr 1
    change A g ((hamiltonianAbelShift ε)⁻¹ • (T * Y - Y * T)) =
      (hamiltonianAbelShift ε)⁻¹ • (A g T * Y - Y * A g T)
    simp only [map_smul, map_sub, map_mul, hY g]
  change matrixSymmetryAverage A (L T) = L (matrixSymmetryAverage A T)
  rw [matrixSymmetryAverage_apply, matrixSymmetryAverage_apply, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun g _ => hc g

theorem matrixSymmetryAverage_abelVariation_eq_zero_of_average_eq_zero (hH : H.IsHermitian)
    (hfix : H ∈ matrixSymmetryFixed A) (ε : Ioi (0 : ℝ))
    (T : Matrix ι ι ℂ) {X : Matrix ι ι ℂ} (hX : X ∈ matrixSymmetryFixed A)
    (hT : matrixSymmetryAverage A T = 0) :
    matrixSymmetryAverage A (abelResponseVariation hH ε T X) = 0 := by
  rw [matrixSymmetryAverage_abelVariation A hH hfix ε T hX, hT,
    ← abelResponseVariationLinear_apply, map_zero]

end Finite

#print axioms abelProbeBohrGaps_map
#print axioms abelResponseFixedLinearEquiv
#print axioms matrixSymmetryAverage_response_orbit
#print axioms matrixSymmetryAverage_abelVariation

end

end GaloisForLFunctions.HTGeometry
