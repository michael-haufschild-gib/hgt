import GaloisForLFunctions.HTGeometry.StabilizerTwoDesign
import GaloisForLFunctions.HTGeometry.PureStateReplicaProjectiveGramLaw

/-!
# Spectral collision and its unitary covariance

The spectral collision of a state in an orthonormal family is the sum of the squared occupation
weights.  Conjugating the family by a unitary is the same as applying the inverse unitary to the
state, because the coordinate inner product moves the conjugate transpose across.

Consequently the collision of a fixed state in the eigenbasis of a conjugated Hamiltonian equals the
collision of the rotated state in the original eigenbasis, which is what turns the stabilizer
two-design bound into a statement about one fixed input and a Clifford-invariant ensemble.
-/

open Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section Collision

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]

/-- The spectral collision of a state in an orthonormal family. -/
def spectralCollision (e : D → α → ℂ) (ψ : α → ℂ) : ℝ :=
  ∑ j, finitePureStateFidelity (e j) ψ ^ 2

theorem spectralCollision_nonneg (e : D → α → ℂ) (ψ : α → ℂ) :
    0 ≤ spectralCollision e ψ :=
  Finset.sum_nonneg fun j _ => by positivity

/-- The coordinate inner product moves a conjugate transpose across. -/
theorem finiteComplexInner_conjTranspose_mulVec (U : Matrix α α ℂ) (u v : α → ℂ) :
    finiteComplexInner (Uᴴ *ᵥ u) v = finiteComplexInner u (U *ᵥ v) := by
  classical
  have hL : ∀ x : α, (Uᴴ *ᵥ u) x = ∑ y, (starRingEnd ℂ) (U y x) * u y := by
    intro x
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  have hR : ∀ y : α, (U *ᵥ v) y = ∑ x, U y x * v x := by
    intro y
    simp [Matrix.mulVec, dotProduct]
  rw [finiteComplexInner, finiteComplexInner]
  simp_rw [hL, hR, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- **Unitary covariance of the spectral collision.**  Rotating the orthonormal family by the
adjoint is the same as rotating the state. -/
theorem spectralCollision_conjTranspose_mulVec (U : Matrix α α ℂ) (e : D → α → ℂ) (ψ : α → ℂ) :
    spectralCollision (fun j => Uᴴ *ᵥ e j) ψ = spectralCollision e (U *ᵥ ψ) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [finitePureStateFidelity, finitePureStateFidelity,
    finiteComplexInner_conjTranspose_mulVec U (e j) ψ]

end Collision

section StabilizerBound

variable {n : ℕ}

/-- The stabilizer two-design bound, stated for the spectral collision. -/
theorem sum_spectralCollision_prodStab_le (s : ℂ) (hs : s * s = 1 / 2)
    (hsc : (starRingEnd ℂ) s = s) {D : Type*} [Fintype D]
    (e : D → (Fin n → Fin 2) → ℂ) (he : ∀ j, ∑ b, ‖e j b‖ ^ 2 = 1) :
    (∑ σ : Fin n → Fin 6, spectralCollision e (prodStabAmp s σ)) ≤
      (Fintype.card D : ℝ) * 2 ^ n := by
  have hrw : ∀ σ : Fin n → Fin 6, spectralCollision e (prodStabAmp s σ) =
      ∑ j : D, ‖∑ b, (starRingEnd ℂ) (e j b) * prodStabAmp s σ b‖ ^ 4 := by
    intro σ
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finitePureStateFidelity, ← pow_mul, finiteComplexInner]
  rw [Finset.sum_congr rfl fun σ _ => hrw σ]
  exact sum_collision_le s hs hsc e he

end StabilizerBound

end GaloisForLFunctions.HTGeometry
