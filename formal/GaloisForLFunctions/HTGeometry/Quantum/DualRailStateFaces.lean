import GaloisForLFunctions.HTGeometry.Quantum.CoordinateStateEmbedding

/-!
# Qubits as the single-occupation face of two-orbital states

The occupation basis of two fermionic modes per site is `σ → Bool × Bool`.
Encoding a qubit bit as `(b, !b)` identifies qubit states with exactly the
positive states killed by every local occupation defect. This gives an explicit
state embedding and its inverse compression, rather than an assumed encoding.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.Quantum

open Matrix _root_.HTGeometry.ConstraintRelativity
open scoped ComplexOrder

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- One occupied orbital per site, chosen by the qubit bit. -/
def dualRailBasis : (σ → Bool) ↪ (σ → Bool × Bool) where
  toFun b := fun s => (b s, !(b s))
  inj' := by
    intro b c h
    exact funext fun s => congrArg (fun x => (x s).1) h

/-- The physical occupation configurations. -/
def SingleOccupation (x : σ → Bool × Bool) : Prop :=
  ∀ s, (x s).2 = !(x s).1

omit [Fintype σ] [DecidableEq σ] in
theorem mem_range_dualRailBasis (x : σ → Bool × Bool) :
    x ∈ Set.range (dualRailBasis (σ := σ)) ↔ SingleOccupation x := by
  constructor
  · rintro ⟨b, rfl⟩ s
    rfl
  · intro h
    refine ⟨fun s => (x s).1, ?_⟩
    funext s
    exact Prod.ext rfl (h s).symm

/-- The signed departure of a site occupation from one. -/
def occupationDefectValue (s : σ) (x : σ → Bool × Bool) : ℂ :=
  (if (x s).1 then 1 else 0) + (if (x s).2 then 1 else 0) - 1

omit [Fintype σ] [DecidableEq σ] in
theorem occupationDefectValue_eq_zero_iff (s : σ) (x : σ → Bool × Bool) :
    occupationDefectValue s x = 0 ↔ (x s).2 = !(x s).1 := by
  unfold occupationDefectValue
  cases h₁ : (x s).1 <;> cases h₂ : (x s).2 <;> simp

/-- Local number minus one, in the occupation basis. -/
def occupationDefect (s : σ) : Matrix (σ → Bool × Bool) (σ → Bool × Bool) ℂ :=
  Matrix.diagonal (occupationDefectValue s)

/-- The joint occupation equations select precisely the dual-rail coordinate sector. -/
theorem occupation_constraints_iff_projection
    (ρ : Matrix (σ → Bool × Bool) (σ → Bool × Bool) ℂ) :
    (∀ s, occupationDefect s * ρ = 0) ↔ coordinateProjection dualRailBasis * ρ = ρ := by
  classical
  rw [coordinateProjection_eq_diagonal]
  simp only [mem_range_dualRailBasis]
  constructor
  · intro h
    ext x y
    rw [Matrix.diagonal_mul]
    by_cases hx : SingleOccupation x
    · simp [hx]
    · obtain ⟨s, hs⟩ := not_forall.mp hx
      have hn : occupationDefectValue s x ≠ 0 :=
        mt (occupationDefectValue_eq_zero_iff s x).mp hs
      have hz := congrFun (congrFun (h s) x) y
      change (Matrix.diagonal (occupationDefectValue s) * ρ) x y = 0 at hz
      rw [Matrix.diagonal_mul] at hz
      have hxy := (mul_eq_zero.mp hz).resolve_left hn
      simp [hx, hxy]
  · intro h s
    ext x y
    change (Matrix.diagonal (occupationDefectValue s) * ρ) x y = 0
    rw [Matrix.diagonal_mul]
    by_cases hx : SingleOccupation x
    · rw [(occupationDefectValue_eq_zero_iff s x).mpr (hx s), zero_mul]
    · have hz := congrFun (congrFun h x) y
      rw [Matrix.diagonal_mul] at hz
      have hxy : ρ x y = 0 := by simpa [hx] using hz.symm
      rw [hxy, mul_zero]

/-- Exact state correspondence: the variance-selected face consists of encoded qubit states. -/
theorem dualRail_state_iff_zero_occupation_energy
    (ρ : DensityMatrix (σ → Bool × Bool)) :
    (∃ τ : DensityMatrix (σ → Bool), embedDensity dualRailBasis τ = ρ) ↔
      (constraintHamiltonian (occupationDefect (σ := σ)) * ρ.1).trace.re = 0 := by
  rw [exists_embedDensity_iff, trace_constraintHamiltonian_eq_zero_iff _ ρ.2.1,
    occupation_constraints_iff_projection]

/-- Encoding is a bijection onto the single-occupation face, including arbitrary mixed states. -/
theorem dualRail_unique_state_iff_zero_occupation_energy
    (ρ : DensityMatrix (σ → Bool × Bool)) :
    (∃! τ : DensityMatrix (σ → Bool), embedDensity dualRailBasis τ = ρ) ↔
      (constraintHamiltonian (occupationDefect (σ := σ)) * ρ.1).trace.re = 0 := by
  rw [← dualRail_state_iff_zero_occupation_energy]
  constructor
  · rintro ⟨τ, hτ, _⟩
    exact ⟨τ, hτ⟩
  · rintro ⟨τ, hτ⟩
    exact ⟨τ, hτ, fun υ hυ => embedDensity_injective dualRailBasis (hυ.trans hτ.symm)⟩

/-- The exact encoded state set is exposed by the sum of local occupation variances. -/
theorem dualRail_isExposed :
    IsExposed ℝ
      {ρ : Matrix (σ → Bool × Bool) (σ → Bool × Bool) ℂ |
        ρ.trace = 1 ∧ ρ.PosSemidef}
      (constraintFace (occupationDefect (σ := σ)) {ρ | ρ.trace = 1}) :=
  constraintFace_isExposed _ _

end GaloisForLFunctions.HTGeometry.Quantum
