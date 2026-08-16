import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import GaloisForLFunctions.HTGeometry.OperatorSquareNormBound

/-!
# The defect-slope normal form

On a one-dimensional differential module a single nonzero defect determines every other one: there
is exactly one slope `ρ` with `ε₂ = ρ ε₁`.  That is the whole of the normal-form construction; the
one-dimensionality is the geometric input and the nonvanishing is the defect-lattice input.

The accompanying regulator identity is branch bookkeeping.  Integrating `d log Y - dX` from `q` to
`p` gives `(L p - L q) - (X p - X q)` for the chosen logarithm branch `L`.  When the endpoint
satisfies `Y p = exp (X p)` the transcendental endpoint coordinate cancels and only the algebraic
base point survives, up to the branch integer:

`∫ = X q - L q + 2πi k`.
-/

open Module

namespace GaloisForLFunctions.HTGeometry

/-! ## The slope is unique -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- **The defect slope exists and is unique.**  On a one-dimensional module a nonzero element is a
basis, so every element is a unique multiple of it. -/
theorem existsUnique_defectSlope (hrank : finrank K V = 1) {ε₁ : V} (hε : ε₁ ≠ 0) (ε₂ : V) :
    ∃! ρ : K, ε₂ = ρ • ε₁ := by
  have hspan : (K ∙ ε₁) = ⊤ := (finrank_eq_one_iff_of_nonzero ε₁ hε).mp hrank
  have hmem : ε₂ ∈ (K ∙ ε₁) := by rw [hspan]; exact Submodule.mem_top
  obtain ⟨ρ, hρ⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨ρ, hρ.symm, fun σ hσ => ?_⟩
  have hzero : (σ - ρ) • ε₁ = 0 := by
    rw [sub_smul, ← hσ, hρ, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hε

/-- The slope of a nonzero defect against itself is one. -/
theorem defectSlope_self (hrank : finrank K V = 1) {ε₁ : V} (hε : ε₁ ≠ 0) :
    (existsUnique_defectSlope hrank hε ε₁).choose = 1 := by
  have h := (existsUnique_defectSlope hrank hε ε₁).choose_spec
  exact (h.2 1 (one_smul K ε₁).symm).symm

/-! ## The regulator identity -/

/-- **The regulator identity.**  If the endpoint value is the exponential of the endpoint
coordinate, then the endpoint coordinate cancels from `(L p - L q) - (X p - X q)` and only the base
point survives, up to a branch integer. -/
theorem regulator_eq_base_add_branch {Xp Xq Lp Lq : ℂ}
    (hbranch : Complex.exp Lp = Complex.exp Xp) :
    ∃ k : ℤ, (Lp - Lq) - (Xp - Xq) = Xq - Lq + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hbranch
  refine ⟨k, ?_⟩
  rw [hk]
  ring

/-- The branch integer is the only freedom: two logarithm branches at the same endpoint give
regulator values differing by an integer multiple of `2πi`. -/
theorem regulator_branch_difference {Lp Lp' Xq Lq Xp : ℂ}
    (h : Complex.exp Lp = Complex.exp Lp') :
    ∃ k : ℤ, ((Lp - Lq) - (Xp - Xq)) - ((Lp' - Lq) - (Xp - Xq))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨k, ?_⟩
  rw [hk]
  ring

end GaloisForLFunctions.HTGeometry
