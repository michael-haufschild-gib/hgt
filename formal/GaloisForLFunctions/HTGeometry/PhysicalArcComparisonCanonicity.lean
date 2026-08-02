import GaloisForLFunctions.HTGeometry.PhysicalArcCriticalCompletion

/-!
# The arc/incidence comparison is canonical

The bounded incidence space is a commutative `ℂ`-algebra under pointwise multiplication, and the
comparison that evaluates an arc-coordinate polynomial at the regularized period symbol is a
homomorphism of `ℂ`-algebras.  Since the arc-coordinate scale is free on the arc coordinate, the
comparison is the unique algebra map sending `λ` to `w`.

So the choice made in the filtration comparison is not a choice: pointing (`1 ↦ 1`), the powers
`λ^k ↦ w^k` and hence the whole filtration are forced by the single normalization `λ ↦ w`, and the
polarization exponent is the unique fixed point of the source-condition duality.
-/

open Filter
open scoped BigOperators Topology ENNReal

namespace GaloisForLFunctions

noncomputable section

variable {L : Submodule ℤ ℂ}

/-! ## The comparison is an algebra map -/

/-- The arc/incidence comparison as a homomorphism of `ℂ`-algebras. -/
def arcEvalHom (L : Submodule ℤ ℂ) :
    Polynomial ℂ →ₐ[ℂ] lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞ where
  toFun := arcEvalVector L
  map_one' := by
    ext q
    rw [arcEvalVector_apply, Polynomial.eval_one]
    rfl
  map_mul' P Q := by
    ext q
    rw [arcEvalVector_apply, Polynomial.eval_mul]
    rfl
  map_zero' := by
    ext q
    rw [arcEvalVector_apply, Polynomial.eval_zero]
    rfl
  map_add' P Q := by
    ext q
    rw [arcEvalVector_apply, Polynomial.eval_add]
    rfl
  commutes' c := by
    ext q
    rw [arcEvalVector_apply, Polynomial.algebraMap_eq, Polynomial.eval_C]
    rfl

@[simp] theorem arcEvalHom_apply (L : Submodule ℤ ℂ) (P : Polynomial ℂ) :
    arcEvalHom L P = arcEvalVector L P := rfl

/-- **The normalization.**  The comparison sends the arc coordinate to the period symbol. -/
theorem arcEvalHom_X (L : Submodule ℤ ℂ) :
    arcEvalHom L Polynomial.X = periodWeightVector L := by
  ext q
  rw [arcEvalHom_apply, arcEvalVector_apply, Polynomial.eval_X]
  rfl

/-! ## Uniqueness -/

/-- **The comparison is the unique algebra map with that normalization.** -/
theorem arcEvalHom_unique (L : Submodule ℤ ℂ)
    (φ : Polynomial ℂ →ₐ[ℂ] lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞)
    (hφ : φ Polynomial.X = periodWeightVector L) : φ = arcEvalHom L :=
  Polynomial.algHom_ext (by rw [hφ, arcEvalHom_X])

/-- **Canonicity of the physical comparison.**  The single normalization `λ ↦ w` determines the
comparison completely; it is pointed, it carries every arc power to the corresponding powered
period symbol, hence it determines the whole filtration comparison, and the polarization exponent
is the unique fixed point of the source-condition duality. -/
theorem arcEval_canonical (L : Submodule ℤ ℂ) :
    (∀ φ : Polynomial ℂ →ₐ[ℂ] lp (fun _ : NonzeroPeriod L ↦ ℂ) ∞,
        φ Polynomial.X = periodWeightVector L → φ = arcEvalHom L) ∧
      arcEvalHom L 1 = 1 ∧
      (∀ k : ℕ, arcEvalHom L (Polynomial.X ^ k) = poweredPeriodWeightVector L k) ∧
      (∀ α : ℝ, 1 - α = α ↔ α = 1 / 2) :=
  ⟨arcEvalHom_unique L, map_one _,
    fun k => (arcEvalHom_apply L _).trans (arcEvalVector_X_pow L k),
    periodIncidenceFractionalDuality_fixed_iff⟩

/-- **Canonicity of the exact filtration comparison.**  For a nondiscrete period source the unique
normalized algebra map detects the `λ`-adic filtration exactly. -/
theorem arcEvalHom_mem_poweredRange_iff (L : Submodule ℤ ℂ) (hL : ¬ DiscreteTopology L)
    (n : ℕ) (P : Polynomial ℂ) :
    arcEvalHom L P ∈ Set.range (poweredPeriodIncidenceMultiplier L n) ↔
      (Polynomial.X : Polynomial ℂ) ^ n ∣ P :=
  arcEvalVector_mem_poweredRange_iff L hL n P

end

end GaloisForLFunctions
