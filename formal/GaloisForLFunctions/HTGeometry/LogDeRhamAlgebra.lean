import GaloisForLFunctions.HTGeometry.CDGATensorAlgebraIncl
import GaloisForLFunctions.HTGeometry.CDGAFreeExterior

/-!
# The logarithmic de Rham algebra of a chart with a smooth divisor

Adjoining to a commutative differential graded algebra one closed generator of degree one whose
square vanishes gives the logarithmic algebra: every element is uniquely `α + ω ∧ β`, which is the
local structure of logarithmic forms along a smooth divisor, with `ω` the class of `d log z`.  The
adjunction is the tensor product with the exterior algebra on a free module of rank one, and it is a
commutative differential graded algebra because that tensor product is.

Above degree one the exterior powers of a rank-one module vanish, so the tensor product has exactly
two nonzero bidegrees in each degree: the ordinary forms and the ones carrying `ω`.  The Poincaré
residue is the projection onto the second.

* `HTGeometry.exteriorPower_rank_one_eq_bot` : `⋀^j R = 0` for `j ≥ 2`.
* `HTGeometry.logCDGA` : the logarithmic algebra.
* `HTGeometry.logCDGAUnit`, `HTGeometry.logInclusion`, `HTGeometry.logDlog` : its unit, the
  inclusion of the ordinary forms, and the class of `d log z`.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct exteriorPower

variable {R : Type u} [CommRing R]

/-- **The exterior powers of a module of rank one vanish above degree one.**  A wedge of two or more
elements of `R` is a multiple of the square of the class of `1`, which is zero. -/
theorem exteriorPower_rank_one_eq_bot (j : ℕ) (hj : 2 ≤ j) : (⋀[R]^j R) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [← exteriorPower.ιMulti_span_fixedDegree (R := R) (n := j) (M := R), Submodule.span_le]
  rintro z ⟨v, rfl⟩
  refine (Submodule.mem_bot R).2 ?_
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply, ← mul_assoc]
  have hsq : ExteriorAlgebra.ι R (v 0) * ExteriorAlgebra.ι R (Matrix.vecTail v 0) = 0 := by
    have h1 : ExteriorAlgebra.ι R (v 0) = (v 0) • ExteriorAlgebra.ι R (1 : R) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    have h2 : ExteriorAlgebra.ι R (Matrix.vecTail v 0)
        = (Matrix.vecTail v 0) • ExteriorAlgebra.ι R (1 : R) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h1, h2, smul_mul_assoc, mul_smul_comm, ExteriorAlgebra.ι_sq_zero, smul_zero, smul_zero]
  rw [hsq, zero_mul]

section LogAlgebra

variable {X : ℕ → Type u} [∀ n, AddCommGroup (X n)] [∀ n, Module R (X n)]

/-- **The logarithmic de Rham algebra**: the algebra with one closed generator of degree one and
vanishing square adjoined, which is the tensor product with the exterior algebra on a free module of
rank one. -/
noncomputable def logCDGA (A : CDGAStructure R X) :
    CDGAStructure R (TensorCarrier (R := R) X (fun n => ⋀[R]^n R)) :=
  tensorCDGA A (exteriorModuleCDGA R R)

/-- The unit of the logarithmic algebra. -/
noncomputable def logCDGAUnit {A : CDGAStructure R X} (u : CDGAUnit A) : CDGAUnit (logCDGA A) :=
  tensorCDGAUnit A (exteriorModuleCDGA R R) u (exteriorModuleCDGAUnit R R)

/-- **The inclusion of the ordinary forms into the logarithmic ones.** -/
noncomputable def logInclusion (A : CDGAStructure R X) : CDGAHom A (logCDGA A) :=
  tensorCDGAInclLeft A (exteriorModuleCDGA R R) (exteriorModuleCDGAUnit R R)

/-- **The class of `d log z`**, the adjoined generator, in degree one. -/
noncomputable def logDlog {A : CDGAStructure R X} (u : CDGAUnit A) :
    TensorCarrier (R := R) X (fun n => ⋀[R]^n R) 1 :=
  (tensorCDGAInclRight A (exteriorModuleCDGA R R) u).toFun 1 (exteriorι R (1 : R))

end LogAlgebra

end GaloisForLFunctions.HTGeometry
