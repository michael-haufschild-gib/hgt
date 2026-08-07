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

section ExteriorOne

variable (R) (M : Type u) [AddCommGroup M] [Module R M]

/-- The class of a vector in the first exterior power, as a linear map. -/
noncomputable def exteriorιₗ : M →ₗ[R] (⋀[R]^1 M) where
  toFun x := exteriorι R x
  map_add' x y := Subtype.ext (by
    show ExteriorAlgebra.ι R (x + y) = ExteriorAlgebra.ι R x + ExteriorAlgebra.ι R y
    rw [map_add])
  map_smul' c x := Subtype.ext (by
    show ExteriorAlgebra.ι R (c • x) = c • ExteriorAlgebra.ι R x
    rw [map_smul])

/-- The first exterior power, back to the module. -/
noncomputable def exteriorOneToBase : (⋀[R]^1 M) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.ofSubsingleton R M M (0 : Fin 1) LinearMap.id)

theorem exteriorOneToBase_ι (x : M) : exteriorOneToBase R M (exteriorιₗ R M x) = x := by
  have hι : (exteriorιₗ R M x : ⋀[R]^1 M) = exteriorPower.ιMulti R 1 (fun _ => x) := by
    refine Subtype.ext ?_
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
    show ExteriorAlgebra.ι R x = ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R 0 _
    rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rw [hι, exteriorOneToBase, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- **The first exterior power is the module itself.** -/
noncomputable def exteriorOneEquiv : (⋀[R]^1 M) ≃ₗ[R] M := by
  refine LinearEquiv.ofLinear (exteriorOneToBase R M) (exteriorιₗ R M) ?_ ?_
  · exact LinearMap.ext fun x => exteriorOneToBase_ι R M x
  · refine exteriorPower.linearMap_ext ?_
    refine AlternatingMap.ext fun v => ?_
    show exteriorιₗ R M (exteriorOneToBase R M (exteriorPower.ιMulti R 1 v)) = _
    have hval : exteriorOneToBase R M (exteriorPower.ιMulti R 1 v) = v 0 := by
      rw [exteriorOneToBase, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      rfl
    rw [hval]
    refine Subtype.ext ?_
    show (ExteriorAlgebra.ι R (v 0) : ExteriorAlgebra R M)
      = ((exteriorPower.ιMulti R 1 v : ⋀[R]^1 M) : ExteriorAlgebra R M)
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]

end ExteriorOne

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

/-- **The Poincaré residue**: the component of a logarithmic form along `d log z`, which is the
bidegree carrying the adjoined generator. -/
noncomputable def logResidue (k : ℕ) :
    TensorCarrier (R := R) X (fun n => ⋀[R]^n R) (k + 1) →ₗ[R] X k :=
  (TensorProduct.rid R (X k)).toLinearMap.comp
    ((TensorProduct.map (LinearMap.id (R := R) (M := X k))
        (exteriorOneEquiv R R).toLinearMap).comp
      (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = k + 1} =>
        TensorProduct R (X q.1.1) (⋀[R]^(q.1.2) R)) ⟨(k, 1), by omega⟩))

/-- **An ordinary form has no residue.**  The inclusion lands in the bidegree with no generator, and
the residue reads a different one. -/
theorem logResidue_inclusion (A : CDGAStructure R X) (k : ℕ) (x : X (k + 1)) :
    logResidue (X := X) k ((logInclusion A).toFun (k + 1) x) = 0 := by
  have hne : (⟨(k, 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = k + 1})
      ≠ ⟨(k + 1, 0), by omega⟩ := by
    intro hEq
    have h1 : ((k, 1) : ℕ × ℕ) = (k + 1, 0) := congrArg Subtype.val hEq
    have h2 : (1 : ℕ) = 0 := congrArg Prod.snd h1
    exact absurd h2 (by omega)
  have hval : (logInclusion A).toFun (k + 1) x
      = tensorSingle (M := X) (N := fun n => ⋀[R]^n R)
        (⟨(k + 1, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = k + 1})
        (x ⊗ₜ[R] (exteriorModuleCDGAUnit R R).one) := rfl
  show (TensorProduct.rid R (X k))
    (TensorProduct.map LinearMap.id (exteriorOneEquiv R R).toLinearMap
      ((logInclusion A).toFun (k + 1) x ⟨(k, 1), by omega⟩)) = 0
  rw [hval, tensorSingle_ne _ hne, map_zero, map_zero]

end LogAlgebra

end GaloisForLFunctions.HTGeometry
