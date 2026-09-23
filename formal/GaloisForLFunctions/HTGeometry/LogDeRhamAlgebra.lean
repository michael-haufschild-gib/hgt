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

/-- The exterior powers of a rank-one module are trivial above degree one. -/
theorem exteriorPower_rank_one_subsingleton (j : ℕ) (hj : 2 ≤ j) :
    Subsingleton (⋀[R]^j R) := by
  rw [exteriorPower_rank_one_eq_bot j hj]
  infer_instance

/-- A tensor product with a trivial second factor is trivial. -/
theorem tensorProduct_eq_zero_of_subsingleton_right {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] (z : TensorProduct R M N) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul x y => rw [Subsingleton.elim y (0 : N), TensorProduct.tmul_zero]
  | add a b ha hb => rw [ha, hb, add_zero]

section ExteriorOne

variable (R) (M : Type u) [AddCommGroup M] [Module R M]

/-- The class of a vector in the first exterior power, as a linear map. -/
noncomputable def exteriorιₗ : M →ₗ[R] (⋀[R]^(1 : ℕ) M) where
  toFun x := exteriorι R x
  map_add' x y := Subtype.ext (by
    show ExteriorAlgebra.ι R (x + y) = ExteriorAlgebra.ι R x + ExteriorAlgebra.ι R y
    rw [map_add])
  map_smul' c x := Subtype.ext (by
    show ExteriorAlgebra.ι R (c • x) = c • ExteriorAlgebra.ι R x
    rw [map_smul])

/-- The first exterior power, back to the module. -/
noncomputable def exteriorOneToBase : (⋀[R]^(1 : ℕ) M) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.ofSubsingleton R M M (0 : Fin 1) LinearMap.id)

theorem exteriorOneToBase_ι (x : M) : exteriorOneToBase R M (exteriorιₗ R M x) = x := by
  have hι : (exteriorιₗ R M x : ⋀[R]^(1 : ℕ) M) = exteriorPower.ιMulti R 1 (fun _ => x) := by
    refine Subtype.ext ?_
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply]
    show ExteriorAlgebra.ι R x = ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R 0 _
    rw [ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  rw [hι, exteriorOneToBase, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- **The first exterior power is the module itself.** -/
noncomputable def exteriorOneEquiv : (⋀[R]^(1 : ℕ) M) ≃ₗ[R] M := by
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
      = ((exteriorPower.ιMulti R 1 v : ⋀[R]^(1 : ℕ) M) : ExteriorAlgebra R M)
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_succ_apply,
      ExteriorAlgebra.ιMulti_zero_apply, mul_one]

/-- The unit of the zeroth exterior power. -/
def exteriorZeroOne : (⋀[R]^(0 : ℕ) M) := ⟨1, SetLike.one_mem_graded _⟩

/-- The zeroth exterior power, to the ring. -/
noncomputable def exteriorZeroToBase : (⋀[R]^(0 : ℕ) M) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.constOfIsEmpty R M (Fin 0) (1 : R))

theorem exteriorZeroOne_eq_ιMulti (v : Fin 0 → M) :
    exteriorZeroOne R M = exteriorPower.ιMulti R 0 v := by
  refine Subtype.ext ?_
  rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
  rfl

theorem exteriorZeroToBase_one : exteriorZeroToBase R M (exteriorZeroOne R M) = 1 := by
  rw [exteriorZeroOne_eq_ιMulti R M (fun i => i.elim0), exteriorZeroToBase,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- **Every element of the zeroth exterior power is a multiple of the unit.** -/
theorem exteriorZero_eq_smul_one (z : ⋀[R]^(0 : ℕ) M) :
    z = exteriorZeroToBase R M z • exteriorZeroOne R M := by
  have hmem : z ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 0 (M := M))) := by
    rw [exteriorPower.ιMulti_span R 0 M]
    trivial
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
  · rintro y ⟨v, rfl⟩
    rw [← exteriorZeroOne_eq_ιMulti R M v, exteriorZeroToBase_one, one_smul]
  · rw [map_zero, zero_smul]
  · intro y y' _ _ hy hy'
    rw [map_add, add_smul, ← hy, ← hy']
  · intro c y _ hy
    rw [map_smul, smul_assoc, ← hy]

/-- **The zeroth exterior power is the ring.** -/
noncomputable def exteriorZeroEquiv : (⋀[R]^(0 : ℕ) M) ≃ₗ[R] R := by
  refine LinearEquiv.ofLinear (exteriorZeroToBase R M)
    ((LinearMap.id (R := R) (M := R)).smulRight (exteriorZeroOne R M)) ?_ ?_
  · refine LinearMap.ext fun r => ?_
    show exteriorZeroToBase R M (r • exteriorZeroOne R M) = r
    rw [map_smul, exteriorZeroToBase_one, smul_eq_mul, mul_one]
  · refine LinearMap.ext fun z => ?_
    exact (exteriorZero_eq_smul_one R M z).symm

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

/-- **A logarithmic form has only two nonzero bidegrees.**  Every component whose exterior degree is
at least two vanishes, because the exterior powers of a rank-one module do. -/
theorem logCarrier_high_eq_zero {n : ℕ}
    (F : TensorCarrier (R := R) X (fun m => ⋀[R]^m R) n)
    (p : {ab : ℕ × ℕ // ab.1 + ab.2 = n}) (hp : 2 ≤ p.1.2) : F p = 0 := by
  haveI := exteriorPower_rank_one_subsingleton (R := R) p.1.2 hp
  exact tensorProduct_eq_zero_of_subsingleton_right (F p)

/-- **The residue is onto.**  The form `x ∧ d log z` has residue `x`. -/
theorem logResidue_surjective (k : ℕ) : Function.Surjective (logResidue (R := R) (X := X) k) := by
  intro x
  refine ⟨tensorSingle (M := X) (N := fun n => ⋀[R]^n R)
    (⟨(k, 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = k + 1})
    (x ⊗ₜ[R] exteriorιₗ R R (1 : R)), ?_⟩
  show (TensorProduct.rid R (X k))
    (TensorProduct.map LinearMap.id (exteriorOneEquiv R R).toLinearMap
      (tensorSingle (M := X) (N := fun n => ⋀[R]^n R)
        (⟨(k, 1), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = k + 1})
        (x ⊗ₜ[R] exteriorιₗ R R (1 : R)) ⟨(k, 1), by omega⟩)) = x
  rw [tensorSingle_same]
  show (TensorProduct.rid R (X k)) (x ⊗ₜ[R] (exteriorOneEquiv R R) (exteriorιₗ R R (1 : R))) = x
  have hone : (exteriorOneEquiv R R) (exteriorιₗ R R (1 : R)) = (1 : R) :=
    exteriorOneToBase_ι R R (1 : R)
  rw [hone, TensorProduct.rid_tmul, one_smul]

/-- The bidegree the residue reads, as an isomorphism. -/
noncomputable def logResidueEquiv (k : ℕ) :
    TensorProduct R (X k) (⋀[R]^(1 : ℕ) R) ≃ₗ[R] X k :=
  (TensorProduct.congr (LinearEquiv.refl R (X k)) (exteriorOneEquiv R R)).trans
    (TensorProduct.rid R (X k))

theorem logResidue_eq_equiv (k : ℕ)
    (F : TensorCarrier (R := R) X (fun n => ⋀[R]^n R) (k + 1)) :
    logResidue (X := X) k F
      = logResidueEquiv (X := X) k (F ⟨(k, 1), by omega⟩) := rfl

/-- The bidegree of the ordinary forms, as an isomorphism. -/
noncomputable def logZeroEquiv (k : ℕ) :
    TensorProduct R (X (k + 1)) (⋀[R]^(0 : ℕ) R) ≃ₗ[R] X (k + 1) :=
  (TensorProduct.congr (LinearEquiv.refl R (X (k + 1))) (exteriorZeroEquiv R R)).trans
    (TensorProduct.rid R (X (k + 1)))

theorem logZeroEquiv_symm (k : ℕ) (x : X (k + 1)) :
    (logZeroEquiv (X := X) k).symm x = x ⊗ₜ[R] exteriorZeroOne R R := by
  refine (logZeroEquiv (X := X) k).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  show x = (TensorProduct.rid R (X (k + 1)))
    (TensorProduct.congr (LinearEquiv.refl R (X (k + 1))) (exteriorZeroEquiv R R)
      (x ⊗ₜ[R] exteriorZeroOne R R))
  rw [TensorProduct.congr_tmul]
  show x = (TensorProduct.rid R (X (k + 1)))
    (x ⊗ₜ[R] exteriorZeroToBase R R (exteriorZeroOne R R))
  rw [exteriorZeroToBase_one, TensorProduct.rid_tmul, one_smul]

/-- **A logarithmic form with no residue is an ordinary form**, and conversely.  This is exactness of
the residue sequence: a form is supported in the two bidegrees, and vanishing of the one carrying the
generator leaves only the ordinary one. -/
theorem logResidue_eq_zero_iff (A : CDGAStructure R X) (k : ℕ)
    (F : TensorCarrier (R := R) X (fun n => ⋀[R]^n R) (k + 1)) :
    logResidue (X := X) k F = 0 ↔ ∃ x : X (k + 1), F = (logInclusion A).toFun (k + 1) x := by
  constructor
  · intro hres
    have h1 : F ⟨(k, 1), by omega⟩ = 0 := by
      refine (logResidueEquiv (X := X) k).injective ?_
      rw [map_zero, ← logResidue_eq_equiv]
      exact hres
    refine ⟨logZeroEquiv (X := X) k (F ⟨(k + 1, 0), by omega⟩), ?_⟩
    funext q
    obtain ⟨⟨qa, qb⟩, hq⟩ := q
    have hval : (logInclusion A).toFun (k + 1)
        (logZeroEquiv (X := X) k (F ⟨(k + 1, 0), by omega⟩))
        = tensorSingle (M := X) (N := fun n => ⋀[R]^n R)
          (⟨(k + 1, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = k + 1})
          (F ⟨(k + 1, 0), by omega⟩) := by
      show tensorSingle (M := X) (N := fun n => ⋀[R]^n R)
        (⟨(k + 1, 0), by omega⟩ : {ab : ℕ × ℕ // ab.1 + ab.2 = k + 1})
        (logZeroEquiv (X := X) k (F ⟨(k + 1, 0), by omega⟩)
          ⊗ₜ[R] (exteriorModuleCDGAUnit R R).one) = _
      refine congrArg (tensorSingle _) ?_
      have := logZeroEquiv_symm (R := R) (X := X) k
        (logZeroEquiv (X := X) k (F ⟨(k + 1, 0), by omega⟩))
      rw [LinearEquiv.symm_apply_apply] at this
      exact this.symm
    rw [hval]
    rcases qb with _ | qb'
    · have hqa : qa = k + 1 := by omega
      subst hqa
      rw [tensorSingle_same]
    · rcases qb' with _ | b
      · have hqa : qa = k := by omega
        subst hqa
        rw [h1]
        refine (tensorSingle_ne (M := X) (N := fun n => ⋀[R]^n R) _ ?_).symm
        intro hEq
        have h2 : ((qa, 1) : ℕ × ℕ) = (qa + 1, 0) := congrArg Subtype.val hEq
        have h3 : (1 : ℕ) = 0 := congrArg Prod.snd h2
        exact absurd h3 (by omega)
      · rw [logCarrier_high_eq_zero F ⟨(qa, b + 1 + 1), hq⟩ (show 2 ≤ b + 1 + 1 by omega)]
        refine (tensorSingle_ne (M := X) (N := fun n => ⋀[R]^n R) _ ?_).symm
        intro hEq
        have h2 : ((qa, b + 1 + 1) : ℕ × ℕ) = (k + 1, 0) := congrArg Subtype.val hEq
        have h3 : b + 1 + 1 = 0 := congrArg Prod.snd h2
        exact absurd h3 (by omega)
  · rintro ⟨x, rfl⟩
    exact logResidue_inclusion A k x

/-- The residue commutes with the differential through the bidegree it reads. -/
theorem logResidueEquiv_map_d (A : CDGAStructure R X) (k : ℕ)
    (z : TensorProduct R (X k) (⋀[R]^(1 : ℕ) R)) :
    logResidueEquiv (X := X) (k + 1) (TensorProduct.map (A.dₗ k) LinearMap.id z)
      = A.d k (logResidueEquiv (X := X) k z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero, map_zero, map_zero]
      exact ((A.dₗ k).map_zero).symm
  | tmul x w =>
      show (TensorProduct.rid R (X (k + 1)))
        (TensorProduct.congr (LinearEquiv.refl R (X (k + 1))) (exteriorOneEquiv R R)
          (A.d k x ⊗ₜ[R] w)) = _
      rw [TensorProduct.congr_tmul, TensorProduct.rid_tmul]
      show ((exteriorOneEquiv R R) w) • A.d k x
        = A.d k ((TensorProduct.rid R (X k))
          (TensorProduct.congr (LinearEquiv.refl R (X k)) (exteriorOneEquiv R R) (x ⊗ₜ[R] w)))
      rw [TensorProduct.congr_tmul, TensorProduct.rid_tmul]
      exact (A.d_smul k ((exteriorOneEquiv R R) w) x).symm
  | add z z' hz hz' =>
      rw [map_add, map_add, hz, hz', map_add, A.d_add]

/-- **The residue commutes with the differential.**  The logarithmic differential has no component
differentiating the adjoined generator, because that generator is closed, so the residue is a
morphism of complexes. -/
theorem logResidue_d (A : CDGAStructure R X) (k : ℕ)
    (F : TensorCarrier (R := R) X (fun n => ⋀[R]^n R) (k + 1)) :
    logResidue (X := X) (k + 1) ((logCDGA A).d (k + 1) F)
      = A.d k (logResidue (X := X) k F) := by
  have hcomp : ((logCDGA A).d (k + 1) F) ⟨(k + 1, 1), by omega⟩
      = TensorProduct.map (A.dₗ k) LinearMap.id (F ⟨(k, 1), by omega⟩) := by
    show (tensorDL (CDGAStructure.selfModule A)
            (zeroActModule (A := A) (exteriorModuleCDGA R R)) (k + 1) F
          + tensorDR (CDGAStructure.selfModule A)
            (zeroActModule (A := A) (exteriorModuleCDGA R R)) (k + 1) F)
        ⟨(k + 1, 1), by omega⟩ = _
    rw [tensorCarrier_add_apply, tensorDL_succ, tensorDR_succ]
    have hzero : (zeroActModule (A := A) (exteriorModuleCDGA R R)).dₗ 0
        = (0 : (⋀[R]^(0 : ℕ) R) →ₗ[R] (⋀[R]^(1 : ℕ) R)) := by
      refine LinearMap.ext fun w => ?_
      rfl
    rw [hzero]
    show TensorProduct.map (A.dₗ k) LinearMap.id (F ⟨(k, 1), by omega⟩)
      + ((-1 : R)) ^ (k + 1) • TensorProduct.map LinearMap.id
        (0 : (⋀[R]^(0 : ℕ) R) →ₗ[R] (⋀[R]^(1 : ℕ) R)) (F ⟨(k + 1, 0), by omega⟩) = _
    rw [TensorProduct.map_zero_right, LinearMap.zero_apply, smul_zero, add_zero]
  rw [logResidue_eq_equiv, hcomp, logResidueEquiv_map_d, ← logResidue_eq_equiv]

end LogAlgebra

end GaloisForLFunctions.HTGeometry
