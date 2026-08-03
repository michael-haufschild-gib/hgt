import GaloisForLFunctions.HTGeometry.FreeDifferentialFamilyScale
import GaloisForLFunctions.HTGeometry.DifferentialIndependentLinearForms
import GaloisForLFunctions.HTGeometry.DifferentialAdjoinScale

/-!
# Constant linear actions on a freely generated differential palette

An invertible matrix of constants recombines a freely generating differentially independent
palette into another one generating the same field, so it extends uniquely to a differential
automorphism.  The assignment is multiplicative up to order, so inverting it turns the invertible
matrices into a group of differential automorphisms.

This is the representation-level input for tail theorems: the differential field of a generic
vector, its finite linear symmetry group, and the induced linear endomorphism are the only data
that survive.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Matrix

noncomputable section

variable {F K L ι : Type*} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra F L] [Differential F] [Differential K] [Differential L]
  [DifferentialAlgebra F K] [DifferentialAlgebra F L] [Fintype ι] [DecidableEq ι]

section Recombination

omit [Differential F] [Differential K] [DifferentialAlgebra F K] in
@[simp]
theorem matrixLinearForms_one (x : ι → K) :
    matrixLinearForms (1 : Matrix ι ι F) x = x := by
  funext i
  rw [matrixLinearForms]
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, map_one, one_mul]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [Differential F] [Differential K] [DifferentialAlgebra F K] [DecidableEq ι] in
theorem matrixLinearForms_mul (M N : Matrix ι ι F) (x : ι → K) :
    matrixLinearForms (M * N) x = matrixLinearForms M (matrixLinearForms N x) := by
  funext i
  rw [matrixLinearForms, matrixLinearForms]
  have hright : ∀ k : ι, algebraMap F K (M i k) * matrixLinearForms N x k
      = ∑ j, algebraMap F K (M i k) * (algebraMap F K (N k j) * x j) := by
    intro k
    rw [matrixLinearForms, Finset.mul_sum]
  simp only [hright]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, mul_assoc]

omit [DecidableEq ι] in
/-- A linear recombination of a palette lives in the field the palette generates. -/
theorem differentialAdjoin_range_matrixLinearForms_le (M : Matrix ι ι F) (x : ι → K) :
    differentialAdjoin F (Set.range (matrixLinearForms M x))
      ≤ differentialAdjoin F (Set.range x) := by
  refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F (Set.range x))
  rintro _ ⟨i, rfl⟩
  refine sum_mem fun j _ => ?_
  exact (differentialAdjoin F (Set.range x)).mul_mem
    ((differentialAdjoin F (Set.range x)).algebraMap_mem (M i j))
    (subset_differentialAdjoin F (Set.range x) (Set.mem_range_self j))

/-- **An invertible constant recombination generates the same differential field.** -/
theorem differentialAdjoin_range_matrixLinearForms_eq {M N : Matrix ι ι F} (hNM : N * M = 1)
    (x : ι → K) :
    differentialAdjoin F (Set.range (matrixLinearForms M x))
      = differentialAdjoin F (Set.range x) := by
  refine le_antisymm (differentialAdjoin_range_matrixLinearForms_le M x) ?_
  have hx : matrixLinearForms N (matrixLinearForms M x) = x := by
    rw [← matrixLinearForms_mul, hNM, matrixLinearForms_one]
  calc differentialAdjoin F (Set.range x)
      = differentialAdjoin F (Set.range (matrixLinearForms N (matrixLinearForms M x))) := by
        rw [hx]
    _ ≤ differentialAdjoin F (Set.range (matrixLinearForms M x)) :=
        differentialAdjoin_range_matrixLinearForms_le N _

omit [Differential F] [DifferentialAlgebra F K] [Fintype ι] [DecidableEq ι] in
/-- Two differential automorphisms of a freely generated field agreeing on the palette are
equal. -/
theorem tailEquiv_ext (x : ι → K) (hgen : differentialAdjoin F (Set.range x) = ⊤)
    {f g : K ≃ₐ[F] K} (hf : ∀ z, f z′ = (f z)′) (hg : ∀ z, g z′ = (g z)′)
    (hfg : ∀ i, f (x i) = g (x i)) : f = g := by
  have h : f.toAlgHom = g.toAlgHom :=
    differentialAlgHom_ext_of_differentialAdjoin_eq_top x hgen f.toAlgHom g.toAlgHom
      (fun z => hf z) (fun z => hg z) (fun i => hfg i)
  exact AlgEquiv.ext fun z => AlgHom.congr_fun h z

end Recombination

section TailAut

variable (x : ι → K) (hx : DifferentialIndependent F x)
  (hgen : differentialAdjoin F (Set.range x) = ⊤) (hconst : ∀ c : F, c′ = 0)

theorem algebraMap_deriv_eq_zero (hconst : ∀ c : F, c′ = 0) (c : F) :
    (algebraMap F K c)′ = 0 := by
  rw [deriv_algebraMap, hconst, map_zero]

include hx hconst in
theorem differentialIndependent_matrixLinearForms_units (M : (Matrix ι ι F)ˣ) :
    DifferentialIndependent F (matrixLinearForms (M : Matrix ι ι F) x) :=
  differentialIndependent_matrixLinearForms_of_mul_eq_one
    (algebraMap_deriv_eq_zero (K := K) hconst) (M : Matrix ι ι F) (↑M⁻¹ : Matrix ι ι F)
    (by exact_mod_cast M.mul_inv) x hx

include hgen in
theorem differentialAdjoin_range_matrixLinearForms_units_eq_top (M : (Matrix ι ι F)ˣ) :
    differentialAdjoin F (Set.range (matrixLinearForms (M : Matrix ι ι F) x)) = ⊤ := by
  rw [differentialAdjoin_range_matrixLinearForms_eq
    (N := (↑M⁻¹ : Matrix ι ι F)) (by exact_mod_cast M.inv_mul) x, hgen]

/-- The differential automorphism recombining a freely generating palette by an invertible
constant matrix. -/
def matrixTailEquiv (M : (Matrix ι ι F)ˣ) : K ≃ₐ[F] K :=
  differentialIndependentTopAlgEquiv x (matrixLinearForms (M : Matrix ι ι F) x) hx
    (differentialIndependent_matrixLinearForms_units x hx hconst M) hgen
    (differentialAdjoin_range_matrixLinearForms_units_eq_top x hgen M)

@[simp]
theorem matrixTailEquiv_apply (M : (Matrix ι ι F)ˣ) (i : ι) :
    matrixTailEquiv x hx hgen hconst M (x i) = matrixLinearForms (M : Matrix ι ι F) x i :=
  differentialIndependentTopAlgEquiv_apply _ _ _ _ _ _ i

theorem matrixTailEquiv_deriv (M : (Matrix ι ι F)ˣ) (z : K) :
    matrixTailEquiv x hx hgen hconst M z′ = (matrixTailEquiv x hx hgen hconst M z)′ :=
  differentialIndependentTopAlgEquiv_deriv _ _ _ _ _ _ z

/-- The differential-automorphism package of a constant recombination. -/
def matrixTailDifferentialAlgEquiv (M : (Matrix ι ι F)ˣ) : DifferentialAlgEquiv F K where
  toAlgEquiv := matrixTailEquiv x hx hgen hconst M
  map_deriv' := matrixTailEquiv_deriv x hx hgen hconst M

@[simp]
theorem matrixTailDifferentialAlgEquiv_toAlgEquiv (M : (Matrix ι ι F)ˣ) :
    (matrixTailDifferentialAlgEquiv x hx hgen hconst M).toAlgEquiv
      = matrixTailEquiv x hx hgen hconst M := rfl

/-- Pushing a recombined palette element through another recombination composes the matrices. -/
theorem matrixTailEquiv_matrixLinearForms (M N : (Matrix ι ι F)ˣ) (i : ι) :
    matrixTailEquiv x hx hgen hconst N (matrixLinearForms (M : Matrix ι ι F) x i)
      = matrixLinearForms ((M : Matrix ι ι F) * (N : Matrix ι ι F)) x i := by
  rw [matrixLinearForms_mul, matrixLinearForms, matrixLinearForms, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, AlgEquiv.commutes, matrixTailEquiv_apply]

/-- Recombination is multiplicative with the order reversed. -/
theorem matrixTailEquiv_comp (M N : (Matrix ι ι F)ˣ) :
    (matrixTailEquiv x hx hgen hconst M).trans (matrixTailEquiv x hx hgen hconst N)
      = matrixTailEquiv x hx hgen hconst (M * N) := by
  refine tailEquiv_ext x hgen (fun z => ?_)
    (matrixTailEquiv_deriv x hx hgen hconst (M * N)) (fun i => ?_)
  · rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, matrixTailEquiv_deriv,
      matrixTailEquiv_deriv]
  · rw [AlgEquiv.trans_apply, matrixTailEquiv_apply, matrixTailEquiv_matrixLinearForms,
      matrixTailEquiv_apply, Units.val_mul]

@[simp]
theorem matrixTailEquiv_one :
    matrixTailEquiv x hx hgen hconst 1 = AlgEquiv.refl := by
  refine tailEquiv_ext x hgen (matrixTailEquiv_deriv x hx hgen hconst 1) (fun z => rfl) ?_
  intro i
  rw [matrixTailEquiv_apply, show ((1 : (Matrix ι ι F)ˣ) : Matrix ι ι F) = 1 from rfl,
    matrixLinearForms_one]
  rfl

/-- The invertible constant matrices act on the freely generated differential field. -/
def tailRepresentation : (Matrix ι ι F)ˣ →* (K ≃ₐ[F] K) where
  toFun M := matrixTailEquiv x hx hgen hconst M⁻¹
  map_one' := by
    rw [inv_one]
    exact matrixTailEquiv_one x hx hgen hconst
  map_mul' M N := by
    rw [_root_.mul_inv_rev, AlgEquiv.aut_mul, ← matrixTailEquiv_comp]

theorem tailRepresentation_eq (M : (Matrix ι ι F)ˣ) :
    tailRepresentation x hx hgen hconst M = matrixTailEquiv x hx hgen hconst M⁻¹ := rfl

@[simp]
theorem tailRepresentation_apply (M : (Matrix ι ι F)ˣ) (i : ι) :
    tailRepresentation x hx hgen hconst M (x i)
      = matrixLinearForms ((M⁻¹ : (Matrix ι ι F)ˣ) : Matrix ι ι F) x i :=
  matrixTailEquiv_apply x hx hgen hconst M⁻¹ i

theorem tailRepresentation_deriv (M : (Matrix ι ι F)ˣ) (z : K) :
    tailRepresentation x hx hgen hconst M z′ =
      (tailRepresentation x hx hgen hconst M z)′ :=
  matrixTailEquiv_deriv x hx hgen hconst M⁻¹ z

/-- The differential field fixed by a linear symmetry group of the palette: the abstract tail of
the representation. -/
def tailFixedField {G : Type*} [Group G] (rho : G →* (Matrix ι ι F)ˣ) : IntermediateField F K :=
  IntermediateField.fixedField ((tailRepresentation x hx hgen hconst).comp rho).range

theorem mem_tailFixedField_iff {G : Type*} [Group G] (rho : G →* (Matrix ι ι F)ˣ) (z : K) :
    z ∈ tailFixedField x hx hgen hconst rho ↔
      ∀ g : G, tailRepresentation x hx hgen hconst (rho g) z = z := by
  rw [tailFixedField, IntermediateField.mem_fixedField_iff]
  constructor
  · intro h g
    exact h _ ⟨g, rfl⟩
  · rintro h _ ⟨g, rfl⟩
    exact h g

end TailAut

end

end GaloisForLFunctions.HTGeometry
