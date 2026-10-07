import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# The natural grading on a Rees algebra

For every ideal `I` of a commutative ring, grade the existing `reesAlgebra I` by polynomial
degree. Each component is reconstructed from its single polynomial coefficient. Finite polynomial
support gives an explicit direct-sum decomposition; no finite generation of `I` is required.
The native homogeneous irrelevant ideal consists exactly of elements with zero constant term.
-/

noncomputable section
open scoped BigOperators DirectSum
namespace GaloisForLFunctions.HTGeometry.ReesGrading
variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The degree-`n` homogeneous component of the native Rees algebra. -/
def grade (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {f | (f : Polynomial R) = Polynomial.monomial n ((f : Polynomial R).coeff n)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change (f : Polynomial R) + g = Polynomial.monomial n (((f : Polynomial R) + g).coeff n)
    rw [Polynomial.coeff_add,map_add,← hf,← hg]
  smul_mem' := by
    intro r f hf
    change r • (f : Polynomial R) = Polynomial.monomial n ((r • (f : Polynomial R)).coeff n)
    rw [Polynomial.coeff_smul,← Polynomial.smul_monomial,← hf]

/-- A homogeneous Rees monomial with coefficient in the corresponding ideal power. -/
def mono (n : ℕ) (a : R) (ha : a ∈ I^n) : reesAlgebra I :=
  ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.2 ha⟩

/-- Every Rees monomial belongs to its prescribed homogeneous component. -/
@[simp] theorem mono_mem_grade (n : ℕ) (a : R) (ha : a ∈ I^n) : mono I n a ha ∈ grade I n := by
  change Polynomial.monomial n a = Polynomial.monomial n ((Polynomial.monomial n a).coeff n)
  simp

/-- The degree-`n` coefficient projection, with its homogeneous membership certificate. -/
def piece (n : ℕ) (f : reesAlgebra I) : grade I n :=
  ⟨mono I n ((f : Polynomial R).coeff n) (f.2 n),mono_mem_grade I n _ _⟩

/-- The homogeneous projection has the prescribed underlying polynomial. -/
@[simp] theorem piece_coe (n : ℕ) (f : reesAlgebra I) :
    ((piece I n f : reesAlgebra I) : Polynomial R) =
      Polynomial.monomial n ((f : Polynomial R).coeff n) := rfl

/-- The homogeneous projection sends zero to zero. -/
@[simp] theorem piece_zero (n : ℕ) : piece I n 0 = 0 := by
  apply Subtype.ext; apply Subtype.ext; simp

/-- The homogeneous projection preserves addition. -/
@[simp] theorem piece_add (n : ℕ) (f g : reesAlgebra I) :
    piece I n (f+g) = piece I n f + piece I n g := by
  apply Subtype.ext; apply Subtype.ext
  change Polynomial.monomial n (((f : Polynomial R)+(g : Polynomial R)).coeff n) = _
  simp

/-- The finite-support direct-sum decomposition of a Rees polynomial. -/
def decomposition (f : reesAlgebra I) : ⨁ n, grade I n :=
  (f : Polynomial R).support.sum (fun n => DirectSum.of (fun n => grade I n) n (piece I n f))

/-- Each coordinate of the decomposition is its coefficient projection. -/
@[simp] theorem decomposition_apply (f : reesAlgebra I) (i : ℕ) :
    decomposition I f i = piece I i f := by
  classical
  unfold decomposition
  rw [DirectSum.sum_apply]
  rw [Finset.sum_eq_single i]
  · exact DirectSum.of_eq_same (β := fun n => grade I n) i (piece I i f)
  · intro b hb hbi
    exact DirectSum.of_eq_of_ne _ _ _ hbi.symm
  · intro hi
    rw [DirectSum.of_eq_same]
    apply Subtype.ext; apply Subtype.ext
    have h : (f : Polynomial R).coeff i = 0 := Polynomial.notMem_support_iff.1 hi
    simp [h]

/-- Coefficient decomposition as an additive homomorphism. -/
def decomposeAddHom : reesAlgebra I →+ ⨁ n, grade I n where
  toFun := decomposition I
  map_zero' := by ext i; simp
  map_add' f g := by ext i; simp

/-- Adding the homogeneous pieces recovers the original Rees polynomial. -/
theorem recompose_decompose :
    (DirectSum.coeAddMonoidHom (grade I)).comp (decomposeAddHom I) = .id _ := by
  apply AddMonoidHom.ext
  intro f
  apply Subtype.ext
  change ((DirectSum.coeAddMonoidHom (grade I)) (decomposition I f) : Polynomial R) = _
  simp only [decomposition,map_sum,DirectSum.coeAddMonoidHom_of]
  change (reesAlgebra I).val (∑ n ∈ (f : Polynomial R).support, (piece I n f : reesAlgebra I)) = _
  rw [map_sum]
  exact Polynomial.sum_monomial_eq _

/-- A homogeneous element decomposes into its own component alone. -/
theorem decompose_coe (i : ℕ) (f : grade I i) :
    decomposeAddHom I f = DirectSum.of (fun n => grade I n) i f := by
  apply DirectSum.ext
  intro j
  change decomposition I f j = _
  rw [decomposition_apply]
  by_cases h : j=i
  · subst j
    rw [DirectSum.of_eq_same]
    apply Subtype.ext; apply Subtype.ext
    exact f.2.symm
  · rw [DirectSum.of_eq_of_ne _ _ _ h]
    apply Subtype.ext; apply Subtype.ext
    change Polynomial.monomial j (((f : reesAlgebra I) : Polynomial R).coeff j) = 0
    rw [f.2]
    simp only [Polynomial.coeff_monomial,if_neg (Ne.symm h),map_zero]

/-- The verified native direct-sum decomposition of the Rees algebra. -/
instance decompositionInstance : DirectSum.Decomposition (grade I) :=
  DirectSum.Decomposition.ofAddHom (grade I) (decomposeAddHom I) (recompose_decompose I) (by
    apply DirectSum.addHom_ext
    intro i f
    change decomposeAddHom I ((DirectSum.coeAddMonoidHom (grade I)) _) = _
    rw [DirectSum.coeAddMonoidHom_of,decompose_coe]
    rfl)

/-- Products of homogeneous Rees elements add their polynomial degrees. -/
instance gradedMonoid : SetLike.GradedMonoid (grade I) where
  one_mem := by
    change (1 : Polynomial R) = Polynomial.monomial 0 ((1 : Polynomial R).coeff 0)
    simp
  mul_mem := by
    intro i j f g hf hg
    change (f : Polynomial R) * (g : Polynomial R) =
      Polynomial.monomial (i+j) (((f : Polynomial R)*(g : Polynomial R)).coeff (i+j))
    rw [hf,hg,Polynomial.monomial_mul_monomial,Polynomial.coeff_monomial]
    simp

/-- The native Rees algebra with its natural grading. -/
instance gradedAlgebra : GradedAlgebra (grade I) where

/-- Native graded decomposition agrees with the explicit coefficient projection. -/
@[simp] theorem decompose_component (f : reesAlgebra I) (n : ℕ) :
    DirectSum.decompose (grade I) f n = piece I n f :=
  decomposition_apply I f n

/-- Membership in the native irrelevant ideal is exactly vanishing of the constant term. -/
@[simp] theorem irrelevant_mem_iff (f : reesAlgebra I) :
    f ∈ HomogeneousIdeal.irrelevant (grade I) ↔ (f : Polynomial R).coeff 0 = 0 := by
  rw [HomogeneousIdeal.mem_irrelevant_iff,GradedRing.proj_apply,decompose_component]
  change (mono I 0 ((f : Polynomial R).coeff 0) (f.2 0)) = 0 ↔ _
  constructor
  · intro h
    have hh := congrArg (fun x : reesAlgebra I => (x : Polynomial R).coeff 0) h
    simpa [mono] using hh
  · intro h
    apply Subtype.ext
    simp [mono,h]

end GaloisForLFunctions.HTGeometry.ReesGrading
