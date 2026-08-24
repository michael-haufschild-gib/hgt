import GaloisForLFunctions.HTGeometry.ABHN.BrauerMoritaCancellation
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionRepresentative
import Mathlib.FieldTheory.JacobsonNoether

/-!
# Separable elements in nonsplit central division representatives

The Jacobson--Noether theorem turns a nonsplit finite-dimensional central division algebra into
a concrete separable element outside the base field.  Combined with central division
representatives, every nonsplit Brauer class therefore carries a nontrivial finite separable
commutative seed.  This is the first field-theoretic step toward a separable maximal subfield and,
over a nonarchimedean local field, an unramified maximal splitting field.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable (K D : Type u) [Field K] [DivisionRing D] [Algebra K D]
  [Module.Finite K D] [Algebra.IsCentral K D]

/-- If the base field already exhausts a central division algebra, its Brauer class is split. -/
theorem brauerClass_centralDivisionCSA_eq_split_of_bot_eq_top
    (h : (⊥ : Subalgebra K D) = ⊤) :
    brauerClass (centralDivisionCSA K D) = brauerSplitClass K := by
  have hsurj : Function.Surjective (Algebra.ofId K D) := by
    intro d
    have hd : d ∈ (⊥ : Subalgebra K D) := by
      rw [h]
      exact Algebra.mem_top
    exact Algebra.mem_bot.mp hd
  let e : K ≃ₐ[K] D := AlgEquiv.ofBijective (Algebra.ofId K D)
    ⟨(algebraMap K D).injective, hsurj⟩
  simpa [brauerSplitClass] using
    brauerClass_eq_of_algEquiv (centralDivisionCSA K D) (scalarCSA K) e.symm

/-- A nonsplit central division representative contains elements outside the base field. -/
theorem centralDivision_bot_ne_top_of_brauerClass_ne_split
    (h : brauerClass (centralDivisionCSA K D) ≠ brauerSplitClass K) :
    (⊥ : Subalgebra K D) ≠ ⊤ := by
  intro htop
  exact h (brauerClass_centralDivisionCSA_eq_split_of_bot_eq_top K D htop)

/-- Jacobson--Noether supplies a separable element outside the base in every nonsplit finite
central division algebra. -/
theorem centralDivision_exists_separable_not_base_of_brauerClass_ne_split
    (h : brauerClass (centralDivisionCSA K D) ≠ brauerSplitClass K) :
    ∃ x : D, x ∉ (⊥ : Subalgebra K D) ∧ IsSeparable K x := by
  letI : Algebra.IsAlgebraic K D := Algebra.IsAlgebraic.of_finite K D
  exact JacobsonNoether.exists_separable_and_not_isCentral'
    (centralDivision_bot_ne_top_of_brauerClass_ne_split K D h)

/-- Every nonsplit Brauer-group element admits a central division representative together with a
separable element that does not come from the base field. -/
theorem brauerGroup_ne_split_exists_centralDivision_separable
    (x : BrauerGroup K) (hx : x ≠ brauerSplitClass K) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : Module.Finite K D) (_ : Algebra.IsCentral K D) (y : D),
      x = brauerClass (centralDivisionCSA K D) ∧
        y ∉ (⊥ : Subalgebra K D) ∧ IsSeparable K y := by
  obtain ⟨D, hD, aD, finD, centralD, hclass⟩ :=
    brauerGroup_exists_centralDivisionRepresentative K x
  have hnonSplit : brauerClass (centralDivisionCSA K D) ≠ brauerSplitClass K := by
    rwa [← hclass]
  obtain ⟨y, hybase, hysep⟩ :=
    centralDivision_exists_separable_not_base_of_brauerClass_ne_split K D hnonSplit
  exact ⟨D, hD, aD, finD, centralD, y, hclass, hybase, hysep⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
