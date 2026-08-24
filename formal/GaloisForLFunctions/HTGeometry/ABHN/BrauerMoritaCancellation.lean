import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Morita.Matrix
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Brauer--Morita cancellation

For finite-dimensional simple algebras, stable matrix equivalence with the base field already
forces an actual matrix-algebra presentation.  The proof supplies the uniqueness step absent from
the existence-only Wedderburn--Artin API: a Morita equivalence sends the regular simple module of
the division-algebra factor to a one-dimensional vector space, and full faithfulness identifies
their endomorphism spaces.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open CategoryTheory

universe u

variable (K : Type u) [Field K]

/-- A division algebra Morita equivalent to its base field has dimension one over that field. -/
theorem divisionRing_finrank_one_of_morita
    (D : Type u) [DivisionRing D] [Algebra K D] (e : MoritaEquivalence K D K) :
    Module.finrank K D = 1 := by
  let X : ModuleCat.{u} D := ModuleCat.of D D
  let V : ModuleCat.{u} K := e.eqv.functor.obj X
  haveI : IsSimpleModule D D :=
    (isSimpleModule_iff_finrank_eq_one).mpr (Module.finrank_self D)
  haveI : Simple X := (simple_iff_isSimpleModule' X).mpr inferInstance
  haveI : Simple V := CategoryTheory.simple_obj e.eqv.functor X
  have hV : Module.finrank K V = 1 :=
    isSimpleModule_iff_finrank_eq_one.mp (isSimpleModule_of_simple V)
  letI : Module K (X ⟶ X) := CategoryTheory.Linear.homModule X X
  letI : Module K (V ⟶ V) := CategoryTheory.Linear.homModule V V
  let mapEnd : (X ⟶ X) ≃ₗ[K] (V ⟶ V) :=
    LinearEquiv.ofBijective (e.eqv.functor.mapLinearMap K)
      ⟨e.eqv.functor.map_injective, e.eqv.functor.map_surjective⟩
  let homX : (X ⟶ X) ≃ₗ[K] Module.End D D :=
    { toEquiv := ModuleCat.homEquiv
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro d
        simp only [ModuleCat.homEquiv]
        change algebraMap K D c * f.hom d =
          ((algebraMap K (Module.End D D) c) * f.hom) d
        simp only [Module.algebraMap_end_apply, Module.End.mul_apply]
        exact (Algebra.smul_def c (f.hom d)).symm }
  let homV : (V ⟶ V) ≃ₗ[K] Module.End K V :=
    { toEquiv := ModuleCat.homEquiv
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c f
        apply LinearMap.ext
        intro v
        simp only [ModuleCat.homEquiv]
        change c • f.hom v = ((algebraMap K (Module.End K V) c) * f.hom) v
        simp }
  have hMap : Module.finrank K (X ⟶ X) = Module.finrank K (V ⟶ V) :=
    mapEnd.finrank_eq
  have hX : Module.finrank K (X ⟶ X) = Module.finrank K D := by
    rw [homX.finrank_eq]
    rw [Module.finrank_linearMap, Module.finrank_self, one_mul]
  have hVEnd : Module.finrank K (V ⟶ V) = 1 := by
    rw [homV.finrank_eq]
    simp [Module.finrank_linearMap, hV]
  rw [hX, hVEnd] at hMap
  exact hMap

/-- A division algebra Morita equivalent to its base field is the base field as an algebra. -/
noncomputable def divisionRingAlgEquivBaseOfMorita
    (D : Type u) [DivisionRing D] [Algebra K D] (e : MoritaEquivalence K D K) :
    D ≃ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K D)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp
      (divisionRing_finrank_one_of_morita K D e))).symm

/-- Stable matrix equivalence of same-universe central simple algebras induces Morita
equivalence. -/
theorem isMoritaEquivalent_of_isBrauerEquivalent
    (A B : CSA.{u, u} K) (h : IsBrauerEquivalent A B) :
    IsMoritaEquivalent K A.carrier B.carrier := by
  obtain ⟨n, m, hn, hm, ⟨stable⟩⟩ := h
  let inx : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  let im : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  refine ⟨⟨MoritaEquivalence.trans K
    (MoritaEquivalence.trans K (moritaEquivalenceMatrix A.carrier K inx)
      (MoritaEquivalence.ofAlgEquiv stable))
    (MoritaEquivalence.symm K (moritaEquivalenceMatrix B.carrier K im))⟩⟩

/-- A finite-dimensional simple algebra Morita equivalent to its base field is a matrix algebra
over that field. -/
theorem exists_algEquiv_matrix_base_of_morita
    (A : Type u) [Ring A] [Algebra K A] [IsSimpleRing A] [Module.Finite K A]
    (e : MoritaEquivalence K A K) :
    ∃ n : ℕ, ∃ _ : NeZero n, Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  obtain ⟨n, hn, D, hD, aD, finD, ⟨splitD⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  let moritaDK : MoritaEquivalence K D K :=
    MoritaEquivalence.trans K
      (MoritaEquivalence.trans K (moritaEquivalenceMatrix D K i)
        (MoritaEquivalence.ofAlgEquiv splitD.symm)) e
  let dK : D ≃ₐ[K] K := divisionRingAlgEquivBaseOfMorita K D moritaDK
  exact ⟨n, hn, ⟨splitD.trans dK.mapMatrix⟩⟩

/-- **Brauer cancellation.** A central simple algebra has split Brauer class exactly when it is
itself a full matrix algebra over the base field. -/
theorem brauerClass_eq_split_iff_exists_matrixAlgEquiv
    (A : CSA.{u, u} K) :
    brauerClass A = brauerSplitClass K ↔
      ∃ n : ℕ, ∃ _ : NeZero n,
        Nonempty (A.carrier ≃ₐ[K] Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro h
    have hrel : IsBrauerEquivalent A (scalarCSA K) := Quotient.exact h
    obtain ⟨e⟩ := (isMoritaEquivalent_of_isBrauerEquivalent K A (scalarCSA K) hrel).cond
    exact exists_algEquiv_matrix_base_of_morita K A.carrier e
  · rintro ⟨n, hn, ⟨e⟩⟩
    letI : NeZero n := hn
    exact (brauerClass_eq_of_algEquiv A (matrixFinCSA (scalarCSA K) n) e).trans
      (brauerClass_matrixFinCSA_scalar_eq n)

end

end GaloisForLFunctions.HTGeometry.ABHN
