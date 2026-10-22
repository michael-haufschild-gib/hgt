import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod

/-!
# Amalgamation of two augmented square-zero sectors

The fibre product of two split square-zero extensions over their common augmentation identifies the
two units and takes the direct sum of the two positive ideals: it is the split square-zero
extension of the sum.  Applied degreewise to a two-term Kummer sector and a two-term radial sector
this produces the amalgamated relevant coefficient, whose totalization against an arithmetic
residue is a three-term complex whose degree-zero cohomology is the unit line, whose degree-two
cohomology is the residue cokernel, and whose middle cohomology is the cokernel of the radial
differential.

* `deningerAmalgam` : the fibre product of two augmented square-zero extensions.
* `deningerAmalgamEquiv` : it is the square-zero extension of the direct sum of the ideals.
* `deningerTotalD0`, `deningerTotalD1` : the totalized three-term complex.
* `deningerTotal_H0`, `deningerTotal_H1Equiv`, `deningerTotal_range_d1` : its cohomology.
-/

namespace RHTower

section Amalgam

variable (k I J : Type*) [CommRing k]
  [AddCommGroup I] [Module k I] [Module kᵐᵒᵖ I] [IsCentralScalar k I]
  [AddCommGroup J] [Module k J] [Module kᵐᵒᵖ J] [IsCentralScalar k J]

/-- The augmentation of a split square-zero extension is surjective, split by the unit inclusion:
this is why the strict fibre product computes the homotopy fibre product. -/
theorem deningerSplitAugmentation_surjective :
    Function.Surjective (TrivSqZeroExt.fstHom k k I) := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩

/-- The amalgamation of two split square-zero extensions over their common augmentation. -/
def deningerAmalgam : Subalgebra k (TrivSqZeroExt k I × TrivSqZeroExt k J) :=
  AlgHom.equalizer ((TrivSqZeroExt.fstHom k k I).comp (AlgHom.fst k _ _))
    ((TrivSqZeroExt.fstHom k k J).comp (AlgHom.snd k _ _))

theorem deningerMem_amalgam (p : TrivSqZeroExt k I × TrivSqZeroExt k J) :
    p ∈ deningerAmalgam k I J ↔ p.1.fst = p.2.fst := Iff.rfl

/-- **The amalgamation identifies the units and takes the direct sum of the positive ideals.** -/
noncomputable def deningerAmalgamEquiv :
    TrivSqZeroExt k (I × J) ≃ₐ[k] deningerAmalgam k I J where
  toFun z := ⟨((z.fst, z.snd.1), (z.fst, z.snd.2)), rfl⟩
  invFun p := ((p : TrivSqZeroExt k I × TrivSqZeroExt k J).1.fst,
    ((p : TrivSqZeroExt k I × TrivSqZeroExt k J).1.snd,
      (p : TrivSqZeroExt k I × TrivSqZeroExt k J).2.snd))
  left_inv z := rfl
  right_inv p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · rfl
    · refine TrivSqZeroExt.ext ?_ rfl
      exact (p.2 : (p : TrivSqZeroExt k I × TrivSqZeroExt k J).1.fst
        = (p : TrivSqZeroExt k I × TrivSqZeroExt k J).2.fst)
  map_mul' z w := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;>
      refine TrivSqZeroExt.ext rfl ?_ <;>
      simp [TrivSqZeroExt.snd_mul, Prod.smul_def]
  map_add' z w := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;>
      refine TrivSqZeroExt.ext rfl ?_ <;>
      simp
  commutes' c := by
    refine Subtype.ext (Prod.ext ?_ ?_) <;>
      refine TrivSqZeroExt.ext ?_ ?_ <;>
      simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- Adjoining a trivial ideal changes nothing. -/
noncomputable def deningerZeroIdealEquiv (k M : Type*) [CommRing k] [AddCommGroup M]
    [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    TrivSqZeroExt k M ≃ₐ[k] TrivSqZeroExt k (PUnit × M) where
  toFun z := (z.fst, (PUnit.unit, z.snd))
  invFun w := (w.fst, w.snd.2)
  left_inv z := rfl
  right_inv w := by
    refine TrivSqZeroExt.ext rfl ?_
    refine Prod.ext ?_ rfl
    exact Subsingleton.elim _ _
  map_mul' z w := by
    refine TrivSqZeroExt.ext rfl ?_
    refine Prod.ext ?_ ?_
    · exact Subsingleton.elim _ _
    · simp [TrivSqZeroExt.snd_mul, Prod.smul_def]
  map_add' z w := by
    refine TrivSqZeroExt.ext rfl ?_
    refine Prod.ext ?_ rfl
    exact Subsingleton.elim _ _
  commutes' c := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · refine Prod.ext ?_ ?_
      · exact Subsingleton.elim _ _
      · simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- **The degree-zero amalgamation.**  Where the Kummer ideal vanishes, the amalgamated algebra is
the square-zero extension by the radial ideal alone. -/
noncomputable def deningerAmalgamDegreeZero (k M : Type*) [CommRing k] [AddCommGroup M]
    [Module k M] [Module kᵐᵒᵖ M] [IsCentralScalar k M] :
    TrivSqZeroExt k M ≃ₐ[k] deningerAmalgam k PUnit M :=
  (deningerZeroIdealEquiv k M).trans (deningerAmalgamEquiv k PUnit M)

end Amalgam

section Totalization

variable {k A B P D : Type*} [CommRing k]
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup P] [Module k P] [AddCommGroup D] [Module k D]

/-- The degree-zero differential of the totalized complex: the radial differential on the radial
summand, zero on the Kummer summand. -/
def deningerTotalD0 (Z : A →ₗ[k] B) : (k × A) →ₗ[k] (B × P) where
  toFun p := (Z p.2, 0)
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · simp
    · simp
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · simp
    · simp

/-- The degree-one differential of the totalized complex: the arithmetic residue on the Kummer
summand, zero on the radial summand. -/
def deningerTotalD1 (pr : P →ₗ[k] D) : (B × P) →ₗ[k] D where
  toFun p := pr p.2
  map_add' p q := by simp
  map_smul' c p := by simp

@[simp] theorem deningerTotalD0_apply (Z : A →ₗ[k] B) (a : k) (f : A) :
    deningerTotalD0 (P := P) Z (a, f) = (Z f, 0) := rfl

@[simp] theorem deningerTotalD1_apply (pr : P →ₗ[k] D) (g : B) (u : P) :
    deningerTotalD1 pr (g, u) = pr u := rfl

/-- **The totalization is a complex**: the arithmetic residue vanishes on the radial summand. -/
theorem deningerTotal_comp (Z : A →ₗ[k] B) (pr : P →ₗ[k] D) :
    (deningerTotalD1 pr).comp (deningerTotalD0 Z) = 0 := by
  refine LinearMap.ext fun p => ?_
  obtain ⟨a, f⟩ := p
  simp

/-- The degree-zero cocycles. -/
theorem deningerTotal_ker_d0 (Z : A →ₗ[k] B) :
    LinearMap.ker (deningerTotalD0 (P := P) Z) = (⊤ : Submodule k k).prod (LinearMap.ker Z) := by
  refine Submodule.ext fun p => ?_
  constructor
  · intro hp
    refine ⟨trivial, ?_⟩
    have : (Z p.2, (0 : P)) = 0 := hp
    exact (Prod.ext_iff.mp this).1
  · rintro ⟨-, hp⟩
    have hz : Z p.2 = 0 := hp
    show (Z p.2, (0 : P)) = 0
    rw [hz]
    rfl

/-- **The degree-zero cohomology is the unit line**, when the radial differential is injective. -/
theorem deningerTotal_H0 (Z : A →ₗ[k] B) (hZ : Function.Injective Z) :
    LinearMap.ker (deningerTotalD0 (P := P) Z) = LinearMap.range (LinearMap.inl k k A) := by
  rw [deningerTotal_ker_d0, LinearMap.ker_eq_bot.mpr hZ]
  refine Submodule.ext fun p => ?_
  constructor
  · rintro ⟨-, hp⟩
    have hp2 : p.2 = 0 := hp
    exact ⟨p.1, Prod.ext rfl hp2.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨trivial, rfl⟩

/-- The degree-one cocycles. -/
theorem deningerTotal_ker_d1 (pr : P →ₗ[k] D) :
    LinearMap.ker (deningerTotalD1 (B := B) pr) = (⊤ : Submodule k B).prod (LinearMap.ker pr) := by
  refine Submodule.ext fun p => ?_
  exact ⟨fun hp => ⟨trivial, hp⟩, fun hp => hp.2⟩

/-- The degree-one coboundaries. -/
theorem deningerTotal_range_d0 (Z : A →ₗ[k] B) :
    LinearMap.range (deningerTotalD0 (P := P) Z)
      = (LinearMap.range Z).prod (⊥ : Submodule k P) := by
  refine Submodule.ext fun p => ?_
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨⟨q.2, rfl⟩, rfl⟩
  · rintro ⟨⟨f, hf⟩, hp2⟩
    refine ⟨(0, f), ?_⟩
    have hp2' : p.2 = 0 := hp2
    exact Prod.ext hf hp2'.symm

/-- **The degree-two cohomology is the cokernel of the arithmetic residue.** -/
theorem deningerTotal_range_d1 (pr : P →ₗ[k] D) :
    LinearMap.range (deningerTotalD1 (B := B) pr) = LinearMap.range pr := by
  refine Submodule.ext fun x => ?_
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.2, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨((0 : B), u), rfl⟩

/-- The degree-one cocycles are the radial summand, when the arithmetic residue is injective. -/
noncomputable def deningerCocycleOneEquiv (pr : P →ₗ[k] D) (hpr : Function.Injective pr) :
    B ≃ₗ[k] ↥(LinearMap.ker (deningerTotalD1 (B := B) pr)) where
  toFun g := ⟨(g, 0), by
    show pr (0 : P) = 0
    simp⟩
  invFun p := (p : B × P).1
  left_inv g := rfl
  right_inv p := by
    refine Subtype.ext (Prod.ext rfl ?_)
    have hp : pr (p : B × P).2 = 0 := p.2
    have : (p : B × P).2 = 0 := hpr (by rw [hp, map_zero])
    exact this.symm
  map_add' g h := by
    refine Subtype.ext (Prod.ext rfl ?_)
    simp
  map_smul' c g := by
    refine Subtype.ext (Prod.ext rfl ?_)
    simp

/-- The middle cohomology of the totalized complex. -/
noncomputable def deningerTotalH1 (Z : A →ₗ[k] B) (pr : P →ₗ[k] D) : Type _ :=
  (↥(LinearMap.ker (deningerTotalD1 (B := B) pr))) ⧸
    (Submodule.comap (LinearMap.ker (deningerTotalD1 (B := B) pr)).subtype
      (LinearMap.range (deningerTotalD0 (P := P) Z)))

noncomputable instance (Z : A →ₗ[k] B) (pr : P →ₗ[k] D) :
    AddCommGroup (deningerTotalH1 Z pr) :=
  inferInstanceAs (AddCommGroup ((↥(LinearMap.ker (deningerTotalD1 (B := B) pr))) ⧸ _))

noncomputable instance (Z : A →ₗ[k] B) (pr : P →ₗ[k] D) :
    Module k (deningerTotalH1 Z pr) :=
  inferInstanceAs (Module k ((↥(LinearMap.ker (deningerTotalD1 (B := B) pr))) ⧸ _))

theorem deningerCocycleOneEquiv_map (Z : A →ₗ[k] B) (pr : P →ₗ[k] D)
    (hpr : Function.Injective pr) :
    (LinearMap.range Z).map (deningerCocycleOneEquiv (B := B) pr hpr).toLinearMap
      = Submodule.comap (LinearMap.ker (deningerTotalD1 (B := B) pr)).subtype
          (LinearMap.range (deningerTotalD0 (P := P) Z)) := by
  refine Submodule.ext fun p => ?_
  constructor
  · rintro ⟨g, ⟨f, rfl⟩, rfl⟩
    show ((Z f, (0 : P)) : B × P) ∈ LinearMap.range (deningerTotalD0 (P := P) Z)
    exact ⟨(0, f), rfl⟩
  · intro hp
    have hmem : (p : B × P) ∈ (LinearMap.range Z).prod (⊥ : Submodule k P) := by
      rw [← deningerTotal_range_d0]
      exact hp
    obtain ⟨f, hf⟩ := hmem.1
    refine ⟨Z f, ⟨f, rfl⟩, ?_⟩
    refine Subtype.ext (Prod.ext hf ?_)
    exact (hmem.2 : (p : B × P).2 = 0).symm

/-- **The middle cohomology is the cokernel of the radial differential**, when the arithmetic
residue is injective. -/
noncomputable def deningerTotal_H1Equiv (Z : A →ₗ[k] B) (pr : P →ₗ[k] D)
    (hpr : Function.Injective pr) :
    (B ⧸ LinearMap.range Z) ≃ₗ[k] deningerTotalH1 Z pr :=
  Submodule.Quotient.equiv _ _ (deningerCocycleOneEquiv (B := B) pr hpr)
    (deningerCocycleOneEquiv_map Z pr hpr)

end Totalization

end RHTower
