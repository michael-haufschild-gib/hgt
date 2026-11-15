import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Classifying transitive abelian actions

In a transitive action of an abelian group, the stabilizer of a point is
the action kernel. The orbit map identifies the labelled set with the
quotient by that kernel. Pointed quotient labellings recover the complete
action, giving the action-to-lattice classification used in Theorem 6.2 of
Kurnosov–Ríos Ortiz, https://arxiv.org/abs/2611.01210.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.TransitiveActions
open scoped BigOperators
variable {A X : Type*} [AddCommGroup A]

abbrev ActionHom (A X : Type*) [AddCommGroup A] := A →+ Additive (Equiv.Perm X)

def act (ρ : ActionHom A X) (a : A) (x : X) : X := (ρ a).toMul x

@[simp] theorem act_zero (ρ : ActionHom A X) (x : X) : act ρ 0 x = x := by
  unfold act
  rw [map_zero]
  rfl

theorem act_add (ρ : ActionHom A X) (a b : A) (x : X) :
    act ρ (a + b) x = act ρ a (act ρ b x) := by
  unfold act
  rw [map_add]
  rfl

theorem act_comm (ρ : ActionHom A X) (a b : A) (x : X) :
    act ρ a (act ρ b x) = act ρ b (act ρ a x) := by
  rw [← act_add, add_comm a b, act_add]

/-- In a transitive abelian action, agreement at one point determines the permutation. -/
theorem hom_eq_of_orbit_eq (ρ : ActionHom A X) (x₀ : X)
    (hρ : Function.Surjective (fun a => act ρ a x₀)) {a b : A}
    (h : act ρ a x₀ = act ρ b x₀) : ρ a = ρ b := by
  change (ρ a).toMul = (ρ b).toMul
  apply Equiv.ext
  intro x
  obtain ⟨c, rfl⟩ := hρ x
  change act ρ a (act ρ c x₀) = act ρ b (act ρ c x₀)
  rw [act_comm ρ a c, act_comm ρ b c, h]

def kernel (ρ : ActionHom A X) : Submodule ℤ A := ρ.ker.toIntSubmodule

theorem mem_kernel (ρ : ActionHom A X) (a : A) : a ∈ kernel ρ ↔ ρ a = 0 := Iff.rfl

def quotientHom (ρ : ActionHom A X) : (A ⧸ kernel ρ) →+ Additive (Equiv.Perm X) :=
  QuotientAddGroup.lift ρ.ker ρ (le_refl _)

@[simp] theorem quotientHom_mk (ρ : ActionHom A X) (a : A) :
    quotientHom ρ (Submodule.Quotient.mk a) = ρ a := rfl

def orbitQuotient (ρ : ActionHom A X) (x₀ : X) : (A ⧸ kernel ρ) → X :=
  fun q => (quotientHom ρ q).toMul x₀

@[simp] theorem orbitQuotient_mk (ρ : ActionHom A X) (x₀ : X) (a : A) :
    orbitQuotient ρ x₀ (Submodule.Quotient.mk a) = act ρ a x₀ := rfl

theorem orbitQuotient_bijective (ρ : ActionHom A X) (x₀ : X)
    (hρ : Function.Surjective (fun a => act ρ a x₀)) :
    Function.Bijective (orbitQuotient ρ x₀) := by
  constructor
  · intro q r
    induction q using Quotient.inductionOn with | h a =>
      induction r using Quotient.inductionOn with | h b =>
        intro h
        apply (Submodule.Quotient.eq _).mpr
        change ρ (a - b) = 0
        rw [map_sub, hom_eq_of_orbit_eq ρ x₀ hρ h, sub_self]
  · intro x
    obtain ⟨a, ha⟩ := hρ x
    exact ⟨Submodule.Quotient.mk a, ha⟩

/-- The orbit map identifies the labelled set with the quotient by the action kernel. -/
def orbitEquiv (ρ : ActionHom A X) (x₀ : X)
    (hρ : Function.Surjective (fun a => act ρ a x₀)) : (A ⧸ kernel ρ) ≃ X :=
  Equiv.ofBijective _ (orbitQuotient_bijective ρ x₀ hρ)

@[simp] theorem orbitEquiv_mk (ρ : ActionHom A X) (x₀ : X)
    (hρ : Function.Surjective (fun a => act ρ a x₀)) (a : A) :
    orbitEquiv ρ x₀ hρ (Submodule.Quotient.mk a) = act ρ a x₀ := rfl

/-- Translation on a quotient, transported through a labelling. -/
def translationHom (L : Submodule ℤ A) (e : (A ⧸ L) ≃ X) : ActionHom A X where
  toFun a := Additive.ofMul (e.symm.trans ((Equiv.addLeft (L.mkQ a)).trans e))
  map_zero' := by
    change e.symm.trans ((Equiv.addLeft (L.mkQ 0)).trans e) = Equiv.refl X
    ext x
    change e (L.mkQ 0 + e.symm x) = x
    simp
  map_add' a b := by
    change e.symm.trans ((Equiv.addLeft (L.mkQ (a + b))).trans e) =
      (e.symm.trans ((Equiv.addLeft (L.mkQ a)).trans e)) *
        (e.symm.trans ((Equiv.addLeft (L.mkQ b)).trans e))
    ext x
    change e (L.mkQ (a + b) + e.symm x) =
      e (L.mkQ a + e.symm (e (L.mkQ b + e.symm x)))
    rw [(L.mkQ).map_add a b, Equiv.symm_apply_apply, add_assoc]

@[simp] theorem act_translationHom (L : Submodule ℤ A) (e : (A ⧸ L) ≃ X)
    (a : A) (x : X) : act (translationHom L e) a x = e (L.mkQ a + e.symm x) := rfl

theorem translationHom_surjective (L : Submodule ℤ A) (e : (A ⧸ L) ≃ X) (x₀ : X)
    (he : e 0 = x₀) : Function.Surjective (fun a => act (translationHom L e) a x₀) := by
  intro x
  obtain ⟨a, ha⟩ := L.mkQ_surjective (e.symm x)
  refine ⟨a, ?_⟩
  change e (L.mkQ a + e.symm x₀) = x
  rw [← he, Equiv.symm_apply_apply, add_zero, ha,
    Equiv.apply_symm_apply]

/-- Translations act trivially exactly for the original lattice vectors. -/
theorem kernel_translationHom (L : Submodule ℤ A) (e : (A ⧸ L) ≃ X) :
    kernel (translationHom L e) = L := by
  ext a
  rw [mem_kernel]
  constructor
  · intro h
    have he := congrArg (fun r : Additive (Equiv.Perm X) => r.toMul (e 0)) h
    change e (L.mkQ a + e.symm (e 0)) = e 0 at he
    rw [Equiv.symm_apply_apply, add_zero] at he
    exact (Submodule.Quotient.mk_eq_zero L).mp (e.injective he)
  · intro h
    change (translationHom L e a).toMul = Equiv.refl X
    ext x
    change e (L.mkQ a + e.symm x) = x
    have hz : L.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero L).mpr h
    rw [hz, zero_add, Equiv.apply_symm_apply]

/-- The quotient orbit map recovers the complete original action. -/
theorem translationHom_orbitEquiv (ρ : ActionHom A X) (x₀ : X)
    (hρ : Function.Surjective (fun a => act ρ a x₀)) :
    translationHom (kernel ρ) (orbitEquiv ρ x₀ hρ) = ρ := by
  apply AddMonoidHom.ext
  intro a
  change (translationHom (kernel ρ) (orbitEquiv ρ x₀ hρ) a).toMul = (ρ a).toMul
  ext x
  obtain ⟨b, rfl⟩ := hρ x
  change orbitEquiv ρ x₀ hρ ((kernel ρ).mkQ a +
    (orbitEquiv ρ x₀ hρ).symm (orbitEquiv ρ x₀ hρ ((kernel ρ).mkQ b))) = _
  rw [Equiv.symm_apply_apply]
  change act ρ (a + b) x₀ = act ρ a (act ρ b x₀)
  exact act_add ρ a b x₀

/-- Transitive actions on a labelled set with a distinguished label. -/
def Transitive (A X : Type*) [AddCommGroup A] (x₀ : X) :=
  {ρ : ActionHom A X // Function.Surjective (fun a => act ρ a x₀)}

/-- An integral submodule together with a labelling that fixes the origin. -/
def Data (A X : Type*) [AddCommGroup A] (x₀ : X) :=
  Σ L : {L : Submodule ℤ A // Nat.card (A ⧸ L) = Nat.card X},
    {e : (A ⧸ L.val) ≃ X // e 0 = x₀}

def fromData (x₀ : X) : Data A X x₀ → Transitive A X x₀ :=
  fun d => ⟨translationHom d.1.val d.2.val,
    translationHom_surjective d.1.val d.2.val x₀ d.2.property⟩

theorem fromData_injective (x₀ : X) : Function.Injective (fromData (A := A) x₀) := by
  rintro ⟨⟨L₁, hL₁⟩, e₁, he₁⟩ ⟨⟨L₂, hL₂⟩, e₂, he₂⟩ h
  have hh : translationHom L₁ e₁ = translationHom L₂ e₂ := congrArg Subtype.val h
  have hL : L₁ = L₂ := (kernel_translationHom L₁ e₁).symm.trans
    ((congrArg kernel hh).trans (kernel_translationHom L₂ e₂))
  cases hL
  have he : e₁ = e₂ := by
    ext q
    obtain ⟨a, rfl⟩ := L₁.mkQ_surjective q
    have ha := congrArg (fun ρ : ActionHom A X => act ρ a x₀) hh
    have hs₁ : e₁.symm x₀ = 0 := e₁.symm_apply_eq.mpr he₁.symm
    have hs₂ : e₂.symm x₀ = 0 := e₂.symm_apply_eq.mpr he₂.symm
    simpa only [act_translationHom, hs₁, hs₂, add_zero] using ha
  cases he
  rfl

theorem fromData_surjective (x₀ : X) : Function.Surjective (fromData (A := A) x₀) := by
  intro ρ
  let e := orbitEquiv ρ.val x₀ ρ.property
  have he : e 0 = x₀ := act_zero ρ.val x₀
  refine ⟨⟨⟨kernel ρ.val, Nat.card_congr e⟩, ⟨e, he⟩⟩, ?_⟩
  exact Subtype.ext (translationHom_orbitEquiv ρ.val x₀ ρ.property)

/-- Transitive abelian actions are classified by their kernels and pointed quotient labellings. -/
def dataEquiv (x₀ : X) : Data A X x₀ ≃ Transitive A X x₀ :=
  Equiv.ofBijective _ ⟨fromData_injective x₀, fromData_surjective x₀⟩

#print axioms orbitEquiv
#print axioms kernel_translationHom
#print axioms dataEquiv
end GaloisForLFunctions.RepresentationLifting.TransitiveActions
