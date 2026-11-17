import GaloisForLFunctions.HTGeometry.ConstraintRelativity.MonogenicKaehler

/-!
# Derivations of a monogenic algebra

Evaluation at the generator identifies actual derivations with the annihilator of the different.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.Differential
open Polynomial
open _root_.HTGeometry.ConstraintRelativity
variable {R : Type*} [CommRing R] (f : R[X])

/-- Allowed tangent values of the monogenic generator are exactly the annihilator of its different. -/
def rootTangentSpace : Submodule (AdjoinRoot f) (AdjoinRoot f) where
  carrier := {u | rootDifferent f * u = 0}
  zero_mem' := mul_zero _
  add_mem' := by
    intro u v hu hv
    change rootDifferent f * u = 0 at hu
    change rootDifferent f * v = 0 at hv
    change rootDifferent f * (u + v) = 0
    rw [mul_add, hu, hv, add_zero]
  smul_mem' := by
    intro c u hu
    change rootDifferent f * (c * u) = 0
    rw [mul_left_comm, hu, mul_zero]

private theorem derivation_root_mem (D : Derivation R (AdjoinRoot f) (AdjoinRoot f)) :
    D (AdjoinRoot.root f) ∈ rootTangentSpace f := by
  have h : D (aeval (AdjoinRoot.root f) f) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  rw [Derivation.map_aeval, ← rootDifferent_eq_aeval] at h
  exact h

/-- Evaluation at the root, with its necessary conormal annihilation condition. -/
def derivationRootEvaluation :
    Derivation R (AdjoinRoot f) (AdjoinRoot f) →ₗ[AdjoinRoot f] rootTangentSpace f where
  toFun D := ⟨D (AdjoinRoot.root f), derivation_root_mem f D⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem derivationRootEvaluation_injective : Function.Injective (derivationRootEvaluation f) := by
  intro D E h
  have he : D (AdjoinRoot.root f) = E (AdjoinRoot.root f) := congrArg Subtype.val h
  apply Derivation.ext
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [← AdjoinRoot.aeval_eq, Derivation.map_aeval, Derivation.map_aeval, he]

private def tangentQuotientMap (u : rootTangentSpace f) :
    MonogenicOmega f →ₗ[AdjoinRoot f] AdjoinRoot f :=
  Submodule.liftQ (Ideal.span {rootDifferent f})
    (LinearMap.toSpanSingleton (AdjoinRoot f) (AdjoinRoot f) u.val) (by
      rw [Ideal.span_le]
      rintro _ rfl
      change rootDifferent f * u.val = 0
      exact u.property)

/-- Every allowed root value gives an actual derivation through the universal differential module. -/
def derivationFromRoot (u : rootTangentSpace f) :
    Derivation R (AdjoinRoot f) (AdjoinRoot f) :=
  KaehlerDifferential.linearMapEquivDerivation R (AdjoinRoot f)
    ((tangentQuotientMap f u).comp (kaehlerEquivMonogenic f).toLinearMap)

@[simp] theorem derivationFromRoot_apply_root (u : rootTangentSpace f) :
    derivationFromRoot f u (AdjoinRoot.root f) = u.val := by
  change tangentQuotientMap f u ((kaehlerEquivMonogenic f)
    (KaehlerDifferential.D R (AdjoinRoot f) (AdjoinRoot.root f))) = u.val
  rw [show AdjoinRoot.root f = AdjoinRoot.mk f X from rfl, kaehlerEquivMonogenic_D]
  simp only [derivative_X, map_one]
  change (1 : AdjoinRoot f) • u.val = u.val
  exact one_smul _ _

/-- Derivations of every monogenic algebra are classified exactly by the annihilator of the different. -/
def derivationRootEquiv :
    Derivation R (AdjoinRoot f) (AdjoinRoot f) ≃ₗ[AdjoinRoot f] rootTangentSpace f :=
  LinearEquiv.ofBijective (derivationRootEvaluation f)
    ⟨derivationRootEvaluation_injective f, fun u => ⟨derivationFromRoot f u, by
      apply Subtype.ext
      exact derivationFromRoot_apply_root f u⟩⟩

/-- The conormal condition is both necessary and sufficient for prescribing a derivation's root value. -/
theorem exists_derivation_root_iff (u : AdjoinRoot f) :
    (∃ D : Derivation R (AdjoinRoot f) (AdjoinRoot f), D (AdjoinRoot.root f) = u) ↔
      rootDifferent f * u = 0 := by
  constructor
  · rintro ⟨D, rfl⟩
    exact derivation_root_mem f D
  · intro hu
    exact ⟨derivationFromRoot f ⟨u, hu⟩, derivationFromRoot_apply_root f ⟨u, hu⟩⟩

#print axioms derivationRootEquiv
#print axioms exists_derivation_root_iff
end GaloisForLFunctions.RepresentationLifting.Differential
