import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicIntegralReduction
import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Invariants

/-! The integral group acts on first principal-congruence fixed
vectors, and the action factors through its finite residue group. -/

noncomputable section

open Matrix

namespace GlobalTheory.GLp

variable {p : ℕ} [Fact p.Prime] {n : Type*} [Fintype n] [DecidableEq n]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL n ℚ_[p]) V)

/-- Vectors fixed by the first principal congruence subgroup. -/
def principalFixed : Submodule ℂ V :=
  Representation.invariants (ρ.comp (principalCongruenceOne p n).subtype)

theorem mem_principalFixed_iff (v : V) :
    v ∈ principalFixed ρ ↔ ∀ x ∈ principalCongruenceOne p n, ρ x v = v :=
  ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.val x.2⟩

theorem integral_conj_mem_principal (k : GL n ℤ_[p]) {x : GL n ℚ_[p]}
    (hx : x ∈ principalCongruenceOne p n) :
    (integralInclusion p n k)⁻¹ * x * integralInclusion p n k ∈ principalCongruenceOne p n := by
  obtain ⟨u, hu, rfl⟩ := hx
  have h : integralReduction p n u = 1 := hu
  refine ⟨k⁻¹ * u * k, ?_, by rw [map_mul, map_mul, map_inv]⟩
  change integralReduction p n (k⁻¹ * u * k) = 1
  simp only [map_mul, map_inv, h, mul_one, inv_mul_cancel]

private theorem apply_integral_mem_principalFixed (k : GL n ℤ_[p]) {v : V}
    (hv : v ∈ principalFixed ρ) : ρ (integralInclusion p n k) v ∈ principalFixed ρ := by
  apply (mem_principalFixed_iff ρ _).mpr
  intro x hx
  let g := integralInclusion p n k
  have hfix := (mem_principalFixed_iff ρ v).mp hv _ (integral_conj_mem_principal k hx)
  change ρ x (ρ g v) = ρ g v
  rw [← Module.End.mul_apply, ← map_mul, show x * g = g * (g⁻¹ * x * g) by group,
    map_mul, Module.End.mul_apply, hfix]

private def integralAction : Representation ℂ (GL n ℤ_[p]) (principalFixed ρ) where
  toFun k := (ρ (integralInclusion p n k)).restrict
    (fun _ hv => apply_integral_mem_principalFixed ρ k hv)
  map_one' := LinearMap.ext fun v => Subtype.ext (by
    change ρ (integralInclusion p n 1) v.val = v.val
    rw [map_one, map_one, Module.End.one_apply])
  map_mul' k l := LinearMap.ext fun v => Subtype.ext (by
    change ρ (integralInclusion p n (k * l)) v.val =
      ρ (integralInclusion p n k) (ρ (integralInclusion p n l) v.val)
    rw [map_mul, map_mul, Module.End.mul_apply])

private theorem integralAction_ker :
    (integralReduction p n).ker ≤ (integralAction ρ).toHomUnits.ker := by
  intro k hk
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ρ (integralInclusion p n k) v.val = v.val
  exact (mem_principalFixed_iff ρ _).mp v.2 _ ⟨k, hk, rfl⟩

/-- The finite general linear representation on principal-congruence fixed vectors. -/
def principalFixedReduction : Representation ℂ (GL n (ZMod p)) (principalFixed ρ) :=
  (Units.coeHom _).comp ((integralReduction p n).liftOfSurjective
    (integralReduction_surjective p n) ⟨(integralAction ρ).toHomUnits, integralAction_ker ρ⟩)

theorem principalFixedReduction_apply (k : GL n ℤ_[p]) (v : principalFixed ρ) :
    ((principalFixedReduction ρ (integralReduction p n k) v : principalFixed ρ) : V) =
      ρ (integralInclusion p n k) v.val := by
  let f := integralReduction p n
  let g := (integralAction ρ).toHomUnits
  have he := f.liftOfRightInverse_comp_apply _ (Function.rightInverse_surjInv
    (integralReduction_surjective p n)) ⟨g, integralAction_ker ρ⟩ k
  exact congrArg (fun u : (Module.End ℂ (principalFixed ρ))ˣ => (u.val v : V)) he

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.principalFixedReduction_apply
