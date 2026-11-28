import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalIdelicPowerSaturation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.RationalRayNeighborhoods

/-! A compact idele class outside the closure of the n-th powers
is separated from the powers by an open subgroup. -/

noncomputable section

open Topology NumberField IsDedekindDomain IntermediateField
open GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay

variable {K : Type} [Field K] [NumberField K]

theorem exists_open_power_quotient_separating (n : ℕ) (a : CompactIdeleClassQuotient K)
    (ha : a ∉ (compactIdelePowers K n).topologicalClosure) :
    ∃ H : Subgroup (CompactIdeleClassQuotient K), IsOpen (H : Set (CompactIdeleClassQuotient K)) ∧
      compactIdelePowers K n ≤ H ∧ a ∉ H := by
  let C := CompactIdeleClassQuotient K
  let P := compactIdelePowers K n
  let U : Set C := (fun x => a * x) ⁻¹' (P.topologicalClosure : Set C)ᶜ
  have hP : IsClosed (P.topologicalClosure : Set C) := isClosed_closure
  have haMul : Continuous (fun x : C => a * x) := continuous_const_mul a
  have hU : IsOpen U := hP.isOpen_compl.preimage haMul
  have h1 : 1 ∈ U := by
    change a * 1 ∉ (P.topologicalClosure : Set C)
    have he : a * (1 : C) = a := mul_one a
    exact he.symm ▸ ha
  obtain ⟨c, hc, h⟩ := exists_rationalRay_ker_mem_nhds U (hU.mem_nhds h1)
  letI := hc
  let m := normModulus K c
  letI : TopologicalSpace (RayClassGroup m) := ⊥
  letI : DiscreteTopology (RayClassGroup m) := ⟨rfl⟩
  let N := (compactToRayClass m).ker
  have hN : IsOpen (N : Set C) :=
    (isOpen_discrete ({1} : Set (RayClassGroup m))).preimage (continuous_compactToRayClass m)
  have hNU : (N : Set C) ⊆ U := by
    intro x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective ((diagonal K).range ⊔ archPositive K) x
    exact h y hx
  refine ⟨P ⊔ N, Subgroup.isOpen_of_mem_nhds (g := 1) _
    (Filter.mem_of_superset (hN.mem_nhds (one_mem _)) (le_sup_right : N ≤ P ⊔ N)),
    le_sup_left, ?_⟩
  rintro hmem
  obtain ⟨p, hp, y, hy, rfl⟩ := Subgroup.mem_sup.mp hmem
  have he := hNU (N.inv_mem hy)
  change p * y * y⁻¹ ∉ (P.topologicalClosure : Set C) at he
  rw [mul_inv_cancel_right] at he
  exact he (P.le_topologicalClosure hp)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_open_power_quotient_separating
