import GaloisForLFunctions.RHTower.Artin.ArtinClassFunctionInduction

/-!
# Artin's identity for the cyclic subgroups

For a subgroup `C` of a finite group `G` let `θ_C` be the function on `C` with the value `|C|`
on the generators of `C` and zero elsewhere (`generatorWeight`). Then

  `Σ_C Ind θ_C = |G|`   (`sum_inducedFunction_generatorWeight`),

the sum over the cyclic subgroups (`cyclicSubgroups`). For `x ∈ G` the function induced from
`θ_C` counts the `y ∈ G` with `⟨y x y⁻¹⟩ = C` (`inducedFunction_generatorWeight`), and every
`y` is counted for exactly one `C`.
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

variable {G : Type u} [Group G]

/-- `θ_C`: the value `|C|` on the generators of `C`, zero elsewhere. -/
def generatorWeight (C : Subgroup G) (c : C) : ℂ :=
  if Subgroup.zpowers (c : G) = C then (Nat.card C : ℂ) else 0

theorem extendByZero_generatorWeight (C : Subgroup G) (z : G) :
    extendByZero C (generatorWeight C) z =
      if Subgroup.zpowers z = C then (Nat.card C : ℂ) else 0 := by
  by_cases hz : z ∈ C
  · rw [extendByZero_of_mem C _ hz]
    rfl
  · rw [extendByZero_of_notMem C _ hz, if_neg]
    rintro rfl
    exact hz (Subgroup.mem_zpowers z)

variable [Fintype G]

/-- The cyclic subgroups of a finite group. -/
def cyclicSubgroups (G : Type u) [Group G] [Fintype G] : Finset (Subgroup G) :=
  Finset.univ.image fun g : G => Subgroup.zpowers g

theorem zpowers_mem_cyclicSubgroups (g : G) : Subgroup.zpowers g ∈ cyclicSubgroups G :=
  Finset.mem_image_of_mem _ (Finset.mem_univ g)

/-- The function induced from `θ_C` counts the conjugates of `x` that generate `C`. -/
theorem inducedFunction_generatorWeight (C : Subgroup G) (x : G) :
    inducedFunction C (generatorWeight C) x =
      ∑ y : G, if Subgroup.zpowers (y * x * y⁻¹) = C then (1 : ℂ) else 0 := by
  have hcard : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [inducedFunction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [extendByZero_generatorWeight]
  split_ifs
  · exact inv_mul_cancel₀ hcard
  · exact mul_zero _

/-- **Artin's identity.** `Σ_C Ind θ_C = |G|`, the sum over the cyclic subgroups. -/
theorem sum_inducedFunction_generatorWeight (x : G) :
    ∑ C ∈ cyclicSubgroups G, inducedFunction C (generatorWeight C) x = (Nat.card G : ℂ) := by
  simp only [inducedFunction_generatorWeight]
  rw [Finset.sum_comm]
  have h : ∀ y : G, ∑ C ∈ cyclicSubgroups G,
      (if Subgroup.zpowers (y * x * y⁻¹) = C then (1 : ℂ) else 0) = 1 := fun y => by
    rw [Finset.sum_ite_eq, if_pos (zpowers_mem_cyclicSubgroups _)]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, Nat.card_eq_fintype_card]

end GaloisForLFunctions
