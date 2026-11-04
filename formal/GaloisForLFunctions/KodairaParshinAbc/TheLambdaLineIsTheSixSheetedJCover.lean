import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfTheModularLambdaFunction
import GaloisForLFunctions.HTGeometry.MonodromyCoverExamples

/-!
# The λ-line is the six-sheeted `j`-cover

The Legendre invariant `J(λ) = 256 (λ² - λ + 1)³ / (λ²(λ - 1)²)` is invariant under the anharmonic
group `⟨S, T⟩` of `ℂ ∖ {0, 1}` (`S : λ ↦ 1 - λ`, `T : λ ↦ λ/(λ - 1)`), and `λ ↦ J(λ)` is the
quotient map.  Its monodromy is the regular action of that group, with generators
`x = S` (order `2`, over `J = 1728`), `y = T S : λ ↦ (λ - 1)/λ` (order `3`, over `J = 0`) and
`x y = S T S : λ ↦ 1/λ` (order `2`, over the cusp `J = ∞`).

The corpus regular-cover construction (`HTGeometry.regularCover`) turns these data into a connected
`(2, 3, 2)` monodromy cover, and the exact modular capacity law
(`MonodromyCover.modular_capacity_exact`, `D = 6 (2g + s - 2)` with `s = D/2` cusps) together with
the six-element bound `anharmonicGroup_subset_sixSet` forces

  `D = |⟨S, T⟩| = 6`,  `g = 0`,  fibres `3, 2, 3` over `1728, 0, ∞`:

the λ-line is a sphere and `J` has degree six, the exponent behind `H(J(λ)) ≍ H(λ)⁶`.
-/

noncomputable section

open Bottcher GaloisForLFunctions.HTGeometry
open scoped Classical

namespace GaloisForLFunctions.KodairaParshinAbc

instance anharmonicGroup_finite : Finite anharmonicGroup :=
  (sixSet_finite.subset anharmonicGroup_subset_sixSet).to_subtype

instance : Fintype anharmonicGroup := Fintype.ofFinite _

/-- The generator `S : λ ↦ 1 - λ` inside the anharmonic group. -/
def anharmS' : anharmonicGroup := ⟨anharmS, Subgroup.subset_closure (Or.inl rfl)⟩

/-- The generator `T : λ ↦ λ/(λ - 1)` inside the anharmonic group. -/
def anharmT' : anharmonicGroup := ⟨anharmT, Subgroup.subset_closure (Or.inr rfl)⟩

/-- The test point `2 ∈ ℂ ∖ {0, 1}`. -/
def puncturedTwo : Punctured := ⟨2, mem_compl01.mpr ⟨two_ne_zero, by norm_num⟩⟩

theorem anharmS_ne_one : anharmS ≠ 1 := by
  intro h
  have := congrArg (fun φ : Equiv.Perm Punctured => ((φ puncturedTwo : Punctured) : ℂ)) h
  simp only [anharmS_apply, Equiv.Perm.coe_one, id_eq, puncturedTwo] at this
  norm_num at this

theorem anharmTS_ne_one : anharmT * anharmS ≠ 1 := by
  intro h
  have := congrArg (fun φ : Equiv.Perm Punctured => ((φ puncturedTwo : Punctured) : ℂ)) h
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply,
    Equiv.Perm.coe_one, id_eq, puncturedTwo] at this
  norm_num at this

theorem anharmSTS_ne_one : anharmS * (anharmT * anharmS) ≠ 1 := by
  intro h
  have := congrArg (fun φ : Equiv.Perm Punctured => ((φ puncturedTwo : Punctured) : ℂ)) h
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply,
    Equiv.Perm.coe_one, id_eq, puncturedTwo] at this
  norm_num at this

theorem anharmTS_pow_three : (anharmT * anharmS) ^ 3 = 1 := by
  calc (anharmT * anharmS) ^ 3 = anharmT * (anharmS * anharmT * anharmS) * (anharmT * anharmS) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = anharmT * (anharmT * anharmS * anharmT) * (anharmT * anharmS) := by rw [anharm_braid]
    _ = (anharmT * anharmT) * anharmS * (anharmT * anharmT) * anharmS := by
        simp only [mul_assoc]
    _ = 1 := by simp only [anharmT_sq, one_mul, mul_one, anharmS_sq]

theorem anharmSTS_pow_two : (anharmS * (anharmT * anharmS)) ^ 2 = 1 := by
  calc (anharmS * (anharmT * anharmS)) ^ 2 =
        anharmS * anharmT * (anharmS * anharmS) * anharmT * anharmS := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [anharmS_sq, mul_one, mul_assoc anharmS anharmT anharmT, anharmT_sq, mul_one,
        anharmS_sq]

theorem orderOf_anharmS' : orderOf anharmS' = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime (by rw [pow_two]; exact anharmS_sq) anharmS_ne_one

theorem orderOf_anharmTS' : orderOf (anharmT' * anharmS') = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime anharmTS_pow_three anharmTS_ne_one

theorem orderOf_anharmSTS' : orderOf (anharmS' * (anharmT' * anharmS')) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_eq_prime anharmSTS_pow_two anharmSTS_ne_one

theorem closure_anharm_generators :
    Subgroup.closure ({anharmS', anharmT' * anharmS'} : Set anharmonicGroup) = ⊤ := by
  have htop : Subgroup.closure ({anharmS', anharmT'} : Set anharmonicGroup) = ⊤ := by
    have hset : (((↑) : anharmonicGroup → Equiv.Perm Punctured) ⁻¹'
        ({anharmS, anharmT} : Set (Equiv.Perm Punctured))) = {anharmS', anharmT'} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
      rfl
    rw [← hset]
    exact Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact Subgroup.subset_closure (Or.inl rfl)
  · have hS2 : anharmS' * anharmS' = 1 := Subtype.ext anharmS_sq
    have h : anharmT' = (anharmT' * anharmS') * anharmS' := by rw [mul_assoc, hS2, mul_one]
    have hmem : (anharmT' * anharmS') * anharmS' ∈
        Subgroup.closure ({anharmS', anharmT' * anharmS'} : Set anharmonicGroup) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr rfl))
        (Subgroup.subset_closure (Or.inl rfl))
    rw [← h] at hmem
    exact hmem

/-- **The `j`-cover of the λ-line** as a connected `(2, 3, 2)` monodromy cover. -/
def lambdaJCover : MonodromyCover 2 3 2 anharmonicGroup :=
  regularCover anharmS' (anharmT' * anharmS') orderOf_anharmS' orderOf_anharmTS'
    orderOf_anharmSTS' closure_anharm_generators

theorem card_anharmonicGroup_le : Fintype.card anharmonicGroup ≤ 6 := by
  rw [← Nat.card_eq_fintype_card]
  show Nat.card ((anharmonicGroup : Set (Equiv.Perm Punctured))) ≤ 6
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_le_ncard anharmonicGroup_subset_sixSet sixSet_finite).trans ?_
  unfold sixSet
  refine (Set.ncard_insert_le _ _).trans ?_
  refine (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Set.ncard_insert_le _ _) 1) 1) 1).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Set.ncard_insert_le _ _) 1) 1) 1) 1).trans ?_
  rw [Set.ncard_singleton]

/-- **The λ-line is a six-sheeted sphere over the `j`-line**: the anharmonic group has order `6`,
the cover has Euler characteristic `2` (genus `0`), and the fibres over `1728`, `0`, `∞` have
`3`, `2`, `3` points. -/
theorem lambdaJCover_genus_zero :
    lambdaJCover.degree = 6 ∧ lambdaJCover.eulerChar = 2 ∧
      lambdaJCover.fibreX = 3 ∧ lambdaJCover.fibreY = 2 ∧ lambdaJCover.fibreZ = 3 := by
  obtain ⟨g, hχ, hD⟩ := lambdaJCover.modular_capacity_exact (le_refl 2)
  have hX := lambdaJCover.a_mul_fibreX (le_refl 2)
  have hY := lambdaJCover.b_mul_fibreY (by norm_num)
  have hZ := lambdaJCover.c_mul_fibreZ (le_refl 2)
  have hle : lambdaJCover.degree ≤ 6 := card_anharmonicGroup_le
  have hpos : 0 < lambdaJCover.degree := Fintype.card_pos
  have hZ' : (2 : ℤ) * lambdaJCover.fibreZ = lambdaJCover.degree := by exact_mod_cast hZ
  have hle' : (lambdaJCover.degree : ℤ) ≤ 6 := by exact_mod_cast hle
  have hpos' : (0 : ℤ) < lambdaJCover.degree := by exact_mod_cast hpos
  have hg : g = 0 := by omega
  have hD6 : lambdaJCover.degree = 6 := by
    have : (lambdaJCover.degree : ℤ) = 6 := by omega
    exact_mod_cast this
  refine ⟨hD6, by rw [hχ, hg]; norm_num, by omega, by omega, by omega⟩

/-- The anharmonic group has exactly six elements. -/
theorem card_anharmonicGroup : Fintype.card anharmonicGroup = 6 := lambdaJCover_genus_zero.1

end GaloisForLFunctions.KodairaParshinAbc
