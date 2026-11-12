import GaloisForLFunctions.RHTower.Artin.ArtinMonomialSpan
import GaloisForLFunctions.RHTower.Artin.ArtinOrbitDecompositionOfACharacter
import GaloisForLFunctions.RHTower.Artin.ArtinScalarActionAndTheCommutatorQuotient
import Mathlib.GroupTheory.Nilpotent

/-!
# The characters of a finite nilpotent group are monomial

**Theorem** (`fdCharacterSet_subset_monomialSpan_of_nilpotent`). Every character of a finite
nilpotent group `E` is an integer combination of characters induced from linear characters of
subgroups.

The proof is by induction on `|E|`.

* If `E` is abelian, its characters are sums of linear characters.
* Otherwise there is `a` in the second centre and not in the centre
  (`exists_commutator_mem_center_not_mem_center`); the subgroup `A = ⟨a⟩ · Z(E)`
  (`centerZpowers`) is abelian, normal and not central. A character of `E` is the sum, over the
  orbits of the characters `χ` of `A`, of `Ind_{T_χ}^E F_χ`, with `T_χ` the stabilizer of `χ`
  and `F_χ` a character of `T_χ`.
  - If `T_χ ≠ E`, then `F_χ` is monomial by induction, and induction in stages applies.
  - If `T_χ = E`, then `A` acts by the scalars `χ` on the range of the idempotent `e_χ`, the
    function `F_χ` is the pullback of a character of `E / [A, E]`, a nilpotent group of smaller
    order since `A` is not central, and the pullback of a monomial character is monomial.
-/

open scoped Classical BigOperators IsMulCommutative commutatorElement

noncomputable section

universe u

namespace GaloisForLFunctions

attribute [local instance] finiteLinearCharacter fintypeLinearCharacter conjCharacterAction

/-! ### An abelian normal subgroup that is not central -/

section GroupTheory

variable {E : Type u} [Group E]

/-- **In a nilpotent group that is not abelian the second centre is larger than the centre.** -/
theorem exists_commutator_mem_center_not_mem_center [Group.IsNilpotent E]
    (hE : ¬ ∀ a b : E, a * b = b * a) :
    ∃ a : E, (∀ y : E, ⁅a, y⁆ ∈ Subgroup.center E) ∧ a ∉ Subgroup.center E := by
  by_contra hcon
  push Not at hcon
  -- otherwise the upper central series stops at the centre
  have hseries : ∀ n : ℕ, Subgroup.upperCentralSeries E (n + 1) ≤ Subgroup.center E := by
    intro n
    induction n with
    | zero => rw [zero_add, Subgroup.upperCentralSeries_one]
    | succ n ih =>
      intro x hx
      exact hcon x fun y => ih (Subgroup.mem_upperCentralSeries_succ_iff.mp hx y)
  obtain ⟨n, hn⟩ := Group.IsNilpotent.nilpotent E
  refine hE fun a b => ?_
  cases n with
  | zero =>
    rw [Subgroup.upperCentralSeries_zero] at hn
    have ha : a ∈ (⊥ : Subgroup E) := hn ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup E) := hn ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb]
  | succ n =>
    have hb : b ∈ Subgroup.center E := hseries n (hn ▸ Subgroup.mem_top b)
    exact Subgroup.mem_center_iff.mp hb a

/-- The subgroup `⟨a⟩ · Z(E)`. -/
def centerZpowers (a : E) : Subgroup E where
  carrier := {x | ∃ k : ℤ, ∃ z ∈ Subgroup.center E, x = a ^ k * z}
  one_mem' := ⟨0, 1, one_mem _, by rw [zpow_zero, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨k, z, hz, rfl⟩ ⟨l, z', hz', rfl⟩
    refine ⟨k + l, z * z', mul_mem hz hz', ?_⟩
    calc a ^ k * z * (a ^ l * z') = a ^ k * (z * a ^ l) * z' := by simp only [mul_assoc]
      _ = a ^ k * (a ^ l * z) * z' := by rw [← Subgroup.mem_center_iff.mp hz (a ^ l)]
      _ = a ^ (k + l) * (z * z') := by
        rw [zpow_add]
        simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨k, z, hz, rfl⟩
    refine ⟨-k, z⁻¹, inv_mem hz, ?_⟩
    rw [mul_inv_rev, ← zpow_neg]
    exact (Subgroup.mem_center_iff.mp (inv_mem hz) (a ^ (-k))).symm

theorem self_mem_centerZpowers (a : E) : a ∈ centerZpowers a :=
  ⟨1, 1, one_mem _, by rw [zpow_one, mul_one]⟩

/-- `⟨a⟩ · Z(E)` is abelian. -/
theorem centerZpowers_comm (a : E) : IsMulCommutative (centerZpowers a) := by
  rw [isMulCommutative_iff]
  rintro ⟨_, k, z, hz, rfl⟩ ⟨_, l, z', hz', rfl⟩
  apply Subtype.ext
  have h1 : Commute (a ^ k) (a ^ l * z') :=
    (Commute.zpow_zpow_self a k l).mul_right (Subgroup.mem_center_iff.mp hz' (a ^ k))
  have h2 : Commute z (a ^ l * z') := (Subgroup.mem_center_iff.mp hz (a ^ l * z')).symm
  exact (h1.mul_left h2).eq

/-- `⟨a⟩ · Z(E)` is normal when every commutator `[a, y]` is central. -/
theorem centerZpowers_normal {a : E} (ha : ∀ y : E, ⁅a, y⁆ ∈ Subgroup.center E) :
    (centerZpowers a).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨k, z, hz, rfl⟩ g
  have hc : ⁅g, a⁆ ∈ Subgroup.center E := by
    rw [← commutatorElement_inv]
    exact inv_mem (ha g)
  have hck : ⁅g, a⁆ ^ k ∈ Subgroup.center E := zpow_mem hc k
  refine ⟨k, ⁅g, a⁆ ^ k * z, mul_mem hck hz, ?_⟩
  -- `g a g⁻¹ = [g, a] a`
  have hconj : g * a ^ k * g⁻¹ = (⁅g, a⁆ * a) ^ k := by
    rw [commutatorElement_def, inv_mul_cancel_right, conj_zpow]
  have hcomm : Commute ⁅g, a⁆ a := (Subgroup.mem_center_iff.mp hc a).symm
  calc g * (a ^ k * z) * g⁻¹ = g * a ^ k * g⁻¹ * (g * z * g⁻¹) := by
        simp only [mul_assoc, inv_mul_cancel_left]
    _ = (⁅g, a⁆ * a) ^ k * z := by
        rw [hconj, Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
    _ = ⁅g, a⁆ ^ k * a ^ k * z := by rw [hcomm.mul_zpow]
    _ = a ^ k * (⁅g, a⁆ ^ k * z) := by
        rw [← Subgroup.mem_center_iff.mp hck (a ^ k), mul_assoc]

/-- **A nilpotent group that is not abelian has an abelian normal subgroup that is not
central.** -/
theorem exists_normal_comm_not_le_center [Group.IsNilpotent E]
    (hE : ¬ ∀ a b : E, a * b = b * a) :
    ∃ A : Subgroup E, A.Normal ∧ IsMulCommutative A ∧ ¬ A ≤ Subgroup.center E := by
  obtain ⟨a, ha, hna⟩ := exists_commutator_mem_center_not_mem_center hE
  exact ⟨centerZpowers a, centerZpowers_normal ha, centerZpowers_comm a,
    fun hle => hna (hle (self_mem_centerZpowers a))⟩

end GroupTheory

/-! ### The induction -/

/-- The statement for groups of a given order. -/
theorem fdCharacterSet_subset_monomialSpan_of_card (n : ℕ) :
    ∀ (E : Type u) [Group E] [Fintype E] [Group.IsNilpotent E], Nat.card E = n →
      fdCharacterSet E ⊆ monomialSpan E := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E _ _ _ hn
    by_cases hab : ∀ a b : E, a * b = b * a
    · exact fdCharacterSet_subset_monomialSpan_of_comm hab
    · obtain ⟨A, hAn, hAc, hAz⟩ := exists_normal_comm_not_le_center hab
      haveI := hAn
      haveI := hAc
      rintro _ ⟨V, rfl⟩
      show Representation.character V.ρ ∈ monomialSpan E
      refine character_mem_of_stabilizerInduced_mem A V.ρ (monomialSpan E) fun χ => ?_
      by_cases hT : MulAction.stabilizer E χ = ⊤
      · -- `A` acts by scalars on the range of `e_χ`: pass to `E / [A, E]`
        have hfix : ∀ g : E, g • χ = χ := fun g =>
          MulAction.mem_stabilizer_iff.mp (hT ▸ Subgroup.mem_top g)
        have hcomm : ∀ g : E, V.ρ g * isotypicProjector A V.ρ χ =
            isotypicProjector A V.ρ χ * V.ρ g := fun g => by
          rw [apply_mul_isotypicProjector_eq, hfix g]
        obtain ⟨τ, hτ, hτg⟩ := exists_character_quotient_commutator V.ρ
          (isotypicProjector A V.ρ χ) A (isotypicProjector_idempotent A V.ρ χ) hcomm χ
          (apply_mul_isotypicProjector A V.ρ χ)
        -- the commutator subgroup is not trivial, since `A` is not central
        have hN : ⁅A, (⊤ : Subgroup E)⁆ ≠ ⊥ := by
          intro hbot
          refine hAz fun a ha => Subgroup.mem_center_iff.mpr fun g => ?_
          have hmem : ⁅a, g⁆ ∈ ⁅A, (⊤ : Subgroup E)⁆ :=
            Subgroup.commutator_mem_commutator ha (Subgroup.mem_top g)
          rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at hmem
          exact hmem.eq.symm
        have hlt : Nat.card (E ⧸ ⁅A, (⊤ : Subgroup E)⁆) < n := by
          have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ⁅A, (⊤ : Subgroup E)⁆
          have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hN
          have hpos : 0 < Nat.card (E ⧸ ⁅A, (⊤ : Subgroup E)⁆) := Nat.card_pos
          rw [← hn, hcard]
          nlinarith
        haveI := Group.nilpotent_quotient_of_nilpotent ⁅A, (⊤ : Subgroup E)⁆
        have hmono := ih _ hlt (E ⧸ ⁅A, (⊤ : Subgroup E)⁆) rfl hτ
        have hcomp := comp_mem_monomialSpan (QuotientGroup.mk' ⁅A, (⊤ : Subgroup E)⁆)
          (QuotientGroup.mk'_surjective _) hmono
        -- with full stabilizer the induced function is `F_χ` itself
        have e : stabilizerInduced A V.ρ χ =
            fun g => τ (QuotientGroup.mk' ⁅A, (⊤ : Subgroup E)⁆ g) := by
          funext g
          have hE : (Nat.card E : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
          have hcardT : Nat.card (MulAction.stabilizer E χ) = Nat.card E := by
            rw [hT, Subgroup.card_top]
          have hsum : ∑ x : E, isotypicTrace A V.ρ (x • χ) g =
              (Nat.card E : ℂ) * isotypicTrace A V.ρ χ g := by
            rw [Finset.sum_congr rfl fun x _ =>
              congrArg (fun ψ => isotypicTrace A V.ρ ψ g) (hfix x), Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
          have h := card_mul_stabilizerInduced A V.ρ χ g
          rw [hcardT, hsum] at h
          rw [mul_left_cancel₀ hE h]
          exact (hτg g).symm
        rw [e]
        exact hcomp
      · -- a proper stabilizer: induction in stages
        have hlt : Nat.card (MulAction.stabilizer E χ) < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group _)
            fun h => hT ((Subgroup.card_eq_iff_eq_top _).mp h)
        have hmem := ih _ hlt (MulAction.stabilizer E χ) rfl
          (isotypicTrace_mem_fdCharacterSet_stabilizer A V.ρ χ)
        exact inducedFunction_mem_monomialSpan _ hmem

/-- **Every character of a finite nilpotent group is an integer combination of characters
induced from linear characters of subgroups.** -/
theorem fdCharacterSet_subset_monomialSpan_of_nilpotent (E : Type u) [Group E] [Fintype E]
    [Group.IsNilpotent E] : fdCharacterSet E ⊆ monomialSpan E :=
  fdCharacterSet_subset_monomialSpan_of_card (Nat.card E) E rfl

end GaloisForLFunctions
