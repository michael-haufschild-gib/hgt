import Mathlib.Algebra.Field.Rat
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FieldSimp

/-!
# Uniform sample fibers inside the symmetric group

Equal-size finite samples have equally large fibers under the map sending a permutation to the
sample it transports. The common fiber cardinality and its normalized rational mass are the
counting content behind sample/permutation independence.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Boolean membership indicator of a finite sample. -/
def sampleIndicator (s : Finset α) (a : α) : Bool := decide (a ∈ s)

theorem card_sampleIndicator_true (s : Finset α) :
    Fintype.card {a // sampleIndicator s a = true} = s.card := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl α) (by simp [sampleIndicator])

theorem card_sampleIndicator_false (s : Finset α) :
    Fintype.card {a // sampleIndicator s a = false} = Fintype.card α - s.card := by
  rw [← Finset.card_compl, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl α) (by simp [sampleIndicator])

/-- Permutations preserving a sample may independently permute the sample and its complement. -/
theorem card_permutations_preserving_sample (s : Finset α) :
    Fintype.card {σ : Equiv.Perm α // sampleIndicator s ∘ σ = sampleIndicator s} =
      s.card.factorial * (Fintype.card α - s.card).factorial := by
  rw [DomMulAct.stabilizer_card (sampleIndicator s)]
  simp [card_sampleIndicator_true, card_sampleIndicator_false]

/-- A canonical ambient permutation extending any equivalence between equal-size samples. -/
noncomputable def sampleTransportPerm (s t : Finset α) (h : s.card = t.card) :
    Equiv.Perm α :=
  Equiv.extendSubtype (Finset.equivOfCardEq h)

theorem sampleIndicator_comp_sampleTransportPerm (s t : Finset α)
    (h : s.card = t.card) :
    sampleIndicator t ∘ sampleTransportPerm s t h = sampleIndicator s := by
  funext x
  by_cases hx : x ∈ s
  · rw [Function.comp_apply, sampleTransportPerm,
      Equiv.extendSubtype_apply_of_mem (Finset.equivOfCardEq h) x hx]
    simp [sampleIndicator]
    exact hx
  · rw [Function.comp_apply, sampleTransportPerm,
      Equiv.extendSubtype_apply_of_not_mem (Finset.equivOfCardEq h) x hx]
    have hout :
        ((Finset.equivOfCardEq h).toCompl ⟨x, hx⟩ : α) ∉ t :=
      (Finset.equivOfCardEq h).toCompl ⟨x, hx⟩ |>.property
    simp [sampleIndicator, hx]
    exact hout

/-- Composition by one transporter identifies a stabilizer with the corresponding transport
fiber. -/
def permCompositionFiberEquiv {f g : α → Bool} (b : Equiv.Perm α)
    (hb : g ∘ b = f) :
    {σ : Equiv.Perm α // f ∘ σ = f} ≃
      {σ : Equiv.Perm α // g ∘ σ = f} where
  toFun σ := ⟨σ.1.trans b, by
    funext x
    change g (b (σ.1 x)) = f x
    calc
      g (b (σ.1 x)) = f (σ.1 x) := by
        simpa only [Function.comp_apply] using congrFun hb (σ.1 x)
      _ = f x := by
        simpa only [Function.comp_apply] using congrFun σ.2 x⟩
  invFun σ := ⟨σ.1.trans b.symm, by
    funext x
    change f (b.symm (σ.1 x)) = f x
    calc
      f (b.symm (σ.1 x)) = g (b (b.symm (σ.1 x))) := by
        symm
        simpa only [Function.comp_apply] using congrFun hb (b.symm (σ.1 x))
      _ = g (σ.1 x) := by rw [b.apply_symm_apply]
      _ = f x := by
        simpa only [Function.comp_apply] using congrFun σ.2 x⟩
  left_inv σ := by
    apply Subtype.ext
    ext x
    simp
  right_inv σ := by
    apply Subtype.ext
    ext x
    simp

/-- Every equal-size target sample has the same permutation-fiber cardinality. -/
theorem card_permutations_mapping_sample (s t : Finset α) (h : s.card = t.card) :
    Fintype.card {σ : Equiv.Perm α // sampleIndicator t ∘ σ = sampleIndicator s} =
      s.card.factorial * (Fintype.card α - s.card).factorial := by
  rw [← card_permutations_preserving_sample s]
  exact Fintype.card_congr
    (permCompositionFiberEquiv (sampleTransportPerm s t h)
      (sampleIndicator_comp_sampleTransportPerm s t h)).symm

/-- Under the uniform distribution on ambient permutations, each equal-size sample fiber has
rational mass `1 / choose n k`. -/
theorem uniform_sample_fiber_mass (s t : Finset α) (h : s.card = t.card) :
    (Fintype.card
        {σ : Equiv.Perm α // sampleIndicator t ∘ σ = sampleIndicator s} : ℚ) /
        ((Fintype.card α).factorial : ℚ) =
      1 / ((Fintype.card α).choose s.card : ℚ) := by
  rw [card_permutations_mapping_sample s t h]
  have hs : s.card ≤ Fintype.card α := Finset.card_le_univ s
  have hchoose : (Fintype.card α).choose s.card ≠ 0 := Nat.choose_ne_zero hs
  have htotal : (Fintype.card α).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hchooseQ : ((Fintype.card α).choose s.card : ℚ) ≠ 0 := by exact_mod_cast hchoose
  have htotalQ : ((Fintype.card α).factorial : ℚ) ≠ 0 := by exact_mod_cast htotal
  field_simp [hchooseQ, htotalQ]
  have hidQ :
      ((Fintype.card α).choose s.card : ℚ) * (s.card.factorial : ℚ) *
          ((Fintype.card α - s.card).factorial : ℚ) =
        ((Fintype.card α).factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hs
  simpa [mul_comm, mul_left_comm, mul_assoc] using hidQ

end GaloisForLFunctions.HTGeometry
