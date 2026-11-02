import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith

/-!
# Unit-window counts for separated height blocks

A unit interval meets at most one block when successive blocks have a gap
greater than one. Per-block three-node bounds therefore give an embedding
of every global unit-window index set into `Fin 3`.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- A unit interval cannot meet two height blocks separated by more than one. -/
lemma same_block_of_unit_interval {n : ℕ → ℕ} {H span : ℕ → ℝ}
    (hspan : ∀ k, 0 < span k) (hgap : ∀ k, H k+span k+1 < H (k+1))
    {γ : (k : ℕ) → Fin (n k) → ℝ}
    (hmem : ∀ k j, γ k j ∈ Set.Icc (H k) (H k+span k))
    {T : ℝ} {i j : (k : ℕ) × Fin (n k)}
    (hi : γ i.1 i.2 ∈ Set.Icc T (T+1))
    (hj : γ j.1 j.2 ∈ Set.Icc T (T+1)) : i.1=j.1 := by
  have hmono : StrictMono H := strictMono_nat_of_lt_succ fun k => by
    have hh := hgap k
    linarith only [hh,hspan k]
  have hne : ∀ i j : (k : ℕ) × Fin (n k),
      γ i.1 i.2 ∈ Set.Icc T (T+1) → γ j.1 j.2 ∈ Set.Icc T (T+1) → ¬i.1<j.1 := by
    intro i j hi hj hij
    have hH := hmono.monotone (Nat.succ_le_of_lt hij)
    have hg := hgap i.1
    have him := hmem i.1 i.2
    have hjm := hmem j.1 j.2
    linarith only [hH,hg,him.2,hjm.1,hi.1,hj.2]
  exact le_antisymm (le_of_not_gt (hne j i hj hi)) (le_of_not_gt (hne i j hi hj))

/-- Per-block three-node bounds become a global bound once the blocks are separated. -/
theorem unit_interval_embedding_of_separated_blocks {n : ℕ → ℕ} {H span : ℕ → ℝ}
    (hspan : ∀ k, 0 < span k) (hgap : ∀ k, H k+span k+1 < H (k+1))
    {γ : (k : ℕ) → Fin (n k) → ℝ}
    (hmem : ∀ k j, γ k j ∈ Set.Icc (H k) (H k+span k))
    (hcount : ∀ k T, ((univ : Finset (Fin (n k))).filter
      (fun j => γ k j ∈ Set.Icc T (T+1))).card ≤ 3) (T : ℝ) :
    Nonempty ({i : (k : ℕ) × Fin (n k) // γ i.1 i.2 ∈ Set.Icc T (T+1)} ↪ Fin 3) := by
  classical
  let A := {i : (k : ℕ) × Fin (n k) // γ i.1 i.2 ∈ Set.Icc T (T+1)}
  by_cases hA : Nonempty A
  · let i₀ : A := Classical.choice hA
    let k := i₀.val.1
    have hsame (i : A) : i.val.1=k := same_block_of_unit_interval hspan hgap hmem i.property i₀.property
    let S : Finset (Fin (n k)) := univ.filter fun j => γ k j ∈ Set.Icc T (T+1)
    let f : A → S := fun i => ⟨Fin.cast (congrArg n (hsame i)) i.val.2,by
      rcases i with ⟨⟨l,j⟩,hi⟩
      have hl : l=k := hsame ⟨⟨l,j⟩,hi⟩
      subst l
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      change γ k j ∈ Set.Icc T (T+1)
      exact hi⟩
    have hf : Function.Injective f := by
      rintro ⟨⟨l,i⟩,hi⟩ ⟨⟨m,j⟩,hj⟩ he
      have hl : l=k := hsame ⟨⟨l,i⟩,hi⟩
      have hm : m=k := hsame ⟨⟨m,j⟩,hj⟩
      subst l
      subst m
      have hij : i=j := by
        have hv := congrArg (fun x : S => x.val.val) he
        exact Fin.ext hv
      subst j
      rfl
    have hcard : Fintype.card S ≤ 3 := by
      simpa only [Fintype.card_coe] using hcount k T
    let e : S ↪ Fin 3 := {
      toFun := fun j => ⟨(Fintype.equivFin S j).val,
        Nat.lt_of_lt_of_le (Fintype.equivFin S j).isLt hcard⟩
      inj' := by
        intro i j he
        apply (Fintype.equivFin S).injective
        exact Fin.ext (congrArg (fun v : Fin 3 => v.val) he)
    }
    exact ⟨(⟨f,hf⟩ : A ↪ S).trans e⟩
  · haveI : IsEmpty A := ⟨fun i => hA ⟨i⟩⟩
    exact ⟨⟨fun i => isEmptyElim i,fun i => isEmptyElim i⟩⟩

#print axioms unit_interval_embedding_of_separated_blocks
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
