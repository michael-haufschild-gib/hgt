import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CountableColoring
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CommonPivotCycles

/-!
# Identification of independent coloring with the cycle character

Invariant subsets split the word sum. A cycle fixes precisely constant words on its support;
disjoint-cycle induction therefore identifies the trace with the product of color power sums
for every finite permutation. Its positivity follows from the fixed-word Gram construction.
-/

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace GaloisForLFunctions.SymmetricCharacters

variable {A X Y : Type*} [Fintype X] [Fintype Y]

/-- Relabeling the finite position set preserves every fixed-word sum. -/
theorem wordCharacter_permCongr (w : A → NNReal) (e : X ≃ Y) (σ : Equiv.Perm X) :
    wordCharacter w (e.permCongr σ) = wordCharacter w σ := by
  let f : (Y → A) ≃ (X → A) := Equiv.arrowCongr e.symm (Equiv.refl A)
  have he (x : Y → A) :
      (if x ∘ e.permCongr σ = x then wordWeight w x else 0) =
      (if (f x) ∘ σ = f x then wordWeight w (f x) else 0) := by
    have hweight : wordWeight w (f x) = wordWeight w x :=
      Equiv.prod_comp e (fun y => (w (x y) : ℝ))
    rw [hweight]
    have hfix : x ∘ e.permCongr σ = x ↔ (x ∘ e) ∘ σ = x ∘ e := by
      constructor
      · intro h
        funext i
        simpa [Equiv.permCongr_apply] using congrFun h (e i)
      · intro h
        funext i
        simpa [Equiv.permCongr_apply] using congrFun h (e.symm i)
    change (if x ∘ e.permCongr σ = x then wordWeight w x else 0) =
      (if (x ∘ e) ∘ σ = x ∘ e then wordWeight w x else 0)
    simp only [hfix]
  exact (tsum_congr he).trans (f.tsum_eq
    (fun x : X → A => if x ∘ σ = x then wordWeight w x else 0))

/-- Independent letters factor across a subset and its complement. -/
theorem wordCharacter_subtypeCongr (w : A → NNReal) (hw : Summable (fun a => (w a : ℝ)))
    (p : X → Prop) [DecidablePred p]
    (σ : Equiv.Perm {x // p x}) (τ : Equiv.Perm {x // ¬p x}) :
    wordCharacter w (σ.subtypeCongr τ) = wordCharacter w σ * wordCharacter w τ := by
  rw [Equiv.Perm.subtypeCongr, wordCharacter_permCongr,
    wordCharacter_sumCongr w hw]


open scoped ComplexOrder
private theorem realMatrix_posSemidef_of_complex {I : Type*} [Fintype I] (M : Matrix I I ℝ)
    (h : Matrix.PosSemidef (fun i j => (M i j : ℂ))) : M.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    have hh := congrArg Complex.re (h.isHermitian.apply i j)
    simpa using hh
  · intro v
    apply Complex.zero_le_real.mp
    convert h.dotProduct_mulVec_nonneg (fun i => (v i : ℂ)) using 1
    simp [dotProduct, Matrix.mulVec]

/-- An invariant subset splits the character into its two restrictions. -/
theorem wordCharacter_split (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (p : X → Prop) [DecidablePred p]
    (σ : Equiv.Perm X) (hσ : ∀ x, p (σ x) ↔ p x) :
    wordCharacter w σ = wordCharacter w (σ.subtypePerm hσ) *
      wordCharacter w (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) := by
  have he : (σ.subtypePerm hσ).subtypeCongr
      (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) = σ := by
    ext x
    by_cases hx : p x
    · simpa using Equiv.Perm.subtypeCongr.left_apply
        (σ.subtypePerm hσ) (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) hx
    · simpa using Equiv.Perm.subtypeCongr.right_apply
        (σ.subtypePerm hσ) (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) hx
  calc
    wordCharacter w σ = wordCharacter w ((σ.subtypePerm hσ).subtypeCongr
        (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not))) := congrArg (wordCharacter w) he.symm
    _ = _ := by
      rw [Equiv.Perm.subtypeCongr, wordCharacter_permCongr,
        wordCharacter_sumCongr w hw]

/-- A transitive permutation fixes exactly the constant words. -/
theorem wordCharacter_transitive (w : A → NNReal) (σ : Equiv.Perm X)
    (hσ : σ.IsCycleOn Set.univ) (a : X) :
    wordCharacter w σ = ∑' b, (w b : ℝ) ^ Fintype.card X := by
  have hfix (x : X → A) : x ∘ σ = x ↔ x = fun _ => x a := by
    constructor
    · intro h
      have hp (n : ℕ) : x ((σ ^ n) a) = x a := by
        induction n with
        | zero => rfl
        | succ n ih =>
          rw [pow_succ', Equiv.Perm.mul_apply, ← Function.comp_apply (f := x)]
          rw [h, ih]
      funext b
      obtain ⟨n, hn⟩ := hσ.exists_pow_eq' (Set.toFinite _) (Set.mem_univ a) (Set.mem_univ b)
      rw [← hn]
      exact hp n
    · intro h
      rw [h]
      rfl
  let c : A → (X → A) := fun b _ => b
  have hc : Function.Injective c := fun b d h => congrFun h a
  let f : (X → A) → ℝ := fun x => if x ∘ σ = x then wordWeight w x else 0
  have hs : Function.support f ⊆ Set.range c := by
    intro x hx
    have hh : x ∘ σ = x := by
      by_contra hn
      exact hx (if_neg hn)
    exact ⟨x a, (hfix x |>.mp hh).symm⟩
  change (∑' x, f x) = _
  rw [← hc.tsum_eq hs]
  apply tsum_congr
  intro b
  simp [f, c, wordWeight, Function.comp_def]

/-- Disjoint permutations act on independent sets of letters. -/
theorem wordCharacter_disjoint (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (hm : (∑' a, (w a : ℝ)) = 1)
    (σ τ : Equiv.Perm X) (hd : Equiv.Perm.Disjoint σ τ) :
    wordCharacter w (σ * τ) = wordCharacter w σ * wordCharacter w τ := by
  let p : X → Prop := fun x => σ x ≠ x
  have hσ (x : X) : p (σ x) ↔ p x := σ.apply_eq_iff_eq.not
  have hτfix (x : X) (hx : p x) : τ x = x := (hd x).resolve_left hx
  have hτ (x : X) : p (τ x) ↔ p x := by
    constructor
    · intro hx
      have he : τ x = x := τ.injective (hτfix (τ x) hx)
      rwa [he] at hx
    · intro hx
      rwa [hτfix x hx]
  have hστ (x : X) : p ((σ * τ) x) ↔ p x := (hσ (τ x)).trans (hτ x)
  have hσc : σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not) = 1 := by
    ext x
    exact not_not.mp x.property
  have hτp : τ.subtypePerm hτ = 1 := by
    ext x
    exact hτfix x x.property
  have hprod : (σ * τ).subtypePerm hστ = σ.subtypePerm hσ := by
    ext x
    change σ (τ x) = σ x
    rw [hτfix x x.property]
  have hprodc : (σ * τ).subtypePerm (p := fun x => ¬p x) (fun x => (hστ x).not) =
      τ.subtypePerm (p := fun x => ¬p x) (fun x => (hτ x).not) := by
    ext x
    change σ (τ x) = τ x
    exact not_not.mp (fun h => x.property ((hτ x).mp h))
  rw [wordCharacter_split w hw p (σ * τ) hστ,
    wordCharacter_split w hw p σ hσ, wordCharacter_split w hw p τ hτ,
    hprod, hprodc, hσc, hτp, wordCharacter_one w hw, wordCharacter_one w hw, hm,
    one_pow, one_pow, mul_one, one_mul]

/-- A single nontrivial cycle contributes the power sum of its support size. -/
theorem wordCharacter_isCycle (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (hm : (∑' a, (w a : ℝ)) = 1)
    (σ : Equiv.Perm X) (hcycle : σ.IsCycle) :
    wordCharacter w σ = ∑' b, (w b : ℝ) ^ σ.support.card := by
  let p : X → Prop := fun x => σ x ≠ x
  have hσ (x : X) : p (σ x) ↔ p x := σ.apply_eq_iff_eq.not
  have hσc : σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not) = 1 := by
    ext x
    exact not_not.mp x.property
  rw [wordCharacter_split w hw p σ hσ, hσc, wordCharacter_one w hw, hm,
    one_pow, mul_one]
  obtain ⟨a, ha⟩ := hcycle.nonempty_support
  have hc : (σ.subtypePerm hσ).IsCycleOn Set.univ := hcycle.isCycleOn.subtypePerm
  rw [wordCharacter_transitive w _ hc ⟨a, Equiv.Perm.mem_support.mp ha⟩]
  have hcard : Fintype.card {x // p x} = σ.support.card := by
    simp only [Fintype.card_subtype, p, Equiv.Perm.support]
  rw [hcard]

/-- The independent-color character equals the literal product over all nontrivial cycles. -/
theorem wordCharacter_eq_cycleMomentCharacter (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (hm : (∑' a, (w a : ℝ)) = 1)
    (σ : Equiv.Perm X) :
    wordCharacter w σ = cycleMomentCharacter (fun n => ∑' a, (w a : ℝ) ^ (n + 1)) σ := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => rw [wordCharacter_one w hw, hm, one_pow, cycleMomentCharacter_one]
  | base_cycles σ hσ =>
    rw [wordCharacter_isCycle w hw hm σ hσ]
    have hpos : 1 ≤ σ.support.card := le_trans (by omega) hσ.two_le_card_support
    simp only [cycleMomentCharacter, hσ.cycleType, Multiset.map_singleton,
      Multiset.prod_singleton, Nat.sub_add_cancel hpos]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [wordCharacter_disjoint w hw hm σ τ hd, hσ, hτ]
    simp only [cycleMomentCharacter, hd.cycleType_mul, Multiset.map_add, Multiset.prod_add]

/-- A probability alphabet produces a positive cycle family on every finite symmetric group. -/
theorem wordCharacter_positiveCycleFamily (w : A → NNReal)
    (hw : Summable (fun a => (w a : ℝ))) (hm : (∑' a, (w a : ℝ)) = 1) :
    PositiveCycleFamily (fun n => ∑' a, (w a : ℝ) ^ (n + 1)) := by
  intro X J _ _ g
  have h := realMatrix_posSemidef_of_complex _ (wordCharacter_posSemidef w hw g)
  simpa only [wordCharacter_eq_cycleMomentCharacter w hw hm] using h

end GaloisForLFunctions.SymmetricCharacters
