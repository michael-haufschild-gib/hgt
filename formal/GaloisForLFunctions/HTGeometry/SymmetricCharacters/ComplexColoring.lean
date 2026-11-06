import GaloisForLFunctions.HTGeometry.SymmetricCharacters.WordProducts
import GaloisForLFunctions.HTGeometry.SymmetricCharacters.CommonPivotCycles
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Absolutely summable complex color alphabets

Complex fixed-word traces factor over permutation cycles. Absolute summability justifies
word reindexing and independent block products; no positivity of individual colors is used.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SymmetricCharacters
variable {A X Y : Type*} [Fintype X] [Fintype Y]

/-- Product of the colors assigned to finitely many positions. -/
def complexWordWeight (w : A → ℂ) (x : X → A) : ℂ := ∏ i, w (x i)

/-- Trace of a permutation on independent words with complex letter weights. -/
def complexWordCharacter (w : A → ℂ) (σ : Equiv.Perm X) : ℂ :=
  ∑' x : X → A, if x ∘ σ = x then complexWordWeight w x else 0

/-- Literal product of the prescribed values over nontrivial permutation cycles. -/
def complexCycleCharacter (p : ℕ → ℂ) (σ : Equiv.Perm X) : ℂ :=
  (σ.cycleType.map (fun k => p (k - 1))).prod

private theorem complexWordWeight_norm_summable (w : A → ℂ) (hw : Summable w) :
    Summable (fun x : X → A => ‖complexWordWeight w x‖) := by
  let e : (Fin (Fintype.card X) → A) ≃ (X → A) :=
    Equiv.arrowCongr (Fintype.equivFin X).symm (Equiv.refl A)
  apply e.summable_iff.mp
  have hs := (wordProducts_summable_and_tsum hw.norm (fun a => norm_nonneg (w a))
    (Fintype.card X)).1
  refine hs.congr fun x => ?_
  simp only [complexWordWeight, norm_prod]
  exact (Equiv.prod_comp (Fintype.equivFin X) (fun j => ‖w (x j)‖)).symm

theorem summable_complexWordWeight (w : A → ℂ) (hw : Summable w) :
    Summable (complexWordWeight (X := X) w) :=
  (complexWordWeight_norm_summable w hw).of_norm

private theorem complexWordWeight_fin_tsum (w : A → ℂ) (hw : Summable w) (n : ℕ) :
    (∑' x : Fin n → A, complexWordWeight w x) = (∑' a, w a) ^ n := by
  induction n with
  | zero =>
    haveI : Unique (Fin 0 → A) := Pi.uniqueOfIsEmpty _
    simp only [complexWordWeight, Fintype.prod_empty, tsum_const, pow_zero,
      Nat.card_eq_fintype_card, Fintype.card_unique, one_smul]
  | succ n ih =>
    have he (p : A × (Fin n → A)) :
        complexWordWeight w (Fin.consEquiv (fun _ => A) p) =
          w p.1 * complexWordWeight w p.2 := by
      simp only [complexWordWeight, Fin.prod_univ_succ, Fin.consEquiv_apply,
        Fin.cons_zero, Fin.cons_succ]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => A)).tsum_eq (complexWordWeight w)]
    simp only [he]
    rw [← tsum_mul_tsum_of_summable_norm hw.norm (complexWordWeight_norm_summable w hw), ih]
    exact (pow_succ' _ _).symm

theorem complexWordCharacter_one (w : A → ℂ) (hw : Summable w) :
    complexWordCharacter (X := X) w 1 = (∑' a, w a) ^ Fintype.card X := by
  let e : (Fin (Fintype.card X) → A) ≃ (X → A) :=
    Equiv.arrowCongr (Fintype.equivFin X).symm (Equiv.refl A)
  have he (x : Fin (Fintype.card X) → A) :
      complexWordWeight w (e x) = complexWordWeight w x :=
    Equiv.prod_comp (Fintype.equivFin X) (fun j => w (x j))
  simp only [complexWordCharacter, Equiv.Perm.coe_one, Function.comp_id, ite_true]
  rw [← e.tsum_eq (complexWordWeight w)]
  simpa only [he] using complexWordWeight_fin_tsum w hw (Fintype.card X)

theorem summable_complexFixedWordWeight (w : A → ℂ) (hw : Summable w)
    (σ : Equiv.Perm X) :
    Summable (fun x : X → A => if x ∘ σ = x then complexWordWeight w x else 0) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
    (complexWordWeight_norm_summable w hw)
  intro x
  split_ifs <;> simp only [norm_zero, le_refl, norm_nonneg]

/-- Disjoint blocks use independent letters, including for infinite summable alphabets. -/
theorem complexWordCharacter_sumCongr (w : A → ℂ)
    (hw : Summable w) (σ : Equiv.Perm X) (τ : Equiv.Perm Y) :
    complexWordCharacter w (Equiv.sumCongr σ τ) = complexWordCharacter w σ * complexWordCharacter w τ := by
  letI : DecidableEq (X ⊕ Y) := Classical.decEq _
  have hterm (x : X ⊕ Y → A) :
      (if x ∘ Equiv.sumCongr σ τ = x then complexWordWeight w x else 0) =
      (if (x ∘ Sum.inl) ∘ σ = x ∘ Sum.inl then complexWordWeight w (x ∘ Sum.inl) else 0) *
      (if (x ∘ Sum.inr) ∘ τ = x ∘ Sum.inr then complexWordWeight w (x ∘ Sum.inr) else 0) := by
    have hfix : x ∘ Equiv.sumCongr σ τ = x ↔
        (x ∘ Sum.inl) ∘ σ = x ∘ Sum.inl ∧
        (x ∘ Sum.inr) ∘ τ = x ∘ Sum.inr := by
      constructor
      · intro h
        exact ⟨funext (fun i => congrFun h (Sum.inl i)),
          funext (fun i => congrFun h (Sum.inr i))⟩
      · rintro ⟨h₁, h₂⟩
        funext i
        cases i with
        | inl i => exact congrFun h₁ i
        | inr i => exact congrFun h₂ i
    have hm : complexWordWeight w x =
        complexWordWeight w (x ∘ Sum.inl) * complexWordWeight w (x ∘ Sum.inr) :=
      Fintype.prod_sum_type (fun i => w (x i))
    simp only [hfix, hm]
    split_ifs <;> simp_all
  unfold complexWordCharacter
  refine (tsum_congr hterm).trans ?_
  refine ((Equiv.sumPiEquivProdPi (fun _ => A)).tsum_eq
    (fun xy : (X → A) × (Y → A) =>
      (if xy.1 ∘ σ = xy.1 then complexWordWeight w xy.1 else 0) *
      (if xy.2 ∘ τ = xy.2 then complexWordWeight w xy.2 else 0))).trans ?_
  exact (tsum_mul_tsum_of_summable_norm
    (summable_complexFixedWordWeight w hw σ).norm (summable_complexFixedWordWeight w hw τ).norm).symm

/-- Relabeling the finite position set preserves every fixed-word sum. -/
theorem complexWordCharacter_permCongr (w : A → ℂ) (e : X ≃ Y) (σ : Equiv.Perm X) :
    complexWordCharacter w (e.permCongr σ) = complexWordCharacter w σ := by
  let f : (Y → A) ≃ (X → A) := Equiv.arrowCongr e.symm (Equiv.refl A)
  have he (x : Y → A) :
      (if x ∘ e.permCongr σ = x then complexWordWeight w x else 0) =
      (if (f x) ∘ σ = f x then complexWordWeight w (f x) else 0) := by
    have hweight : complexWordWeight w (f x) = complexWordWeight w x :=
      Equiv.prod_comp e (fun y => w (x y))
    rw [hweight]
    have hfix : x ∘ e.permCongr σ = x ↔ (x ∘ e) ∘ σ = x ∘ e := by
      constructor
      · intro h
        funext i
        simpa [Equiv.permCongr_apply] using congrFun h (e i)
      · intro h
        funext i
        simpa [Equiv.permCongr_apply] using congrFun h (e.symm i)
    change (if x ∘ e.permCongr σ = x then complexWordWeight w x else 0) =
      (if (x ∘ e) ∘ σ = x ∘ e then complexWordWeight w x else 0)
    simp only [hfix]
  exact (tsum_congr he).trans (f.tsum_eq
    (fun x : X → A => if x ∘ σ = x then complexWordWeight w x else 0))

/-- Independent letters factor across a subset and its complement. -/
theorem complexWordCharacter_subtypeCongr (w : A → ℂ) (hw : Summable w)
    (p : X → Prop) [DecidablePred p]
    (σ : Equiv.Perm {x // p x}) (τ : Equiv.Perm {x // ¬p x}) :
    complexWordCharacter w (σ.subtypeCongr τ) = complexWordCharacter w σ * complexWordCharacter w τ := by
  rw [Equiv.Perm.subtypeCongr, complexWordCharacter_permCongr,
    complexWordCharacter_sumCongr w hw]


/-- An invariant subset splits the character into its two restrictions. -/
theorem complexWordCharacter_split (w : A → ℂ)
    (hw : Summable w) (p : X → Prop) [DecidablePred p]
    (σ : Equiv.Perm X) (hσ : ∀ x, p (σ x) ↔ p x) :
    complexWordCharacter w σ = complexWordCharacter w (σ.subtypePerm hσ) *
      complexWordCharacter w (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) := by
  have he : (σ.subtypePerm hσ).subtypeCongr
      (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) = σ := by
    ext x
    by_cases hx : p x
    · simpa using Equiv.Perm.subtypeCongr.left_apply
        (σ.subtypePerm hσ) (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) hx
    · simpa using Equiv.Perm.subtypeCongr.right_apply
        (σ.subtypePerm hσ) (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not)) hx
  calc
    complexWordCharacter w σ = complexWordCharacter w ((σ.subtypePerm hσ).subtypeCongr
        (σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not))) := congrArg (complexWordCharacter w) he.symm
    _ = _ := by
      rw [Equiv.Perm.subtypeCongr, complexWordCharacter_permCongr,
        complexWordCharacter_sumCongr w hw]

/-- A transitive permutation fixes exactly the constant words. -/
theorem complexWordCharacter_transitive (w : A → ℂ) (σ : Equiv.Perm X)
    (hσ : σ.IsCycleOn Set.univ) (a : X) :
    complexWordCharacter w σ = ∑' b, w b ^ Fintype.card X := by
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
  let f : (X → A) → ℂ := fun x => if x ∘ σ = x then complexWordWeight w x else 0
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
  simp [f, c, complexWordWeight, Function.comp_def]

/-- Disjoint permutations act on independent sets of letters. -/
theorem complexWordCharacter_disjoint (w : A → ℂ)
    (hw : Summable w) (hm : (∑' a, w a) = 1)
    (σ τ : Equiv.Perm X) (hd : Equiv.Perm.Disjoint σ τ) :
    complexWordCharacter w (σ * τ) = complexWordCharacter w σ * complexWordCharacter w τ := by
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
  rw [complexWordCharacter_split w hw p (σ * τ) hστ,
    complexWordCharacter_split w hw p σ hσ, complexWordCharacter_split w hw p τ hτ,
    hprod, hprodc, hσc, hτp, complexWordCharacter_one w hw, complexWordCharacter_one w hw, hm,
    one_pow, one_pow, mul_one, one_mul]

/-- A single nontrivial cycle contributes the power sum of its support size. -/
theorem complexWordCharacter_isCycle (w : A → ℂ)
    (hw : Summable w) (hm : (∑' a, w a) = 1)
    (σ : Equiv.Perm X) (hcycle : σ.IsCycle) :
    complexWordCharacter w σ = ∑' b, w b ^ σ.support.card := by
  let p : X → Prop := fun x => σ x ≠ x
  have hσ (x : X) : p (σ x) ↔ p x := σ.apply_eq_iff_eq.not
  have hσc : σ.subtypePerm (p := fun x => ¬p x) (fun x => (hσ x).not) = 1 := by
    ext x
    exact not_not.mp x.property
  rw [complexWordCharacter_split w hw p σ hσ, hσc, complexWordCharacter_one w hw, hm,
    one_pow, mul_one]
  obtain ⟨a, ha⟩ := hcycle.nonempty_support
  have hc : (σ.subtypePerm hσ).IsCycleOn Set.univ := hcycle.isCycleOn.subtypePerm
  rw [complexWordCharacter_transitive w _ hc ⟨a, Equiv.Perm.mem_support.mp ha⟩]
  have hcard : Fintype.card {x // p x} = σ.support.card := by
    simp only [Fintype.card_subtype, p, Equiv.Perm.support]
  rw [hcard]

/-- The independent-color character equals the literal product over all nontrivial cycles. -/
theorem complexWordCharacter_eq_complexCycleCharacter (w : A → ℂ)
    (hw : Summable w) (hm : (∑' a, w a) = 1)
    (σ : Equiv.Perm X) :
    complexWordCharacter w σ = complexCycleCharacter (fun n => ∑' a, w a ^ (n + 1)) σ := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => simp only [complexWordCharacter_one w hw, hm, one_pow, complexCycleCharacter, Equiv.Perm.cycleType_one, Multiset.map_zero, Multiset.prod_zero]
  | base_cycles σ hσ =>
    rw [complexWordCharacter_isCycle w hw hm σ hσ]
    have hpos : 1 ≤ σ.support.card := le_trans (by omega) hσ.two_le_card_support
    simp only [complexCycleCharacter, hσ.cycleType, Multiset.map_singleton,
      Multiset.prod_singleton, Nat.sub_add_cancel hpos]
  | induction_disjoint σ τ hd _ hσ hτ =>
    rw [complexWordCharacter_disjoint w hw hm σ τ hd, hσ, hτ]
    simp only [complexCycleCharacter, hd.cycleType_mul, Multiset.map_add, Multiset.prod_add]


end GaloisForLFunctions.SymmetricCharacters
