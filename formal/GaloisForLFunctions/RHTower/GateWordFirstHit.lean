import Mathlib
import GaloisForLFunctions.RHTower.DiscreteMarkovRenewal

/-!
# First-hit gate words of a target

A finite gate alphabet acts on a state space, and a gate word is evaluated by letting its last
letter act first, so that extending a word on the right refines the synthesis.  The first-hit
language of a target consists of the words that reach it with no earlier prefix already reaching
it; it is prefix-free.

Discounting a first-hit word by the geometric weight of its length gives the discounted first-hit
mass.  Grouping by length identifies it with the length-graded first-entrance series, and the
shortest hitting word is itself a first-hit word.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section GateWords

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {X : Type*}

/-- Evaluation of a gate word on a seed: the last letter acts first. -/
def wordEval (act : Γ → X → X) : List Γ → X → X
  | [], x => x
  | g :: w, x => act g (wordEval act w x)

@[simp] theorem wordEval_nil (act : Γ → X → X) (x : X) : wordEval act [] x = x := rfl

@[simp] theorem wordEval_cons (act : Γ → X → X) (g : Γ) (w : List Γ) (x : X) :
    wordEval act (g :: w) x = act g (wordEval act w x) := rfl

/-- The words that reach the target with no earlier prefix already reaching it. -/
def FirstHitWord (act : Γ → X → X) (χ : X) (A : Set X) (w : List Γ) : Prop :=
  wordEval act w χ ∈ A ∧ ∀ k < w.length, wordEval act (w.take k) χ ∉ A

theorem firstHitWord_nil_iff (act : Γ → X → X) (χ : X) (A : Set X) :
    FirstHitWord act χ A ([] : List Γ) ↔ χ ∈ A := by
  constructor
  · rintro ⟨h, -⟩; simpa using h
  · intro h; exact ⟨by simpa using h, by simp⟩

/-- **Prefix-freeness of the first-hit language.** -/
theorem firstHitWord_eq_of_prefix {act : Γ → X → X} {χ : X} {A : Set X} {u v : List Γ}
    (hu : FirstHitWord act χ A u) (hv : FirstHitWord act χ A v) (huv : u <+: v) : u = v := by
  by_contra hne
  have hlen : u.length < v.length := by
    rcases lt_or_eq_of_le huv.length_le with h | h
    · exact h
    · exact absurd (huv.eq_of_length h) hne
  obtain ⟨s, hs⟩ := huv
  exact hv.2 u.length hlen (by rw [← hs, List.take_left]; exact hu.1)

/-- Discounted first-hit mass of a target. -/
noncomputable def firstHitMass (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
    (fun w => (a / Fintype.card Γ) ^ w.length) w

/-- **Prefix-free first-hit partition function.**  Grouping the first-hit words by length turns the
discounted first-hit mass into the length-graded first-entrance series. -/
theorem firstHitMass_eq_tsum_length (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ≥0∞) :
    firstHitMass act χ A a =
      ∑' ℓ : ℕ, (a / Fintype.card Γ) ^ ℓ *
        (Nat.card {w : List Γ // w.length = ℓ ∧ FirstHitWord act χ A w} : ℝ≥0∞) := by
  classical
  rw [firstHitMass, tsum_list_regroup (S := Γ)]
  refine tsum_congr fun ℓ => ?_
  have hval : ∀ w : {w : List Γ // w.length = ℓ},
      Set.indicator {w : List Γ | FirstHitWord act χ A w}
        (fun w => (a / Fintype.card Γ) ^ w.length) (w : List Γ) =
      Set.indicator {w : {w : List Γ // w.length = ℓ} | FirstHitWord act χ A (w : List Γ)}
        (fun _ => (a / Fintype.card Γ) ^ ℓ) w := by
    intro w
    by_cases hw : FirstHitWord act χ A (w : List Γ)
    · rw [Set.indicator_of_mem
        (show (w : List Γ) ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
        Set.indicator_of_mem (show w ∈ {w : {w : List Γ // w.length = ℓ} |
          FirstHitWord act χ A (w : List Γ)} from hw), w.2]
    · rw [Set.indicator_of_notMem
        (show (w : List Γ) ∉ {w : List Γ | FirstHitWord act χ A w} from hw),
        Set.indicator_of_notMem (show w ∉ {w : {w : List Γ // w.length = ℓ} |
          FirstHitWord act χ A (w : List Γ)} from hw)]
  haveI : Finite {w : List Γ // w.length = ℓ} := inferInstanceAs (Finite (List.Vector Γ ℓ))
  haveI : Finite ↑{w : {w : List Γ // w.length = ℓ} | FirstHitWord act χ A (w : List Γ)} :=
    Subtype.finite
  rw [tsum_congr hval, ← tsum_subtype, ENNReal.tsum_const, ENat.card_eq_coe_natCard]
  have hcard : Nat.card ↑{w : {w : List Γ // w.length = ℓ} |
      FirstHitWord act χ A (w : List Γ)} =
      Nat.card {w : List Γ // w.length = ℓ ∧ FirstHitWord act χ A w} :=
    Nat.card_congr
      { toFun := fun w => ⟨(w : {w : List Γ // w.length = ℓ}), (w : {w : List Γ //
          w.length = ℓ}).2, w.2⟩
        invFun := fun w => ⟨⟨(w : List Γ), w.2.1⟩, w.2.2⟩
        left_inv := fun w => rfl
        right_inv := fun w => rfl }
  rw [hcard, mul_comm]
  norm_cast

/-- **Exact recurrence collapse.**  A seed already inside the target has first-hit mass one. -/
theorem firstHitMass_of_mem (act : Γ → X → X) {χ : X} {A : Set X} (a : ℝ≥0∞) (hχ : χ ∈ A) :
    firstHitMass act χ A a = 1 := by
  classical
  rw [firstHitMass]
  have hsingle : ∀ w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (fun w => (a / Fintype.card Γ) ^ w.length) w =
      if w = [] then 1 else 0 := by
    intro w
    cases w with
    | nil =>
        rw [Set.indicator_of_mem (show ([] : List Γ) ∈ {w : List Γ | FirstHitWord act χ A w} from
          (firstHitWord_nil_iff act χ A).mpr hχ), if_pos rfl]
        simp
    | cons g w =>
        rw [Set.indicator_of_notMem (show (g :: w) ∉ {w : List Γ | FirstHitWord act χ A w} from
          fun hc => hc.2 0 (by simp) (by simpa using hχ)), if_neg (by simp)]
  rw [tsum_congr hsingle]
  exact tsum_ite_eq [] 1

end GateWords

end GaloisForLFunctions.RHTower
