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

section Kraft

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {X : Type*}

/-- Length-`n` completions of a word shorter than `n`. -/
noncomputable def wordCompletions (w : List Γ) (n : ℕ) (hw : w.length ≤ n) :
    Finset (List.Vector Γ n) :=
  Finset.univ.image fun m : List.Vector Γ (n - w.length) =>
    (⟨w ++ m.1, by
      rw [List.length_append, m.2]
      omega⟩ : List.Vector Γ n)

theorem card_wordCompletions (w : List Γ) (n : ℕ) (hw : w.length ≤ n) :
    (wordCompletions w n hw).card = Fintype.card Γ ^ (n - w.length) := by
  classical
  rw [wordCompletions, Finset.card_image_of_injective _ ?_, Finset.card_univ,
    card_vector]
  rintro ⟨m, hm⟩ ⟨m', hm'⟩ h
  have : w ++ m = w ++ m' := congrArg Subtype.val h
  exact Subtype.ext (List.append_cancel_left this)

theorem mem_wordCompletions_iff {w : List Γ} {n : ℕ} (hw : w.length ≤ n)
    (v : List.Vector Γ n) : v ∈ wordCompletions w n hw ↔ w <+: v.1 := by
  classical
  constructor
  · intro hv
    rw [wordCompletions, Finset.mem_image] at hv
    obtain ⟨m, -, hm⟩ := hv
    exact ⟨m.1, congrArg Subtype.val hm⟩
  · rintro ⟨s, hs⟩
    have hlen : s.length = n - w.length := by
      have := v.2
      rw [← hs, List.length_append] at this
      omega
    rw [wordCompletions, Finset.mem_image]
    exact ⟨⟨s, hlen⟩, Finset.mem_univ _, Subtype.ext hs⟩

/-- **Kraft inequality for the first-hit language.**  A prefix-free gate language has total
inverse-alphabet mass at most one. -/
theorem tsum_firstHitWord_inv_card_le_one [Nonempty Γ] (act : Γ → X → X) (χ : X) (A : Set X) :
    (∑' w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (fun w => ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ w.length) w) ≤ 1 := by
  classical
  have hM : 0 < Fintype.card Γ := Fintype.card_pos
  have hMR : (Fintype.card Γ : ℝ≥0∞) ≠ 0 := by
    simp
  have hMtop : (Fintype.card Γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set n : ℕ := s.sup List.length with hn
  set s' : Finset (List Γ) := s.filter (fun w => FirstHitWord act χ A w) with hs'
  have hlen : ∀ w ∈ s', w.length ≤ n := fun w hw =>
    Finset.le_sup (f := List.length) (Finset.mem_of_mem_filter w hw)
  have hcardsum : ∑ w ∈ s'.attach, Fintype.card Γ ^ (n - (w : List Γ).length) ≤
      Fintype.card Γ ^ n := by
    have hbi : (s'.attach.biUnion fun w =>
        wordCompletions (w : List Γ) n (hlen (w : List Γ) w.2)).card ≤
        Fintype.card (List.Vector Γ n) := Finset.card_le_univ _
    rw [card_vector] at hbi
    refine le_trans (le_of_eq ?_) hbi
    rw [Finset.card_biUnion]
    · exact (Finset.sum_congr rfl fun w _ => (card_wordCompletions _ _ _).symm)
    · intro w hw w' hw' hne
      refine Finset.disjoint_left.mpr fun v hv hv' => hne (Subtype.ext ?_)
      have h1 : (w : List Γ) <+: v.1 := (mem_wordCompletions_iff _ v).mp hv
      have h2 : (w' : List Γ) <+: v.1 := (mem_wordCompletions_iff _ v).mp hv'
      have hwF : FirstHitWord act χ A (w : List Γ) := (Finset.mem_filter.mp w.2).2
      have hw'F : FirstHitWord act χ A (w' : List Γ) := (Finset.mem_filter.mp w'.2).2
      rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
      · exact firstHitWord_eq_of_prefix hwF hw'F h
      · exact (firstHitWord_eq_of_prefix hw'F hwF h).symm
  have hsum : ∑ w ∈ s, Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (fun w => ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ w.length) w =
      ∑ w ∈ s'.attach, ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ (w : List Γ).length := by
    rw [Finset.sum_attach s' (fun w => ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ w.length), hs',
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : FirstHitWord act χ A w
    · rw [Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
        if_pos hw]
    · rw [Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw),
        if_neg hw]
  have hkey : ∀ k : ℕ, k ≤ n →
      ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ k * (Fintype.card Γ : ℝ≥0∞) ^ n =
        (Fintype.card Γ : ℝ≥0∞) ^ (n - k) := by
    intro k hk
    have hsplit : (Fintype.card Γ : ℝ≥0∞) ^ n =
        (Fintype.card Γ : ℝ≥0∞) ^ k * (Fintype.card Γ : ℝ≥0∞) ^ (n - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, ← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel hMR hMtop, one_pow, one_mul]
  have hcast : ((∑ w ∈ s'.attach, Fintype.card Γ ^ (n - (w : List Γ).length) : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card Γ ^ n : ℕ) : ℝ≥0∞) := by exact_mod_cast hcardsum
  have hfinal : (∑ w ∈ s'.attach, ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ (w : List Γ).length) *
      (Fintype.card Γ : ℝ≥0∞) ^ n ≤ 1 * (Fintype.card Γ : ℝ≥0∞) ^ n := by
    rw [Finset.sum_mul, one_mul]
    calc (∑ w ∈ s'.attach, ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ (w : List Γ).length *
          (Fintype.card Γ : ℝ≥0∞) ^ n)
        = ∑ w ∈ s'.attach, (Fintype.card Γ : ℝ≥0∞) ^ (n - (w : List Γ).length) :=
          Finset.sum_congr rfl fun w _ => hkey _ (hlen (w : List Γ) w.2)
      _ ≤ (Fintype.card Γ : ℝ≥0∞) ^ n := by
          refine le_trans (le_of_eq ?_) (le_trans hcast (le_of_eq ?_)) <;> push_cast <;> ring
  have hne0 : (Fintype.card Γ : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ hMR
  have hnetop : (Fintype.card Γ : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top hMtop
  rw [hsum]
  exact (ENNReal.mul_le_mul_iff_left hne0 hnetop).mp hfinal

end Kraft

section Sandwich

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] {X : Type*}

/-- A shortest hitting word is a first-hit word. -/
theorem firstHitWord_of_minimal (act : Γ → X → X) (χ : X) (A : Set X) {w₀ : List Γ}
    (hw₀ : wordEval act w₀ χ ∈ A)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ A → w₀.length ≤ w.length) :
    FirstHitWord act χ A w₀ := by
  refine ⟨hw₀, fun k hk hmem => ?_⟩
  have hlen : (w₀.take k).length = k := by
    rw [List.length_take, min_eq_left hk.le]
  have := hmin (w₀.take k) hmem
  omega

/-- **Complexity lower calibration.**  The shortest hitting word contributes its geometric weight
to the discounted first-hit mass. -/
theorem pow_le_firstHitMass (act : Γ → X → X) (χ : X) (A : Set X) (a : ℝ≥0∞) {w₀ : List Γ}
    (hw₀ : wordEval act w₀ χ ∈ A)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ A → w₀.length ≤ w.length) :
    (a / Fintype.card Γ) ^ w₀.length ≤ firstHitMass act χ A a := by
  classical
  rw [firstHitMass]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum w₀)
  rw [Set.indicator_of_mem (show w₀ ∈ {w : List Γ | FirstHitWord act χ A w} from
    firstHitWord_of_minimal act χ A hw₀ hmin)]

/-- **Complexity upper calibration.**  Every first-hit word is at least as long as the robust
complexity, so the discounted first-hit mass is bounded by the discount power. -/
theorem firstHitMass_le_pow (act : Γ → X → X) (χ : X) (A : Set X) {a : ℝ≥0∞} (ha : a ≤ 1)
    {c : ℕ} (hmin : ∀ w : List Γ, FirstHitWord act χ A w → c ≤ w.length) :
    firstHitMass act χ A a ≤ a ^ c := by
  classical
  have hterm : ∀ w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
      (fun w => (a / Fintype.card Γ) ^ w.length) w ≤
      a ^ c * Set.indicator {w : List Γ | FirstHitWord act χ A w}
        (fun w => ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ w.length) w := by
    intro w
    by_cases hw : FirstHitWord act χ A w
    · rw [Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
        Set.indicator_of_mem (show w ∈ {w : List Γ | FirstHitWord act χ A w} from hw),
        div_eq_mul_inv, mul_pow]
      exact mul_le_mul_left (pow_le_pow_right_of_le_one' ha (hmin w hw)) _
    · rw [Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw),
        Set.indicator_of_notMem (show w ∉ {w : List Γ | FirstHitWord act χ A w} from hw),
        mul_zero]
  calc firstHitMass act χ A a
      ≤ ∑' w : List Γ, a ^ c * Set.indicator {w : List Γ | FirstHitWord act χ A w}
          (fun w => ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ w.length) w := by
        rw [firstHitMass]
        exact ENNReal.tsum_le_tsum hterm
    _ = a ^ c * ∑' w : List Γ, Set.indicator {w : List Γ | FirstHitWord act χ A w}
          (fun w => ((Fintype.card Γ : ℝ≥0∞))⁻¹ ^ w.length) w := ENNReal.tsum_mul_left
    _ ≤ a ^ c * 1 := mul_le_mul_right (tsum_firstHitWord_inv_card_le_one act χ A) _
    _ = a ^ c := mul_one _

end Sandwich

end GaloisForLFunctions.RHTower
