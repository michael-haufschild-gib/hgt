import Mathlib

/-!
# Frobenius classes in a sign-extended abelian group

The host group is `G = (ℤ/2)² × H` for a finite abelian `H`. A class `g` is *split* when its first
sign coordinate vanishes; the split classes `Φ` form a subgroup of index two. For a height `t ∈ H`
the *partner* `g ↦ c + g + (0, t)` (with `c = ((1,1),0)`) maps the non-split classes bijectively onto
the split ones.

Characters of `G` separate classes (`sum_conj_mul_apply`), and the non-split classes see only the
trivial character and the sign character `g ↦ (-1)^{g_{1,1}}` (`sum_nonsplit_conj`). For a subgroup
`I` (an inertia group) the average of `ψ` over a coset `h + I` is recovered by
`(1/|Φ|) Σ_ψ conj ψ(g) · avg_{h+I} ψ = (2/|I|)·[g - h ∈ I]` (`sum_conj_mul_cosetAverage`).
-/

open Finset

namespace WindowedLandauTheory

noncomputable section

/-- The sign group `(ℤ/2)²`. -/
abbrev SignPair := ZMod 2 × ZMod 2

theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

section Classes

variable {H : Type}

/-- A class is split when its first sign coordinate vanishes. -/
def IsSplit (g : SignPair × H) : Prop := g.1.1 = 0

instance : DecidablePred (IsSplit (H := H)) := fun g => inferInstanceAs (Decidable (g.1.1 = 0))

theorem not_isSplit_iff (g : SignPair × H) : ¬IsSplit g ↔ g.1.1 = 1 := by
  unfold IsSplit
  rcases zmod_two_eq_zero_or_one g.1.1 with h | h <;> rw [h] <;> decide

variable [AddCommGroup H]

theorem IsSplit.add {x y : SignPair × H} (hx : IsSplit x) (hy : IsSplit y) : IsSplit (x + y) := by
  unfold IsSplit at *
  simp [hx, hy]

theorem IsSplit.nsmul {x : SignPair × H} (hx : IsSplit x) (i : ℕ) : IsSplit (i • x) := by
  unfold IsSplit at *
  simp [hx]

/-- The class `((1,1),0)`. -/
def conjClass : SignPair × H := ((1, 1), 0)

/-- The class `((0,0),t)` of height `t`. -/
def heightClass (t : H) : SignPair × H := ((0, 0), t)

/-- The class `((1,0),0)` that generates the inertia at the ramified prime. -/
def ramifiedClass : SignPair × H := ((1, 0), 0)

/-- The partner `c + g + (0, t)` of a class `g` at height `t`. -/
def partnerClass (t : H) (g : SignPair × H) : SignPair × H := conjClass + g + heightClass t

theorem partnerClass_fst (t : H) (g : SignPair × H) : (partnerClass t g).1.1 = 1 + g.1.1 := by
  simp [partnerClass, conjClass, heightClass]

theorem isSplit_partnerClass (t : H) {g : SignPair × H} (hg : ¬IsSplit g) :
    IsSplit (partnerClass t g) := by
  have h := (not_isSplit_iff g).1 hg
  unfold IsSplit
  rw [partnerClass_fst, h]
  decide

/-! ## Characters -/

/-- The sign character `g ↦ (-1)^{g_{1,1}}`, trivial exactly on the split classes. -/
def splitSign : AddChar (SignPair × H) ℂ where
  toFun g := if g.1.1 = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases zmod_two_eq_zero_or_one a.1.1 with ha | ha <;>
      rcases zmod_two_eq_zero_or_one b.1.1 with hb | hb <;> simp [Prod.fst_add, ha, hb, h11, h10]

theorem splitSign_apply (g : SignPair × H) : splitSign g = if g.1.1 = 0 then 1 else -1 := rfl

theorem splitSign_mul_self (g : SignPair × H) : splitSign g * splitSign g = (1 : ℂ) := by
  rw [splitSign_apply]
  split_ifs <;> norm_num

theorem splitSign_ne_zero : (splitSign : AddChar (SignPair × H) ℂ) ≠ 0 := by
  intro h
  have h1 : splitSign (((1, 0), 0) : SignPair × H) = 1 := by rw [h, AddChar.zero_apply]
  rw [splitSign_apply] at h1
  norm_num at h1

theorem mul_splitSign_eq_zero_iff (ψ : AddChar (SignPair × H) ℂ) :
    ψ * splitSign = 0 ↔ ψ = splitSign := by
  constructor
  · intro h
    ext g
    have h1 : ψ g * splitSign g = 1 := by rw [← AddChar.mul_apply, h, AddChar.zero_apply]
    calc ψ g = ψ g * (splitSign g * splitSign g) := by rw [splitSign_mul_self, mul_one]
      _ = (ψ g * splitSign g) * splitSign g := by ring
      _ = splitSign g := by rw [h1, one_mul]
  · rintro rfl
    ext g
    rw [AddChar.mul_apply, splitSign_mul_self, AddChar.zero_apply]

variable [Fintype H]

variable (H) in
/-- The split classes `Φ`. -/
def splitSet : Finset (SignPair × H) := univ.filter IsSplit

variable (H) in
/-- The non-split classes. -/
def nonsplitSet : Finset (SignPair × H) := univ.filter fun g => ¬IsSplit g

/-- The partner map is a bijection from the non-split onto the split classes. -/
theorem sum_nonsplit_partnerClass {β : Type*} [AddCommMonoid β] (t : H) (F : SignPair × H → β) :
    ∑ g ∈ nonsplitSet H, F (partnerClass t g) = ∑ ρ ∈ splitSet H, F ρ := by
  refine Finset.sum_nbij' (partnerClass t) (fun ρ => ρ - heightClass t - conjClass) ?_ ?_ ?_ ?_ ?_
  · intro g hg
    have hg' : ¬IsSplit g := by simpa [nonsplitSet] using hg
    simpa [splitSet] using isSplit_partnerClass t hg'
  · intro ρ hρ
    have hρ' : ρ.1.1 = 0 := by simpa [splitSet, IsSplit] using hρ
    have e : (ρ - heightClass t - conjClass).1.1 = ρ.1.1 - 1 := by
      simp [heightClass, conjClass]
    have hn : ¬IsSplit (ρ - heightClass t - conjClass) := by
      rw [not_isSplit_iff, e, hρ']
      decide
    simpa [nonsplitSet] using hn
  · intro g _
    simp only [partnerClass]
    abel
  · intro ρ _
    simp only [partnerClass]
    abel
  · intro g _
    rfl

variable [DecidableEq H]

omit [DecidableEq H] in
theorem card_nonsplitSet : (nonsplitSet H).card = (splitSet H).card := by
  have h := sum_nonsplit_partnerClass (H := H) (0 : H) (fun _ => (1 : ℕ))
  simpa using h

omit [DecidableEq H] in
theorem card_eq_two_mul_card_splitSet :
    (Fintype.card (SignPair × H) : ℂ) = 2 * ((splitSet H).card : ℂ) := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (SignPair × H)))
    (p := IsSplit)
  have h2 : (splitSet H).card + (nonsplitSet H).card = Fintype.card (SignPair × H) := by
    simpa [splitSet, nonsplitSet] using h
  rw [card_nonsplitSet] at h2
  rw [← h2]
  push_cast
  ring

omit [DecidableEq H] in
theorem splitSet_card_ne_zero : ((splitSet H).card : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨0, by simp [splitSet, IsSplit]⟩

/-- Characters separate classes: `Σ_ψ conj ψ(g) ψ(h) = |G|·[g = h]`. -/
theorem sum_conj_mul_apply (g h : SignPair × H) :
    ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * ψ h =
      if g = h then (Fintype.card (SignPair × H) : ℂ) else 0 := by
  have e : ∀ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * ψ h = ψ (h - g) := fun ψ => by
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, neg_add_eq_sub]
  simp_rw [e]
  rw [AddChar.sum_apply_eq_ite]
  by_cases hgh : g = h
  · subst hgh
    simp
  · rw [if_neg (fun h0 => hgh (sub_eq_zero.mp h0).symm), if_neg hgh]

omit [DecidableEq H] in
theorem sum_conj_apply (ψ : AddChar (SignPair × H) ℂ) :
    ∑ g : SignPair × H, starRingEnd ℂ (ψ g) =
      if ψ = 0 then (Fintype.card (SignPair × H) : ℂ) else 0 := by
  simp_rw [← AddChar.map_neg_eq_conj]
  rw [Fintype.sum_equiv (Equiv.neg (SignPair × H)) (fun x => ψ (-x)) (fun x => ψ x) (fun x => rfl),
    AddChar.sum_eq_ite]

omit [DecidableEq H] in
/-- **The non-split classes see only the trivial and the sign character.** -/
theorem sum_nonsplit_conj (ψ : AddChar (SignPair × H) ℂ) :
    ∑ g ∈ nonsplitSet H, starRingEnd ℂ (ψ g) =
      ((splitSet H).card : ℂ) * ((if ψ = 0 then 1 else 0) - (if ψ = splitSign then 1 else 0)) := by
  have hind : ∀ g : SignPair × H, (if ¬IsSplit g then starRingEnd ℂ (ψ g) else 0) =
      (starRingEnd ℂ (ψ g) - splitSign g * starRingEnd ℂ (ψ g)) / 2 := by
    intro g
    rw [splitSign_apply]
    by_cases h : g.1.1 = 0
    · rw [if_neg (show ¬¬IsSplit g from not_not.2 h), if_pos h]
      ring
    · rw [if_pos (show ¬IsSplit g from h), if_neg h]
      ring
  have hB : ∑ g : SignPair × H, splitSign g * starRingEnd ℂ (ψ g) =
      if ψ = splitSign then (Fintype.card (SignPair × H) : ℂ) else 0 := by
    have e : ∀ g : SignPair × H, splitSign g * starRingEnd ℂ (ψ g) =
        starRingEnd ℂ ((ψ * splitSign : AddChar (SignPair × H) ℂ) g) := fun g => by
      rw [AddChar.mul_apply, map_mul, mul_comm]
      congr 1
      rw [splitSign_apply]
      split_ifs <;> simp
    simp_rw [e]
    rw [sum_conj_apply]
    simp only [mul_splitSign_eq_zero_iff]
  rw [nonsplitSet, Finset.sum_filter]
  simp_rw [hind]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_conj_apply, hB, card_eq_two_mul_card_splitSet]
  split_ifs <;> ring

/-! ## Coset averages -/

open Classical in
/-- The average of `ψ` over the coset `h + I`. -/
def cosetAverage (I : AddSubgroup (SignPair × H)) (h : SignPair × H)
    (ψ : AddChar (SignPair × H) ℂ) : ℂ :=
  (∑ x ∈ univ.filter (· ∈ I), ψ (h + x)) / ((univ.filter (· ∈ I)).card : ℂ)

omit [DecidableEq H] in
open Classical in
theorem cosetAverage_zero (I : AddSubgroup (SignPair × H)) (h : SignPair × H) :
    cosetAverage I h 0 = 1 := by
  unfold cosetAverage
  simp only [AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  refine div_self ?_
  rw [Nat.cast_ne_zero, Finset.card_ne_zero]
  exact ⟨0, by simp⟩

open Classical in
/-- **Recovering a coset from its averages:**
`(1/|Φ|) Σ_ψ conj ψ(g) · avg_{h+I} ψ = (2/|I|)·[g - h ∈ I]`. -/
theorem sum_conj_mul_cosetAverage (I : AddSubgroup (SignPair × H)) (h g : SignPair × H) :
    (1 / ((splitSet H).card : ℂ)) * ∑ ψ : AddChar (SignPair × H) ℂ,
        starRingEnd ℂ (ψ g) * cosetAverage I h ψ =
      if g - h ∈ I then 2 / ((univ.filter (· ∈ I)).card : ℂ) else 0 := by
  have hc : ((univ.filter (· ∈ I)).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨0, by simp⟩
  have e1 : ∑ ψ : AddChar (SignPair × H) ℂ, starRingEnd ℂ (ψ g) * cosetAverage I h ψ =
      (∑ x ∈ univ.filter (· ∈ I), ∑ ψ : AddChar (SignPair × H) ℂ,
        starRingEnd ℂ (ψ g) * ψ (h + x)) / ((univ.filter (· ∈ I)).card : ℂ) := by
    unfold cosetAverage
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [mul_div_assoc', Finset.mul_sum]
  rw [e1]
  simp_rw [sum_conj_mul_apply]
  have e2 : ∀ x : SignPair × H, (g = h + x) ↔ (x = g - h) := fun x => by
    rw [eq_sub_iff_add_eq, add_comm, eq_comm]
  simp_rw [e2]
  rw [Finset.sum_ite_eq']
  have hΦ := splitSet_card_ne_zero (H := H)
  by_cases hm : g - h ∈ I
  · rw [if_pos (by simpa using hm), if_pos hm, card_eq_two_mul_card_splitSet]
    field_simp
  · rw [if_neg (by simpa using hm), if_neg hm]
    simp

end Classes

end

end WindowedLandauTheory
