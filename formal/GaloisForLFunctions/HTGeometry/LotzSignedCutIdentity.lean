import Mathlib

/-!
# The finite endpoint identity behind signed stellar subdivision

This is the combinatorial core of Lotz's signed simplex identity
(arXiv:2609.09335, Lemma 3.5). Positive-sign indices select a minimum,
negative-sign indices select a maximum, and the two endpoint contributions
cancel away from coordinate-zero and equal-ratio walls. All sign patterns
and arbitrary finite nonempty index types are covered.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The scalar endpoint condition for a replacement cone. -/
def lotzCut (s : ι → Bool) (t : ι → ℝ) (j : ι) : Prop :=
  0 ≤ t j ∧ ∀ k, if s k then t j ≤ t k else t k ≤ t j

/-- The original orthant in signed ratio coordinates. -/
def lotzSignedOrthant (s : ι → Bool) (t : ι → ℝ) : Prop :=
  ∀ k, if s k then 0 ≤ t k else t k ≤ 0

/-- Signed multiplicity of all replacement cones at a ratio vector. -/
def lotzSignedCutTotal (s : ι → Bool) (t : ι → ℝ) : ℝ :=
  ∑ j, if lotzCut s t j then (if s j then 1 else -1) else 0

/-- The generic locus removes coordinate-zero and equal-ratio walls. -/
def lotzGenericRatios : Set (ι → ℝ) :=
  {t | (∀ i, t i ≠ 0) ∧ Function.Injective t}

/-- The signed stellar identity in arbitrary finite dimension, before choosing coordinates. -/
theorem lotz_signedCuts_eqOn (s : ι → Bool) :
    Set.EqOn (fun t => (if lotzSignedOrthant s t then (1 : ℝ) else 0)-lotzSignedCutTotal s t)
      (fun _ => if ∀ i, s i=false then (1 : ℝ) else 0) lotzGenericRatios := by
  classical
  intro t ht
  dsimp only
  obtain ⟨hne,hinj⟩ := ht
  have hsplit : lotzSignedCutTotal s t =
      (∑ i, if s i=true ∧ lotzCut s t i then (1 : ℝ) else 0)-
      (∑ i, if s i=false ∧ lotzCut s t i then (1 : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    unfold lotzSignedCutTotal
    apply Finset.sum_congr rfl
    intro i _
    cases hs : s i <;> by_cases hc : lotzCut s t i <;> simp [hc]
  have hplus (p : ι) (hsp : s p=true) (hmin : ∀ k, s k=true → t p ≤ t k) :
      (∑ i, if s i=true ∧ lotzCut s t i then (1 : ℝ) else 0) =
        if 0 ≤ t p ∧ (∀ k, s k=false → t k ≤ t p) then 1 else 0 := by
    have hi (i : ι) : (s i=true ∧ lotzCut s t i) ↔
        i=p ∧ 0 ≤ t p ∧ (∀ k, s k=false → t k ≤ t p) := by
      constructor
      · rintro ⟨hsi,hti,hall⟩
        have hip : t i ≤ t p := by simpa [hsp] using hall p
        have he : i=p := hinj (le_antisymm hip (hmin i hsi))
        subst i
        exact ⟨rfl,hti,fun k hk => by simpa [hk] using hall k⟩
      · rintro ⟨rfl,hp,hall⟩
        refine ⟨hsp,hp,fun k => ?_⟩
        cases hk : s k with
        | false => simpa [hk] using hall k hk
        | true => simpa [hk] using hmin k hk
    by_cases hc : 0 ≤ t p ∧ (∀ k, s k=false → t k ≤ t p)
    · rw [if_pos hc]
      calc
        _ = ∑ i, if i=p then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases he : i=p
          · subst i
            rw [if_pos ((hi p).mpr ⟨rfl,hc⟩),if_pos rfl]
          · rw [if_neg (fun h => he ((hi i).mp h).1),if_neg he]
        _ = 1 := by simp
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => hc ((hi i).mp h).2)
  have hminus (q : ι) (hsq : s q=false) (hmax : ∀ k, s k=false → t k ≤ t q) :
      (∑ i, if s i=false ∧ lotzCut s t i then (1 : ℝ) else 0) =
        if 0 ≤ t q ∧ (∀ k, s k=true → t q ≤ t k) then 1 else 0 := by
    have hi (i : ι) : (s i=false ∧ lotzCut s t i) ↔
        i=q ∧ 0 ≤ t q ∧ (∀ k, s k=true → t q ≤ t k) := by
      constructor
      · rintro ⟨hsi,hti,hall⟩
        have hqi : t q ≤ t i := by simpa [hsq] using hall q
        have he : i=q := hinj (le_antisymm (hmax i hsi) hqi)
        subst i
        exact ⟨rfl,hti,fun k hk => by simpa [hk] using hall k⟩
      · rintro ⟨rfl,hq,hall⟩
        refine ⟨hsq,hq,fun k => ?_⟩
        cases hk : s k with
        | false => simpa [hk] using hmax k hk
        | true => simpa [hk] using hall k hk
    by_cases hc : 0 ≤ t q ∧ (∀ k, s k=true → t q ≤ t k)
    · rw [if_pos hc]
      calc
        _ = ∑ i, if i=q then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases he : i=q
          · subst i
            rw [if_pos ((hi q).mpr ⟨rfl,hc⟩),if_pos rfl]
          · rw [if_neg (fun h => he ((hi i).mp h).1),if_neg he]
        _ = 1 := by simp
    · rw [if_neg hc]
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => hc ((hi i).mp h).2)
  have hchooseP : (∃ i, s i=true) → ∃ p, s p=true ∧ ∀ k, s k=true → t p ≤ t k := by
    rintro ⟨i,hi⟩
    let P := Finset.univ.filter (fun k => s k=true)
    have hp : P.Nonempty := ⟨i,by simp [P,hi]⟩
    obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image P t hp
    exact ⟨p,(Finset.mem_filter.mp hp).2,fun k hk => hmin k (by simp [P,hk])⟩
  have hchooseN : (∃ i, s i=false) → ∃ q, s q=false ∧ ∀ k, s k=false → t k ≤ t q := by
    rintro ⟨i,hi⟩
    let N := Finset.univ.filter (fun k => s k=false)
    have hn : N.Nonempty := ⟨i,by simp [N,hi]⟩
    obtain ⟨q,hq,hmax⟩ := Finset.exists_max_image N t hn
    exact ⟨q,(Finset.mem_filter.mp hq).2,fun k hk => hmax k (by simp [N,hk])⟩
  by_cases hp : ∃ i, s i=true
  · obtain ⟨p,hsp,hmin⟩ := hchooseP hp
    have hnotall : ¬ ∀ i, s i=false := by
      intro h
      have he := h p
      simp [hsp] at he
    simp only [hnotall, if_false]
    rw [hsplit,hplus p hsp hmin]
    by_cases hn : ∃ i, s i=false
    · obtain ⟨q,hsq,hmax⟩ := hchooseN hn
      rw [hminus q hsq hmax]
      have hl : (∀ k, s k=false → t k ≤ t p) ↔ t q ≤ t p :=
        ⟨fun h => h q hsq, fun h k hk => (hmax k hk).trans h⟩
      have hu : (∀ k, s k=true → t q ≤ t k) ↔ t q ≤ t p :=
        ⟨fun h => h p hsp, fun h k hk => h.trans (hmin k hk)⟩
      have ho : lotzSignedOrthant s t ↔ 0 ≤ t p ∧ t q ≤ 0 := by
        constructor
        · intro h
          exact ⟨by simpa [lotzSignedOrthant,hsp] using h p,
            by simpa [lotzSignedOrthant,hsq] using h q⟩
        · rintro ⟨ha,hb⟩ k
          cases hk : s k with
          | false => simpa [hk] using (hmax k hk).trans hb
          | true => simpa [hk] using ha.trans (hmin k hk)
      simp only [hl,hu,ho]
      rcases lt_or_gt_of_ne (hne q) with hq | hq
      · by_cases hpa : 0 ≤ t p
        · have hqp : t q ≤ t p := hq.le.trans hpa
          simp [hpa,hq.le,not_le_of_gt hq,hqp]
        · simp [hpa,not_le_of_gt hq]
      · by_cases hqp : t q ≤ t p
        · have hpa : 0 ≤ t p := hq.le.trans hqp
          simp [hpa,hq.le,not_le_of_gt hq,hqp]
        · simp [hqp,not_le_of_gt hq]
    · have hs (i : ι) : s i=true := by cases h : s i <;> simp_all
      have hz : (∑ i, if s i=false ∧ lotzCut s t i then (1 : ℝ) else 0) = 0 := by simp [hs]
      rw [hz]
      have hl : ∀ k, s k=false → t k ≤ t p := by intro k hk; simp [hs k] at hk
      have ho : lotzSignedOrthant s t ↔ 0 ≤ t p := by
        constructor
        · intro h; simpa [lotzSignedOrthant,hsp] using h p
        · intro h k; simpa [hs k] using h.trans (hmin k (hs k))
      have hc : (0 ≤ t p ∧ ∀ k,s k=false → t k ≤ t p) ↔ 0 ≤ t p :=
        ⟨fun h => h.1,fun h => ⟨h,hl⟩⟩
      simp only [ho,hc,sub_zero,sub_self]
  · have hs (i : ι) : s i=false := by cases h : s i <;> simp_all
    have hn : ∃ i, s i=false := ⟨Classical.arbitrary ι,hs _⟩
    obtain ⟨q,hsq,hmax⟩ := hchooseN hn
    have hz : (∑ i, if s i=true ∧ lotzCut s t i then (1 : ℝ) else 0) = 0 := by simp [hs]
    rw [hsplit,hz,hminus q hsq hmax]
    have hu : ∀ k, s k=true → t q ≤ t k := by intro k hk; simp [hs k] at hk
    have ho : lotzSignedOrthant s t ↔ t q ≤ 0 := by
      constructor
      · intro h; simpa [lotzSignedOrthant,hsq] using h q
      · intro h k; simpa [hs k] using (hmax k (hs k)).trans h
    have hc : (0 ≤ t q ∧ ∀ k,s k=true → t q ≤ t k) ↔ 0 ≤ t q :=
      ⟨fun h => h.1,fun h => ⟨h,hu⟩⟩
    rw [if_pos hs]
    simp only [ho,hc]
    rcases lt_or_gt_of_ne (hne q) with hq | hq
    · simp [hq.le,not_le_of_gt hq]
    · simp [hq.le,not_le_of_gt hq]

end GaloisForLFunctions.HTGeometry
