import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.IncreasingPrefixCosts
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.CarryModifiedComposition
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.GeometricCarryGain
import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.PrefixWeightIdentity

/-!
# Weight gain of the singleton carry modification

The terminal losses put larger available digits in the last part and separate
retained terminal exponents from its maximum. Increasing-prefix cost bounds
and the exact prefix-weight identity then quantify the carry modification.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

private theorem drop_lt_of_positive_total {a b t : ℤ} (hb : 0 < b) (ht : 0 < t)
    (hdrop : a ≤ max 0 (t - b)) : a < t :=
  hdrop.trans_lt (max_lt ht (by omega))

private theorem gap_of_positive_retained_count {a b t : ℤ} (ha : 0 < a)
    (hdrop : a ≤ max 0 (t - b)) : a + b ≤ t := by
  by_cases hle : t - b ≤ 0
  · rw [max_eq_left hle] at hdrop
    omega
  · rw [max_eq_right (by omega : 0 ≤ t - b)] at hdrop
    omega

namespace DigitComposition
variable {p s k : ℕ} {S : Finset (Digit p)}

/-- Outside the singleton's residue, the proper prefix contains all available digits. -/
private theorem singleton_prefix_content_eq_total
    (C : DigitComposition p s (k + 2) S) {x : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x}) (h : ZMod s)
    (hne : (x.1 : ZMod s) ≠ h) :
    tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h =
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) S h := by
  let colour : Digit p → ZMod s := fun t => t.1
  have hf : ({x} : Finset (Digit p)).filter (fun t => colour t = h) = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨hz, hcol⟩ := mem_filter.mp hz
    have he := mem_singleton.mp hz
    subst z
    exact hne hcol
  have hz : tokenContent colour {x} h = 0 := by
    simp only [tokenContent, hf, card_empty, Nat.cast_zero]
  have hu := congrFun (tokenContent_union colour C.prefix_disjoint_last) h
  rw [C.prefix_union_last, hlast] at hu
  simpa only [Pi.add_apply, hz, add_zero] using hu.symm

/-- A positive retained residue turns the terminal drop into a full cardinality gap. -/
private theorem terminal_drop_card_gap (C Z : DigitComposition p s (k + 2) S)
    (hp : 2 ≤ p) {x : Digit p} (hlast : C.parts (Fin.last (k + 1)) = {x})
    (h : ZMod s) (hne : (x.1 : ZMod s) ≠ h)
    (hdrop : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (k + 1)) h ≤
      max 0 (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h -
        ((p : ℤ) - 1)))
    (hretained : (Z.residuePrefixDigits (k + 1) h).Nonempty) :
    (Z.residuePrefixDigits (k + 1) h).card + (p - 1) ≤
      (S.filter fun t => (t.1 : ZMod s) = h).card := by
  rw [C.singleton_prefix_content_eq_total hlast h hne] at hdrop
  have hpos : (0 : ℤ) < (Z.residuePrefixDigits (k + 1) h).card := by
    exact_mod_cast card_pos.mpr hretained
  change ((Z.residuePrefixDigits (k + 1) h).card : ℤ) ≤
    max 0 (((S.filter fun t => (t.1 : ZMod s) = h).card : ℤ) - ((p : ℤ) - 1)) at hdrop
  have hg := gap_of_positive_retained_count hpos hdrop
  have hc : (((Z.residuePrefixDigits (k + 1) h).card + (p - 1) : ℕ) : ℤ) ≤
      ((S.filter fun t => (t.1 : ZMod s) = h).card : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    exact hg
  exact_mod_cast hc

/-- Every occupied affected residue leaves a digit in the new last part. -/
private theorem terminal_drop_leaves_last (C Z : DigitComposition p s (k + 2) S)
    (hp : 2 ≤ p) {x : Digit p} (hlast : C.parts (Fin.last (k + 1)) = {x})
    (h : ZMod s) (hne : (x.1 : ZMod s) ≠ h)
    (hdrop : tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (k + 1)) h ≤
      max 0 (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h -
        ((p : ℤ) - 1)))
    (havailable : (S.filter fun t => (t.1 : ZMod s) = h).Nonempty) :
    ((Z.parts (Fin.last (k + 1))).filter fun t => (t.1 : ZMod s) = h).Nonempty := by
  rw [C.singleton_prefix_content_eq_total hlast h hne] at hdrop
  have hpos : (0 : ℤ) < (S.filter fun t => (t.1 : ZMod s) = h).card := by
    exact_mod_cast card_pos.mpr havailable
  change ((Z.residuePrefixDigits (k + 1) h).card : ℤ) ≤
    max 0 (((S.filter fun t => (t.1 : ZMod s) = h).card : ℤ) - ((p : ℤ) - 1)) at hdrop
  have hlt := drop_lt_of_positive_total (by omega : (0 : ℤ) < p - 1) hpos hdrop
  apply Z.last_residue_nonempty_of_prefix_card_lt h
  exact_mod_cast hlt

private def priorPrefixCost (C : DigitComposition p s (k + 2) S) (h : ZMod s) : ℤ :=
  ∑ j ∈ Icc 1 k, digitValue p (C.residuePrefixDigits j h)

private theorem priorPrefixCost_nonneg (C : DigitComposition p s (k + 2) S) (h : ZMod s) :
    0 ≤ C.priorPrefixCost h :=
  sum_nonneg fun _ _ => digitValue_nonneg _ _

private theorem priorPrefixCost_eq_zero (C : DigitComposition p s (k + 2) S) (h : ZMod s)
    (he : ¬ (C.residuePrefixDigits (k + 1) h).Nonempty) : C.priorPrefixCost h = 0 := by
  apply sum_eq_zero
  intro j hj
  have hempty : C.residuePrefixDigits j h = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    exact he ⟨x, C.residuePrefixDigits_mono (by have := mem_Icc.mp hj; omega) h hx⟩
  simp only [hempty, digitValue, tokenValue, sum_empty]

variable [NeZero s]

omit [NeZero s] in
/-- The old singleton bounds every available exponent in its own residue. -/
private theorem singleton_residue_max {C : DigitComposition p s (k + 2) S}
    (hC : C.TauMonotone) {x : Digit p} (hlast : C.parts (Fin.last (k + 1)) = {x}) :
    ∀ z ∈ S, (z.1 : ZMod s) = (x.1 : ZMod s) → z.1 ≤ x.1 := by
  have hx : x ∈ C.parts (Fin.last (k + 1)) := by rw [hlast]; exact mem_singleton_self x
  obtain ⟨y, hy, _, hmax⟩ := hC.exists_last_max (h := (x.1 : ZMod s))
    ⟨x, mem_filter.mpr ⟨hx, rfl⟩⟩
  rw [hlast, mem_singleton] at hy
  subst y
  exact hmax

/-- One terminal exponent per retained residue controls all its earlier-prefix costs. -/
private theorem exists_retained_cost_bound
    (C Z : DigitComposition p s (k + 2) S) (hp : 2 ≤ p)
    (hZ : Z.TauMonotone) {x : Digit p} (hlast : C.parts (Fin.last (k + 1)) = {x})
    (α E : ℕ)
    (hmax : ∀ z ∈ Z.parts (Fin.last (k + 1)), z.1 ≤ E)
    (hdrop : ∀ h : ZMod s, α ≤ h.val → h.val < (x.1 : ZMod s).val →
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (k + 1)) h ≤
        max 0 (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h -
          ((p : ℤ) - 1)))
    (hgap : ∀ h : ZMod s, α ≤ h.val → h.val ≤ (x.1 : ZMod s).val →
      ∀ j < k + 1,
        0 < tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits j) h →
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits j) h + ((p : ℤ) - 1) ≤
          tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (j + 1)) h) :
    ∃ V : ℤ,
      (p : ℤ) ^ s * ((p : ℤ) - 1) * V ≤ (p : ℤ) * (p : ℤ) ^ E ∧
      ((p : ℤ) ^ s - 1) ^ 2 *
          (∑ h ∈ univ.filter (fun h : ZMod s => α ≤ h.val ∧ h.val < (x.1 : ZMod s).val),
            Z.priorPrefixCost h) ≤
        ((p : ℤ) - 1) * (p : ℤ) ^ s * V := by
  let B := univ.filter fun h : ZMod s => α ≤ h.val ∧ h.val < (x.1 : ZMod s).val
  let H := B.filter fun h => (Z.residuePrefixDigits (k + 1) h).Nonempty
  have hm (h : ZMod s) : ∃ e : ℕ, h ∈ H →
      (∃ z ∈ Z.residuePrefixDigits (k + 1) h, z.1 = e) ∧
        ∀ z ∈ Z.residuePrefixDigits (k + 1) h, z.1 ≤ e := by
    by_cases hh : h ∈ H
    · obtain ⟨z, hz, hzmax⟩ :=
        (Z.residuePrefixDigits (k + 1) h).exists_max_image Prod.fst (mem_filter.mp hh).2
      exact ⟨z.1, fun _ => ⟨⟨z, hz, rfl⟩, hzmax⟩⟩
    · exact ⟨0, fun hh' => False.elim (hh hh')⟩
  choose e he using hm
  have hemod (h : ZMod s) (hh : h ∈ H) : e h % s = h.val := by
    obtain ⟨z, hz, hez⟩ := (he h hh).1
    rw [← hez]
    exact Z.residuePrefixDigits_mod (k + 1) h hz
  have hegap (h : ZMod s) (hh : h ∈ H) : e h + s ≤ E := by
    obtain ⟨hB, hret⟩ := mem_filter.mp hh
    have hb := (mem_filter.mp hB).2
    have hne : (x.1 : ZMod s) ≠ h := by
      intro heq
      have hv := congrArg ZMod.val heq
      omega
    obtain ⟨z, hz, hez⟩ := (he h hh).1
    rw [← hez]
    exact hZ.retained_exponent_gap hp h hmax
      (C.terminal_drop_card_gap Z hp hlast h hne (hdrop h hb.1 hb.2) hret) hz
  have hinj : Set.InjOn e (↑H : Set (ZMod s)) := by
    intro h hh t ht het
    apply ZMod.val_injective s
    rw [← hemod h hh, ← hemod t ht, het]
  have hsum := retained_exponent_sum_le hp (H.image e) (fun n hn => by
    obtain ⟨h, hh, rfl⟩ := mem_image.mp hn
    exact hegap h hh)
  rw [sum_image hinj] at hsum
  refine ⟨∑ h ∈ H, (p : ℤ) ^ e h, hsum, ?_⟩
  have hcost (h : ZMod s) (hh : h ∈ H) :
      ((p : ℤ) ^ s - 1) ^ 2 * Z.priorPrefixCost h ≤
        ((p : ℤ) - 1) * (p : ℤ) ^ s * (p : ℤ) ^ e h := by
    have hb := (mem_filter.mp (mem_filter.mp hh).1).2
    exact hZ.residue_prefix_cost_le hp h (e h) (hemod h hh) (he h hh).2
      (hgap h hb.1 hb.2.le)
  have hreduce : (∑ h ∈ B, Z.priorPrefixCost h) = ∑ h ∈ H, Z.priorPrefixCost h := by
    symm
    apply sum_subset (filter_subset _ _)
    intro h hB hnH
    exact Z.priorPrefixCost_eq_zero h (fun hne => hnH (mem_filter.mpr ⟨hB, hne⟩))
  change ((p : ℤ) ^ s - 1) ^ 2 * (∑ h ∈ B, Z.priorPrefixCost h) ≤ _
  rw [hreduce, mul_sum, mul_sum]
  exact sum_le_sum hcost

/-- Adding the singleton residue gives the complete affected-prefix cost. -/
private theorem exists_carry_cost_bound
    (C Z : DigitComposition p s (k + 2) S) (hp : 2 ≤ p)
    (hC : C.TauMonotone) (hZ : Z.TauMonotone) {x : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x}) (α E : ℕ)
    (hα : α < (x.1 : ZMod s).val)
    (hmax : ∀ z ∈ Z.parts (Fin.last (k + 1)), z.1 ≤ E)
    (hdrop : ∀ h : ZMod s, α ≤ h.val → h.val < (x.1 : ZMod s).val →
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (k + 1)) h ≤
        max 0 (tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits (k + 1)) h -
          ((p : ℤ) - 1)))
    (hgap : ∀ h : ZMod s, α ≤ h.val → h.val ≤ (x.1 : ZMod s).val →
      ∀ j < k + 1,
        0 < tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits j) h →
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits j) h + ((p : ℤ) - 1) ≤
          tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits (j + 1)) h) :
    ∃ V : ℤ,
      (p : ℤ) ^ s * ((p : ℤ) - 1) * V ≤ (p : ℤ) * (p : ℤ) ^ E ∧
      ((p : ℤ) ^ s - 1) ^ 2 *
          (∑ h ∈ univ.filter (fun h : ZMod s => α ≤ h.val ∧ h.val ≤ (x.1 : ZMod s).val),
            Z.priorPrefixCost h) ≤
        ((p : ℤ) - 1) * (p : ℤ) ^ s * ((p : ℤ) ^ x.1 + V) := by
  obtain ⟨V, hV, hcost⟩ := C.exists_retained_cost_bound Z hp hZ hlast α E hmax hdrop hgap
  refine ⟨V, hV, ?_⟩
  let β : ZMod s := x.1
  let B := univ.filter fun h : ZMod s => α ≤ h.val ∧ h.val < β.val
  have htop := hZ.residue_prefix_cost_le hp β x.1 (by simp only [β, ZMod.val_natCast])
    (fun z hz => singleton_residue_max hC hlast z
      (mem_filter.mp (Z.residuePrefixDigits_subset (k + 1) β hz)).1 (mem_filter.mp hz).2)
    (hgap β hα.le le_rfl)
  have hset : univ.filter (fun h : ZMod s => α ≤ h.val ∧ h.val ≤ β.val) = insert β B := by
    ext h
    simp only [mem_filter, mem_univ, true_and, mem_insert, B]
    constructor
    · intro hh
      by_cases he : h.val = β.val
      · exact Or.inl (ZMod.val_injective s he)
      · exact Or.inr ⟨hh.1, by omega⟩
    · rintro (rfl | hh)
      · exact ⟨hα.le, le_rfl⟩
      · exact ⟨hh.1, hh.2.le⟩
  have hβ : β ∉ B := by simp only [B, mem_filter, mem_univ, lt_self_iff_false, and_false, not_false_eq_true]
  change ((p : ℤ) ^ s - 1) ^ 2 * (∑ h ∈ univ.filter
    (fun h : ZMod s => α ≤ h.val ∧ h.val ≤ β.val), Z.priorPrefixCost h) ≤ _
  rw [hset, sum_insert hβ, mul_add]
  change ((p : ℤ) ^ s - 1) ^ 2 * Z.priorPrefixCost β ≤ _ at htop
  change ((p : ℤ) ^ s - 1) ^ 2 * (∑ h ∈ B, Z.priorPrefixCost h) ≤ _ at hcost
  linarith only [htop, hcost]

/-- Unchanged residue prefixes cancel; the others cost at most their new values. -/
private theorem prior_weight_difference_lower_bound
    (C Z : DigitComposition p s (k + 2) S) (hp : 2 ≤ p)
    (hC : C.TauMonotone) (hZ : Z.TauMonotone) (I : Finset (ZMod s))
    (hout : ∀ h ∉ I, ∀ j ≤ k + 1,
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits j) h =
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h) :
    -(∑ h ∈ I, Z.priorPrefixCost h) ≤
      ∑ j ∈ Icc 1 k, (digitValue p (C.prefixDigits j) - digitValue p (Z.prefixDigits j)) := by
  have he : (∑ j ∈ Icc 1 k, (digitValue p (C.prefixDigits j) - digitValue p (Z.prefixDigits j))) =
      ∑ h : ZMod s, (C.priorPrefixCost h - Z.priorPrefixCost h) := by
    calc
      _ = ∑ j ∈ Icc 1 k, ∑ h : ZMod s,
          (digitValue p (C.residuePrefixDigits j h) - digitValue p (Z.residuePrefixDigits j h)) := by
        apply sum_congr rfl
        intro j _
        rw [C.value_prefix_eq_sum_residue, Z.value_prefix_eq_sum_residue, sum_sub_distrib]
      _ = ∑ h : ZMod s, ∑ j ∈ Icc 1 k,
          (digitValue p (C.residuePrefixDigits j h) - digitValue p (Z.residuePrefixDigits j h)) := sum_comm
      _ = _ := sum_congr rfl fun _ _ => sum_sub_distrib _ _
  have hsum : (∑ h : ZMod s, if h ∈ I then -Z.priorPrefixCost h else 0) ≤
      ∑ h : ZMod s, (C.priorPrefixCost h - Z.priorPrefixCost h) := by
    apply sum_le_sum
    intro h _
    by_cases hh : h ∈ I
    · rw [if_pos hh]
      have hc := C.priorPrefixCost_nonneg h
      omega
    · rw [if_neg hh]
      have hcost : C.priorPrefixCost h = Z.priorPrefixCost h := by
        apply sum_congr rfl
        intro j hj
        exact hC.residue_prefix_value_eq hp hZ j h (hout h hh j (by have := mem_Icc.mp hj; omega)).symm
      rw [hcost, sub_self]
  have hfilter : univ.filter (fun h : ZMod s => h ∈ I) = I := by ext h; simp only [mem_filter, mem_univ, true_and]
  rw [← sum_filter, hfilter, sum_neg_distrib] at hsum
  rw [he]
  exact hsum

/-- The exact prefix identity isolates the new last-part gain. -/
private theorem weight_gain_lower_bound
    (C Z : DigitComposition p s (k + 2) S) (hp : 2 ≤ p)
    (hC : C.TauMonotone) (hZ : Z.TauMonotone) {x z : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x}) (hz : z ∈ Z.parts (Fin.last (k + 1)))
    (I : Finset (ZMod s))
    (hout : ∀ h ∉ I, ∀ j ≤ k + 1,
      tokenContent (fun t : Digit p => (t.1 : ZMod s)) (Z.prefixDigits j) h =
        tokenContent (fun t : Digit p => (t.1 : ZMod s)) (C.prefixDigits j) h) :
    (p : ℤ) ^ z.1 - (p : ℤ) ^ x.1 - (∑ h ∈ I, Z.priorPrefixCost h) ≤ Z.weight - C.weight := by
  have hprior := C.prior_weight_difference_lower_bound Z hp hC hZ I hout
  have hCsum := digitValue_union (p := p) C.prefix_disjoint_last
  have hZsum := digitValue_union (p := p) Z.prefix_disjoint_last
  rw [C.prefix_union_last, hlast] at hCsum
  rw [Z.prefix_union_last] at hZsum
  have hsingle : digitValue p ({x} : Finset (Digit p)) = (p : ℤ) ^ x.1 := by
    simp only [digitValue, tokenValue, sum_singleton]
  rw [hsingle] at hCsum
  have hlastle : (p : ℤ) ^ z.1 ≤ digitValue p (Z.parts (Fin.last (k + 1))) := by
    change (p : ℤ) ^ z.1 ≤ ∑ t ∈ Z.parts (Fin.last (k + 1)), (p : ℤ) ^ t.1
    exact single_le_sum (f := fun t : Digit p => (p : ℤ) ^ t.1)
      (fun t _ => pow_nonneg (Nat.cast_nonneg p) t.1) hz
  have hset : Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
    ext j
    simp only [mem_Icc, mem_insert]
    omega
  have hnot : k + 1 ∉ Icc 1 k := by simp only [mem_Icc]; omega
  rw [C.weight_sub_eq_prefix_sum Z, hset, sum_insert hnot]
  linarith only [hprior, hCsum, hZsum, hlastle]

/-- A normalized increasing singleton composition with a larger competing
last digit admits a strictly larger weight. The interval carry construction
and its geometric losses supply the improving composition explicitly. -/
theorem exists_strict_weight_improvement
    (C D : DigitComposition p s (k + 2) S) (hp : 2 ≤ p) (hs : 2 ≤ s)
    (hC : C.TauMonotone) {x y : Digit p}
    (hlast : C.parts (Fin.last (k + 1)) = {x})
    (hnorm : ∀ i : Fin (k + 1),
      inverseContent (p : ℚ) (fun j => (C.content i.castSucc j : ℚ)) 0 = 1)
    (hy : y ∈ D.parts (Fin.last (k + 1))) (hxy : x.1 < y.1)
    (hweight : cyclicWeighted (p : ℤ) (D.content (Fin.last (k + 1))) 0 =
      (p : ℤ) ^ (x.1 : ZMod s).val)
    (hbelow : ∀ z ∈ D.parts (Fin.last (k + 1)), (z.1 : ZMod s).val < (x.1 : ZMod s).val) :
    ∃ Z : DigitComposition p s (k + 2) S, C.weight < Z.weight := by
  have hyx : y ≠ x := by intro he; subst y; exact lt_irrefl _ hxy
  obtain ⟨α, Z, hα, hZ, hsupport, hout, _, hdrop, hgap⟩ :=
    C.exists_singleton_carry_modification D hp hlast hnorm hy hyx hweight hbelow
  obtain ⟨z, hz, hzmax⟩ := (Z.parts (Fin.last (k + 1))).exists_max_image Prod.fst
    (Z.nonempty (Fin.last (k + 1)))
  have hne : (x.1 : ZMod s) ≠ (y.1 : ZMod s) := by
    intro he
    have hh := hbelow y hy
    rw [← he] at hh
    exact lt_irrefl _ hh
  have hr := C.terminal_drop_leaves_last Z hp hlast (y.1 : ZMod s) hne
    (hdrop (y.1 : ZMod s) (hsupport y hy) (hbelow y hy))
    ⟨y, mem_filter.mpr ⟨D.subset _ hy, rfl⟩⟩
  obtain ⟨t, ht, _, htmax⟩ := hZ.exists_last_max hr
  have hxz : x.1 < z.1 := hxy.trans_le ((htmax y (D.subset _ hy) rfl).trans (hzmax t ht))
  have hpZ : (2 : ℤ) ≤ p := by exact_mod_cast hp
  have hp1 : (1 : ℤ) ≤ p := by omega
  have hPX : (p : ℤ) * (p : ℤ) ^ x.1 ≤ (p : ℤ) ^ z.1 := by
    calc
      (p : ℤ) * (p : ℤ) ^ x.1 = (p : ℤ) ^ (x.1 + 1) := by rw [pow_succ]; ring
      _ ≤ (p : ℤ) ^ z.1 := pow_le_pow_right₀ hp1 hxz
  obtain ⟨V, hV, hcost⟩ := C.exists_carry_cost_bound Z hp hC hZ hlast α z.1 hα hzmax hdrop hgap
  let I := univ.filter fun h : ZMod s => α ≤ h.val ∧ h.val ≤ (x.1 : ZMod s).val
  have hw := C.weight_gain_lower_bound Z hp hC hZ hlast hz I (fun h hh =>
    hout h (fun hb => hh (mem_filter.mpr ⟨mem_univ h, hb⟩)))
  have hw' := mul_le_mul_of_nonneg_left hw (sq_nonneg ((p : ℤ) ^ s - 1))
  change ((p : ℤ) ^ s - 1) ^ 2 * (∑ h ∈ I, Z.priorPrefixCost h) ≤ _ at hcost
  have hgain := positive_gain_of_geometric_bounds hpZ
    (pow_le_pow_right₀ hp1 hs) (pow_pos (by omega : (0 : ℤ) < p) z.1) hPX hV
    (show ((p : ℤ) ^ s - 1) ^ 2 * ((p : ℤ) ^ z.1 - (p : ℤ) ^ x.1) -
        ((p : ℤ) - 1) * (p : ℤ) ^ s * ((p : ℤ) ^ x.1 + V) ≤
          ((p : ℤ) ^ s - 1) ^ 2 * (Z.weight - C.weight) by
      nlinarith only [hw', hcost])
  exact ⟨Z, sub_pos.mp hgain⟩

end DigitComposition
end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.DigitComposition.exists_strict_weight_improvement
