import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.ReciprocalTorusSingularities

/-!
# The constant trace of the reciprocal torus critical locus

Every normalized critical coordinate is a sign. Consequently all critical points
descend through every field embedding, including in characteristic two. Their
finite-field count is unchanged by extension and supplies a trace with eigenvalue one.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

section FieldEmbedding

variable {F E : Type*} [Field F] [Field E]

/-- Apply a field embedding coordinatewise to a nonzero torus tuple. -/
def momentTorusMap (φ : F →+* E) {m : ℕ} (x : MomentTorus F m) : MomentTorus E m :=
  fun i => ⟨φ (x i), fun h => (x i).property (φ.injective (h.trans φ.map_zero.symm))⟩

theorem momentTorusMap_apply (φ : F →+* E) {m : ℕ} (x : MomentTorus F m) (i : Fin m) :
    (momentTorusMap φ x i : E) = φ (x i) := rfl

theorem momentTorusMap_injective (φ : F →+* E) (m : ℕ) :
    Function.Injective (momentTorusMap φ (m := m)) := by
  intro x y h
  funext i
  apply Subtype.ext
  apply φ.injective
  exact congrArg (fun z : {a : E // a ≠ 0} => z.val) (congrFun h i)

/-- Sign coordinates descend through every field embedding. -/
theorem momentTorusMap_signs_descend (φ : F →+* E) {m : ℕ} (x : MomentTorus E m)
    (hx : ∀ i, (x i : E) = 1 ∨ (x i : E) = -1) :
    ∃ y : MomentTorus F m, (∀ i, (y i : F) = 1 ∨ (y i : F) = -1) ∧
      momentTorusMap φ y = x := by
  classical
  let y : MomentTorus F m := fun i =>
    ⟨if (x i : E) = 1 then 1 else -1, by split_ifs <;> simp⟩
  refine ⟨y, ?_, ?_⟩
  · intro i
    by_cases hi : (x i : E) = 1
    · exact Or.inl (if_pos hi)
    · exact Or.inr (if_neg hi)
  · funext i
    apply Subtype.ext
    change φ (if (x i : E) = 1 then 1 else -1) = (x i : E)
    by_cases hi : (x i : E) = 1
    · rw [if_pos hi, map_one, hi]
    · rw [if_neg hi, map_neg, map_one, (hx i).resolve_left hi]

end FieldEmbedding

section FiniteField

variable {F E : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Field E] [Fintype E] [DecidableEq E]

/-- The actual critical locus in the normalized torus chart. -/
def reciprocalTorusCriticalPoints (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) : Finset (MomentTorus F m) := by
  classical
  exact (normalizedDoubleZeroTorus (F := F) m).filter (fun x =>
    ∀ v : Fin (m + 1) → F, (∑ i, v i) = 0 → v 0 = 0 →
      reciprocalLinear (Fin.cons 1 (fun j => (x j : F))) v = 0)

/-- Criticality is equivalent to the double-zero equations and sign coordinates. -/
theorem mem_reciprocalTorusCriticalPoints_iff {m : ℕ} (x : MomentTorus F m) :
    x ∈ reciprocalTorusCriticalPoints F m ↔
      x ∈ normalizedDoubleZeroTorus (F := F) m ∧
        ∀ i, (x i : F) = 1 ∨ (x i : F) = -1 := by
  classical
  constructor
  · intro hx
    have h := mem_filter.mp hx
    exact ⟨h.1, (normalizedDoubleZeroTorus_critical_iff x h.1).mp h.2⟩
  · rintro ⟨hx, hs⟩
    exact mem_filter.mpr ⟨hx, (normalizedDoubleZeroTorus_critical_iff x hx).mpr hs⟩

/-- A field embedding preserves and reflects both normalized vanishing equations. -/
theorem momentTorusMap_mem_double_iff (φ : F →+* E) {m : ℕ} (x : MomentTorus F m) :
    momentTorusMap φ x ∈ normalizedDoubleZeroTorus (F := E) m ↔
      x ∈ normalizedDoubleZeroTorus (F := F) m := by
  have hs : 1 + ∑ i, (momentTorusMap φ x i : E) = φ (1 + ∑ i, (x i : F)) := by
    simp only [momentTorusMap_apply, map_add, map_one, map_sum]
  have hr : 1 + ∑ i, (momentTorusMap φ x i : E)⁻¹ = φ (1 + ∑ i, (x i : F)⁻¹) := by
    simp only [momentTorusMap_apply, map_add, map_one, map_sum, map_inv₀]
  have hz (z : F) : φ z = 0 ↔ z = 0 := by
    constructor
    · intro h
      exact φ.injective (h.trans φ.map_zero.symm)
    · intro h
      rw [h, map_zero]
  simp only [normalizedDoubleZeroTorus, normalizedCoordinateZeroTorus,
    mem_filter, mem_univ, true_and, hs, hr, hz]

/-- Every normalized critical point is already defined over the smaller field. -/
theorem reciprocalTorusCriticalPoints_card_embedding (φ : F →+* E) (m : ℕ) :
    (reciprocalTorusCriticalPoints F m).card = (reciprocalTorusCriticalPoints E m).card := by
  classical
  apply card_bij (fun x _ => momentTorusMap φ x)
  · intro x hx
    obtain ⟨hd, hs⟩ := (mem_reciprocalTorusCriticalPoints_iff x).mp hx
    apply (mem_reciprocalTorusCriticalPoints_iff _).mpr
    refine ⟨(momentTorusMap_mem_double_iff φ x).mpr hd, ?_⟩
    intro i
    rcases hs i with hi | hi
    · exact Or.inl (by rw [momentTorusMap_apply, hi, map_one])
    · exact Or.inr (by rw [momentTorusMap_apply, hi, map_neg, map_one])
  · intro x _ y _ h
    exact momentTorusMap_injective φ m h
  · intro x hx
    obtain ⟨hd, hs⟩ := (mem_reciprocalTorusCriticalPoints_iff x).mp hx
    obtain ⟨y, hy, he⟩ := momentTorusMap_signs_descend φ x hs
    refine ⟨y, (mem_reciprocalTorusCriticalPoints_iff y).mpr ⟨?_, hy⟩, he⟩
    apply (momentTorusMap_mem_double_iff φ y).mp
    rwa [he]

omit [Field E] [Fintype E] [DecidableEq E] in
/-- The critical-point trace has one eigenvalue `1` for each actual critical point. -/
def criticalPointTateTrace (m e : ℕ) : ℂ :=
  ∑ _x ∈ reciprocalTorusCriticalPoints F m, (1 : ℂ) ^ e

omit [Field E] [Fintype E] [DecidableEq E] in
/-- The constant Tate trace counts the critical locus over every finite extension. -/
theorem criticalPointTateTrace_extension_count (m : ℕ) (E : Type*) [Field E] [Fintype E]
    [DecidableEq E] [Algebra F E] :
    criticalPointTateTrace (F := F) m (Module.finrank F E) =
      ((reciprocalTorusCriticalPoints E m).card : ℂ) := by
  simp only [criticalPointTateTrace, one_pow, sum_const, nsmul_eq_mul, mul_one]
  exact congrArg (fun n : ℕ => (n : ℂ))
    (reciprocalTorusCriticalPoints_card_embedding (algebraMap F E) m)

end FiniteField

section SignCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The subset records exactly the coordinates assigned the negative sign. -/
def signedMomentTorus {m : ℕ} (S : Finset (Fin m)) : MomentTorus F m :=
  fun i => ⟨if i ∈ S then -1 else 1, by split_ifs <;> simp⟩

omit [Fintype F] [DecidableEq F] in
theorem signedMomentTorus_sum {m : ℕ} (S : Finset (Fin m)) :
    (∑ i, (signedMomentTorus (F := F) S i : F)) = (m : F) - 2 * S.card := by
  have hi : ∀ i, (signedMomentTorus (F := F) S i : F) =
      1 - 2 * (if i ∈ S then 1 else 0) := by
    intro i
    by_cases h : i ∈ S
    · simp only [signedMomentTorus, if_pos h]
      ring
    · simp only [signedMomentTorus, if_neg h, mul_zero, sub_zero]
  simp only [hi, sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sum_boole]
  simp

/-- For sign coordinates, both normalized equations reduce to the same cardinality equation. -/
theorem signedMomentTorus_mem_critical_iff {m : ℕ} (S : Finset (Fin m)) :
    signedMomentTorus (F := F) S ∈ reciprocalTorusCriticalPoints F m ↔
      ((m + 1 : ℕ) : F) = 2 * S.card := by
  have hs : ∀ i, (signedMomentTorus (F := F) S i : F) = 1 ∨
      (signedMomentTorus (F := F) S i : F) = -1 := by
    intro i
    by_cases hi : i ∈ S
    · exact Or.inr (if_pos hi)
    · exact Or.inl (if_neg hi)
  have hinv : ∀ i, (signedMomentTorus (F := F) S i : F)⁻¹ =
      (signedMomentTorus (F := F) S i : F) := by
    intro i
    rcases hs i with hi | hi <;> simp only [hi, inv_one, inv_neg]
  rw [mem_reciprocalTorusCriticalPoints_iff]
  have hd : signedMomentTorus (F := F) S ∈ normalizedDoubleZeroTorus (F := F) m ↔
      ((m + 1 : ℕ) : F) = 2 * S.card := by
    simp only [normalizedDoubleZeroTorus, normalizedCoordinateZeroTorus,
      mem_filter, mem_univ, true_and, hinv, signedMomentTorus_sum, and_self,
      Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linear_combination h
  exact ⟨fun h => hd.mp h.1, fun h => ⟨hd.mpr h, hs⟩⟩

/-- Subsets whose sign vectors satisfy the normalized sum equation. -/
def criticalSignSubsets (F : Type*) [Field F] [DecidableEq F] (m : ℕ) : Finset (Finset (Fin m)) :=
  univ.filter (fun S => ((m + 1 : ℕ) : F) = 2 * S.card)

/-- Away from characteristic two, negative-coordinate subsets parametrize every critical point. -/
theorem criticalSignSubsets_card (h₂ : (2 : F) ≠ 0) (m : ℕ) :
    (criticalSignSubsets F m).card = (reciprocalTorusCriticalPoints F m).card := by
  have hsign : (1 : F) ≠ -1 := by
    intro h
    apply h₂
    calc (2 : F) = 1 + 1 := by ring
      _ = -1 + 1 := congrArg (fun z : F => z + 1) h
      _ = 0 := neg_add_cancel _
  have hmem (S : Finset (Fin m)) (i : Fin m) :
      (signedMomentTorus (F := F) S i : F) = -1 ↔ i ∈ S := by
    by_cases hi : i ∈ S <;> simp [signedMomentTorus, hi, hsign]
  apply card_bij (fun S _ => signedMomentTorus (F := F) S)
  · intro S hS
    exact (signedMomentTorus_mem_critical_iff S).mpr (mem_filter.mp hS).2
  · intro S _ T _ h
    ext i
    rw [← hmem S i, ← hmem T i, h]
  · intro x hx
    let S : Finset (Fin m) := univ.filter (fun i => (x i : F) = -1)
    have he : signedMomentTorus (F := F) S = x := by
      funext i
      apply Subtype.ext
      rcases ((mem_reciprocalTorusCriticalPoints_iff x).mp hx).2 i with hi | hi
      · simp [signedMomentTorus, S, hi, hsign]
      · simp [signedMomentTorus, S, hi]
    refine ⟨S, mem_filter.mpr ⟨mem_univ _, ?_⟩, he⟩
    exact (signedMomentTorus_mem_critical_iff S).mp (he.symm ▸ hx)

/-- The exact critical-point count, including all characteristic-dependent sign strata. -/
theorem reciprocalTorusCriticalPoints_card (h₂ : (2 : F) ≠ 0) (m : ℕ) :
    (reciprocalTorusCriticalPoints F m).card =
      ∑ r ∈ (range (m + 1)).filter (fun r : ℕ => ((m + 1 : ℕ) : F) = 2 * (r : F)),
        m.choose r := by
  rw [← criticalSignSubsets_card h₂]
  have hsplit : criticalSignSubsets F m =
      ((range (m + 1)).filter (fun r : ℕ => ((m + 1 : ℕ) : F) = 2 * (r : F))).biUnion
        (fun r => (univ : Finset (Fin m)).powersetCard r) := by
    ext S
    simp only [criticalSignSubsets, mem_filter, mem_univ, true_and, mem_biUnion,
      mem_range, mem_powersetCard, subset_univ]
    constructor
    · intro hS
      have hc : S.card ≤ m := by simpa only [Fintype.card_fin] using card_le_univ S
      exact ⟨S.card, ⟨by omega, hS⟩, rfl⟩
    · rintro ⟨r, ⟨_, hr⟩, he⟩
      rwa [he]
  rw [hsplit, card_biUnion]
  · simp only [card_powersetCard, card_univ, Fintype.card_fin]
  · intro r _ s _ hrs
    apply disjoint_left.mpr
    intro S hr hs
    exact hrs ((mem_powersetCard.mp hr).2.symm.trans (mem_powersetCard.mp hs).2)

/-- In characteristic two, the only possible normalized critical point is the all-one tuple. -/
theorem reciprocalTorusCriticalPoints_card_char_two (h₂ : (2 : F) = 0) (m : ℕ) :
    (reciprocalTorusCriticalPoints F m).card =
      if ((m + 1 : ℕ) : F) = 0 then 1 else 0 := by
  have hneg : (-1 : F) = 1 := by
    calc (-1 : F) = -1 + 2 := by rw [h₂, add_zero]
      _ = 1 := by ring
  have huniq : ∀ x ∈ reciprocalTorusCriticalPoints F m,
      x = signedMomentTorus (F := F) ∅ := by
    intro x hx
    funext i
    apply Subtype.ext
    rcases ((mem_reciprocalTorusCriticalPoints_iff x).mp hx).2 i with hi | hi
    · simpa [signedMomentTorus] using hi
    · simpa [signedMomentTorus, hneg] using hi
  have hmem : signedMomentTorus (F := F) (∅ : Finset (Fin m)) ∈
      reciprocalTorusCriticalPoints F m ↔ ((m + 1 : ℕ) : F) = 0 := by
    rw [signedMomentTorus_mem_critical_iff]
    simp only [card_empty, Nat.cast_zero, mul_zero]
  by_cases hn : ((m + 1 : ℕ) : F) = 0
  · have heq : reciprocalTorusCriticalPoints F m = {signedMomentTorus (F := F) ∅} := by
      ext x
      simp only [mem_singleton]
      exact ⟨huniq x, fun h => h.symm ▸ hmem.mpr hn⟩
    rw [heq, card_singleton, if_pos hn]
  · have heq : reciprocalTorusCriticalPoints F m = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim (hn (hmem.mp ((huniq x hx) ▸ hx)))
      · intro hx
        simp at hx
    rw [heq, card_empty, if_neg hn]

end SignCount

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
