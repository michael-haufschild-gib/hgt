import GaloisForLFunctions.HTGeometry.MilnorKDegTwoSymbol
import GaloisForLFunctions.HTGeometry.SteinbergKTwoCenter
import GaloisForLFunctions.HTGeometry.SteinbergMatsumotoComparison

/-!
# The degree-two Milnor-to-Steinberg map

Matsumoto's theorem begins with a concrete map from degree-two Milnor `K`-theory to `K₂`:

```text
{a,b} ↦ h_ij(ab) h_ij(a)⁻¹ h_ij(b)⁻¹.
```

At finite rank, its correct target is the central part of `K₂`; this file constructs that map
without any stable-range shortcut.  The two multilinearity relations are discharged by the exact
cross-torus comparison and spare-index bilinearity, while the Steinberg relation is the
complementary-unit Weyl calculation from `SteinbergMatsumotoRelation`.

This is the forward half of Matsumoto comparison.  It does not claim surjectivity onto all of
finite-rank `K₂`: that is the separate field-generation theorem, whose stable-range content must be
proved rather than inferred from the present construction.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : Type*} [DecidableEq n] [Fintype n]

/-- First entry of a degree-two Milnor symbol. -/
def milnorDegTwoFirst (s : MilnorSymbolDeg F 2) : Fˣ :=
  s.val.get ⟨0, by rw [s.property]; omega⟩

/-- Second entry of a degree-two Milnor symbol. -/
def milnorDegTwoSecond (s : MilnorSymbolDeg F 2) : Fˣ :=
  s.val.get ⟨1, by rw [s.property]; omega⟩

@[simp]
theorem milnorDegTwoFirst_pair (a b : Fˣ) :
    milnorDegTwoFirst (F := F) ⟨[a, b], rfl⟩ = a := rfl

@[simp]
theorem milnorDegTwoSecond_pair (a b : Fˣ) :
    milnorDegTwoSecond (F := F) ⟨[a, b], rfl⟩ = b := rfl

/-- The Steinberg word attached to a degree-two Milnor symbol, packaged in central `K₂`. -/
def milnorDegTwoSteinbergSymbol {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (s : MilnorSymbolDeg F 2) : steinbergKTwoCenter F n :=
  ⟨⟨steinbergSymbol hij (milnorDegTwoFirst s) (milnorDegTwoSecond s),
      steinbergSymbol_mem_center hij _ _ (Ne.symm hik) (Ne.symm hjk)⟩,
    steinbergSymbol_mem_KTwo hij _ _⟩

/-- The free additive map on degree-two Milnor symbols. -/
noncomputable def milnorDegTwoSteinbergLift {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    FreeAbelianGroup (MilnorSymbolDeg F 2) →+ Additive (steinbergKTwoCenter F n) :=
  FreeAbelianGroup.lift fun s => Additive.ofMul (milnorDegTwoSteinbergSymbol hij hik hjk s)

@[simp]
theorem milnorDegTwoSteinbergLift_of_pair {i j k : n} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (a b : Fˣ) :
    milnorDegTwoSteinbergLift hij hik hjk (FreeAbelianGroup.of ⟨[a, b], rfl⟩)
      = Additive.ofMul ⟨⟨steinbergSymbol hij a b,
          steinbergSymbol_mem_center hij a b (Ne.symm hik) (Ne.symm hjk)⟩,
        steinbergSymbol_mem_KTwo hij a b⟩ := by
  rw [milnorDegTwoSteinbergLift, FreeAbelianGroup.lift_apply_of]
  rfl

/-- The free degree-two Steinberg-symbol map kills both Milnor relation families. -/
theorem milnorDegTwoSteinbergLift_ker {i j k ℓ : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k) :
    milnorRelSubgroupDeg F 2 ≤ (milnorDegTwoSteinbergLift hij hik hjk).ker := by
  rw [milnorRelSubgroupDeg, AddSubgroup.closure_le]
  rintro x (⟨a, b, l₁, l₂, h, rfl⟩ | ⟨a, ha, l₁, l₂, h, rfl⟩)
  · rw [List.length_append] at h
    rcases show (l₁.length = 0 ∧ l₂.length = 1) ∨ (l₁.length = 1 ∧ l₂.length = 0) by omega with
      ⟨hl₁, hl₂⟩ | ⟨hl₁, hl₂⟩
    · have hnil : l₁ = [] := List.eq_nil_of_length_eq_zero hl₁
      subst hnil
      cases l₂ with
      | nil => simp at hl₂
      | cons c l₂ =>
        have htail : l₂ = [] := List.eq_nil_of_length_eq_zero (by simpa using hl₂)
        subst htail
        show milnorDegTwoSteinbergLift hij hik hjk _ = 0
        simp only [List.nil_append] at ⊢
        rw [map_sub, map_sub, milnorDegTwoSteinbergLift_of_pair,
          milnorDegTwoSteinbergLift_of_pair, milnorDegTwoSteinbergLift_of_pair]
        have hmul :
            (Additive.ofMul ⟨⟨steinbergSymbol hij (a * b) c,
              steinbergSymbol_mem_center hij _ _ (Ne.symm hik) (Ne.symm hjk)⟩,
                steinbergSymbol_mem_KTwo hij _ _⟩ :
              Additive (steinbergKTwoCenter F n))
              = (Additive.ofMul ⟨⟨steinbergSymbol hij a c,
                steinbergSymbol_mem_center hij _ _ (Ne.symm hik) (Ne.symm hjk)⟩,
                  steinbergSymbol_mem_KTwo hij _ _⟩ :
                Additive (steinbergKTwoCenter F n))
                + (Additive.ofMul ⟨⟨steinbergSymbol hij b c,
                  steinbergSymbol_mem_center hij _ _ (Ne.symm hik) (Ne.symm hjk)⟩,
                    steinbergSymbol_mem_KTwo hij _ _⟩ :
                  Additive (steinbergKTwoCenter F n)) := by
          apply Additive.toMul.injective
          apply Subtype.ext
          apply Subtype.ext
          exact steinbergSymbol_mul_left_of_spare_index hij hik hjk hℓi hℓj hℓk a b c
        rw [hmul]
        abel
    · have hnil : l₂ = [] := List.eq_nil_of_length_eq_zero hl₂
      subst hnil
      cases l₁ with
      | nil => simp at hl₁
      | cons c l₁ =>
        have htail : l₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hl₁)
        subst htail
        show milnorDegTwoSteinbergLift hij hik hjk _ = 0
        simp only [List.cons_append, List.nil_append] at ⊢
        rw [map_sub, map_sub, milnorDegTwoSteinbergLift_of_pair,
          milnorDegTwoSteinbergLift_of_pair, milnorDegTwoSteinbergLift_of_pair]
        have hmul :
            (Additive.ofMul ⟨⟨steinbergSymbol hij c (a * b),
              steinbergSymbol_mem_center hij _ _ (Ne.symm hik) (Ne.symm hjk)⟩,
                steinbergSymbol_mem_KTwo hij _ _⟩ :
              Additive (steinbergKTwoCenter F n))
              = (Additive.ofMul ⟨⟨steinbergSymbol hij c a,
                steinbergSymbol_mem_center hij _ _ (Ne.symm hik) (Ne.symm hjk)⟩,
                  steinbergSymbol_mem_KTwo hij _ _⟩ :
                Additive (steinbergKTwoCenter F n))
                + (Additive.ofMul ⟨⟨steinbergSymbol hij c b,
                  steinbergSymbol_mem_center hij _ _ (Ne.symm hik) (Ne.symm hjk)⟩,
                    steinbergSymbol_mem_KTwo hij _ _⟩ :
                  Additive (steinbergKTwoCenter F n)) := by
          apply Additive.toMul.injective
          apply Subtype.ext
          apply Subtype.ext
          exact steinbergSymbol_mul_right_of_spare_index hij hik hjk hℓi hℓj hℓk c a b
        rw [hmul]
        abel
  · rw [List.length_append] at h
    have hl₁ : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hl₂ : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hl₁
    subst hl₂
    show milnorDegTwoSteinbergLift hij hik hjk _ = 0
    simp only [List.nil_append] at ⊢
    rw [milnorDegTwoSteinbergLift_of_pair]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply steinbergSymbol_of_add_one hij hik hjk a (oneSubUnit ha)
    change (a : F) + (1 - (a : F)) = 1
    ring

/-- **The degree-two Milnor-to-Steinberg map** at four explicit indices. -/
noncomputable def milnorKTwoToSteinbergKTwoCenter {i j k ℓ : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k) :
    MilnorKDeg F 2 →+ Additive (steinbergKTwoCenter F n) :=
  QuotientAddGroup.lift _ (milnorDegTwoSteinbergLift hij hik hjk)
    (milnorDegTwoSteinbergLift_ker hij hik hjk hℓi hℓj hℓk)

@[simp]
theorem milnorKTwoToSteinbergKTwoCenter_pair {i j k ℓ : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hℓi : ℓ ≠ i) (hℓj : ℓ ≠ j) (hℓk : ℓ ≠ k) (a b : Fˣ) :
    milnorKTwoToSteinbergKTwoCenter hij hik hjk hℓi hℓj hℓk
      (milnorClassDeg F 2 ⟨[a, b], rfl⟩)
      = Additive.ofMul ⟨⟨steinbergSymbol hij a b,
          steinbergSymbol_mem_center hij a b (Ne.symm hik) (Ne.symm hjk)⟩,
        steinbergSymbol_mem_KTwo hij a b⟩ := by
  show milnorDegTwoSteinbergLift hij hik hjk (FreeAbelianGroup.of ⟨[a, b], rfl⟩) = _
  rw [milnorDegTwoSteinbergLift_of_pair]

end GaloisForLFunctions.HTGeometry

end
