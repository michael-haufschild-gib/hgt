import GaloisForLFunctions.HTGeometry.ZeroCountSturm

/-!
# The zero set itself is bounded

`zero_count_le` bounds a family of consecutive zeros.  Enumerating the finite zero set in increasing
order turns that into a bound on the zero set: an increasing enumeration has no element of the set
strictly between consecutive values, which is exactly the gap-freeness hypothesis.

Negating `f` turns the Sturm expression into its negative, so the bound holds wherever
`f'' + γ² f` merely does not vanish, in either sign.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

/-- **The zero set is bounded.**  Where `f'' + γ² f > 0` on `[a,b]`, the zeros of `f` there number at
most `2(b-a)γ/π + 2`. -/
theorem card_zeros_le {f fd fdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ 2 * f t)
    (hhpos : ∀ t ∈ Ioo a b, 0 < h t)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b) (hZzero : ∀ x ∈ Z, f x = 0)
    (hZall : ∀ x ∈ Icc a b, f x = 0 → x ∈ Z) :
    (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 2 := by
  have hnn : (0 : ℝ) ≤ (b - a) * γ / π := by
    have : (0 : ℝ) ≤ b - a := by linarith
    positivity
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Z.card = m := ⟨Z.card, rfl⟩
  match m, hm with
  | 0, hm =>
    rw [hm]
    simpa using by linarith
  | (n + 1), hm =>
    set e : Fin (n + 1) ↪o ℝ := Z.orderEmbOfFin hm with he
    set t : ℕ → ℝ := fun i => if hi : i < n + 1 then e ⟨i, hi⟩ else 0 with ht
    have hteq : ∀ i (hi : i < n + 1), t i = e ⟨i, hi⟩ := by
      intro i hi
      rw [ht]
      simp [hi]
    have hmono : ∀ i j, i < j → j ≤ n → t i < t j := by
      intro i j hij hjn
      rw [hteq i (by omega), hteq j (by omega)]
      exact (OrderEmbedding.lt_iff_lt e).mpr (by exact hij)
    have hmemZ : ∀ i, i ≤ n → t i ∈ Z := by
      intro i hi
      rw [hteq i (by omega)]
      exact Z.orderEmbOfFin_mem hm _
    have hmem : ∀ i, i ≤ n → t i ∈ Icc a b := fun i hi => hZmem _ (hmemZ i hi)
    have hzero : ∀ i, i ≤ n → f (t i) = 0 := fun i hi => hZzero _ (hmemZ i hi)
    have hgapfree : ∀ i, i < n → ∀ s ∈ Ioo (t i) (t (i + 1)), f s ≠ 0 := by
      intro i hi s hs hfs
      have hsab : s ∈ Icc a b := by
        refine ⟨le_trans (hmem i (by omega)).1 (le_of_lt hs.1),
          le_trans (le_of_lt hs.2) (hmem (i + 1) (by omega)).2⟩
      have hsZ : s ∈ Z := hZall s hsab hfs
      have hrange : s ∈ Set.range (e : Fin (n + 1) → ℝ) := by
        rw [Z.range_orderEmbOfFin hm]
        exact hsZ
      obtain ⟨j, hj⟩ := hrange
      have h1 : e ⟨i, by omega⟩ < e j := by
        rw [hj, ← hteq i (by omega)]
        exact hs.1
      have h2 : e j < e ⟨i + 1, by omega⟩ := by
        rw [hj, ← hteq (i + 1) (by omega)]
        exact hs.2
      have h1' : (⟨i, by omega⟩ : Fin (n + 1)) < j := (OrderEmbedding.lt_iff_lt e).mp h1
      have h2' : j < (⟨i + 1, by omega⟩ : Fin (n + 1)) := (OrderEmbedding.lt_iff_lt e).mp h2
      have : (i : ℕ) < (j : ℕ) := h1'
      have : (j : ℕ) < i + 1 := h2'
      omega
    have hcount := zero_count_le hγ hab hf hfd hh hhpos t hmono hmem hzero hgapfree
    rw [hm]
    push_cast
    linarith

/-- The same bound where the Sturm expression is negative, by negating `f`. -/
theorem card_zeros_le_neg {f fd fdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a ≤ b)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ 2 * f t)
    (hhneg : ∀ t ∈ Ioo a b, h t < 0)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b) (hZzero : ∀ x ∈ Z, f x = 0)
    (hZall : ∀ x ∈ Icc a b, f x = 0 → x ∈ Z) :
    (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 2 := by
  refine card_zeros_le (f := fun t => -f t) (fd := fun t => -fd t) (fdd := fun t => -fdd t)
    (h := fun t => -h t) hγ hab (fun t => (hf t).neg) (fun t => (hfd t).neg)
    (fun t => by rw [hh]; ring) (fun t htmem => by
      have := hhneg t htmem
      linarith) Z hZmem (fun x hx => by rw [hZzero x hx]; ring)
    (fun x hx hfx => hZall x hx (by linarith [hfx]))

/-- **The bound wherever the Sturm expression does not vanish** on the open interval. -/
theorem card_zeros_le_of_ne {f fd fdd h : ℝ → ℝ} {γ a b : ℝ} (hγ : 0 < γ) (hab : a < b)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ 2 * f t) (hhcont : Continuous h)
    (hhne : ∀ t ∈ Ioo a b, h t ≠ 0)
    (Z : Finset ℝ) (hZmem : ∀ x ∈ Z, x ∈ Icc a b) (hZzero : ∀ x ∈ Z, f x = 0)
    (hZall : ∀ x ∈ Icc a b, f x = 0 → x ∈ Z) :
    (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 2 := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hconst : ∀ s ∈ Ioo a b, h s ≠ 0 → (0 < h ((a + b) / 2) ↔ 0 < h s) := by
    intro s hs _
    constructor
    · intro hpos
      by_contra hcon
      push Not at hcon
      have hsne := hhne s hs
      have hslt : h s < 0 := lt_of_le_of_ne hcon hsne
      obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_uIcc (a := (a + b) / 2) (b := s)
        hhcont.continuousOn
        (show (0 : ℝ) ∈ uIcc (h ((a + b) / 2)) (h s) from by
          rw [Set.mem_uIcc]; exact Or.inr ⟨le_of_lt hslt, le_of_lt hpos⟩)
      exact hhne ξ ((Set.ordConnected_Ioo).uIcc_subset hmid hs hξ) hξ0
    · intro hpos
      by_contra hcon
      push Not at hcon
      have hmne := hhne _ hmid
      have hmlt : h ((a + b) / 2) < 0 := lt_of_le_of_ne hcon hmne
      obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_uIcc (a := (a + b) / 2) (b := s)
        hhcont.continuousOn
        (show (0 : ℝ) ∈ uIcc (h ((a + b) / 2)) (h s) from by
          rw [Set.mem_uIcc]; exact Or.inl ⟨le_of_lt hmlt, le_of_lt hpos⟩)
      exact hhne ξ ((Set.ordConnected_Ioo).uIcc_subset hmid hs hξ) hξ0
  rcases lt_trichotomy (h ((a + b) / 2)) 0 with hlt | heq | hgt
  · refine card_zeros_le_neg hγ hab.le hf hfd hh (fun s hs => ?_) Z hZmem hZzero hZall
    have hsne := hhne s hs
    rcases lt_trichotomy (h s) 0 with h1 | h1 | h1
    · exact h1
    · exact absurd h1 hsne
    · exact absurd ((hconst s hs hsne).mpr h1) (not_lt.mpr hlt.le)
  · exact absurd heq (hhne _ hmid)
  · refine card_zeros_le hγ hab.le hf hfd hh (fun s hs => ?_) Z hZmem hZzero hZall
    have hsne := hhne s hs
    exact (hconst s hs hsne).mp hgt


/-! ## Splitting at the zeros of the Sturm expression -/

/-- **The descent step.**  Splitting `[a,b]` at the zeros of `f'' + γ² f`, the zeros of `f` are
bounded by the interval length plus three times the number of Sturm zeros. -/
theorem card_zeros_le_split {f fd fdd h : ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ 2 * f t) (hhcont : Continuous h) :
    ∀ (M : ℕ) (a b : ℝ) (Z W : Finset ℝ), a < b → W.card ≤ M →
      (∀ x ∈ W, x ∈ Ioo a b) → (∀ x ∈ Ioo a b, h x = 0 → x ∈ W) →
      (∀ x ∈ Z, x ∈ Icc a b) → (∀ x ∈ Z, f x = 0) → (∀ x ∈ Icc a b, f x = 0 → x ∈ Z) →
      (Z.card : ℝ) ≤ 2 * ((b - a) * γ / π) + 3 * M + 2 := by
  classical
  intro M
  induction M with
  | zero =>
    intro a b Z W hab hW hWmem hWall hZmem hZzero hZall
    have hWe : W = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hW)
    have hne : ∀ t ∈ Ioo a b, h t ≠ 0 := by
      intro t ht hz
      have := hWall t ht hz
      rw [hWe] at this
      exact absurd this (Finset.notMem_empty t)
    have := card_zeros_le_of_ne hγ hab hf hfd hh hhcont hne Z hZmem hZzero hZall
    push_cast
    linarith
  | succ M ih =>
    intro a b Z W hab hW hWmem hWall hZmem hZzero hZall
    have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    by_cases hWe : W = ∅
    · have hne : ∀ t ∈ Ioo a b, h t ≠ 0 := by
        intro t ht hz
        have := hWall t ht hz
        rw [hWe] at this
        exact absurd this (Finset.notMem_empty t)
      have := card_zeros_le_of_ne hγ hab hf hfd hh hhcont hne Z hZmem hZzero hZall
      push_cast
      linarith
    · obtain ⟨w, hwW⟩ := Finset.nonempty_iff_ne_empty.mpr hWe
      set wm : ℝ := W.max' ⟨w, hwW⟩ with hwm
      have hwmW : wm ∈ W := W.max'_mem _
      have hwmIoo : wm ∈ Ioo a b := hWmem _ hwmW
      have hwmax : ∀ x ∈ W, x ≤ wm := fun x hx => W.le_max' x hx
      -- right piece: no Sturm zeros above the maximum
      set Z₂ : Finset ℝ := Z.filter (fun x => wm ≤ x) with hZ2
      have hZ2mem : ∀ x ∈ Z₂, x ∈ Icc wm b := by
        intro x hx
        rw [hZ2, Finset.mem_filter] at hx
        exact ⟨hx.2, (hZmem x hx.1).2⟩
      have hZ2zero : ∀ x ∈ Z₂, f x = 0 := by
        intro x hx
        rw [hZ2, Finset.mem_filter] at hx
        exact hZzero x hx.1
      have hZ2all : ∀ x ∈ Icc wm b, f x = 0 → x ∈ Z₂ := by
        intro x hx hfx
        rw [hZ2, Finset.mem_filter]
        exact ⟨hZall x ⟨le_trans hwmIoo.1.le hx.1, hx.2⟩ hfx, hx.1⟩
      have hne2 : ∀ t ∈ Ioo wm b, h t ≠ 0 := by
        intro t ht hz
        have htab : t ∈ Ioo a b := ⟨lt_trans hwmIoo.1 ht.1, ht.2⟩
        exact absurd (hwmax t (hWall t htab hz)) (not_le.mpr ht.1)
      have hbound2 := card_zeros_le_of_ne hγ hwmIoo.2 hf hfd hh hhcont hne2 Z₂
        hZ2mem hZ2zero hZ2all
      -- left piece: one fewer Sturm zero
      set Z₁ : Finset ℝ := Z.filter (fun x => x ≤ wm) with hZ1
      set W₁ : Finset ℝ := W.erase wm with hW1
      have hW1card : W₁.card ≤ M := by
        have := Finset.card_erase_of_mem hwmW
        rw [hW1, this]
        omega
      have hW1mem : ∀ x ∈ W₁, x ∈ Ioo a wm := by
        intro x hx
        rw [hW1, Finset.mem_erase] at hx
        exact ⟨(hWmem x hx.2).1, lt_of_le_of_ne (hwmax x hx.2) hx.1⟩
      have hW1all : ∀ x ∈ Ioo a wm, h x = 0 → x ∈ W₁ := by
        intro x hx hz
        rw [hW1, Finset.mem_erase]
        exact ⟨ne_of_lt hx.2, hWall x ⟨hx.1, lt_trans hx.2 hwmIoo.2⟩ hz⟩
      have hZ1mem : ∀ x ∈ Z₁, x ∈ Icc a wm := by
        intro x hx
        rw [hZ1, Finset.mem_filter] at hx
        exact ⟨(hZmem x hx.1).1, hx.2⟩
      have hZ1zero : ∀ x ∈ Z₁, f x = 0 := by
        intro x hx
        rw [hZ1, Finset.mem_filter] at hx
        exact hZzero x hx.1
      have hZ1all : ∀ x ∈ Icc a wm, f x = 0 → x ∈ Z₁ := by
        intro x hx hfx
        rw [hZ1, Finset.mem_filter]
        exact ⟨hZall x ⟨hx.1, le_trans hx.2 hwmIoo.2.le⟩ hfx, hx.2⟩
      have hbound1 := ih a wm Z₁ W₁ hwmIoo.1 hW1card hW1mem hW1all hZ1mem hZ1zero hZ1all
      -- combine
      have hsub : Z ⊆ Z₁ ∪ Z₂ := by
        intro x hx
        rw [Finset.mem_union, hZ1, hZ2, Finset.mem_filter, Finset.mem_filter]
        rcases le_total x wm with hle | hge
        · exact Or.inl ⟨hx, hle⟩
        · exact Or.inr ⟨hx, hge⟩
      have hcard : Z.card ≤ Z₁.card + Z₂.card :=
        le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have hcast : (Z.card : ℝ) ≤ (Z₁.card : ℝ) + (Z₂.card : ℝ) := by exact_mod_cast hcard
      have hsplit : (b - a) * γ / π = (wm - a) * γ / π + (b - wm) * γ / π := by
        field_simp
        ring
      push_cast
      rw [hsplit]
      linarith

end GaloisForLFunctions.HTGeometry
