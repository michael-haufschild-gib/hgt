import Mathlib

/-!
# Counting separated points in intervals

A finite set of reals whose distinct elements are at pairwise distance at least `L` meets an
interval of length `ℓ` in at most `ℓ/L + 1` points, and a union of `k` such intervals in at most
`(total length)/L + k` points.  The proof compares the elements through the floor map
`x ↦ ⌊(x - a)/L⌋`, which is injective on an `L`-separated set.
-/

open Finset


/-- An `L`-separated finite set of reals contained in `[a, b]` has at most `(b - a)/L + 1`
elements. -/
theorem card_le_of_separated_of_subset_Icc
    {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → L ≤ |x - y|)
    (hsub : ∀ x ∈ S, x ∈ Set.Icc a b) :
    (S.card : ℝ) ≤ (b - a) / L + 1 := by
  classical
  have hmaps : Set.MapsTo (fun x : ℝ => ⌊(x - a) / L⌋) (S : Set ℝ)
      ((Finset.Icc (0 : ℤ) ⌊(b - a) / L⌋ : Finset ℤ) : Set ℤ) := by
    intro x hx
    have hxS : x ∈ S := by simpa using hx
    obtain ⟨hxa, hxb⟩ := hsub x hxS
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨Int.le_floor.2 ?_, Int.floor_le_floor ?_⟩
    · simpa using div_nonneg (by linarith) hL.le
    · exact div_le_div_of_nonneg_right (by linarith) hL.le
  have hinj : Set.InjOn (fun x : ℝ => ⌊(x - a) / L⌋) (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hxS : x ∈ S := by simpa using hx
    have hyS : y ∈ S := by simpa using hy
    have hsep' := hsep x hxS y hyS hne
    have h1 : (x - a) / L < ((⌊(x - a) / L⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 : ((⌊(y - a) / L⌋ : ℤ) : ℝ) ≤ (y - a) / L := Int.floor_le _
    have h3 : (y - a) / L < ((⌊(y - a) / L⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h4 : ((⌊(x - a) / L⌋ : ℤ) : ℝ) ≤ (x - a) / L := Int.floor_le _
    simp only at hxy
    rw [hxy] at h1 h4
    have hlt : |(x - y) / L| < 1 := by
      have hrw : (x - y) / L = (x - a) / L - (y - a) / L := by
        field_simp
        ring
      rw [hrw, abs_lt]
      constructor <;> linarith
    rw [abs_div, abs_of_pos hL, div_lt_one hL] at hlt
    linarith
  have key := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Int.card_Icc] at key
  have hfl : (0 : ℤ) ≤ ⌊(b - a) / L⌋ :=
    Int.le_floor.2 (by simpa using div_nonneg (by linarith) hL.le)
  have hz : ((⌊(b - a) / L⌋ + 1 - 0).toNat : ℤ) = ⌊(b - a) / L⌋ + 1 := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hcast : ((⌊(b - a) / L⌋ + 1 - 0).toNat : ℝ) = (⌊(b - a) / L⌋ : ℝ) + 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
  have h5 : (S.card : ℝ) ≤ ((⌊(b - a) / L⌋ + 1 - 0).toNat : ℝ) := by exact_mod_cast key
  rw [hcast] at h5
  have h6 : (⌊(b - a) / L⌋ : ℝ) ≤ (b - a) / L := Int.floor_le _
  linarith

/-- An `L`-separated finite set of reals covered by the intervals `[a i, b i]`, `i ∈ I`, has at
most `(∑ i ∈ I, (b i - a i))/L + #I` elements. -/
theorem card_le_of_separated_of_subset_iUnion_Icc
    {ι : Type*} [DecidableEq ι] {L : ℝ} (hL : 0 < L) (I : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ I, a i ≤ b i) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → L ≤ |x - y|)
    (hsub : ∀ x ∈ S, ∃ i ∈ I, x ∈ Set.Icc (a i) (b i)) :
    (S.card : ℝ) ≤ (∑ i ∈ I, (b i - a i)) / L + I.card := by
  classical
  have hsum : (0 : ℝ) ≤ ∑ i ∈ I, (b i - a i) :=
    Finset.sum_nonneg fun i hi => by linarith [hab i hi]
  rcases S.eq_empty_or_nonempty with rfl | hS
  · have h1 : (0 : ℝ) ≤ (∑ i ∈ I, (b i - a i)) / L := div_nonneg hsum hL.le
    have h2 : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  obtain ⟨x0, hx0⟩ := hS
  obtain ⟨i0, -, -⟩ := hsub x0 hx0
  have hsub' : ∀ x : ℝ, ∃ i : ι, x ∈ S → (i ∈ I ∧ x ∈ Set.Icc (a i) (b i)) := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨i, hiI, hmem⟩ := hsub x hx
      exact ⟨i, fun _ => ⟨hiI, hmem⟩⟩
    · exact ⟨i0, fun h => absurd h hx⟩
  choose g hg using hsub'
  have hgI : ∀ x ∈ S, g x ∈ I := fun x hx => (hg x hx).1
  have hgmem : ∀ x ∈ S, x ∈ Set.Icc (a (g x)) (b (g x)) := fun x hx => (hg x hx).2
  have hfib : S.card = ∑ i ∈ I, (S.filter fun x => g x = i).card :=
    Finset.card_eq_sum_card_fiberwise hgI
  have hbound : ∀ i ∈ I, ((S.filter fun x => g x = i).card : ℝ) ≤ (b i - a i) / L + 1 := by
    intro i hi
    refine card_le_of_separated_of_subset_Icc hL (hab i hi) _ ?_ ?_
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_of_mem_filter x hx) y (Finset.mem_of_mem_filter y hy) hxy
    · intro x hx
      have hxS : x ∈ S := Finset.mem_of_mem_filter x hx
      have hgx : g x = i := (Finset.mem_filter.1 hx).2
      have := hgmem x hxS
      rwa [hgx] at this
  calc (S.card : ℝ) = ∑ i ∈ I, ((S.filter fun x => g x = i).card : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hfib
    _ ≤ ∑ i ∈ I, ((b i - a i) / L + 1) := Finset.sum_le_sum hbound
    _ = (∑ i ∈ I, (b i - a i)) / L + I.card := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
        simp

/-- If `f` expands distances by a factor at least `c > 0` on an `L`-separated finite set `S` whose
image lies in `[a, b]`, then `S` has at most `(b - a)/(cL) + 1` elements. -/
theorem card_le_of_expanding_of_separated
    {c L a b : ℝ} (hc : 0 < c) (hL : 0 < L) (hab : a ≤ b)
    (f : ℝ → ℝ) (S : Finset ℝ)
    (hexp : ∀ x ∈ S, ∀ y ∈ S, c * |x - y| ≤ |f x - f y|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → L ≤ |x - y|)
    (hmaps : ∀ x ∈ S, f x ∈ Set.Icc a b) :
    (S.card : ℝ) ≤ (b - a) / (c * L) + 1 := by
  classical
  have hinj : Set.InjOn f (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hxS : x ∈ S := by simpa using hx
    have hyS : y ∈ S := by simpa using hy
    have h1 : L ≤ |x - y| := hsep x hxS y hyS hne
    have h2 : c * |x - y| ≤ |f x - f y| := hexp x hxS y hyS
    rw [hxy] at h2
    simp only [sub_self, abs_zero] at h2
    nlinarith
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hsepT : ∀ u ∈ S.image f, ∀ v ∈ S.image f, u ≠ v → c * L ≤ |u - v| := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    have hne : x ≠ y := fun h => huv (by rw [h])
    have h1 : L ≤ |x - y| := hsep x hx y hy hne
    have h2 : c * |x - y| ≤ |f x - f y| := hexp x hx y hy
    nlinarith
  have hsubT : ∀ u ∈ S.image f, u ∈ Set.Icc a b := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    exact hmaps x hx
  have := card_le_of_separated_of_subset_Icc (mul_pos hc hL) hab (S.image f) hsepT hsubT
  rwa [hcard] at this

/-- If `f` expands distances by a factor at least `c > 0` on an `L`-separated finite set `S` whose
image is covered by the intervals `[a i, b i]`, `i ∈ I`, then
`#S ≤ (∑ i ∈ I, (b i - a i))/(cL) + #I`. -/
theorem card_le_of_expanding_of_separated_iUnion_Icc
    {ι : Type*} [DecidableEq ι] {c L : ℝ} (hc : 0 < c) (hL : 0 < L)
    (I : Finset ι) (a b : ι → ℝ) (hab : ∀ i ∈ I, a i ≤ b i)
    (f : ℝ → ℝ) (S : Finset ℝ)
    (hexp : ∀ x ∈ S, ∀ y ∈ S, c * |x - y| ≤ |f x - f y|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → L ≤ |x - y|)
    (hmaps : ∀ x ∈ S, ∃ i ∈ I, f x ∈ Set.Icc (a i) (b i)) :
    (S.card : ℝ) ≤ (∑ i ∈ I, (b i - a i)) / (c * L) + I.card := by
  classical
  have hinj : Set.InjOn f (S : Set ℝ) := by
    intro x hx y hy hxy
    by_contra hne
    have hxS : x ∈ S := by simpa using hx
    have hyS : y ∈ S := by simpa using hy
    have h1 : L ≤ |x - y| := hsep x hxS y hyS hne
    have h2 : c * |x - y| ≤ |f x - f y| := hexp x hxS y hyS
    rw [hxy] at h2
    simp only [sub_self, abs_zero] at h2
    nlinarith
  have hcard : (S.image f).card = S.card := Finset.card_image_of_injOn hinj
  have hsepT : ∀ u ∈ S.image f, ∀ v ∈ S.image f, u ≠ v → c * L ≤ |u - v| := by
    intro u hu v hv huv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    have hne : x ≠ y := fun h => huv (by rw [h])
    have h1 : L ≤ |x - y| := hsep x hx y hy hne
    have h2 : c * |x - y| ≤ |f x - f y| := hexp x hx y hy
    nlinarith
  have hsubT : ∀ u ∈ S.image f, ∃ i ∈ I, u ∈ Set.Icc (a i) (b i) := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    exact hmaps x hx
  have := card_le_of_separated_of_subset_iUnion_Icc (mul_pos hc hL) I a b hab
    (S.image f) hsepT hsubT
  rwa [hcard] at this
