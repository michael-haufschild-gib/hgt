import GaloisForLFunctions.HTGeometry.SeparatedPointCount

/-!
# Counting multiples and large gcds in an interval

The multiples of `g` in `[B, C)` are `g`-separated, so there are at most `(C-B)/g + 1` of them.
Fibering over `gcd A m` turns this into a bound for the number of `m ∈ [B, C)` whose gcd with a fixed
`A` exceeds a threshold: such `m` are multiples of a divisor of `A` above the threshold.
-/

open Finset

/-- The multiples of `g` in `[B, C)` number at most `(C - B)/g + 1`. -/
theorem card_multiples_Ico_le {g B C : ℕ} (hg : 0 < g) (hBC : B ≤ C) :
    ((((Finset.Ico B C).filter (fun m => g ∣ m)).card : ℝ)) ≤ ((C : ℝ) - B) / g + 1 := by
  classical
  set F := (Finset.Ico B C).filter (fun m => g ∣ m) with hF
  set S : Finset ℝ := F.image (fun m : ℕ => (m : ℝ)) with hS
  have hcard : S.card = F.card := Finset.card_image_of_injective _ Nat.cast_injective
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (g : ℝ) ≤ |x - y| := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨u, rfl⟩ := (Finset.mem_filter.1 ha).2
    obtain ⟨v, rfl⟩ := (Finset.mem_filter.1 hb).2
    have huv : u ≠ v := by
      intro h; exact hxy (by rw [h])
    rcases lt_trichotomy u v with h | h | h
    · have hnat : g * u + g ≤ g * v := by nlinarith
      have hR : (g : ℝ) * u + g ≤ (g : ℝ) * v := by exact_mod_cast hnat
      rw [abs_sub_comm, abs_of_nonneg (by push_cast; linarith)]
      push_cast
      linarith
    · exact absurd h huv
    · have hnat : g * v + g ≤ g * u := by nlinarith
      have hR : (g : ℝ) * v + g ≤ (g : ℝ) * u := by exact_mod_cast hnat
      rw [abs_of_nonneg (by push_cast; linarith)]
      push_cast
      linarith
  have hsub : ∀ x ∈ S, x ∈ Set.Icc (B : ℝ) (C : ℝ) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    have hmem := Finset.mem_Ico.1 (Finset.mem_of_mem_filter a ha)
    exact ⟨by exact_mod_cast hmem.1, by exact_mod_cast hmem.2.le⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hBCR : (B : ℝ) ≤ C := by exact_mod_cast hBC
  have := card_le_of_separated_of_subset_Icc hgR hBCR S hsep hsub
  rwa [hcard] at this

/-- The `m ∈ [B, C)` with `gcd A m > G` number at most `∑ g ∣ A, g > G, ((C - B)/g + 1)`. -/
theorem card_gcd_gt_le {A B C G : ℕ} (hA : A ≠ 0) (hBC : B ≤ C)
    :
    (((Finset.Ico B C).filter (fun m => G < Nat.gcd A m)).card : ℝ)
      ≤ ∑ g ∈ A.divisors.filter (fun g => G < g), (((C : ℝ) - B) / g + 1) := by
  classical
  set F := (Finset.Ico B C).filter (fun m => G < Nat.gcd A m) with hF
  set D := A.divisors.filter (fun g => G < g) with hD
  have hmaps : ∀ m ∈ F, Nat.gcd A m ∈ D := by
    intro m hm
    have hgt : G < Nat.gcd A m := (Finset.mem_filter.1 hm).2
    exact Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left A m, hA⟩, hgt⟩
  have hfib : F.card = ∑ g ∈ D, (F.filter fun m => Nat.gcd A m = g).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ g ∈ D, (((F.filter fun m => Nat.gcd A m = g).card : ℝ)) ≤ ((C : ℝ) - B) / g + 1 := by
    intro g hg
    have hgpos : 0 < g := by
      have := Nat.mem_divisors.1 (Finset.mem_of_mem_filter g hg)
      exact Nat.pos_of_mem_divisors (Nat.mem_divisors.2 this)
    refine le_trans ?_ (card_multiples_Ico_le hgpos hBC)
    have hsub : (F.filter fun m => Nat.gcd A m = g) ⊆ (Finset.Ico B C).filter (fun m => g ∣ m) := by
      intro m hm
      have h1 : m ∈ F := Finset.mem_of_mem_filter m hm
      have h2 : Nat.gcd A m = g := (Finset.mem_filter.1 hm).2
      refine Finset.mem_filter.2 ⟨Finset.mem_of_mem_filter m h1, ?_⟩
      rw [← h2]; exact Nat.gcd_dvd_right A m
    exact_mod_cast Finset.card_le_card hsub
  calc (F.card : ℝ) = ∑ g ∈ D, ((F.filter fun m => Nat.gcd A m = g).card : ℝ) := by
        exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hfib
    _ ≤ ∑ g ∈ D, (((C : ℝ) - B) / g + 1) := Finset.sum_le_sum hbound
