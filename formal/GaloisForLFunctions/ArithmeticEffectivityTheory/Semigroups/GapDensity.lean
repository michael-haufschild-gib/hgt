import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ResidueColumns

/-!
# The genus bounds every additive-column gap

Reflection about a missing exponent sends every allowed exponent below it
injectively into the gaps. The missing exponent is therefore strictly less
than twice the genus. This is the counting mechanism behind the staircase
bound in Raja--Rashid, arXiv:2611.20832, Theorem 7.2.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns

/-- Allowed exponents strictly below a cutoff. -/
def allowedBelow (m : ℕ) (k : ℕ → ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (· ∈ carrier m k)

/-- Missing exponents strictly below a cutoff. -/
def gapsBelow (m : ℕ) (k : ℕ → ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (· ∉ carrier m k)

theorem mem_allowedBelow (m : ℕ) (k : ℕ → ℕ) (N i : ℕ) :
    i ∈ allowedBelow m k N ↔ i < N ∧ i ∈ carrier m k := by
  simp only [allowedBelow, Finset.mem_filter, Finset.mem_range]

theorem mem_gapsBelow (m : ℕ) (k : ℕ → ℕ) (N i : ℕ) :
    i ∈ gapsBelow m k N ↔ i < N ∧ i ∉ carrier m k := by
  simp only [gapsBelow, Finset.mem_filter, Finset.mem_range]

/-- Reflection about a gap sends allowed exponents to missing exponents. -/
def reflectAllowedIntoGaps (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) :
    allowedBelow m k (n + 1) → gapsBelow m k (n + 1) := fun i =>
  ⟨n - i.val, (mem_gapsBelow m k (n + 1) _).mpr ⟨by omega, by
    intro hi
    have hmem := (mem_allowedBelow m k (n + 1) i.val).mp i.property
    have hsum := (add_closed_iff m k).mpr hK _ hi _ hmem.2
    rw [Nat.sub_add_cancel (by omega : i.val ≤ n)] at hsum
    exact hn hsum⟩⟩

theorem reflectAllowedIntoGaps_injective (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) :
    Function.Injective (reflectAllowedIntoGaps m k hK n hn) := by
  intro i j hij
  apply Subtype.ext
  have hi := ((mem_allowedBelow m k (n + 1) i.val).mp i.property).1
  have hj := ((mem_allowedBelow m k (n + 1) j.val).mp j.property).1
  have he : n - i.val = n - j.val := congrArg Subtype.val hij
  omega

/-- A gap injects its preceding allowed exponents into gaps in the same interval. -/
theorem allowedBelow_card_le_gapsBelow_of_gap (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) :
    (allowedBelow m k (n + 1)).card ≤ (gapsBelow m k (n + 1)).card := by
  have h := Fintype.card_le_of_injective (reflectAllowedIntoGaps m k hK n hn)
    (reflectAllowedIntoGaps_injective m k hK n hn)
  simpa only [Fintype.card_coe] using h

theorem gapsBelow_card_le_genus (m : ℕ) (k : ℕ → ℕ) (N : ℕ) :
    (gapsBelow m k N).card ≤ genus m k := by
  have h := Fintype.card_le_of_injective
    (fun i : gapsBelow m k N => (⟨i.val, ((mem_gapsBelow m k N i.val).mp i.property).2⟩ :
      {j : ℕ // j ∉ carrier m k}))
    (fun i j h => Subtype.ext
      (congrArg (fun x : {j : ℕ // j ∉ carrier m k} => x.val) h))
  simpa only [Fintype.card_coe, card_gaps] using h

theorem prefix_partition (m : ℕ) (k : ℕ → ℕ) (N : ℕ) :
    (allowedBelow m k N).card + (gapsBelow m k N).card = N := by
  classical
  simpa only [allowedBelow, gapsBelow, Finset.card_range] using
    (Finset.card_filter_add_card_filter_not (s := Finset.range N) (· ∈ carrier m k))

/-- Every prefix ending in a gap contains at least as many gaps as allowed exponents. -/
theorem gap_prefix_density (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) :
    n + 1 ≤ 2 * (gapsBelow m k (n + 1)).card := by
  have ha := allowedBelow_card_le_gapsBelow_of_gap m k hK n hn
  have hp := prefix_partition m k (n + 1)
  omega

/-- Every gap of additively closed residue columns lies strictly below twice their genus. -/
theorem gap_lt_two_genus (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) : n < 2 * genus m k := by
  have ha := gap_prefix_density m k hK n hn
  have hg := gapsBelow_card_le_genus m k (n + 1)
  omega

/-- The conductor bound is independent of the chosen residue period. -/
theorem mem_of_two_genus_le (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    {n : ℕ} (hn : 2 * genus m k ≤ n) : n ∈ carrier m k := by
  by_contra h
  exact (not_lt_of_ge hn) (gap_lt_two_genus m k hK n h)

/-- Once all gaps precede the cutoff, the prefix deficit equals the genus exactly. -/
theorem prefix_count_of_all_gaps_lt (m : ℕ) (k : ℕ → ℕ) (N : ℕ)
    (hN : ∀ n, n ∉ carrier m k → n < N) :
    (allowedBelow m k N).card + genus m k = N := by
  have hg : genus m k ≤ (gapsBelow m k N).card := by
    have h := Fintype.card_le_of_injective
      (fun i : {j : ℕ // j ∉ carrier m k} =>
        (⟨i.val, (mem_gapsBelow m k N i.val).mpr ⟨hN i.val i.property, i.property⟩⟩ :
          gapsBelow m k N))
      (fun i j h => Subtype.ext
        (congrArg (fun x : gapsBelow m k N => x.val) h))
    simpa only [Fintype.card_coe, card_gaps] using h
  rw [← Nat.le_antisymm (gapsBelow_card_le_genus m k N) hg]
  exact prefix_partition m k N

/-- Past twice the genus, the allowed-exponent count is affine with the exact gap deficit. -/
theorem prefix_count_of_two_genus_le (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    {N : ℕ} (hN : 2 * genus m k ≤ N) :
    (allowedBelow m k N).card + genus m k = N := by
  apply prefix_count_of_all_gaps_lt
  intro n hn
  exact (gap_lt_two_genus m k hK n hn).trans_le hN

#print axioms gap_prefix_density
#print axioms gap_lt_two_genus
#print axioms mem_of_two_genus_le
#print axioms prefix_count_of_two_genus_le

end GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns
