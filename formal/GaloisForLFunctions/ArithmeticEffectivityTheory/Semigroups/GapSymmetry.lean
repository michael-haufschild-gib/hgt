import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.GapDensity
import Mathlib.Data.Fintype.EquivFin

/-!
# Equality in the genus bound

Reflection about a gap is bijective exactly when membership and nonmembership
are complementary across that gap. At the largest gap, this characterizes
conductor equal to twice the genus. The equality case refines the finite
staircase counting mechanism for numerical semigroups.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns

/-- Every missing exponent below the reflection center has an allowed partner. -/
theorem reflection_surjective_iff (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) :
    Function.Surjective (reflectAllowedIntoGaps m k hK n hn) ↔
      ∀ i ≤ n, i ∈ carrier m k ↔ n - i ∉ carrier m k := by
  constructor
  · intro hs i hi
    constructor
    · intro hmem
      exact ((mem_gapsBelow m k (n + 1) _).mp
        (reflectAllowedIntoGaps m k hK n hn
          ⟨i, (mem_allowedBelow m k (n + 1) i).mpr ⟨by omega, hmem⟩⟩).property).2
    · intro hgap
      obtain ⟨a, ha⟩ := hs
        ⟨n - i, (mem_gapsBelow m k (n + 1) _).mpr ⟨by omega, hgap⟩⟩
      have ha' := (mem_allowedBelow m k (n + 1) a.val).mp a.property
      have he : n - a.val = n - i := congrArg Subtype.val ha
      have hai : a.val = i := by omega
      exact hai ▸ ha'.2
  · intro hs j
    have hj := (mem_gapsBelow m k (n + 1) j.val).mp j.property
    have hcancel : n - (n - j.val) = j.val := by omega
    have ha : n - j.val ∈ carrier m k :=
      (hs (n - j.val) (by omega)).mpr (by simpa only [hcancel] using hj.2)
    refine ⟨⟨n - j.val, (mem_allowedBelow m k (n + 1) _).mpr ⟨by omega, ha⟩⟩, ?_⟩
    apply Subtype.ext
    exact hcancel

/-- A gap prefix has exactly half gaps precisely when reflection exchanges gaps and allowed exponents. -/
theorem gap_prefix_equality_iff (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) :
    n + 1 = 2 * (gapsBelow m k (n + 1)).card ↔
      ∀ i ≤ n, i ∈ carrier m k ↔ n - i ∉ carrier m k := by
  have hi := reflectAllowedIntoGaps_injective m k hK n hn
  have hp := prefix_partition m k (n + 1)
  rw [← reflection_surjective_iff m k hK n hn]
  constructor
  · intro he
    have hc : Fintype.card (allowedBelow m k (n + 1)) =
        Fintype.card (gapsBelow m k (n + 1)) := by
      simp only [Fintype.card_coe]
      omega
    exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, hc⟩).2
  · intro hs
    have hc := ((Fintype.bijective_iff_injective_and_card _).mp ⟨hi, hs⟩).2
    simp only [Fintype.card_coe] at hc
    omega

/-- Equality in the global genus bound identifies both the last gap and its reflection symmetry. -/
theorem conductor_equality_iff (m : ℕ) (k : ℕ → ℕ) (hK : Kunz m k)
    (n : ℕ) (hn : n ∉ carrier m k) :
    n + 1 = 2 * genus m k ↔
      (∀ j, j ∉ carrier m k → j ≤ n) ∧
      (∀ i ≤ n, i ∈ carrier m k ↔ n - i ∉ carrier m k) := by
  constructor
  · intro he
    have hlast : ∀ j, j ∉ carrier m k → j < n + 1 := by
      intro j hj
      rw [he]
      exact gap_lt_two_genus m k hK j hj
    have hc := prefix_count_of_all_gaps_lt m k (n + 1) hlast
    have hp := prefix_partition m k (n + 1)
    refine ⟨fun j hj => by have := hlast j hj; omega, ?_⟩
    apply (gap_prefix_equality_iff m k hK n hn).mp
    omega
  · rintro ⟨hlast, hsym⟩
    have he := (gap_prefix_equality_iff m k hK n hn).mpr hsym
    have hc := prefix_count_of_all_gaps_lt m k (n + 1)
      (fun j hj => by have := hlast j hj; omega)
    have hp := prefix_partition m k (n + 1)
    omega

#print axioms reflection_surjective_iff
#print axioms gap_prefix_equality_iff
#print axioms conductor_equality_iff

end GaloisForLFunctions.ArithmeticEffectivityTheory.ResidueColumns
