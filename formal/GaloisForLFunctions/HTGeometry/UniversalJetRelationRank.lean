import GaloisForLFunctions.HTGeometry.FreeJetTangentClosure
import GaloisForLFunctions.HTGeometry.DifferentialSolutionSpace

/-!
# A field of infinite rank over its constants admits no universal jet relation

A nonzero linear jet relation valid for *every* element of a differential field says that the whole
field solves one monic scalar linear differential equation, and the solution space of a monic
equation of order `n` carries at most `n` elements independent over the constants.  So the relation
is impossible as soon as the field contains arbitrarily large independent families.

* `InfiniteConstantRank`;
* `infiniteConstantRank_iff_and_noUniversalJetRelation`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable (C : Type*) [Field C] [Differential C]

/-- A differential field containing, for every `n`, a family of `n + 1` elements with no nontrivial
relation over the constants. -/
def InfiniteConstantRank : Prop :=
  ∀ n : ℕ, ∃ x : Fin (n + 1) → C,
    ∀ (t : Finset (Fin (n + 1))) (d : Fin (n + 1) → C), t.Nonempty →
      (∀ j ∈ t, (d j)′ = 0) → (∀ j ∈ t, d j ≠ 0) → ∑ j ∈ t, d j * x j ≠ 0

variable {C}

/-- **No universal linear jet relation on a field of infinite rank over its constants.** -/
private theorem noUniversalJetRelation_of_infiniteConstantRank
    (h : InfiniteConstantRank C) : NoUniversalJetRelation C := by
  classical
  intro s c hrel k hk
  by_contra hck
  set T : Finset ℕ := s.filter fun m => c m ≠ 0 with hT
  have hTne : T.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, hck⟩⟩
  set N : ℕ := T.max' hTne with hN
  have hNmem : N ∈ T := T.max'_mem hTne
  have hNs : N ∈ s := (Finset.mem_filter.mp hNmem).1
  have hcN : c N ≠ 0 := (Finset.mem_filter.mp hNmem).2
  set c' : ℕ → C := fun m => if m ∈ s then c m else 0 with hc'
  have hc'N : c' N = c N := by rw [hc']; exact if_pos hNs
  have hsum : ∀ y : C, ∑ m ∈ Finset.range (N + 1), c' m * differentialJet m y = 0 := by
    intro y
    have hR : ∑ m ∈ Finset.range (N + 1), c' m * differentialJet m y
        = ∑ m ∈ (Finset.range (N + 1)).filter (fun m => m ∈ s), c m * differentialJet m y := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hc', ite_mul, zero_mul]
    have hL : ∑ m ∈ s, c m * differentialJet m y
        = ∑ m ∈ s.filter (fun m => m ∈ Finset.range (N + 1)), c m * differentialJet m y := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) fun m hm hmn => ?_).symm
      have hnot : m ∉ Finset.range (N + 1) := by
        intro hcon; exact hmn (Finset.mem_filter.mpr ⟨hm, hcon⟩)
      have hgt : N < m := by
        rw [Finset.mem_range] at hnot; omega
      have hzero : c m = 0 := by
        by_contra hcm
        exact absurd (T.le_max' m (Finset.mem_filter.mpr ⟨hm, hcm⟩)) (by omega)
      rw [hzero, zero_mul]
    have hswap : s.filter (fun m => m ∈ Finset.range (N + 1))
        = (Finset.range (N + 1)).filter (fun m => m ∈ s) := by
      rw [Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
    rw [hR, ← hswap, ← hL]
    exact hrel y
  -- the monic scalar equation of order `N`
  set a : Fin N → C := fun i => -(c' (i : ℕ)) / c N with ha
  have hx : ∀ y : C, differentialJet N y = ∑ i : Fin N, a i * differentialJet (i : ℕ) y := by
    intro y
    have hsp := hsum y
    rw [Finset.sum_range_succ, hc'N] at hsp
    have hcast : ∑ i : Fin N, a i * differentialJet (i : ℕ) y
        = ∑ m ∈ Finset.range N, (-(c' m) / c N) * differentialJet m y := by
      rw [Fin.sum_univ_eq_sum_range (fun m => (-(c' m) / c N) * differentialJet m y) N]
    rw [hcast]
    have hfac : ∑ m ∈ Finset.range N, (-(c' m) / c N) * differentialJet m y
        = (-1 / c N) * ∑ m ∈ Finset.range N, c' m * differentialJet m y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      field_simp
    rw [hfac]
    have hval : ∑ m ∈ Finset.range N, c' m * differentialJet m y = -(c N * differentialJet N y) := by
      linear_combination hsp
    rw [hval]
    field_simp
  obtain ⟨y, hy⟩ := h N
  have hcard := card_le_of_no_constantRelation_scalar (K := C) a (x := y)
    (fun j => hx (y j)) hy
  simp only [Fintype.card_fin] at hcard
  omega

/-- **Exact rank absorption law.**  Infinite rank already contains the absence of every universal
linear jet relation, so adjoining that consequence leaves the rank predicate unchanged. -/
theorem infiniteConstantRank_iff_and_noUniversalJetRelation :
    InfiniteConstantRank C ↔ InfiniteConstantRank C ∧ NoUniversalJetRelation C := by
  constructor
  · intro h
    exact ⟨h, noUniversalJetRelation_of_infiniteConstantRank h⟩
  · exact And.left

end

end GaloisForLFunctions.HTGeometry
