import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardInclude

/-!
# Translation invariance of Grynkiewicz's theorem

Replacing `B` by a translate `x · B` translates every `i`-representable set by `x` and leaves
`repSum`, the stabiliser, the defect and the hole count unchanged.  Consequently both
alternatives of Grynkiewicz's theorem, and hence `PollardConclusion`, are translation invariant.
This is what allows the Dyson witness to be normalised to `x = 1`, where
`dysonSmall A B 1 = A ∩ B` and `dysonLarge A B 1 = A ∪ B`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

omit [Fintype G] in
theorem mem_smul_finset_iff {s : Finset G} {x a : G} : a ∈ x • s ↔ x⁻¹ * a ∈ s := by
  rw [Finset.mem_smul_finset]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [smul_eq_mul] using hy
  · intro h
    exact ⟨x⁻¹ * a, h, by simp [smul_eq_mul, mul_inv_cancel_left]⟩

omit [Fintype G] in
theorem rep_smul_right (A B : Finset G) (x c : G) : rep A (x • B) c = rep A B (x⁻¹ * c) := by
  classical
  rw [rep_eq_card_inter, rep_eq_card_inter]
  congr 1
  ext z
  simp only [Finset.mem_inter, mem_smul_finset_iff, Finset.mem_inv']
  have harg : x⁻¹ * (c⁻¹ * z)⁻¹ = ((x⁻¹ * c)⁻¹ * z)⁻¹ := by
    simp only [mul_inv_rev, inv_inv]
    rw [mul_comm x⁻¹ (z⁻¹ * c), mul_assoc, mul_comm c x⁻¹]
  rw [harg]

theorem repSet_smul_right (A B : Finset G) (x : G) (i : ℕ) :
    repSet A (x • B) i = x • repSet A B i := by
  ext c
  rw [mem_repSet, rep_smul_right, mem_smul_finset_iff, mem_repSet]

theorem repSum_smul_right (A B : Finset G) (x : G) (t : ℕ) :
    repSum A (x • B) t = repSum A B t := by
  rw [repSum, repSum]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [repSet_smul_right, Finset.card_smul_finset])

omit [Fintype G] in
theorem smul_finset_sdiff (x : G) (s u : Finset G) : x • (s \ u) = (x • s) \ (x • u) := by
  ext z
  simp only [mem_smul_finset_iff, Finset.mem_sdiff]

theorem pollardWeak_smul_right {A B : Finset G} {t : ℕ} (x : G)
    (h : PollardWeak A B t) : PollardWeak A (x • B) t := by
  rw [PollardWeak] at h ⊢
  rwa [Finset.card_smul_finset, repSum_smul_right]

theorem pollardStruct_smul_right {A B : Finset G} {t : ℕ} (x : G)
    (h : PollardStruct A B t) : PollardStruct A (x • B) t := by
  classical
  obtain ⟨A', B', hA', hB', hdef, h1, h2, h3⟩ := h
  have hmul : ∀ S : Finset G, A' * (x • S) = x • (A' * S) := by
    intro S
    rw [mul_smul_comm]
  have hdefeq : defect A A' (x • B) (x • B') = defect A A' B B' := by
    rw [defect, defect, ← smul_finset_sdiff, Finset.card_smul_finset]
  have hstab : mulStab (repSet A (x • B) t) = mulStab (repSet A B t) := by
    rw [repSet_smul_right, mulStab_smul]
  have hprod : A' * (x • B') = repSet A (x • B) t := by
    rw [hmul, h2, repSet_smul_right]
  refine ⟨A', x • B', hA', Finset.smul_finset_subset_smul_finset hB', by rw [hdefeq]; exact hdef,
    ?_, hprod, ?_⟩
  · rw [repSet_smul_right, h1, hmul]
  · have hholes : holes (mulStab (repSet A (x • B) t)) A' (x • B')
        = holes (mulStab (repSet A B t)) A' B' := by
      rw [hstab, holes, holes, smul_mul_assoc, ← smul_finset_sdiff, Finset.card_smul_finset]
    rw [hholes, hdefeq, hstab, Finset.card_smul_finset, repSum_smul_right]
    exact h3

theorem pollardConclusion_smul_right {A B : Finset G} {t : ℕ} (x : G)
    (h : PollardConclusion A B t) : PollardConclusion A (x • B) t :=
  h.imp (pollardWeak_smul_right x) (pollardStruct_smul_right x)

theorem pollardConclusion_of_smul_right {A B : Finset G} {t : ℕ} {x : G}
    (h : PollardConclusion A (x • B) t) : PollardConclusion A B t := by
  have := pollardConclusion_smul_right x⁻¹ h
  rwa [inv_smul_smul] at this

end GaloisForLFunctions.HTGeometry.AddComb
