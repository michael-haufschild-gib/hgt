/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
import Mathlib.Topology.Subpath

/-!
# Loop decomposition subordinate to an open cover

Project-local adaptation of the path-factorization half of van Kampen's theorem. If an open cover
has path-connected pairwise intersections and every cover member contains the basepoint, every
based loop is homotopic to a finite concatenation of loops, each lying in one cover member.

The proof follows Hatcher, Lemma 1.15, and Sebastian Kumar's mathlib contribution #28246.
-/

open Fin Set unitInterval

namespace GaloisForLFunctions.HTGeometry

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v}
  {c : ι → Set X} {a : X}

/-- Pull an open cover back along a loop and extract a finite interval partition subordinate to it. -/
theorem exists_path_partition_unitInterval_of_open_cover
    (hcOpen : ∀ i, IsOpen (c i)) (hcCover : Set.univ ⊆ ⋃ i, c i)
    (γ : Path a a) :
    ∃ (n : ℕ) (t : Fin (n + 2) → unitInterval),
      t 0 = 0 ∧ t (last (n + 1)) = 1 ∧
        ∀ k : Fin (n + 1), ∃ i,
          γ '' uIcc (t k.castSucc) (t k.succ) ⊆ c i := by
  have ⟨t, htZero, htMono, ⟨n, htOne⟩, htSub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i ↦ IsOpen.preimage γ.continuous (hcOpen i))
      (fun s _ ↦ (preimage_iUnion ▸ hcCover (mem_univ _)))
  use n, t ∘ Fin.toNat
  suffices ∀ k : Fin (n + 1),
      ∃ i, uIcc (t ↑k) (t (↑k + 1)) ⊆ ⇑γ ⁻¹' c i by
    simpa [htZero, htOne]
  intro k
  obtain ⟨i, hi⟩ := htSub k
  use i
  rwa [uIcc_of_le (htMono (Nat.le_add_right _ _))]

/-- Connect every partition switch point back to the common basepoint inside the corresponding
pairwise cover intersection. -/
theorem exists_path_range_of_isPathConnected_inter
    (hcInter : ∀ i j, IsPathConnected (c i ∩ c j))
    (ha : ∀ i, a ∈ c i) {n : ℕ} (τ : Fin (n + 1) → ι)
    (p : Fin (n + 2) → X)
    (hLeft : ∀ k, p k.castSucc ∈ c (τ k))
    (hRight : ∀ k, p k.succ ∈ c (τ k)) :
    ∀ k : Fin n, ∃ g : Path a (p k.succ.castSucc),
      Set.range g ⊆ c (τ k.castSucc) ∩ c (τ k.succ) := by
  intro k
  obtain ⟨γ, hγ⟩ := (hcInter (τ k.castSucc) (τ k.succ)).joinedIn
    a ⟨ha (τ k.castSucc), ha (τ k.succ)⟩
      (p k.castSucc.succ) ⟨hRight k.castSucc, hLeft k.succ⟩
  exact ⟨γ, Set.range_subset_iff.mpr hγ⟩

/-- Cancelling connector paths rewrites the concatenation of conjugated path pieces as the
original concatenation, up to endpoint-fixed homotopy. -/
theorem concat_trans_trans_symm_homotopic {n : ℕ}
    (p q : Fin (n + 1) → X)
    (F : ∀ k : Fin n, Path (p k.castSucc) (p k.succ))
    (G : ∀ k : Fin (n + 1), Path (q k) (p k)) :
    (Path.concat q (fun k ↦
      (G k.castSucc).trans ((F k).trans (G k.succ).symm))).Homotopic
      ((G 0).trans ((Path.concat p F).trans (G (last n)).symm)) := by
  induction n with
  | zero =>
      simp only [Path.concat_zero, ← FundamentalGroupoid.fromPath_eq_iff_homotopic]
      aesop_cat
  | succ n hn =>
      have h := Path.Homotopic.Quotient.eq.mpr
        (hn (p ∘ castSucc) (q ∘ castSucc)
          (fun k ↦ F k.castSucc) (fun k ↦ G k.castSucc))
      simp at h
      refine Quotient.exact (s := Path.Homotopic.setoid _ _) ?_
      simp only [Path.concat_succ, Function.comp_apply, castSucc_zero, succ_last,
        Nat.succ_eq_add_one, Path.Homotopic.Quotient.mk_trans, h,
        Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.mk_symm]
      grind

private theorem cast_trans_trans_homotopic_of_homotopic_cast
    {x x₀ x₁ : X} {h₀ : x₀ = x} {h₁ : x₁ = x}
    {p : Path x₀ x₁} {q : Path x x}
    (h : p.Homotopic (q.cast h₀ h₁)) :
    ((Path.refl x).cast rfl h₀ |>.trans
      (p.trans ((Path.refl x).cast h₁ rfl))).Homotopic q := by
  subst_vars
  exact Path.Homotopic.trans
    (Path.Homotopic.trans ⟨Path.Homotopy.reflTrans _⟩
      ⟨Path.Homotopy.transRefl _⟩) h

/-- Any based loop subordinate to an open cover with path-connected pairwise intersections is
homotopic to a finite concatenation of based loops, each contained in one cover member. -/
theorem exists_loops_homotopic_concat_of_open_cover
    (hcOpen : ∀ i, IsOpen (c i)) (hcCover : Set.univ ⊆ ⋃ i, c i)
    (hcInter : ∀ i j, IsPathConnected (c i ∩ c j))
    (ha : ∀ i, a ∈ c i) (γ : Path a a) :
    ∃ (n : ℕ) (D : Fin (n + 1) → Path a a),
      (Path.concat (fun _ ↦ a) D).Homotopic γ ∧
        ∀ k, ∃ i : ι, Set.range (D k) ⊆ c i := by
  obtain ⟨n, t, htZero, htOne, htRange⟩ :=
    exists_path_partition_unitInterval_of_open_cover hcOpen hcCover γ
  choose τ hτ using htRange
  have hConnect := exists_path_range_of_isPathConnected_inter hcInter ha τ (γ ∘ t)
    (fun k ↦ hτ k (mem_image_of_mem γ left_mem_uIcc))
    (fun k ↦ hτ k (mem_image_of_mem γ right_mem_uIcc))
  choose G hG using hConnect
  let G' := snoc (α := fun k ↦ Path a (γ (t k)))
    (cons (α := fun k ↦ Path a (γ (t k.castSucc)))
      ((Path.refl a).cast rfl (htZero ▸ γ.source)) G)
    ((Path.refl a).cast rfl (htOne ▸ γ.target))
  have hG'Zero : G' 0 = (Path.refl a).cast rfl (htZero ▸ γ.source) :=
    (snoc_apply_zero _ _).trans (cons_zero _ _)
  have hG'One : G' (last (n + 1)) =
      (Path.refl a).cast rfl (htOne ▸ γ.target) :=
    snoc_last _ _
  have hG'RangeLeft k : Set.range (G' k.castSucc) ⊆ c (τ k) := by
    unfold G'
    rw [snoc_castSucc]
    cases k using Fin.cases with
    | zero =>
        rw [cons_zero, Path.cast_coe, Path.refl_range, singleton_subset_iff]
        exact ha _
    | succ j => exact (subset_inter_iff.mp (hG j)).right
  have hG'RangeRight k : Set.range (G' k.succ) ⊆ c (τ k) := by
    unfold G'
    cases k using Fin.lastCases with
    | cast =>
        rw [succ_castSucc, snoc_castSucc]
        exact (subset_inter_iff.mp (hG _)).left
    | last =>
        rw [succ_last, snoc_last, Path.cast_coe, Path.refl_range,
          singleton_subset_iff]
        exact ha _
  use n, fun k ↦
    (G' k.castSucc).trans
      ((γ.subpath (t k.castSucc) (t k.succ)).trans (G' k.succ).symm)
  constructor
  · apply Path.Homotopic.trans (concat_trans_trans_symm_homotopic _ _ _ _)
    rw [hG'Zero, hG'One, ← Path.cast_symm, Path.refl_symm]
    refine cast_trans_trans_homotopic_of_homotopic_cast
      (Path.Homotopic.trans ⟨Path.Homotopy.concatSubpath γ t⟩ ?_)
    rw! (castMode := .all) [htZero, htOne, Path.subpath_zero_one]
    rfl
  · intro k
    use τ k
    grind [Path.trans_range, Path.symm_range, union_subset, Path.range_subpath]

end GaloisForLFunctions.HTGeometry
