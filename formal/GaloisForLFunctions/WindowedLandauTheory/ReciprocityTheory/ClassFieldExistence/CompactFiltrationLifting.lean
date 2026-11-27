import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Compactness.Compact

/-! Successive lifts modulo a separated filtration give an exact lift
when the source subgroup is compact. -/

open Topology

namespace GlobalTheory.Reciprocity

theorem compactSpace_units_of_compact {M : Type*} [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] [CompactSpace M] [T2Space M] : CompactSpace Mˣ := by
  let f : Mˣ → M × M := fun u => ((u : M), ((u⁻¹ : Mˣ) : M))
  have hf : IsEmbedding f :=
    ((Homeomorph.refl M).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp
      (Units.isEmbedding_embedProduct (M := M))
  refine ⟨hf.isCompact_iff.mpr ?_⟩
  rw [Set.image_univ]
  have he : Set.range f = {p : M × M | p.1 * p.2 = 1} := by
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact Units.mul_inv u
    · intro h
      exact ⟨⟨p.1, p.2, h, (mul_comm p.2 p.1).trans h⟩, Prod.ext rfl rfl⟩
  rw [he]
  exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).isCompact

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup H]

theorem map_eq_of_compact_filtration_lifts (F : ℕ → Subgroup G) (E : ℕ → Subgroup H)
    (f : G →* H) (hf : Continuous f) (k d : ℕ)
    (hF : Antitone F) (hE : Antitone E)
    (hK : IsCompact (F k : Set G)) (hc : ∀ j, IsClosed (E j : Set H))
    (hsep : ∀ y : H, (∀ j, y ∈ E j) → y = 1)
    (hmap : ∀ j ≥ k, (F j).map f ≤ E (j + d))
    (hlift : ∀ j ≥ k, ∀ y ∈ E (j + d), ∃ x ∈ F j, y / f x ∈ E (j + d + 1)) :
    (F k).map f = E (k + d) := by
  refine le_antisymm (hmap k le_rfl) ?_
  intro y hy
  let S (j : ℕ) := {x : G | x ∈ F k ∧ y / f x ∈ E (k + j + d)}
  have hne (j : ℕ) : (S j).Nonempty := by
    induction j with
    | zero =>
      exact ⟨1, one_mem _, by simpa using hy⟩
    | succ j ih =>
      obtain ⟨x, hx, hxy⟩ := ih
      obtain ⟨z, hz, hzr⟩ := hlift (k + j) (Nat.le_add_right _ _) (y / f x) hxy
      have he : y / f (z * x) = (y / f x) / f z := by
        simp only [map_mul, div_eq_mul_inv, mul_inv_rev, mul_assoc]
      refine ⟨z * x, mul_mem (hF (Nat.le_add_right _ _) hz) hx, ?_⟩
      simpa only [he, Nat.succ_eq_add_one, add_assoc, add_comm 1 d] using hzr
  have hdir : Directed (· ⊇ ·) S := fun i j => ⟨max i j,
    fun _ ⟨hx, hxy⟩ => ⟨hx, hE (by omega) hxy⟩,
    fun _ ⟨hx, hxy⟩ => ⟨hx, hE (by omega) hxy⟩⟩
  have hS (j : ℕ) : IsClosed {x : G | y / f x ∈ E (k + j + d)} :=
    (hc _).preimage (continuous_const.div' hf)
  have hne' : ∃ x ∈ F k, ∀ j, y / f x ∈ E (k + j + d) := by
    let T (j : ℕ) : Set ↥(F k) := {x | y / f (x : G) ∈ E (k + j + d)}
    letI : CompactSpace ↥(F k) := isCompact_iff_compactSpace.mp hK
    have hcl (j : ℕ) : IsClosed (T j) := by
      exact (hS j).preimage (continuous_subtype_val : Continuous (Subtype.val : ↥(F k) → G))
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      T (fun i j => by
        obtain ⟨l, hi, hj⟩ := hdir i j
        exact ⟨l, fun x h => (hi (show (x : G) ∈ S l from ⟨x.2, h⟩)).2,
          fun x h => (hj (show (x : G) ∈ S l from ⟨x.2, h⟩)).2⟩)
      (fun j => by obtain ⟨x, hx⟩ := hne j; exact ⟨⟨x, hx.1⟩, hx.2⟩)
      (fun j => (hcl j).isCompact) hcl
    exact ⟨x, x.2, fun j => Set.mem_iInter.mp hx j⟩
  obtain ⟨x, hx, hxy⟩ := hne'
  have he : y / f x = 1 := hsep _ fun j => hE (by omega) (hxy j)
  exact ⟨x, hx, (div_eq_one.mp he).symm⟩

end GlobalTheory.Reciprocity
