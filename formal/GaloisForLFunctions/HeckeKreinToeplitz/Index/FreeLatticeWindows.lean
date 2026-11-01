import GaloisForLFunctions.ArithmeticPositiveDuality.HerglotzBochnerOnLattices
import Mathlib.Data.Finsupp.Basic

/-!
# Expanding windows in a countable free lattice

A coordinate box has exact Fejér pair counts. Its coefficient at a fixed
frequency eventually depends only on that frequency’s support, so tends to one
as both the coordinate set and box size grow.
-/

open Finset
open scoped Classical
open GaloisForLFunctions.ArithmeticPositiveDuality

namespace GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

variable {I : Type*}

/-- A finite coordinate box, embedded by zero outside its coordinate set. -/
def freeLatticeWindow (F : Finset I) (N : ℕ) (j : F → Fin (N + 1)) : I →₀ ℤ :=
  Finsupp.embDomain (.subtype (fun i => i ∈ F))
    (Finsupp.equivFunOnFinite.symm (windowPt N j))

theorem freeLatticeWindow_apply_mem (F : Finset I) (N : ℕ)
    (j : F → Fin (N + 1)) (i : F) :
    freeLatticeWindow F N j i = ((j i : ℕ) : ℤ) := by
  exact Finsupp.embDomain_apply_self _ _ i

theorem freeLatticeWindow_apply_notMem (F : Finset I) (N : ℕ)
    (j : F → Fin (N + 1)) {i : I} (hi : i ∉ F) :
    freeLatticeWindow F N j i = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨p, hp⟩
  exact hi (hp ▸ p.2)

theorem freeLatticeWindow_injective (F : Finset I) (N : ℕ) :
    Function.Injective (freeLatticeWindow F N) := by
  intro j k h
  funext i
  apply Fin.ext
  have he := congrArg (fun f : I →₀ ℤ => f i) h
  simp only [freeLatticeWindow_apply_mem] at he
  exact_mod_cast he

theorem freeLatticeWindow_sub_eq_iff (F : Finset I) (N : ℕ)
    (j k : F → Fin (N + 1)) {t : I →₀ ℤ} (ht : t.support ⊆ F) :
    freeLatticeWindow F N k - freeLatticeWindow F N j = t ↔
      windowPt N k - windowPt N j = fun p : F => t p := by
  classical
  constructor
  · intro h
    funext p
    have he := congrArg (fun f : I →₀ ℤ => f p) h
    simpa only [Finsupp.sub_apply, freeLatticeWindow_apply_mem, Pi.sub_apply, windowPt] using he
  · intro h
    ext i
    by_cases hi : i ∈ F
    · have he := congrFun h ⟨i, hi⟩
      rw [Finsupp.sub_apply, freeLatticeWindow_apply_mem F N k ⟨i, hi⟩,
        freeLatticeWindow_apply_mem F N j ⟨i, hi⟩]
      simpa only [Pi.sub_apply, windowPt] using he
    · have ht0 : t i = 0 := Finsupp.notMem_support_iff.mp (fun hmem => hi (ht hmem))
      simp only [Finsupp.sub_apply, freeLatticeWindow_apply_notMem F N k hi,
        freeLatticeWindow_apply_notMem F N j hi, ht0, sub_self]

/-- Pair counts in a free-lattice box are the finite-rank Fejér pair counts. -/
theorem sum_freeLatticeWindow_pairs (F : Finset I) (N : ℕ)
    {t : I →₀ ℤ} (ht : t.support ⊆ F) :
    (∑ j : F → Fin (N + 1), ∑ k : F → Fin (N + 1),
      if freeLatticeWindow F N k - freeLatticeWindow F N j = t then (1 : ℂ) else 0) =
      ∏ p : F, (GaloisForLFunctions.HTGeometry.Bochner.pairCount N (t p) : ℂ) := by
  classical
  simp_rw [freeLatticeWindow_sub_eq_iff F N _ _ ht]
  exact sum_window_pairs N (fun p : F => t p)


open Filter Topology

/-- Zero coordinates contribute unit factors to a Fejér weight. -/
theorem fejerWeight_restrict_freeSupport (F : Finset I) (N : ℕ)
    (t : I →₀ ℤ) (ht : t.support ⊆ F) :
    fejerWeight N (fun p : F => t p) =
      fejerWeight N (fun p : t.support => t p) := by
  classical
  let f : I → ℝ := fun i =>
    (GaloisForLFunctions.HTGeometry.Bochner.pairCount N (t i) : ℝ) / ((N : ℝ) + 1)
  calc
    fejerWeight N (fun p : F => t p) = ∏ i ∈ F, f i := prod_coe_sort F f
    _ = ∏ i ∈ t.support, f i := by
      symm
      apply prod_subset ht
      intro i _ hi
      dsimp only [f]
      rw [Finsupp.notMem_support_iff.mp hi,
        GaloisForLFunctions.HTGeometry.Bochner.pairCount_zero]
      push_cast
      exact div_self (by positivity)
    _ = fejerWeight N (fun p : t.support => t p) := (prod_coe_sort t.support f).symm

/-- The coefficient weight of a box is zero outside its coordinate span. -/
def freeLatticeFejerWeight (F : Finset I) (N : ℕ) (t : I →₀ ℤ) : ℝ := by
  classical
  exact if t.support ⊆ F then fejerWeight N (fun p : t.support => t p) else 0

theorem normalized_freeLatticeWindow_pairs (F : Finset I) (N : ℕ) (t : I →₀ ℤ) :
    (∑ j : F → Fin (N + 1), ∑ k : F → Fin (N + 1),
      if freeLatticeWindow F N k - freeLatticeWindow F N j = t then (1 : ℂ) else 0) /
        Fintype.card (F → Fin (N + 1)) = (freeLatticeFejerWeight F N t : ℂ) := by
  classical
  by_cases ht : t.support ⊆ F
  · rw [freeLatticeFejerWeight, if_pos ht, sum_freeLatticeWindow_pairs F N ht,
      ← fejerWeight_restrict_freeSupport F N t ht]
    unfold fejerWeight
    push_cast
    rw [prod_div_distrib, prod_const, card_univ]
    simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  · have hne (j k : F → Fin (N + 1)) :
        freeLatticeWindow F N k - freeLatticeWindow F N j ≠ t := by
      intro heq
      apply ht
      intro i hi
      by_contra hif
      have he := congrArg (fun a : I →₀ ℤ => a i) heq
      simp only [Finsupp.sub_apply, freeLatticeWindow_apply_notMem F N k hif,
        freeLatticeWindow_apply_notMem F N j hif, sub_self] at he
      exact Finsupp.mem_support_iff.mp hi he.symm
    simp only [hne, if_false, sum_const_zero, zero_div, freeLatticeFejerWeight,
      if_neg ht, Complex.ofReal_zero]

/-- Every fixed frequency sees asymptotically full weight along expanding
coordinate sets and expanding boxes. -/
theorem tendsto_freeLatticeFejerWeight (t : I →₀ ℤ) :
    Tendsto (fun a : Finset I × ℕ => freeLatticeFejerWeight a.1 a.2 t)
      (atTop ×ˢ atTop) (𝓝 1) := by
  classical
  have h := (tendsto_fejerWeight (fun p : t.support => t p)).comp
    (tendsto_snd : Tendsto (Prod.snd : Finset I × ℕ → ℕ) (atTop ×ˢ atTop) atTop)
  apply h.congr'
  have hF : ∀ᶠ a : Finset I × ℕ in atTop ×ˢ atTop, t.support ⊆ a.1 :=
    tendsto_fst.eventually (eventually_ge_atTop t.support)
  filter_upwards [hF] with a ha
  simp only [Function.comp_apply, freeLatticeFejerWeight, if_pos ha]

/-- Enumerate a coordinate box by a single finite index type. -/
def freeLatticeFinWindow (F : Finset I) (N : ℕ) :
    Fin (Fintype.card (F → Fin (N + 1))) → I →₀ ℤ :=
  freeLatticeWindow F N ∘ (Fintype.equivFin (F → Fin (N + 1))).symm

theorem freeLatticeFinWindow_injective (F : Finset I) (N : ℕ) :
    Function.Injective (freeLatticeFinWindow F N) :=
  (freeLatticeWindow_injective F N).comp (Fintype.equivFin _).symm.injective

theorem freeLatticeWindow_card_pos (F : Finset I) (N : ℕ) :
    0 < Fintype.card (F → Fin (N + 1)) := Fintype.card_pos

/-- Enumeration leaves the normalized pair count unchanged. -/
theorem normalized_freeLatticeFinWindow_pairs (F : Finset I) (N : ℕ) (t : I →₀ ℤ) :
    (∑ j, ∑ k, if freeLatticeFinWindow F N k - freeLatticeFinWindow F N j = t
      then (1 : ℂ) else 0) / Fintype.card (F → Fin (N + 1)) =
      (freeLatticeFejerWeight F N t : ℂ) := by
  classical
  let e : Fin (Fintype.card (F → Fin (N + 1))) ≃ (F → Fin (N + 1)) :=
    (Fintype.equivFin (F → Fin (N + 1))).symm
  change (∑ j, ∑ k, if freeLatticeWindow F N (e k) - freeLatticeWindow F N (e j) = t
    then (1 : ℂ) else 0) / _ = _
  have hs (j : F → Fin (N + 1)) :
      (∑ k, if freeLatticeWindow F N (e k) - freeLatticeWindow F N j = t
        then (1 : ℂ) else 0) =
      ∑ k : F → Fin (N + 1), if freeLatticeWindow F N k - freeLatticeWindow F N j = t
        then (1 : ℂ) else 0 :=
    e.sum_comp (fun k : F → Fin (N + 1) =>
      if freeLatticeWindow F N k - freeLatticeWindow F N j = t then (1 : ℂ) else 0)
  simp_rw [hs]
  rw [e.sum_comp (fun j : F → Fin (N + 1) =>
    ∑ k : F → Fin (N + 1),
      if freeLatticeWindow F N k - freeLatticeWindow F N j = t then (1 : ℂ) else 0)]
  exact normalized_freeLatticeWindow_pairs F N t

end

end GaloisForLFunctions.HeckeKreinToeplitz
