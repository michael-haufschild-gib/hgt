/-
# Gap-thin sets of integers

A set `S ⊆ ℤ` is *gap thin* when, beyond some threshold, any `m + 1` of its elements are spread out:
`α * t₀ ^ q < (t_m - t₀) ^ E`.  With `m = 0` this forces `S` to be bounded above; with `m ≥ 1` it is
exactly the conclusion of the divided-difference gap estimate.

The point of the notion is `infinite_compl_of_thin`: finitely many gap-thin sets cannot cover the
integers, because a window of `r * M + 1` consecutive integers placed far enough out meets each of
the `r` sets in at most `M` points.

This is the combinatorial skeleton of steps 4 and 5 of Coleman--Zwald's proof of Hilbert's
irreducibility theorem.
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Positivity

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Finset

/-- `S` is **gap thin**: past a threshold, any `m + 1` members are spread by `α * t₀ ^ q`. -/
def Thin (S : Set ℤ) : Prop :=
  ∃ (m q E : ℕ) (T α : ℝ), 0 < α ∧ 0 < q ∧ 0 < E ∧
    ∀ t : Fin (m + 1) → ℤ, StrictMono t → (∀ i, T < (t i : ℝ)) → (∀ i, t i ∈ S) →
      α * (t 0 : ℝ) ^ q < ((t (Fin.last m) : ℝ) - (t 0 : ℝ)) ^ E

/-- A set bounded above is gap thin: the hypothesis of the spread condition is never met. -/
theorem thin_of_bddAbove {S : Set ℤ} {T : ℝ} (h : ∀ n ∈ S, (n : ℝ) ≤ T) : Thin S :=
  ⟨0, 1, 1, T, 1, one_pos, one_pos, one_pos, fun t _ hT hS =>
    absurd (h (t 0) (hS 0)) (not_le.mpr (hT 0))⟩

/-- A gap-thin set meets a short far-out window in at most `m` points. -/
theorem card_filter_le_of_thin {S : Set ℤ} [DecidablePred (· ∈ S)] {m q E : ℕ} {T α : ℝ}
    (hα : 0 < α)
    (hthin : ∀ t : Fin (m + 1) → ℤ, StrictMono t → (∀ i, T < (t i : ℝ)) → (∀ i, t i ∈ S) →
      α * (t 0 : ℝ) ^ q < ((t (Fin.last m) : ℝ) - (t 0 : ℝ)) ^ E)
    {X : Finset ℤ} {U W : ℝ} (hU : 0 < U) (hTU : T < U)
    (hX : ∀ n ∈ X, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ U + W) (hW : W ^ E ≤ α * U ^ q) :
    (X.filter (· ∈ S)).card ≤ m := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcon)
  set e : Fin (m + 1) ↪o ℤ := B.orderEmbOfFin hBcard with he
  have hmem : ∀ i : Fin (m + 1), e i ∈ X.filter (· ∈ S) := fun i =>
    hBsub (by rw [he]; exact B.orderEmbOfFin_mem hBcard i)
  have hS : ∀ i, e i ∈ S := fun i => (Finset.mem_filter.mp (hmem i)).2
  have hXi : ∀ i, U ≤ ((e i : ℤ) : ℝ) ∧ ((e i : ℤ) : ℝ) ≤ U + W := fun i =>
    hX _ (Finset.mem_filter.mp (hmem i)).1
  have hT : ∀ i, T < ((e i : ℤ) : ℝ) := fun i => lt_of_lt_of_le hTU (hXi i).1
  have hkey := hthin (fun i => e i) (fun i j hij => e.strictMono hij) hT hS
  have h1 : ((e (Fin.last m) : ℤ) : ℝ) - ((e 0 : ℤ) : ℝ) ≤ W := by
    have h2 := (hXi (Fin.last m)).2
    have h3 := (hXi 0).1
    linarith
  have h1' : (0 : ℝ) ≤ ((e (Fin.last m) : ℤ) : ℝ) - ((e 0 : ℤ) : ℝ) := by
    have h : (e 0 : ℤ) ≤ e (Fin.last m) := e.monotone (Fin.zero_le _)
    have : ((e 0 : ℤ) : ℝ) ≤ ((e (Fin.last m) : ℤ) : ℝ) := by exact_mod_cast h
    linarith
  have hpow : (((e (Fin.last m) : ℤ) : ℝ) - ((e 0 : ℤ) : ℝ)) ^ E ≤ W ^ E :=
    pow_le_pow_left₀ h1' h1 E
  have hUq : α * U ^ q ≤ α * ((e 0 : ℤ) : ℝ) ^ q :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hU) (hXi 0).1 q) (le_of_lt hα)
  linarith

/-- **Assembly.**  Finitely many gap-thin sets leave arbitrarily large integers uncovered. -/
theorem exists_gt_notMem_of_thin {r : ℕ} (S : Fin r → Set ℤ) (h : ∀ j, Thin (S j)) (B : ℝ) :
    ∃ n : ℤ, B < (n : ℝ) ∧ ∀ j, n ∉ S j := by
  classical
  choose m q E T α hα hq hE hthin using h
  set M : ℕ := Finset.univ.sup m with hM
  set W : ℕ := r * M + 1 with hWdef
  have hWpos : 0 < W := Nat.succ_pos _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ j, max (T j) (((W : ℝ) ^ (E j)) / α j) ≤ C := by
    refine ⟨∑ k, max (max (T k) (((W : ℝ) ^ (E k)) / α k)) 0, fun j => ?_⟩
    refine le_trans (le_max_left _ (0 : ℝ)) ?_
    exact Finset.single_le_sum (f := fun k => max (max (T k) (((W : ℝ) ^ (E k)) / α k)) 0)
      (fun k _ => le_max_right _ _) (Finset.mem_univ j)
  set U : ℝ := max (max B 1) C + 1 with hUdef
  have hU1 : (1 : ℝ) ≤ U := by
    have : (1 : ℝ) ≤ max (max B 1) C := le_trans (le_max_right B 1) (le_max_left _ _)
    linarith
  have hUpos : 0 < U := lt_of_lt_of_le one_pos hU1
  have hUB : B < U := by
    have : B ≤ max (max B 1) C := le_trans (le_max_left B 1) (le_max_left _ _)
    linarith
  have hUT : ∀ j, T j < U := by
    intro j
    have h1 : T j ≤ C := le_trans (le_max_left _ _) (hC j)
    have h2 : C ≤ max (max B 1) C := le_max_right _ _
    linarith
  have hUpow : ∀ j, (W : ℝ) ^ (E j) ≤ α j * U ^ (q j) := by
    intro j
    have hUq : U ≤ U ^ (q j) := le_self_pow₀ hU1 (hq j).ne'
    have h1 : ((W : ℝ) ^ (E j)) / α j ≤ C := le_trans (le_max_right _ _) (hC j)
    have h2 : C ≤ max (max B 1) C := le_max_right _ _
    have h3 : ((W : ℝ) ^ (E j)) / α j ≤ U := by linarith
    have h4 : (W : ℝ) ^ (E j) ≤ α j * U := by
      rw [div_le_iff₀ (hα j)] at h3
      linarith [h3]
    exact le_trans h4 (mul_le_mul_of_nonneg_left hUq (le_of_lt (hα j)))
  set a : ℤ := ⌈U⌉ with ha
  set X : Finset ℤ := (Finset.range W).image (fun i : ℕ => a + (i : ℤ)) with hX
  have haU : U ≤ (a : ℝ) := Int.le_ceil U
  have hXmem : ∀ n ∈ X, U ≤ (n : ℝ) ∧ (n : ℝ) ≤ U + (W : ℝ) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have hiW : (i : ℝ) < (W : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
    have hcast : ((a + (i : ℤ) : ℤ) : ℝ) = (a : ℝ) + (i : ℝ) := by push_cast; ring
    rw [hcast]
    constructor
    · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    · have hceil : (a : ℝ) < U + 1 := by
        have := Int.ceil_lt_add_one U
        exact_mod_cast this
      have : (i : ℝ) ≤ (W : ℝ) - 1 := by
        have : (i : ℕ) + 1 ≤ W := Finset.mem_range.mp hi
        have : ((i : ℕ) : ℝ) + 1 ≤ (W : ℝ) := by exact_mod_cast this
        linarith
      linarith
  have hXcard : X.card = W := by
    rw [hX, Finset.card_image_of_injective _ (fun i j hij => by omega), Finset.card_range]
  have hjcard : ∀ j, (X.filter (· ∈ S j)).card ≤ m j := fun j =>
    card_filter_le_of_thin (hα j) (hthin j) hUpos (hUT j) hXmem (hUpow j)
  have hsub : X.filter (fun n => ∃ j, n ∈ S j)
      ⊆ Finset.univ.biUnion (fun j => X.filter (· ∈ S j)) := by
    intro n hn
    obtain ⟨hn1, j, hj⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_filter.mpr ⟨hn1, hj⟩⟩
  have hcov : (X.filter (fun n => ∃ j, n ∈ S j)).card ≤ r * M := by
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    refine le_trans (Finset.sum_le_sum fun j _ => hjcard j) ?_
    refine le_trans (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      Finset.le_sup (f := m) (Finset.mem_univ j)) ?_
    simp [hM]
  have hne : (X.filter (fun n => ¬ ∃ j, n ∈ S j)).Nonempty := by
    rw [← Finset.card_pos]
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := X) (p := fun n => ∃ j, n ∈ S j)
    omega
  obtain ⟨n, hn⟩ := hne
  obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
  refine ⟨n, ?_, ?_⟩
  · exact lt_of_lt_of_le hUB (hXmem n hn1).1
  · push_neg at hn2
    exact hn2

/-- **Finitely many gap-thin sets do not cover the integers.** -/
theorem infinite_compl_of_thin {r : ℕ} (S : Fin r → Set ℤ) (h : ∀ j, Thin (S j)) :
    {n : ℤ | ∀ j, n ∉ S j}.Infinite := by
  intro hfin
  obtain ⟨A, hA⟩ := hfin.bddAbove
  obtain ⟨n, hn, hn2⟩ := exists_gt_notMem_of_thin S h (A : ℝ)
  exact absurd (hA hn2) (not_le.mpr (by exact_mod_cast hn))

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
