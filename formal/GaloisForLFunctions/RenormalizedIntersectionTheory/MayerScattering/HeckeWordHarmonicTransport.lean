import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.HeckePositiveWordReduction
import GaloisForLFunctions.HTGeometry.WordSeriesCompleteGradedAlgebra

/-!
# Finite harmonic transport through Hecke words

Unique suffix partitions turn left-generator harmonicity into right-generator
harmonicity after summation over the actual finite Hecke bases.
-/

set_option autoImplicit false
noncomputable section
open Matrix Finset
open GaloisForLFunctions RenormalizedIntersectionTheory MayerCoding
open HTGeometry.WordSeries

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering


private theorem boolWords_zero : (wordsOfLength 0 : Finset (List Bool)) = {[]} := by
  ext w
  simp only [mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]

private theorem boolWords_succ (N : ℕ) :
    (wordsOfLength (N + 1) : Finset (List Bool)) =
      (wordsOfLength N).image (List.cons false) ∪ (wordsOfLength N).image (List.cons true) := by
  ext w
  cases w with
  | nil => simp [mem_wordsOfLength]
  | cons b w => cases b <;> simp [mem_wordsOfLength]

private theorem sum_boolWords_succ (N : ℕ) (f : List Bool → ℂ) :
    (∑ w ∈ wordsOfLength (N + 1), f w) =
      (∑ w ∈ wordsOfLength N, f (false :: w)) +
      (∑ w ∈ wordsOfLength N, f (true :: w)) := by
  classical
  have hd : Disjoint ((wordsOfLength N).image (List.cons false))
      ((wordsOfLength N).image (List.cons true)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hw
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hw'
    have he := hu.trans hv.symm
    cases he
  rw [boolWords_succ, Finset.sum_union hd]
  rw [Finset.sum_image (by intro a ha b hb h; exact (List.cons.inj h).2),
    Finset.sum_image (by intro a ha b hb h; exact (List.cons.inj h).2)]

/-- The Lewis binary splitting identity sums exactly over every fixed word length. -/
theorem sum_heckeWords_of_harmonic {n : ℕ} (H : NatMatrix → ℂ)
    (hH : ∀ A, HasHeckeDeterminant n A →
      H A = H (generator true * A) + H (generator false * A))
    {A : NatMatrix} (hA : HasHeckeDeterminant n A) (N : ℕ) :
    (∑ w ∈ wordsOfLength N, H (matrixWord w * A)) = H A := by
  induction N with
  | zero => rw [boolWords_zero, Finset.sum_singleton, matrixWord, one_mul]
  | succ N ih =>
      rw [sum_boolWords_succ, ← Finset.sum_add_distrib]
      calc
        (∑ w ∈ wordsOfLength N,
          (H (matrixWord (false :: w) * A) + H (matrixWord (true :: w) * A))) =
            ∑ w ∈ wordsOfLength N, H (matrixWord w * A) := by
          apply Finset.sum_congr rfl
          intro w hw
          simpa only [matrixWord, mul_assoc, add_comm] using
            (hH (matrixWord w * A) (hasHeckeDeterminant_word_mul hA w)).symm
        _ = H A := ih

/-- A complete finite suffix partition preserves every left-harmonic matrix value.
No convergence or infinite-tree measure is used. -/
theorem sum_heckeSuffixPartition {ι : Type*} [DecidableEq ι] {n : ℕ}
    (H : NatMatrix → ℂ)
    (hH : ∀ A, HasHeckeDeterminant n A →
      H A = H (generator true * A) + H (generator false * A))
    {A : NatMatrix} (hA : HasHeckeDeterminant n A)
    (I : Finset ι) (u : ι → List Bool) (N : ℕ)
    (hbound : ∀ i ∈ I, (u i).length ≤ N)
    (hcover : ∀ W : List Bool, W.length = N → ∃ i ∈ I, ∃ v : List Bool, W = v ++ u i)
    (hunique : ∀ i ∈ I, ∀ j ∈ I, ∀ v v' : List Bool,
      v ++ u i = v' ++ u j → i = j ∧ v = v') :
    (∑ i ∈ I, H (matrixWord (u i) * A)) = H A := by
  classical
  let S := I.sigma (fun i => (wordsOfLength (N - (u i).length) : Finset (List Bool)))
  have hsum : (∑ x ∈ S, H (matrixWord (x.2 ++ u x.1) * A)) =
      ∑ W ∈ wordsOfLength N, H (matrixWord W * A) := by
    apply Finset.sum_bij (fun x _ => x.2 ++ u x.1)
    · intro x hx
      obtain ⟨hi, hv⟩ := Finset.mem_sigma.mp hx
      have hv' := mem_wordsOfLength.mp hv
      have hb := hbound x.1 hi
      apply mem_wordsOfLength.mpr
      simp only [List.length_append]
      omega
    · intro x hx y hy he
      have hx' := Finset.mem_sigma.mp hx
      have hy' := Finset.mem_sigma.mp hy
      obtain ⟨hij, hv⟩ := hunique x.1 hx'.1 y.1 hy'.1 x.2 y.2 he
      cases x
      cases y
      dsimp at hij hv
      subst_vars
      rfl
    · intro W hW
      have hw := mem_wordsOfLength.mp hW
      obtain ⟨i, hi, v, hv⟩ := hcover W hw
      refine ⟨⟨i, v⟩, Finset.mem_sigma.mpr ⟨hi, ?_⟩, hv.symm⟩
      apply mem_wordsOfLength.mpr
      change v.length = N - (u i).length
      rw [hv, List.length_append] at hw
      omega
    · intro x hx
      rfl
  calc
    (∑ i ∈ I, H (matrixWord (u i) * A)) =
        ∑ i ∈ I, ∑ v ∈ wordsOfLength (N - (u i).length),
          H (matrixWord (v ++ u i) * A) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := sum_heckeWords_of_harmonic H hH (hasHeckeDeterminant_word_mul hA (u i))
        (N - (u i).length)
      simpa only [matrixWord_append, mul_assoc] using h.symm
    _ = ∑ x ∈ S, H (matrixWord (x.2 ++ u x.1) * A) := by
      rw [Finset.sum_sigma]
    _ = ∑ W ∈ wordsOfLength N, H (matrixWord W * A) := hsum
    _ = H A := sum_heckeWords_of_harmonic H hH hA N

#print axioms sum_heckeWords_of_harmonic
#print axioms sum_heckeSuffixPartition


private abbrev HeckeBranch (n : ℕ) := {B : NatMatrix // B ∈ naturalHeckeSet n} × Bool

private structure HeckeTransition (n : ℕ) (j : HeckeBranch n) where
  word : List Bool
  target : NatMatrix
  target_mem : target ∈ naturalHeckeSet n
  matrix_eq : matrixWord word * target = j.1.val * generator j.2
  length_le : word.length ≤ 8 * n

private noncomputable def actualHeckeTransition {n : ℕ} (hn : 0 < n) (j : HeckeBranch n) :
    HeckeTransition n j := by
  let h := heckeTransition_exists hn j.1.property j.2
  let u := Classical.choose h
  let hu := Classical.choose_spec h
  let C := Classical.choose hu
  have hC := Classical.choose_spec hu
  exact ⟨u, C, hC.1, hC.2.1, hC.2.2⟩

private noncomputable def heckeTransitionFiber {n : ℕ} (hn : 0 < n) (C : NatMatrix) :
    Finset (HeckeBranch n) := by
  classical
  exact Finset.univ.filter (fun j => (actualHeckeTransition hn j).target = C)

private theorem heckeTransitionFiber_sum {n : ℕ} (hn : 0 < n)
    (H : NatMatrix → ℂ)
    (hH : ∀ A, HasHeckeDeterminant n A →
      H A = H (generator true * A) + H (generator false * A))
    {C : NatMatrix} (hC : C ∈ naturalHeckeSet n) :
    (∑ j ∈ heckeTransitionFiber hn C, H (j.1.val * generator j.2)) = H C := by
  classical
  let t := actualHeckeTransition hn
  have hc := mem_naturalHeckeSet_iff.mp hC
  have hcut := sum_heckeSuffixPartition H hH hc.1 (heckeTransitionFiber hn C)
    (fun j => (t j).word) (8 * n + 1)
  have hb : ∀ j ∈ heckeTransitionFiber hn C, (t j).word.length ≤ 8 * n + 1 := by
    intro j hj
    exact (t j).length_le.trans (Nat.le_succ _)
  have hcover : ∀ W : List Bool, W.length = 8 * n + 1 →
      ∃ j ∈ heckeTransitionFiber hn C, ∃ v : List Bool, W = v ++ (t j).word := by
    intro W hW
    obtain ⟨B, hB, b, u, v, hu, hw, _⟩ := heckeTransition_suffix_exists hn hC W (by omega)
    let j : HeckeBranch n := (⟨B, hB⟩, b)
    have ht := mem_naturalHeckeSet_iff.mp (t j).target_mem
    have he : matrixWord (t j).word * (t j).target = matrixWord u * C :=
      (t j).matrix_eq.trans hu.symm
    obtain ⟨hw', ht'⟩ := heckeWordNormalForm_unique hn ht.1 hc.1 ht.2 hc.2
      (t j).word u he
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'⟩, v, ?_⟩
    rw [hw']
    exact hw
  have huniq : ∀ i ∈ heckeTransitionFiber hn C, ∀ j ∈ heckeTransitionFiber hn C,
      ∀ v v' : List Bool, v ++ (t i).word = v' ++ (t j).word → i = j ∧ v = v' := by
    intro i hi j hj v v' hw
    have hiC : (t i).target = C := (Finset.mem_filter.mp hi).2
    have hjC : (t j).target = C := (Finset.mem_filter.mp hj).2
    have hiM : matrixWord (t i).word * C = i.1.val * generator i.2 := by
      rw [← hiC]
      exact (t i).matrix_eq
    have hjM : matrixWord (t j).word * C = j.1.val * generator j.2 := by
      rw [← hjC]
      exact (t j).matrix_eq
    obtain ⟨hij, hBB, hvv, _⟩ := heckeTransition_suffix_unique hn
      i.1.property j.1.property i.2 j.2 (t i).word (t j).word v v' hiM hjM hw
    exact ⟨Prod.ext (Subtype.ext hBB) hij, hvv⟩
  have he := hcut hb hcover huniq
  calc
    (∑ j ∈ heckeTransitionFiber hn C, H (j.1.val * generator j.2)) =
        ∑ j ∈ heckeTransitionFiber hn C, H (matrixWord (t j).word * C) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjC : (t j).target = C := (Finset.mem_filter.mp hj).2
      rw [← hjC, (t j).matrix_eq]
    _ = H C := he

/-- Summing over the actual Hecke bases turns left-generator harmonicity into
right-generator harmonicity, for every positive determinant. -/
theorem hecke_sum_right_harmonic {n : ℕ} (hn : 0 < n)
    (H : NatMatrix → ℂ)
    (hH : ∀ A, HasHeckeDeterminant n A →
      H A = H (generator true * A) + H (generator false * A)) :
    (∑ B ∈ naturalHeckeSet n, (H (B * generator true) + H (B * generator false))) =
      ∑ B ∈ naturalHeckeSet n, H B := by
  classical
  have hf : (∑ C ∈ naturalHeckeSet n,
      ∑ j ∈ heckeTransitionFiber hn C, H (j.1.val * generator j.2)) =
      ∑ j : HeckeBranch n, H (j.1.val * generator j.2) := by
    simp only [heckeTransitionFiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp [(actualHeckeTransition hn j).target_mem]
  have hsum : (∑ j : HeckeBranch n, H (j.1.val * generator j.2)) =
      ∑ B ∈ naturalHeckeSet n, (H (B * generator true) + H (B * generator false)) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    exact Finset.sum_coe_sort (naturalHeckeSet n)
      (fun B => H (B * generator true) + H (B * generator false))
  rw [← hsum, ← hf]
  exact Finset.sum_congr rfl (fun C hC => heckeTransitionFiber_sum hn H hH hC)

#print axioms hecke_sum_right_harmonic

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
