import GaloisForLFunctions.HTGeometry.BeurlingCrossSystemBlindness
import GaloisForLFunctions.RHTower.ProlateActionLinear

/-!
# Finite layer cake for powers of a minimum

This module factors a finite bivariate sum weighted by `min(A x, B y)^(k+1)` into the integral of
two one-variable threshold sums.  It reuses the corpus's polynomial indicator integral and finite
interval-integrability lemmas.
-/

open Finset MeasureTheory intervalIntegral

namespace RHTower.Sieve

noncomputable section

/-- Finite weighted layer-cake factorization for every positive power of a minimum. -/
theorem finite_sum_min_pow_succ_eq_layerCake
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ)
    (c : ι → ℝ) (d : κ → ℝ) (A : ι → ℝ) (B : κ → ℝ)
    (i j k : ℕ) (L : ℝ)
    (hA0 : ∀ x ∈ S, 0 ≤ A x) (hAL : ∀ x ∈ S, A x ≤ L)
    (hB0 : ∀ y ∈ T, 0 ≤ B y) :
    (∑ x ∈ S, ∑ y ∈ T,
      c x * d y * A x ^ i * B y ^ j * min (A x) (B y) ^ (k + 1)) =
      ∫ u in (0 : ℝ)..L,
        ((k : ℝ) + 1) * u ^ k *
          (∑ x ∈ S, c x * A x ^ i * (if u < A x then (1 : ℝ) else 0)) *
          (∑ y ∈ T, d y * B y ^ j * (if u < B y then (1 : ℝ) else 0)) := by
  let atom : ι → κ → ℝ → ℝ := fun x y u =>
    c x * d y * A x ^ i * B y ^ j *
      (((k : ℝ) + 1) * u ^ k *
        (if u < min (A x) (B y) then (1 : ℝ) else 0))
  have hatom : ∀ x ∈ S, ∀ y ∈ T,
      IntervalIntegrable (atom x y) volume 0 L := by
    intro x hx y hy
    exact (GaloisForLFunctions.HTGeometry.Beurling.intervalIntegrable_layer_atom
      k (min (A x) (B y)) 0 L).const_mul _
  have hpoint : ∀ u : ℝ,
      ((k : ℝ) + 1) * u ^ k *
          (∑ x ∈ S, c x * A x ^ i * (if u < A x then (1 : ℝ) else 0)) *
          (∑ y ∈ T, d y * B y ^ j * (if u < B y then (1 : ℝ) else 0)) =
        ∑ x ∈ S, ∑ y ∈ T, atom x y u := by
    intro u
    rw [show ((k : ℝ) + 1) * u ^ k *
        (∑ x ∈ S, c x * A x ^ i * (if u < A x then (1 : ℝ) else 0)) *
        (∑ y ∈ T, d y * B y ^ j * (if u < B y then (1 : ℝ) else 0)) =
      ((∑ x ∈ S, c x * A x ^ i * (if u < A x then (1 : ℝ) else 0)) *
        (∑ y ∈ T, d y * B y ^ j * (if u < B y then (1 : ℝ) else 0))) *
          (((k : ℝ) + 1) * u ^ k) by ring]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [atom]
    by_cases hmin : u < min (A x) (B y)
    · have hAx : u < A x := hmin.trans_le (min_le_left _ _)
      have hBy : u < B y := hmin.trans_le (min_le_right _ _)
      simp only [if_pos hmin, if_pos hAx, if_pos hBy, mul_one]
      ring
    · by_cases hAx : u < A x
      · have hBy : ¬ u < B y := fun h => hmin (lt_min hAx h)
        simp [hmin, hAx, hBy]
      · simp [hmin, hAx]
  rw [intervalIntegral.integral_congr
    (g := fun u => ∑ x ∈ S, ∑ y ∈ T, atom x y u)
    (fun u hu => hpoint u)]
  rw [intervalIntegral.integral_finsetSum (fun x hx =>
    RHTower.intervalIntegrable_finsetSum T (fun y hy => hatom x hx y hy))]
  apply Finset.sum_congr rfl
  intro x hx
  rw [intervalIntegral.integral_finsetSum (fun y hy => hatom x hx y hy)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [show (∫ u in (0 : ℝ)..L, atom x y u) =
      c x * d y * A x ^ i * B y ^ j *
        (min (A x) (B y) ^ (k + 1)) by
    change (∫ u in (0 : ℝ)..L,
      (c x * d y * A x ^ i * B y ^ j) *
        (((k : ℝ) + 1) * u ^ k *
          (if u < min (A x) (B y) then (1 : ℝ) else 0))) = _
    rw [intervalIntegral.integral_const_mul,
      GaloisForLFunctions.HTGeometry.Beurling.integral_layer_atom k
        (le_min (hA0 x hx) (hB0 y hy))
        (min_le_left (A x) (B y) |>.trans (hAL x hx))]]

/-- Weak-threshold version of the finite layer-cake factorization.  It differs from the strict
version only on the finite set of layer endpoints. -/
theorem finite_sum_min_pow_succ_eq_layerCake_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (T : Finset κ)
    (c : ι → ℝ) (d : κ → ℝ) (A : ι → ℝ) (B : κ → ℝ)
    (i j k : ℕ) (L : ℝ)
    (hA0 : ∀ x ∈ S, 0 ≤ A x) (hAL : ∀ x ∈ S, A x ≤ L)
    (hB0 : ∀ y ∈ T, 0 ≤ B y) :
    (∑ x ∈ S, ∑ y ∈ T,
      c x * d y * A x ^ i * B y ^ j * min (A x) (B y) ^ (k + 1)) =
      ∫ u in (0 : ℝ)..L,
        ((k : ℝ) + 1) * u ^ k *
          (∑ x ∈ S, c x * A x ^ i * (if u ≤ A x then (1 : ℝ) else 0)) *
          (∑ y ∈ T, d y * B y ^ j * (if u ≤ B y then (1 : ℝ) else 0)) := by
  rw [finite_sum_min_pow_succ_eq_layerCake S T c d A B i j k L hA0 hAL hB0]
  refine intervalIntegral.integral_congr_ae ?_
  have hae : ∀ᵐ u : ℝ,
      u ∉ ((↑(S.image A ∪ T.image B) : Set ℝ)) := by
    apply MeasureTheory.compl_mem_ae_iff.mpr
    simpa using (Set.Finite.measure_zero (μ := volume)
      (Finset.finite_toSet (S.image A ∪ T.image B)))
  filter_upwards [hae] with u hu hmem
  have hsumA :
      (∑ x ∈ S, c x * A x ^ i * (if u < A x then (1 : ℝ) else 0)) =
        ∑ x ∈ S, c x * A x ^ i * (if u ≤ A x then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hne : u ≠ A x := by
      intro h
      apply hu
      subst u
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    by_cases hlt : u < A x
    · rw [if_pos hlt, if_pos hlt.le]
    · have hnotle : ¬ u ≤ A x := fun h => hlt (lt_of_le_of_ne h hne)
      rw [if_neg hlt, if_neg hnotle]
  have hsumB :
      (∑ y ∈ T, d y * B y ^ j * (if u < B y then (1 : ℝ) else 0)) =
        ∑ y ∈ T, d y * B y ^ j * (if u ≤ B y then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro y hy
    have hne : u ≠ B y := by
      intro h
      apply hu
      subst u
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    by_cases hlt : u < B y
    · rw [if_pos hlt, if_pos hlt.le]
    · have hnotle : ¬ u ≤ B y := fun h => hlt (lt_of_le_of_ne h hne)
      rw [if_neg hlt, if_neg hnotle]
  rw [hsumA, hsumB]

end

end RHTower.Sieve
