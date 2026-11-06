import GaloisForLFunctions.SignedSuccessorArithmetic.TheKloostermanSecondMomentIsACount

/-!
# The hypersurface carrying Kloosterman moments

Every tensor moment of the Kloosterman family is a character sum on the torus
hypersurface `Σ xⱼ = 0`. Expanding the tensor power and using character orthogonality
in the family parameter contributes the single factor `#F`, independently of the
tensor degree. Cancellation in the remaining character sum is a separate question.
-/

open Finset AddChar
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

open SignedSuccessorArithmetic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Ordered nonzero coordinates of a split torus. -/
abbrev MomentTorus (F : Type*) [Zero F] (m : ℕ) := Fin m → {x : F // x ≠ 0}

omit [Fintype F] [DecidableEq F] in
private theorem character_sum {J : Type*} (ψ : AddChar F ℂ) (s : Finset J) (f : J → F) :
    ψ (∑ j ∈ s, f j) = ∏ j ∈ s, ψ (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty, map_zero_eq_one, prod_empty]
  | @insert j s hj ih =>
      rw [sum_insert hj, prod_insert hj, map_add_eq_mul, ih]

/-- A tensor trace is the character of the sum of its coordinate phases. -/
theorem kloosterman_tensor_expansion (ψ : AddChar F ℂ) (a b : F) (m : ℕ) :
    kloosterman ψ a b ^ m = ∑ x : MomentTorus F m,
      ψ (a * (∑ j, (x j : F)) + b * (∑ j, (x j : F)⁻¹)) := by
  have hk : kloosterman ψ a b =
      ∑ x : {x : F // x ≠ 0}, ψ (a * (x : F) + b * (x : F)⁻¹) :=
    sum_subtype _ (by simp) _
  calc kloosterman ψ a b ^ m
      = ∏ _ : Fin m, ∑ x : {x : F // x ≠ 0}, ψ (a * (x : F) + b * (x : F)⁻¹) := by
        rw [hk]
        simp only [prod_const, card_univ, Fintype.card_fin]
    _ = ∑ x : MomentTorus F m, ∏ j, ψ (a * (x j : F) + b * (x j : F)⁻¹) :=
      Fintype.prod_sum (fun (_ : Fin m) (x : {x : F // x ≠ 0}) =>
        ψ (a * (x : F) + b * (x : F)⁻¹))
    _ = _ := by
      apply sum_congr rfl
      intro x _
      rw [← character_sum]
      congr 1
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]

/-- All Kloosterman moments are character sums on `Σ xⱼ = 0` in a split torus.
The parameter contributes exactly one factor `#F` in every tensor degree. -/
theorem kloosterman_moment_hypersurface {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (b : F) (m : ℕ) :
    ∑ a : F, kloosterman ψ a b ^ m = (Fintype.card F : ℂ) *
      ∑ x ∈ (univ : Finset (MomentTorus F m)).filter (fun x => ∑ j, (x j : F) = 0),
        ψ (b * (∑ j, (x j : F)⁻¹)) := by
  simp_rw [kloosterman_tensor_expansion]
  rw [sum_comm, sum_filter, mul_sum]
  apply sum_congr rfl
  intro x _
  simp_rw [map_add_eq_mul]
  rw [← sum_mul, sum_mulShift _ hψ]
  split_ifs <;> simp

/-- Removing the singular parameter `a = 0` subtracts its exact trace `(-1)^m`. -/
theorem kloosterman_punctured_moment_hypersurface {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {b : F} (hb : b ≠ 0) (m : ℕ) :
    ∑ a ∈ (univ : Finset F).filter (· ≠ 0), kloosterman ψ a b ^ m =
      (Fintype.card F : ℂ) *
        ∑ x ∈ (univ : Finset (MomentTorus F m)).filter (fun x => ∑ j, (x j : F) = 0),
          ψ (b * (∑ j, (x j : F)⁻¹)) - (-1) ^ m := by
  have h := kloosterman_moment_hypersurface hψ b m
  rw [← sum_filter_add_sum_filter_not univ (fun a : F => a ≠ 0)] at h
  have hz : (univ : Finset F).filter (fun a => ¬ a ≠ 0) = {0} := by ext; simp
  rw [hz, sum_singleton, kloosterman_zero_left hψ hb] at h
  exact eq_sub_iff_add_eq.mpr h

/-- Negating the summation variable proves that every finite-field Kloosterman sum is real. -/
theorem kloosterman_conj (ψ : AddChar F ℂ) (a b : F) :
    starRingEnd ℂ (kloosterman ψ a b) = kloosterman ψ a b := by
  simp only [kloosterman, map_sum, conj_addChar]
  refine sum_nbij' (fun x : F => -x) (fun x : F => -x)
    (by simp) (by simp) (by simp) (by simp) ?_
  intro x _
  congr 1
  rw [inv_neg]
  ring

private theorem kloosterman_eq_re (ψ : AddChar F ℂ) (a b : F) :
    kloosterman ψ a b = ((kloosterman ψ a b).re : ℂ) := by
  have h := congrArg Complex.im (kloosterman_conj ψ a b)
  rw [Complex.conj_im] at h
  apply Complex.ext
  · rfl
  · change (kloosterman ψ a b).im = 0
    linarith only [h]

/-- Every even tensor trace is nonnegative without using a purity estimate. -/
theorem kloosterman_even_trace_nonneg (ψ : AddChar F ℂ) (a b : F) (k : ℕ) :
    0 ≤ (kloosterman ψ a b ^ (2 * k)).re := by
  rw [kloosterman_eq_re, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact pow_nonneg (sq_nonneg _) k |>.trans_eq (pow_mul _ 2 k).symm

/-- Even moments over any set of family parameters are nonnegative. -/
theorem kloosterman_even_moment_nonneg (ψ : AddChar F ℂ) (b : F) (k : ℕ) (S : Finset F) :
    0 ≤ (∑ a ∈ S, kloosterman ψ a b ^ (2 * k)).re := by
  rw [Complex.re_sum]
  exact sum_nonneg fun a _ => kloosterman_even_trace_nonneg ψ a b k

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
