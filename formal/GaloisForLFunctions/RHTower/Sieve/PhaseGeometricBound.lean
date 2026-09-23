import GaloisForLFunctions.RHTower.Sieve.FinitePhaseMomentExpansion
import GaloisForLFunctions.RHTower.Sieve.GeometricSumBound
import Mathlib.Analysis.Normed.Group.AddCircle

namespace RHTower.Sieve

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Distance of a real phase to the nearest integer.  Using the norm on the
additive circle makes the quantity intrinsic, including at half-integers. -/
def unitPhaseDistance (x : ℝ) : ℝ :=
  ‖(x : AddCircle (1 : ℝ))‖

theorem unitPhaseDistance_eq_abs_sub_round (x : ℝ) :
    unitPhaseDistance x = |x - (round x : ℝ)| := by
  unfold unitPhaseDistance
  simpa using (AddCircle.norm_eq (p := (1 : ℝ)) (x := x))

theorem finitePhaseChar_intCast (z : ℤ) :
    finitePhaseChar (z : ℝ) = 1 := by
  unfold finitePhaseChar
  convert Complex.exp_int_mul_two_pi_mul_I z using 1
  push_cast
  ring

theorem finitePhaseChar_sub_intCast (x : ℝ) (z : ℤ) :
    finitePhaseChar (x - (z : ℝ)) = finitePhaseChar x := by
  rw [sub_eq_add_neg, finitePhaseChar_add, finitePhaseChar_neg,
    finitePhaseChar_intCast]
  simp

/-- Chord length on the unit circle is at least four times distance of the
phase to the nearest integer.  This is the exact denominator estimate used
in Vinogradov's endpoint-perturbation argument. -/
theorem four_mul_unitPhaseDistance_le_norm_finitePhaseChar_sub_one (x : ℝ) :
    4 * unitPhaseDistance x ≤ ‖finitePhaseChar x - 1‖ := by
  let δ : ℝ := x - (round x : ℝ)
  have hδ : |δ| ≤ (1 : ℝ) / 2 := by
    simpa [δ] using abs_sub_round x
  have hprincipal : |2 * Real.pi * δ| ≤ Real.pi := by
    rw [abs_mul]
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    nlinarith
  have hnorm :
      ‖Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I) - 1‖ =
        2 * |Real.sin ((2 * Real.pi * δ) / 2)| := by
    rw [show (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I) =
      Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ) by ring]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    simp
  have hhalf : |(2 * Real.pi * δ) / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsin := Real.mul_abs_le_abs_sin hhalf
  have hchord :
      4 * |δ| ≤
        ‖Complex.exp (((2 * Real.pi * δ : ℝ) : ℂ) * Complex.I) - 1‖ := by
    rw [hnorm]
    have hpi : 0 < Real.pi := Real.pi_pos
    calc
      4 * |δ| = 2 * ((2 / Real.pi) * |(2 * Real.pi * δ) / 2|) := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos hpi,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        field_simp
        ring
      _ ≤ 2 * |Real.sin ((2 * Real.pi * δ) / 2)| := by
        nlinarith
  rw [unitPhaseDistance_eq_abs_sub_round]
  rw [← finitePhaseChar_sub_intCast x (round x)]
  unfold finitePhaseChar
  exact hchord

def finitePhaseProgression (H : ℕ) (x : ℝ) : ℂ :=
  ∑ n : Fin H, finitePhaseChar ((n.val : ℝ) * x)

theorem finitePhaseProgression_eq_geom (H : ℕ) (x : ℝ) :
    finitePhaseProgression H x =
      ∑ n ∈ Finset.range H, finitePhaseChar x ^ n := by
  unfold finitePhaseProgression
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [dif_pos (Finset.mem_range.mp hn)]
  unfold finitePhaseChar
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_finitePhaseProgression_le_length (H : ℕ) (x : ℝ) :
    ‖finitePhaseProgression H x‖ ≤ H := by
  unfold finitePhaseProgression
  calc
    ‖∑ n : Fin H, finitePhaseChar ((n.val : ℝ) * x)‖ ≤
        ∑ n : Fin H, ‖finitePhaseChar ((n.val : ℝ) * x)‖ :=
      norm_sum_le _ _
    _ = H := by simp [norm_finitePhaseChar]

theorem norm_finitePhaseProgression_le_inv_distance
    (H : ℕ) {x : ℝ} (hx : unitPhaseDistance x ≠ 0) :
    ‖finitePhaseProgression H x‖ ≤ 1 / (2 * unitPhaseDistance x) := by
  have hdist : 0 < unitPhaseDistance x :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  have hphase : finitePhaseChar x ≠ 1 := by
    intro h
    have hchord := four_mul_unitPhaseDistance_le_norm_finitePhaseChar_sub_one x
    rw [h, sub_self, norm_zero] at hchord
    nlinarith
  rw [finitePhaseProgression_eq_geom]
  have hgeom := norm_geom_sum_le
    (le_of_eq (norm_finitePhaseChar x)) hphase H
  have hchord := four_mul_unitPhaseDistance_le_norm_finitePhaseChar_sub_one x
  have hden : 0 < ‖finitePhaseChar x - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hphase)
  calc
    ‖∑ n ∈ Finset.range H, finitePhaseChar x ^ n‖ ≤
        2 / ‖finitePhaseChar x - 1‖ := hgeom
    _ ≤ 1 / (2 * unitPhaseDistance x) := by
      rw [div_le_div_iff₀ hden (by positivity : 0 < 2 * unitPhaseDistance x)]
      nlinarith

/-- Exact pair-difference expansion of the squared phase progression.  This is
the finite Fejér identity before collecting equal differences. -/
theorem finitePhaseProgression_normSq_expansion (H : ℕ) (x : ℝ) :
    ((Complex.normSq (finitePhaseProgression H x) : ℝ) : ℂ) =
      ∑ uv : Fin H × Fin H,
        finitePhaseChar ((((uv.1.val : ℝ) - uv.2.val) * x)) := by
  calc
    ((Complex.normSq (finitePhaseProgression H x) : ℝ) : ℂ) =
        finitePhaseProgression H x * conj (finitePhaseProgression H x) := by
      rw [Complex.mul_conj]
    _ = (∑ u : Fin H, finitePhaseChar ((u.val : ℝ) * x)) *
        (∑ v : Fin H, conj (finitePhaseChar ((v.val : ℝ) * x))) := by
      unfold finitePhaseProgression
      rw [map_sum]
    _ = ∑ uv : Fin H × Fin H,
        finitePhaseChar ((uv.1.val : ℝ) * x) *
          conj (finitePhaseChar ((uv.2.val : ℝ) * x)) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
    _ = ∑ uv : Fin H × Fin H,
        finitePhaseChar ((((uv.1.val : ℝ) - uv.2.val) * x)) := by
      apply Finset.sum_congr rfl
      intro uv _
      rw [← finitePhaseChar_neg, ← finitePhaseChar_add]
      congr 1
      ring

def finiteFejerKernel (H : ℕ) (x : ℝ) : ℝ :=
  (2 / (H : ℝ)) * Complex.normSq (finitePhaseProgression H x)

theorem finiteFejerKernel_nonneg (H : ℕ) (x : ℝ) :
    0 ≤ finiteFejerKernel H x := by
  unfold finiteFejerKernel
  exact mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg H))
    (Complex.normSq_nonneg _)

theorem finitePhaseProgression_neg (H : ℕ) (x : ℝ) :
    finitePhaseProgression H (-x) = conj (finitePhaseProgression H x) := by
  unfold finitePhaseProgression
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [← finitePhaseChar_neg]
  congr 1
  ring

theorem finiteFejerKernel_neg (H : ℕ) (x : ℝ) :
    finiteFejerKernel H (-x) = finiteFejerKernel H x := by
  unfold finiteFejerKernel
  rw [finitePhaseProgression_neg, Complex.normSq_conj]

theorem finiteFejerKernel_expansion (H : ℕ) (x : ℝ) :
    ((finiteFejerKernel H x : ℝ) : ℂ) =
      ∑ uv : Fin H × Fin H,
        ((2 / (H : ℝ) : ℝ) : ℂ) *
          finitePhaseChar ((((uv.1.val : ℝ) - uv.2.val) * x)) := by
  unfold finiteFejerKernel
  rw [Complex.ofReal_mul]
  rw [finitePhaseProgression_normSq_expansion]
  rw [Finset.mul_sum]

/-- Fejér-scale geometric bound in the exact normalization used by
Montgomery--Vaughan Theorem 24.7.  The zero-distance branch is absorbed by
the trivial term; away from it one gains the reciprocal square. -/
theorem fejerScale_finitePhaseProgression_le
    {H : ℕ} (hH : H ≠ 0) (x : ℝ) :
    (2 / (H : ℝ)) * ‖finitePhaseProgression H x‖ ^ (2 : ℕ) ≤
      if unitPhaseDistance x = 0 then
        2 * (H : ℝ)
      else
        min (2 * (H : ℝ))
          (1 / (2 * (H : ℝ) * unitPhaseDistance x ^ (2 : ℕ))) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  split_ifs with hx
  · have hlength := norm_finitePhaseProgression_le_length H x
    have hsquare : ‖finitePhaseProgression H x‖ ^ (2 : ℕ) ≤ (H : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hlength 2
    calc
      (2 / (H : ℝ)) * ‖finitePhaseProgression H x‖ ^ (2 : ℕ) ≤
          (2 / (H : ℝ)) * (H : ℝ) ^ (2 : ℕ) := by gcongr
      _ = 2 * (H : ℝ) := by field_simp
  · have hlength := norm_finitePhaseProgression_le_length H x
    have hinv := norm_finitePhaseProgression_le_inv_distance H hx
    have hdist : 0 < unitPhaseDistance x :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    apply le_min
    · have hsquare : ‖finitePhaseProgression H x‖ ^ (2 : ℕ) ≤ (H : ℝ) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) hlength 2
      calc
        (2 / (H : ℝ)) * ‖finitePhaseProgression H x‖ ^ (2 : ℕ) ≤
            (2 / (H : ℝ)) * (H : ℝ) ^ (2 : ℕ) := by gcongr
        _ = 2 * (H : ℝ) := by field_simp
    · have hsquare :
          ‖finitePhaseProgression H x‖ ^ (2 : ℕ) ≤
            (1 / (2 * unitPhaseDistance x)) ^ (2 : ℕ) := by
        exact pow_le_pow_left₀ (norm_nonneg _) hinv 2
      calc
        (2 / (H : ℝ)) * ‖finitePhaseProgression H x‖ ^ (2 : ℕ) ≤
            (2 / (H : ℝ)) * (1 / (2 * unitPhaseDistance x)) ^ (2 : ℕ) := by
          gcongr
        _ = 1 / (2 * (H : ℝ) * unitPhaseDistance x ^ (2 : ℕ)) := by
          field_simp

theorem finiteFejerKernel_le
    {H : ℕ} (hH : H ≠ 0) (x : ℝ) :
    finiteFejerKernel H x ≤
      if unitPhaseDistance x = 0 then
        2 * (H : ℝ)
      else
        min (2 * (H : ℝ))
          (1 / (2 * (H : ℝ) * unitPhaseDistance x ^ (2 : ℕ))) := by
  simpa [finiteFejerKernel, Complex.normSq_eq_norm_sq] using
    fejerScale_finitePhaseProgression_le hH x

theorem finiteFejerKernel_le_two_mul_length
    {H : ℕ} (hH : H ≠ 0) (x : ℝ) :
    finiteFejerKernel H x ≤ 2 * (H : ℝ) := by
  have h := finiteFejerKernel_le hH x
  split_ifs at h with hx
  · exact h
  · exact h.trans (min_le_left _ _)

end

end RHTower.Sieve
