import GaloisForLFunctions.RHTower.HermiteEvenCarrier
import GaloisForLFunctions.RHTower.ConstrainedProlateSignedSpectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Positive and negative spectral sectors of the even prolate Fourier block

The concentration spectrum forgets the sign of the compressed Fourier eigenvalues.  This file
recovers genuine sign information without assuming classical prolate numbering.

First, C-star spectral order and the compact Fredholm alternative give an abstract bridge: a
strictly negative quadratic witness for a compact self-adjoint operator forces a negative
eigenvalue, and completeness of the signed greedy exhaustion forces that eigenvalue to occur as
one of its signed values.  Applying the bridge to the `4j+2` Hermite sector and to the `4j`
sector proves that the actual even prolate block has both negative and positive signed values at
every sufficiently large aperture.
-/

open Filter
open scoped InnerProduct InnerProductSpace

noncomputable section

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- If `x` is closer to a `-1` eigenvector than to zero, its quadratic value is negative. -/
theorem re_inner_neg_of_norm_add_lt_norm (S : H →L[ℂ] H) (x : H)
    (h : ‖x + S x‖ < ‖x‖) : RCLike.re (inner ℂ (S x) x) < 0 := by
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (norm_nonneg (x + S x)) h
  have hre : RCLike.re (inner ℂ (x + S x) x) ≤ ‖x + S x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hmul : ‖x + S x‖ * ‖x‖ < ‖x‖ ^ 2 := by
    calc
      ‖x + S x‖ * ‖x‖ < ‖x‖ * ‖x‖ := mul_lt_mul_of_pos_right h hxpos
      _ = ‖x‖ ^ 2 := by ring
  have hform : RCLike.re (inner ℂ (S x) x) =
      RCLike.re (inner ℂ (x + S x) x) - ‖x‖ ^ 2 := by
    have hS : S x = (x + S x) - x := by abel
    calc
      RCLike.re (inner ℂ (S x) x) =
          RCLike.re (inner ℂ ((x + S x) - x) x) :=
        congrArg (fun y : H => RCLike.re (inner ℂ y x)) hS
      _ = RCLike.re (inner ℂ (x + S x) x) - ‖x‖ ^ 2 := by
        rw [inner_sub_left, map_sub, inner_self_eq_norm_sq_to_K]
        rw [RCLike.re_ofReal_pow]
  rw [hform]
  linarith

variable [CompleteSpace H]

/-- A negative quadratic witness for a compact self-adjoint operator produces a genuine negative
real eigenpair. -/
theorem exists_negative_eigenpair_of_re_inner_neg {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {x : H}
    (hx : RCLike.re (inner ℂ (S x) x) < 0) :
    ∃ (c : ℝ) (v : H), c < 0 ∧ v ≠ 0 ∧ S v = (c : ℂ) • v := by
  have hself : IsSelfAdjoint S := isSelfAdjoint_iff_isSymmetric.mpr hsym
  have hnotnonneg : ¬ (0 : H →L[ℂ] H) ≤ S := by
    intro hnonneg
    have hpos : S.IsPositive := (nonneg_iff_isPositive S).mp hnonneg
    exact (not_lt_of_ge (hpos.re_inner_nonneg_left x)) hx
  have hnotall : ¬ ∀ c ∈ spectrum ℝ S, 0 ≤ c := by
    intro hall
    exact hnotnonneg ((StarOrderedRing.nonneg_iff_spectrum_nonneg S hself).mpr hall)
  push Not at hnotall
  obtain ⟨c, hcspec, hcneg⟩ := hnotall
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_lt hcneg)
  have hcspecComplex : ((c : ℝ) : ℂ) ∈ spectrum ℂ S :=
    spectrum.algebraMap_mem ℂ hcspec
  have heigenvalue : Module.End.HasEigenvalue (S : Module.End ℂ H) (c : ℂ) :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt hc0).mpr hcspecComplex
  obtain ⟨v, hv⟩ := heigenvalue.exists_hasEigenvector
  exact ⟨c, v, hcneg, hv.2, hv.apply_eq_smul⟩

/-- Negative quadratic form forces a negative member of the complete signed-greedy spectrum. -/
theorem exists_sgVal_neg_of_re_inner_neg {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {x : H}
    (hx : RCLike.re (inner ℂ (S x) x) < 0) :
    ∃ n : ℕ, sgVal S n < 0 := by
  obtain ⟨c, v, hcneg, hv0, hv⟩ :=
    exists_negative_eigenpair_of_re_inner_neg hcpt hsym hx
  have hc0 : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_lt hcneg)
  obtain ⟨n, hn⟩ := exists_sgVal_eq_of_eigenvalue hcpt hsym hv0 hv hc0
  refine ⟨n, ?_⟩
  have hnreal : sgVal S n = c := by exact_mod_cast hn
  rwa [hnreal]

/-- Positive quadratic form forces a positive member of the complete signed-greedy spectrum. -/
theorem exists_sgVal_pos_of_re_inner_pos {S : H →L[ℂ] H}
    (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) {x : H}
    (hx : 0 < RCLike.re (inner ℂ (S x) x)) :
    ∃ n : ℕ, 0 < sgVal S n := by
  have hneg : RCLike.re (inner ℂ ((-S) x) x) < 0 := by
    simpa using (neg_lt_zero.mpr hx)
  have hsymneg : (-S).IsSymmetric := by
    intro u v
    change inner ℂ (-(S u)) v = inner ℂ u (-(S v))
    rw [inner_neg_left, inner_neg_right]
    exact congrArg Neg.neg (hsym u v)
  obtain ⟨c, v, hcneg, hv0, hv⟩ :=
    exists_negative_eigenpair_of_re_inner_neg hcpt.neg hsymneg hneg
  have hpos : 0 < -c := neg_pos.mpr hcneg
  have hv' : S v = ((-c : ℝ) : ℂ) • v := by
    simpa [neg_smul] using congrArg Neg.neg hv
  have hc0 : (((-c : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  obtain ⟨n, hn⟩ := exists_sgVal_eq_of_eigenvalue hcpt hsym hv0 hv' hc0
  refine ⟨n, ?_⟩
  have hnreal : sgVal S n = -c := by exact_mod_cast hn
  rwa [hnreal]

end ContinuousLinearMap

namespace RHTower

/-! ## Uniform finite-depth Hermite sectors -/

/-- Sum of the positive-sector aperture truncation errors at fixed depth. -/
def hermitePositiveTruncationSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin (n + 1),
    ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖

/-- Sum of the negative-sector aperture truncation errors at fixed depth. -/
def hermiteNegativeTruncationSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin (n + 1),
    ‖hermiteEvenNegativeUnit (j : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (j : ℕ))‖

theorem tendsto_hermitePositiveTruncationSum (n : ℕ) :
    Tendsto (fun a : ℝ => hermitePositiveTruncationSum a n) atTop (nhds 0) := by
  have h : Tendsto (fun a : ℝ => ∑ j : Fin (n + 1),
      ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖)
      atTop (nhds (∑ _j : Fin (n + 1), (0 : ℝ))) :=
    tendsto_finsetSum _ fun j _ => tendsto_norm_sub_cut (hermiteEvenUnit (j : ℕ))
  simpa [hermitePositiveTruncationSum] using h

theorem tendsto_hermiteNegativeTruncationSum (n : ℕ) :
    Tendsto (fun a : ℝ => hermiteNegativeTruncationSum a n) atTop (nhds 0) := by
  have h : Tendsto (fun a : ℝ => ∑ j : Fin (n + 1),
      ‖hermiteEvenNegativeUnit (j : ℕ) -
        evenIndicatorCutoff a (hermiteEvenNegativeUnit (j : ℕ))‖)
      atTop (nhds (∑ _j : Fin (n + 1), (0 : ℝ))) :=
    tendsto_finsetSum _ fun j _ =>
      tendsto_norm_sub_cut (hermiteEvenNegativeUnit (j : ℕ))
  simpa [hermiteNegativeTruncationSum] using h

theorem norm_hermiteEvenUnit_sub_cut_le_truncationSum
    (a : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    ‖hermiteEvenUnit (j : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (j : ℕ))‖
      ≤ hermitePositiveTruncationSum a n := by
  exact Finset.single_le_sum (f := fun k : Fin (n + 1) =>
    ‖hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))‖)
    (fun k _ => norm_nonneg
    (hermiteEvenUnit (k : ℕ) - evenIndicatorCutoff a (hermiteEvenUnit (k : ℕ))))
    (Finset.mem_univ j)

theorem norm_hermiteEvenNegativeUnit_sub_cut_le_truncationSum
    (a : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    ‖hermiteEvenNegativeUnit (j : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (j : ℕ))‖
      ≤ hermiteNegativeTruncationSum a n := by
  exact Finset.single_le_sum (f := fun k : Fin (n + 1) =>
    ‖hermiteEvenNegativeUnit (k : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (k : ℕ))‖)
    (fun k _ => norm_nonneg
    (hermiteEvenNegativeUnit (k : ℕ) -
      evenIndicatorCutoff a (hermiteEvenNegativeUnit (k : ℕ))))
    (Finset.mem_univ j)

/-- At every fixed depth, the actual compressed Fourier quadratic form is eventually strictly
positive on the entire nonzero positive Hermite trial space. -/
theorem eventually_strictlyPositiveOn_hermiteTrialSpace (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ f : evenSubspace, f ∈ hermiteTrialSpace n → f ≠ 0 →
      0 < RCLike.re (inner ℂ (evenTimeBandFourier a f) f) := by
  let C : ℝ → ℝ := fun a =>
    ((n + 1 : ℕ) : ℝ) * (2 * hermitePositiveTruncationSum a n) ^ 2
  have hC : Tendsto C atTop (nhds 0) := by
    have hη := tendsto_hermitePositiveTruncationSum n
    have h2η : Tendsto (fun a : ℝ => 2 * hermitePositiveTruncationSum a n)
        atTop (nhds 0) := by simpa using hη.const_mul 2
    have hsq : Tendsto (fun a : ℝ => (2 * hermitePositiveTruncationSum a n) ^ 2)
        atTop (nhds 0) := by simpa using h2η.pow 2
    simpa [C] using hsq.const_mul (((n + 1 : ℕ) : ℝ))
  have hsmall : ∀ᶠ a : ℝ in atTop, C a < 1 := hC.eventually_lt_const one_pos
  filter_upwards [hsmall] with a ha f hf hf0
  have hsq := norm_sq_sub_timeBand_le_of_hermite_trial a n
    (fun j => norm_hermiteEvenUnit_sub_cut_le_truncationSum a n j) hf
  have hfnorm : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf0)
  have hdefectsq : ‖f - evenTimeBandFourier a f‖ ^ 2 < ‖f‖ ^ 2 := by
    refine hsq.trans_lt ?_
    change C a * ‖f‖ ^ 2 < ‖f‖ ^ 2
    nlinarith [mul_lt_mul_of_pos_right ha hfnorm]
  have hdefect : ‖f - evenTimeBandFourier a f‖ < ‖f‖ := by
    nlinarith [sq_nonneg ‖f - evenTimeBandFourier a f‖, sq_nonneg ‖f‖,
      norm_nonneg (f - evenTimeBandFourier a f), norm_nonneg f]
  have hneg := ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
    (-evenTimeBandFourier a) f (by
      rw [show (-evenTimeBandFourier a) f = -(evenTimeBandFourier a f) from rfl]
      simpa [sub_eq_add_neg] using hdefect)
  simpa using hneg

/-- At every fixed depth, the actual compressed Fourier quadratic form is eventually strictly
negative on the entire nonzero negative Hermite trial space. -/
theorem eventually_strictlyNegativeOn_hermiteNegativeTrialSpace (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, ∀ f : evenSubspace, f ∈ hermiteNegativeTrialSpace n → f ≠ 0 →
      RCLike.re (inner ℂ (evenTimeBandFourier a f) f) < 0 := by
  let C : ℝ → ℝ := fun a =>
    ((n + 1 : ℕ) : ℝ) * (2 * hermiteNegativeTruncationSum a n) ^ 2
  have hC : Tendsto C atTop (nhds 0) := by
    have hη := tendsto_hermiteNegativeTruncationSum n
    have h2η : Tendsto (fun a : ℝ => 2 * hermiteNegativeTruncationSum a n)
        atTop (nhds 0) := by simpa using hη.const_mul 2
    have hsq : Tendsto (fun a : ℝ => (2 * hermiteNegativeTruncationSum a n) ^ 2)
        atTop (nhds 0) := by simpa using h2η.pow 2
    simpa [C] using hsq.const_mul (((n + 1 : ℕ) : ℝ))
  have hsmall : ∀ᶠ a : ℝ in atTop, C a < 1 := hC.eventually_lt_const one_pos
  filter_upwards [hsmall] with a ha f hf hf0
  have hsq := norm_sq_add_timeBand_le_of_negative_hermite_trial a n
    (fun j => norm_hermiteEvenNegativeUnit_sub_cut_le_truncationSum a n j) hf
  have hfnorm : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf0)
  have hdefectsq : ‖f + evenTimeBandFourier a f‖ ^ 2 < ‖f‖ ^ 2 := by
    refine hsq.trans_lt ?_
    change C a * ‖f‖ ^ 2 < ‖f‖ ^ 2
    nlinarith [mul_lt_mul_of_pos_right ha hfnorm]
  have hdefect : ‖f + evenTimeBandFourier a f‖ < ‖f‖ := by
    nlinarith [sq_nonneg ‖f + evenTimeBandFourier a f‖, sq_nonneg ‖f‖,
      norm_nonneg (f + evenTimeBandFourier a f), norm_nonneg f]
  exact ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
    (evenTimeBandFourier a) f hdefect

/-- Each fixed positive Hermite mode becomes an approximate `+1` eigenvector. -/
theorem tendsto_norm_hermiteEvenUnit_sub_timeBand (j : ℕ) :
    Tendsto (fun a : ℝ =>
      ‖hermiteEvenUnit j - evenTimeBandFourier a (hermiteEvenUnit j)‖)
      atTop (nhds 0) := by
  have hbound : Tendsto (fun a : ℝ =>
      2 * ‖hermiteEvenUnit j - evenIndicatorCutoff a (hermiteEvenUnit j)‖)
      atTop (nhds 0) := by
    simpa using (tendsto_norm_sub_cut (hermiteEvenUnit j)).const_mul 2
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards with a
    exact norm_nonneg _
  · filter_upwards with a
    exact norm_hermiteEvenUnit_sub_timeBand_le a j

/-- The actual even prolate Fourier block has a positive signed eigenvalue at every sufficiently
large aperture. -/
theorem eventually_exists_evenProlateSignedValue_pos :
    ∀ᶠ a : ℝ in atTop, ∃ n : ℕ, 0 < evenProlateSignedValue a n := by
  have hsmall : ∀ᶠ a : ℝ in atTop,
      ‖hermiteEvenUnit 0 - evenTimeBandFourier a (hermiteEvenUnit 0)‖ < 1 :=
    (tendsto_norm_hermiteEvenUnit_sub_timeBand 0).eventually_lt_const one_pos
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with a ha hdefect
  have hquad : 0 < RCLike.re
      (inner ℂ (evenTimeBandFourier a (hermiteEvenUnit 0)) (hermiteEvenUnit 0)) := by
    have hneg := ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
      (-evenTimeBandFourier a) (hermiteEvenUnit 0) (by
        change ‖hermiteEvenUnit 0 - evenTimeBandFourier a (hermiteEvenUnit 0)‖ <
          ‖hermiteEvenUnit 0‖
        rw [norm_hermiteEvenUnit]
        exact hdefect)
    simpa using hneg
  exact ContinuousLinearMap.exists_sgVal_pos_of_re_inner_pos
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a)) hquad

/-- The actual even prolate Fourier block has a negative signed eigenvalue at every sufficiently
large aperture. -/
theorem eventually_exists_evenProlateSignedValue_neg :
    ∀ᶠ a : ℝ in atTop, ∃ n : ℕ, evenProlateSignedValue a n < 0 := by
  have hsmall : ∀ᶠ a : ℝ in atTop,
      ‖hermiteEvenNegativeUnit 0 +
        evenTimeBandFourier a (hermiteEvenNegativeUnit 0)‖ < 1 :=
    (tendsto_norm_hermiteEvenNegativeUnit_add_timeBand 0).eventually_lt_const one_pos
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with a ha hdefect
  have hquad : RCLike.re
      (inner ℂ (evenTimeBandFourier a (hermiteEvenNegativeUnit 0))
        (hermiteEvenNegativeUnit 0)) < 0 :=
    ContinuousLinearMap.re_inner_neg_of_norm_add_lt_norm
      (evenTimeBandFourier a) (hermiteEvenNegativeUnit 0) (by
        change ‖hermiteEvenNegativeUnit 0 +
          evenTimeBandFourier a (hermiteEvenNegativeUnit 0)‖ <
            ‖hermiteEvenNegativeUnit 0‖
        rw [norm_hermiteEvenNegativeUnit]
        exact hdefect)
  exact ContinuousLinearMap.exists_sgVal_neg_of_re_inner_neg
    (isCompactOperator_evenTimeBandFourier a ha)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (adjoint_evenTimeBandFourier a)) hquad

/-- Coarse Fourier-parity separation: for all sufficiently large apertures the true signed
prolate spectrum simultaneously contains positive and negative values. -/
theorem eventually_exists_positive_and_negative_evenProlateSignedValues :
    ∀ᶠ a : ℝ in atTop,
      (∃ n : ℕ, 0 < evenProlateSignedValue a n) ∧
        ∃ n : ℕ, evenProlateSignedValue a n < 0 :=
  eventually_exists_evenProlateSignedValue_pos.and
    eventually_exists_evenProlateSignedValue_neg

end RHTower

end
