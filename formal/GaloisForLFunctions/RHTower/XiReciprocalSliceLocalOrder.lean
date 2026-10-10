import GaloisForLFunctions.RHTower.XiReciprocalSliceCriterion
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion

/-!
# RH from reciprocal total positivity of local order

At a height `t` with `Ξ(t) ≠ 0` let `F_t = xiSliceLift t`, so `F_t(−σ²) = Ξ(t+σ)Ξ(t−σ)` and every
zero `z` of `Ξ` gives the zero `−(z−t)²` of `F_t`.  Let `xiSliceLocalCount t` be the number of
zeros of `F_t`, with multiplicity, in the disk `‖y‖ ≤ 1/4`.  These are the zeros of `Ξ` within
distance `1/2` of `t`.

**Theorem** (`riemannHypothesis_iff_forall_reciprocalTPUpTo_localCount`).  RH holds iff for every
height `t` with `Ξ(t) ≠ 0`, the reciprocal slice coefficients at `t` are nonnegative and their
consecutive-row minors of order `≤ xiSliceLocalCount t` are nonnegative.

So total positivity of unbounded order at one height (`riemannHypothesis_iff_reciprocalTP_xiSliceLift`)
trades for total positivity of local order at every height.

* `⟹`: RH gives full reciprocal total positivity at every such height.
* `⟸`: let `z` be a non-real zero.  Then `|Im z| < 1/2`, so some `t` near `Re z` with `Ξ(t) ≠ 0`
  has `|z − t| ≤ 1/2`.  The zero `−(z−t)²` of `F_t` is not a negative real.  Its disk lies in
  `‖y‖ ≤ 1/4`, which contradicts finite-order zero location
  (`ReciprocalTPUpTo.eq_neg_of_apply_eq_zero`).
-/

open Complex Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The number of zeros, with multiplicity, of the slice lift `F_t` in the disk `‖y‖ ≤ 1/4`. -/
def xiSliceLocalCount (t : ℝ) : ℕ :=
  ∑ᶠ y ∈ closedBall (0 : ℂ) (1 / 4), analyticOrderNatAt (xiSliceLift t) y

theorem xiSliceLift_zero_ne_zero {t : ℝ} (ht : XiC t ≠ 0) : xiSliceLift t 0 ≠ 0 := by
  have h := xiSliceLift_neg_sq t 0
  rw [show -((0 : ℂ) ^ 2) = 0 by ring] at h
  rw [h]
  unfold xiHorizontalPair
  simpa using mul_ne_zero ht ht

/-- The local count as a finite sum over the zeros in the disk. -/
theorem xiSliceLocalCount_eq_sum {t : ℝ} (ht : XiC t ≠ 0) :
    xiSliceLocalCount t = ∑ y ∈ (zeros_finite_closedBall (differentiable_xiSliceLift t)
      (xiSliceLift_zero_ne_zero ht) (1 / 4)).toFinset, analyticOrderNatAt (xiSliceLift t) y := by
  unfold xiSliceLocalCount
  refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
  ext y
  simp only [Set.mem_inter_iff, Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hy, hord⟩
    refine ⟨⟨hy, ?_⟩, hord⟩
    by_contra hne
    exact hord (by
      simp [analyticOrderNatAt,
        ((differentiable_xiSliceLift t).analyticAt y).analyticOrderAt_eq_zero.mpr hne])
  · rintro ⟨⟨hy, _⟩, hord⟩
    exact ⟨hy, hord⟩

/-- **Reciprocal total positivity of local order at every height implies RH.** -/
theorem riemannHypothesis_of_forall_reciprocalTPUpTo_localCount
    (h : ∀ t : ℝ, XiC t ≠ 0 → ReciprocalTPUpTo (xiSliceLocalCount t) (xiSliceLift t)) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  intro z hz
  by_contra hne
  obtain ⟨him1, him2⟩ := xiC_zero_im_mem_openHalf hz
  -- a nearby real height with `Ξ(t) ≠ 0`
  set ε : ℝ := Real.sqrt (1 / 4 - z.im ^ 2) with hεdef
  have hε : 0 < ε := Real.sqrt_pos.mpr (by nlinarith)
  have hεsq : ε ^ 2 = 1 / 4 - z.im ^ 2 := Real.sq_sqrt (by nlinarith)
  have hXi0 : XiC 0 ≠ 0 := by
    have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by simp [XiC]
    rw [this]
    exact xi_ne_zero_of_real _
  have hfinXi := zeros_finite_closedBall XiC_differentiable hXi0 (|z.re| + 1)
  have hfinR : ((fun x : ℝ => (x : ℂ)) ⁻¹' {w ∈ closedBall (0 : ℂ) (|z.re| + 1) | XiC w = 0}).Finite :=
    hfinXi.preimage (Complex.ofReal_injective.injOn)
  obtain ⟨t, ⟨htl, htr⟩, htnot⟩ :=
    ((Set.Ioo_infinite (by linarith [lt_min hε one_pos] :
      z.re - min ε 1 < z.re + min ε 1)).sdiff hfinR).nonempty
  have hmin1 : min ε 1 ≤ 1 := min_le_right _ _
  have hminε : min ε 1 ≤ ε := min_le_left _ _
  have ht : XiC t ≠ 0 := by
    intro h0
    apply htnot
    refine ⟨?_, h0⟩
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have := neg_abs_le z.re
    have := le_abs_self z.re
    constructor <;> linarith
  -- the zero `−(z−t)²` of `F_t`
  have hzero : xiSliceLift t (-((z - t) ^ 2)) = 0 := by
    rw [xiSliceLift_neg_sq]
    unfold xiHorizontalPair
    rw [show (t : ℂ) + (z - t) = z by ring, hz, zero_mul]
  have hdist : |z.re - t| ≤ ε := by
    rw [abs_le]
    constructor <;> linarith
  have hnorm : ‖-((z - t) ^ 2)‖ ≤ 1 / 4 := by
    rw [norm_neg, norm_pow, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    have hsq : (z.re - t) ^ 2 ≤ ε ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hdist 2
    nlinarith
  obtain ⟨D, hD, hDeq⟩ := (h t ht).eq_neg_of_apply_eq_zero hzero
    (S := (zeros_finite_closedBall (differentiable_xiSliceLift t)
      (xiSliceLift_zero_ne_zero ht) (1 / 4)).toFinset)
    (fun y hy hy0 => by
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, mem_closedBall, dist_zero_right]
      exact ⟨hy.trans hnorm, hy0⟩)
    (xiSliceLocalCount_eq_sum ht).symm.le
  have ht2 : (z - t) ^ 2 = (D : ℂ) := by linear_combination -hDeq
  have him := congrArg Complex.im ht2
  have hre := congrArg Complex.re ht2
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, sub_zero] at him hre
  have hre0 : z.re - t = 0 := by
    have : 2 * (z.re - t) * z.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hne
  rw [hre0] at hre
  nlinarith [sq_nonneg z.im]

/-- **RH is reciprocal total positivity of local order at every height.** -/
theorem riemannHypothesis_iff_forall_reciprocalTPUpTo_localCount :
    RiemannHypothesis ↔
      ∀ t : ℝ, XiC t ≠ 0 → ReciprocalTPUpTo (xiSliceLocalCount t) (xiSliceLift t) :=
  ⟨fun hRH _ ht => ((riemannHypothesis_iff_reciprocalTP_xiSliceLift ht).mp hRH).upTo _,
    riemannHypothesis_of_forall_reciprocalTPUpTo_localCount⟩

end

end RHTower
