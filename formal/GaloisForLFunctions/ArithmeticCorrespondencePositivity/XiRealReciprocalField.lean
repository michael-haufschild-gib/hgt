import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiTerminalOutwardLogDeriv
import GaloisForLFunctions.RHTower.XiWindowZeroCount
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinBufferedTail
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.XiLocalZeroDensity

/-!
# The real reciprocal field of the Xi divisor

The real part of a reciprocal zero term has inverse-square decay in the
ordinate. This permits absolute summation and local passage to a zero after
removing its multiplicity fibre.
-/

open Finset Filter Set RHTower
open scoped Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- Real reciprocal contribution of a zero copy at a horizontal shift. -/
def xiRealReciprocal (z : ℂ) (h : ℝ) (q : XiZeroCopy) : ℝ :=
  (((z + (h : ℂ)) - (q.1 : ℂ))⁻¹).re

/-- A distant zero contributes at most an inverse-square ordinate weight,
uniformly for horizontal shifts of size at most one. -/
theorem xiRealReciprocal_tail_bound (z : ℂ) {h : ℝ} (hh : |h| ≤ 1)
    (q : XiZeroCopy) (hfar : 2 * |z.im| + 1 < |(q.1 : ℂ).im|) :
    ‖xiRealReciprocal z h q‖ ≤
      (4 * (|z.re| + 2)) * (1 / |(q.1 : ℂ).im| ^ 2) := by
  have htri := abs_add_le ((q.1 : ℂ).im - z.im) z.im
  have heq : ((q.1 : ℂ).im - z.im) + z.im = (q.1 : ℂ).im := by ring
  rw [heq] at htri
  have hhalf : |(q.1 : ℂ).im| / 2 ≤ |z.im - (q.1 : ℂ).im| := by
    rw [abs_sub_comm]
    linarith only [htri, hfar]
  have hsq : (q.1 : ℂ).im ^ 2 / 4 ≤ (z.im - (q.1 : ℂ).im) ^ 2 := by
    have hp := mul_nonneg
      (show 0 ≤ |z.im - (q.1 : ℂ).im| - |(q.1 : ℂ).im| / 2 by linarith only [hhalf])
      (show 0 ≤ |z.im - (q.1 : ℂ).im| + |(q.1 : ℂ).im| / 2 by positivity)
    nlinarith only [hp, sq_abs (z.im - (q.1 : ℂ).im), sq_abs (q.1 : ℂ).im]
  have hqpos : 0 < |(q.1 : ℂ).im| := by linarith [abs_nonneg z.im]
  have hq2 : 0 < (q.1 : ℂ).im ^ 2 := by
    have hp := mul_pos hqpos hqpos
    nlinarith only [hp, sq_abs (q.1 : ℂ).im]
  have hq0 : (q.1 : ℂ).im ≠ 0 := by
    intro hz
    rw [hz] at hq2
    norm_num at hq2
  have hden : (q.1 : ℂ).im ^ 2 / 4 ≤
      Complex.normSq ((z + (h : ℂ)) - (q.1 : ℂ)) := by
    rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.sub_im, Complex.add_im, Complex.ofReal_im, add_zero]
    nlinarith only [hsq, sq_nonneg (z.re + h - (q.1 : ℂ).re)]
  have hden0 : 0 < Complex.normSq ((z + (h : ℂ)) - (q.1 : ℂ)) :=
    lt_of_lt_of_le (by positivity) hden
  have hnum : |((z + (h : ℂ)) - (q.1 : ℂ)).re| ≤ |z.re| + 2 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    have hqre := xi_divisor_support_re_mem_open_unit q.1
    have hzre := abs_le.mp (le_refl |z.re|)
    have hh' := abs_le.mp hh
    rw [abs_le]
    constructor <;> linarith only [hqre.1, hqre.2, hzre.1, hzre.2, hh'.1, hh'.2]
  unfold xiRealReciprocal
  rw [Complex.inv_re, Real.norm_eq_abs, abs_div, abs_of_pos hden0]
  calc
    _ ≤ (|z.re| + 2) / Complex.normSq ((z + (h : ℂ)) - (q.1 : ℂ)) :=
      div_le_div_of_nonneg_right hnum hden0.le
    _ ≤ (|z.re| + 2) / ((q.1 : ℂ).im ^ 2 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      rw [sq_abs]
      field_simp [hq0]

/-- The real reciprocal field is absolutely summable at every bounded
horizontal shift, with multiplicity copies included. -/
theorem xiRealReciprocal_summable (z : ℂ) {h : ℝ} (hh : |h| ≤ 1) :
    Summable (xiRealReciprocal z h) := by
  let R : ℝ := 2 * |z.im| + 1
  have hfinite : (xiOrdinateWindow R 0).Finite := finite_xiOrdinateWindow R 0
  have hmajor : Summable (fun q : XiZeroCopy =>
      (4 * (|z.re| + 2)) * (1 / |(q.1 : ℂ).im| ^ 2)) :=
    RHTower.Sieve.summable_xiZeroCopy_one_div_abs_im_sq.mul_left _
  refine Summable.of_norm_bounded_eventually hmajor ?_
  filter_upwards [hfinite.compl_mem_cofinite] with q hq
  have hn : ¬ |(q.1 : ℂ).im - 0| ≤ R := by
    intro hle
    exact hq (mem_xiOrdinateWindow_iff.mpr hle)
  have hfar : 2 * |z.im| + 1 < |(q.1 : ℂ).im| := by
    have ht := lt_of_not_ge hn
    simpa only [R, sub_zero] using ht
  exact xiRealReciprocal_tail_bound z hh q hfar

/-- The absolute values of the real reciprocal terms are summable. -/
theorem xiRealReciprocal_norm_summable (z : ℂ) {h : ℝ} (hh : |h| ≤ 1) :
    Summable (fun q : XiZeroCopy => ‖xiRealReciprocal z h q‖) :=
  (xiRealReciprocal_summable z hh).norm

/-- At a zero the totalized own-fibre terms are zero and the remaining
terms are the usual real reciprocal field. -/
theorem xiRealReciprocal_zero_eq (p q : XiZeroCopy) :
    xiRealReciprocal (p.1 : ℂ) 0 q =
      ((p.1 : ℂ).re - (q.1 : ℂ).re) / ‖(p.1 : ℂ) - (q.1 : ℂ)‖ ^ 2 := by
  simp [xiRealReciprocal, Complex.inv_re, Complex.normSq_eq_norm_sq]

/-- The centered real reciprocal terms are absolutely summable. -/
theorem xiCenteredReciprocal_summable :
    Summable (fun q : XiZeroCopy => (((q.1 : ℂ) - 1 / 2)⁻¹).re) := by
  have hsum := xiRealReciprocal_summable (1 / 2 : ℂ) (h := 0) (by norm_num)
  refine hsum.neg.congr ?_
  intro q
  have hcenter : (1 / 2 : ℂ) - (q.1 : ℂ) = -((q.1 : ℂ) - 1 / 2) := by ring
  simp only [xiRealReciprocal, Complex.ofReal_zero, add_zero, hcenter,
    inv_neg, Complex.neg_re, neg_neg]

/-- Functional-equation reflection cancels the centered real reciprocal sum. -/
theorem xiCenteredReciprocal_tsum_eq_zero :
    (∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹).re) = 0 := by
  let f : XiZeroCopy → ℝ := fun q => (((q.1 : ℂ) - 1 / 2)⁻¹).re
  have hreflect : ∀ q : XiZeroCopy, f (xiZeroCopyReflectEquiv q) = -f q := by
    intro q
    have hcenter : ((xiZeroCopyReflectEquiv q).1 : ℂ) - 1 / 2 =
        -((q.1 : ℂ) - 1 / 2) := by
      rw [xiZeroCopyReflect_coe]
      ring
    dsimp only [f]
    rw [hcenter, inv_neg, Complex.neg_re]
  have hsum : (∑' q : XiZeroCopy, f q) = -(∑' q : XiZeroCopy, f q) := by
    calc
      _ = ∑' q : XiZeroCopy, f (xiZeroCopyReflectEquiv q) :=
        (xiZeroCopyReflectEquiv.tsum_eq f).symm
      _ = ∑' q : XiZeroCopy, -f q := tsum_congr hreflect
      _ = _ := tsum_neg
  change (∑' q : XiZeroCopy, f q) = 0
  linarith only [hsum]

/-- Away from the Xi divisor, the real logarithmic derivative is exactly
the absolutely convergent real reciprocal field. -/
theorem re_logDeriv_xi_eq_realReciprocal_tsum {s : ℂ} (hs : xi s ≠ 0) :
    (logDeriv xi s).re = ∑' q : XiZeroCopy, xiRealReciprocal s 0 q := by
  have hbase := xiCenteredReciprocal_summable
  have hrec := xiRealReciprocal_summable s (h := 0) (by norm_num)
  rw [re_logDeriv_xi_eq_tsum hs]
  calc
    _ = ∑' q : XiZeroCopy, ((((q.1 : ℂ) - 1 / 2)⁻¹).re +
        xiRealReciprocal s 0 q) := by
      apply tsum_congr
      intro q
      simp [xiPartialFractionTerm, xiRealReciprocal]
    _ = (∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹).re) +
        ∑' q : XiZeroCopy, xiRealReciprocal s 0 q := hbase.tsum_add hrec
    _ = _ := by rw [xiCenteredReciprocal_tsum_eq_zero, zero_add]

/-- Real reciprocal field with the complete multiplicity fibre at `p` removed. -/
def xiRealAwayReciprocal (p : XiZeroCopy) (h : ℝ) (q : XiZeroCopy) : ℝ := by
  classical
  exact if q ∈ xiZeroCopyFiber p.1 then 0 else xiRealReciprocal (p.1 : ℂ) h q

/-- At zero shift the removed fibre already contributes zero. -/
theorem xiRealAwayReciprocal_zero (p q : XiZeroCopy) :
    xiRealAwayReciprocal p 0 q = xiRealReciprocal (p.1 : ℂ) 0 q := by
  classical
  by_cases hq : q ∈ xiZeroCopyFiber p.1
  · have hpoint := xiZeroCopyFiber_point p q hq
    simp [xiRealAwayReciprocal, xiRealReciprocal, hq, hpoint]
  · simp [xiRealAwayReciprocal, hq]

/-- Removing one fibre preserves summability of the real field. -/
theorem xiRealAwayReciprocal_summable (p : XiZeroCopy) {h : ℝ} (hh : |h| ≤ 1) :
    Summable (xiRealAwayReciprocal p h) := by
  classical
  have hsum := (xiRealReciprocal_summable (p.1 : ℂ) hh).norm
  refine Summable.of_norm_bounded hsum ?_
  intro q
  by_cases hq : q ∈ xiZeroCopyFiber p.1
  · simp [xiRealAwayReciprocal, hq]
  · simp [xiRealAwayReciprocal, hq]

/-- Each deflated reciprocal term is continuous along the outward ray. -/
theorem xiRealAwayReciprocal_tendsto (p q : XiZeroCopy) :
    Tendsto (fun h : ℝ => xiRealAwayReciprocal p h q) (𝓝[>] (0 : ℝ))
      (𝓝 (xiRealAwayReciprocal p 0 q)) := by
  classical
  by_cases hq : q ∈ xiZeroCopyFiber p.1
  · simpa only [xiRealAwayReciprocal, if_pos hq] using
      (tendsto_const_nhds (x := (0 : ℝ)))
  · have hpq : (p.1 : ℂ) ≠ (q.1 : ℂ) := by
      intro heq
      apply hq
      apply mem_xiZeroCopyFiber.mpr
      apply Subtype.ext
      exact heq.symm
    have hden : (p.1 : ℂ) - (q.1 : ℂ) ≠ 0 := sub_ne_zero.mpr hpq
    have hf : ContinuousAt (fun h : ℝ => (p.1 : ℂ) + (h : ℂ) - (q.1 : ℂ)) 0 := by
      fun_prop
    have hf0 : (fun h : ℝ => (p.1 : ℂ) + (h : ℂ) - (q.1 : ℂ)) 0 ≠ 0 := by
      simpa using hden
    have hinv := hf.inv₀ hf0
    have hcont : ContinuousAt (fun h : ℝ => ((((p.1 : ℂ) + (h : ℂ)) - (q.1 : ℂ))⁻¹).re) 0 :=
      Complex.continuous_re.continuousAt.comp hinv
    have ht : Tendsto (fun h : ℝ => ((((p.1 : ℂ) + (h : ℂ)) - (q.1 : ℂ))⁻¹).re)
        (𝓝[>] (0 : ℝ)) (𝓝 ((((p.1 : ℂ) + (0 : ℂ)) - (q.1 : ℂ))⁻¹).re) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [xiRealAwayReciprocal, if_neg hq, xiRealReciprocal,
      Complex.ofReal_zero, add_zero] using ht

/-- The deflated field converges to the reciprocal field at the zero. A
finite ordinate window is handled termwise; its complement has a uniform
inverse-square majorant. -/
theorem xiRealAwayReciprocal_tsum_tendsto (p : XiZeroCopy) :
    Tendsto (fun h : ℝ => ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' q : XiZeroCopy, xiRealReciprocal (p.1 : ℂ) 0 q)) := by
  classical
  let R : ℝ := 2 * |(p.1 : ℂ).im| + 1
  let F : Finset XiZeroCopy := (finite_xiOrdinateWindow R 0).toFinset
  let K : ℝ := 4 * (|(p.1 : ℂ).re| + 2)
  have hfar (q : {q : XiZeroCopy // q ∉ F}) :
      2 * |(p.1 : ℂ).im| + 1 < |((q.1 : XiZeroCopy).1 : ℂ).im| := by
    have hn : ¬ |((q.1 : XiZeroCopy).1 : ℂ).im - 0| ≤ R := by
      intro hle
      have hmem : (q.1 : XiZeroCopy) ∈ xiOrdinateWindow R 0 :=
        mem_xiOrdinateWindow_iff.mpr hle
      apply q.2
      exact (Set.Finite.mem_toFinset (finite_xiOrdinateWindow R 0)).mpr hmem
    have ht := lt_of_not_ge hn
    simpa only [R, sub_zero] using ht
  have hmajor : Summable (fun q : {q : XiZeroCopy // q ∉ F} =>
      K * (1 / |((q.1 : XiZeroCopy).1 : ℂ).im| ^ 2)) :=
    (RHTower.Sieve.summable_xiZeroCopy_one_div_abs_im_sq.mul_left K).subtype _
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), |h| ≤ 1 := by
    have hlt : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), h < 1 :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin, hlt] with h hpos hlt'
    change 0 < h at hpos
    rw [abs_of_pos hpos]
    exact le_of_lt hlt'
  have hdom : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      ∀ q : {q : XiZeroCopy // q ∉ F}, ‖xiRealAwayReciprocal p h q.1‖ ≤
        K * (1 / |((q.1 : XiZeroCopy).1 : ℂ).im| ^ 2) := by
    filter_upwards [hsmall] with h hh q
    have hb := xiRealReciprocal_tail_bound (p.1 : ℂ) hh q.1 (hfar q)
    by_cases hq : q.1 ∈ xiZeroCopyFiber p.1
    · dsimp only [xiRealAwayReciprocal]
      rw [if_pos hq]
      have hnonneg : 0 ≤ K * (1 / |((q.1 : XiZeroCopy).1 : ℂ).im| ^ 2) := by
        dsimp only [K]
        positivity
      simpa using hnonneg
    · simpa only [xiRealAwayReciprocal, if_neg hq, K] using hb
  have htail : Tendsto
      (fun h : ℝ => ∑' q : {q : XiZeroCopy // q ∉ F}, xiRealAwayReciprocal p h q.1)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∑' q : {q : XiZeroCopy // q ∉ F}, xiRealAwayReciprocal p 0 q.1)) :=
    tendsto_tsum_of_dominated_convergence hmajor
      (fun q => xiRealAwayReciprocal_tendsto p q.1) hdom
  have hnear : Tendsto (fun h : ℝ => ∑ q ∈ F, xiRealAwayReciprocal p h q)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ q ∈ F, xiRealAwayReciprocal p 0 q)) :=
    tendsto_finsetSum F (fun q _ => xiRealAwayReciprocal_tendsto p q)
  have hsum0 : Summable (xiRealAwayReciprocal p 0) :=
    xiRealAwayReciprocal_summable p (h := 0) (by norm_num)
  have hlim : (∑ q ∈ F, xiRealAwayReciprocal p 0 q) +
      (∑' q : {q : XiZeroCopy // q ∉ F}, xiRealAwayReciprocal p 0 q.1) =
        ∑' q : XiZeroCopy, xiRealReciprocal (p.1 : ℂ) 0 q := by
    rw [hsum0.sum_add_tsum_subtype_compl F]
    exact tsum_congr (xiRealAwayReciprocal_zero p)
  have hcombined := hnear.add htail
  rw [hlim] at hcombined
  have hsplit : (fun h : ℝ => (∑ q ∈ F, xiRealAwayReciprocal p h q) +
      (∑' q : {q : XiZeroCopy // q ∉ F}, xiRealAwayReciprocal p h q.1))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun h : ℝ => ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q) := by
    filter_upwards [hsmall] with h hh
    exact (xiRealAwayReciprocal_summable p hh).sum_add_tsum_subtype_compl F
  exact Filter.Tendsto.congr' hsplit hcombined

/-- Away from the divisor, subtracting the principal fibre leaves exactly
the sum of the deflated real reciprocal terms. -/
theorem re_logDeriv_xi_sub_fiber_eq_away_tsum (p : XiZeroCopy) {h : ℝ}
    (hh : |h| ≤ 1) (hxi : xi ((p.1 : ℂ) + (h : ℂ)) ≠ 0) :
    (logDeriv xi ((p.1 : ℂ) + (h : ℂ))).re -
        ((xiZeroCopyFiber p.1).card : ℝ) / h =
      ∑' q : XiZeroCopy, xiRealAwayReciprocal p h q := by
  classical
  let A : Finset XiZeroCopy := xiZeroCopyFiber p.1
  have hfull := xiRealReciprocal_summable (p.1 : ℂ) hh
  have haway := xiRealAwayReciprocal_summable p hh
  have hzero : (∑ q ∈ A, xiRealAwayReciprocal p h q) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hq' : q ∈ xiZeroCopyFiber p.1 := by simpa only [A] using hq
    simp only [xiRealAwayReciprocal, if_pos hq']
  have htail : (∑' q : {q : XiZeroCopy // q ∉ A}, xiRealAwayReciprocal p h q.1) =
      ∑' q : {q : XiZeroCopy // q ∉ A}, xiRealReciprocal (p.1 : ℂ) h q.1 := by
    apply tsum_congr
    intro q
    have hq : q.1 ∉ xiZeroCopyFiber p.1 := by simpa only [A] using q.2
    simp only [xiRealAwayReciprocal, if_neg hq]
  have haway' : (∑' q : XiZeroCopy, xiRealAwayReciprocal p h q) =
      ∑' q : {q : XiZeroCopy // q ∉ A}, xiRealReciprocal (p.1 : ℂ) h q.1 := by
    have hs := haway.sum_add_tsum_subtype_compl A
    rw [hzero, zero_add, htail] at hs
    exact hs.symm
  have hfirst : (∑ q ∈ A, xiRealReciprocal (p.1 : ℂ) h q) = (A.card : ℝ) / h := by
    calc
      _ = ∑ _q ∈ A, 1 / h := by
        apply Finset.sum_congr rfl
        intro q hq
        have hpoint := xiZeroCopyFiber_point p q (by simpa only [A] using hq)
        have hsub : (p.1 : ℂ) + (h : ℂ) - (q.1 : ℂ) = (h : ℂ) := by
          rw [hpoint]
          ring
        rw [xiRealReciprocal, hsub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hfull' := hfull.sum_add_tsum_subtype_compl A
  rw [hfirst] at hfull'
  have hre := re_logDeriv_xi_eq_realReciprocal_tsum hxi
  have hshift : (∑' q : XiZeroCopy,
      xiRealReciprocal ((p.1 : ℂ) + (h : ℂ)) 0 q) =
      ∑' q : XiZeroCopy, xiRealReciprocal (p.1 : ℂ) h q := by
    apply tsum_congr
    intro q
    simp only [xiRealReciprocal, Complex.ofReal_zero, add_zero]
  rw [hshift] at hre
  change (logDeriv xi ((p.1 : ℂ) + (h : ℂ))).re - (A.card : ℝ) / h = _
  linarith only [hre, hfull', haway']

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
