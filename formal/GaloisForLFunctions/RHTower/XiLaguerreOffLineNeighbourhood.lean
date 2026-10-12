import GaloisForLFunctions.RHTower.XiLaguerreZeroSumIdentity
import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivityConverse

/-!
# An off-line pair breaks the first Laguerre inequality on a whole neighbourhood of its ordinate

For a real height `t` with `ΞC(t) ≠ 0`, the second slice coefficient is the first Laguerre
expression (`xiSliceCoeff_two_eq_laguerre`):

  `c₂(t) = ΞC'(t)² − ΞC(t)·ΞC''(t) = ΞC(t)² · Σ_q (t − a_q)⁻²`.

A conjugate pair of zeros `a = γ ∓ δ i` contributes `2(u² − δ²)/(u² + δ²)²`, `u = t − γ`.  On the
neighbourhood `|u| ≤ |δ|/2` this is at most `−(24/25)/δ²` (`re_inv_sq_pair_le`), uniformly, and not
only at the ordinate `u = 0`.

**Theorem** (`laguerre_re_neg_near_offLine_pair`).  If `|t − γ| ≤ |δ|/2`, `ΞC(t) ≠ 0`, and the
remaining zero copies carry inverse-square mass `Σ 1/|t − a_q|² ≤ S` at `t` with `δ²S < 24/25`,
then `Re c₂(t) < 0`.

So the slice criterion fails at order one on the whole interval of heights `|t − γ| ≤ |δ|/2`
around an isolated off-line pair, not merely at its ordinate.  The visibility cone `|t − γ| < |δ|`
of the pair bounds the failure set from above.  This bound from below has the same size, so for
isolated pairs near the critical line the failure measure is `≍ δ`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The second slice coefficient is the first Laguerre expression.** -/
theorem xiSliceCoeff_two_eq_laguerre (t : ℝ) :
    xiSliceCoeff t 2 = deriv XiC t ^ 2 - XiC t * deriv (deriv XiC) t := by
  have hfun : xiSliceProduct t = fun x => XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x) := by
    funext x
    exact xiSliceProduct_eq_XiC t x
  have hD := XiC_differentiable
  have hD1 := XiC_differentiable.deriv
  have ha : ∀ x : ℂ, HasDerivAt (fun x : ℂ => (t : ℂ) - I * x) (-I) x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul I).const_sub (t : ℂ)
  have hb : ∀ x : ℂ, HasDerivAt (fun x : ℂ => (t : ℂ) + I * x) I x := fun x => by
    simpa using ((hasDerivAt_id x).const_mul I).const_add (t : ℂ)
  -- first derivative
  have h1 : ∀ x : ℂ, HasDerivAt (fun x => XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x))
      (-I * deriv XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x) +
        XiC ((t : ℂ) - I * x) * (I * deriv XiC ((t : ℂ) + I * x))) x := by
    intro x
    have hA := (hD ((t : ℂ) - I * x)).hasDerivAt.comp x (ha x)
    have hB := (hD ((t : ℂ) + I * x)).hasDerivAt.comp x (hb x)
    exact (hA.mul hB).congr_deriv (by simp only [Function.comp_apply]; ring)
  have hderiv : deriv (fun x => XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x)) =
      fun x => -I * deriv XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x) +
        XiC ((t : ℂ) - I * x) * (I * deriv XiC ((t : ℂ) + I * x)) := by
    funext x
    exact (h1 x).deriv
  -- second derivative at `0`
  have hA := (hD ((t : ℂ) - I * 0)).hasDerivAt.comp (0 : ℂ) (ha 0)
  have hB := (hD ((t : ℂ) + I * 0)).hasDerivAt.comp (0 : ℂ) (hb 0)
  have hA1 := (hD1 ((t : ℂ) - I * 0)).hasDerivAt.comp (0 : ℂ) (ha 0)
  have hB1 := (hD1 ((t : ℂ) + I * 0)).hasDerivAt.comp (0 : ℂ) (hb 0)
  have h2 : HasDerivAt (fun x => -I * deriv XiC ((t : ℂ) - I * x) * XiC ((t : ℂ) + I * x) +
        XiC ((t : ℂ) - I * x) * (I * deriv XiC ((t : ℂ) + I * x)))
      (2 * (deriv XiC t ^ 2 - XiC t * deriv (deriv XiC) t)) 0 := by
    have := ((hA1.const_mul (-I)).mul hB).add (hA.mul (hB1.const_mul I))
    refine this.congr_deriv ?_
    simp only [Function.comp_apply, mul_zero, sub_zero, add_zero]
    ring_nf
    rw [I_sq]
    ring
  rw [xiSliceCoeff, hfun, iteratedDeriv_succ, iteratedDeriv_one, hderiv, h2.deriv]
  norm_num [Nat.factorial]
  ring

/-- **The pair term near the ordinate.**  For `|t − γ| ≤ |δ|/2`, the contribution of the pair
`γ ∓ δ i` to the inverse-square sum at `t` has real part at most `−(24/25)/δ²`. -/
theorem re_inv_sq_pair_le {γ δ t : ℝ} (hδ : δ ≠ 0) (ht : |t - γ| ≤ |δ| / 2) :
    ((((t : ℂ) - ((γ : ℂ) - (δ : ℂ) * I)) ^ 2)⁻¹ + (((t : ℂ) - ((γ : ℂ) + (δ : ℂ) * I)) ^ 2)⁻¹).re
      ≤ -(24 / 25) / δ ^ 2 := by
  set u := t - γ with hu
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hden : 0 < u ^ 2 + δ ^ 2 := by positivity
  have hu2 : u ^ 2 ≤ δ ^ 2 / 4 := by
    have h0 : 0 ≤ |u| := abs_nonneg u
    have h := mul_self_le_mul_self h0 ht
    have e : |u| * |u| = u ^ 2 := by rw [← sq, sq_abs]
    have e' : |δ| / 2 * (|δ| / 2) = δ ^ 2 / 4 := by
      rw [show |δ| / 2 * (|δ| / 2) = |δ| ^ 2 / 4 by ring, sq_abs]
    linarith
  have e1 : (t : ℂ) - ((γ : ℂ) - (δ : ℂ) * I) = (u : ℂ) + (δ : ℂ) * I := by rw [hu]; push_cast; ring
  have e2 : (t : ℂ) - ((γ : ℂ) + (δ : ℂ) * I) = (u : ℂ) - (δ : ℂ) * I := by rw [hu]; push_cast; ring
  have hne : ∀ s : ℝ, s ≠ 0 → ((u : ℂ) + (s : ℂ) * I) ≠ 0 := by
    intro s hs h
    have := congrArg Complex.im h
    simp at this
    exact hs this
  have hne1 : ((u : ℂ) + (δ : ℂ) * I) ^ 2 ≠ 0 := pow_ne_zero _ (hne δ hδ)
  have hne2 : ((u : ℂ) - (δ : ℂ) * I) ^ 2 ≠ 0 := by
    have := hne (-δ) (neg_ne_zero.mpr hδ)
    refine pow_ne_zero _ ?_
    simpa [sub_eq_add_neg] using this
  have hmul : ((u : ℂ) + (δ : ℂ) * I) * ((u : ℂ) - (δ : ℂ) * I) = ((u ^ 2 + δ ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hsq : ((u : ℂ) + (δ : ℂ) * I) ^ 2 + ((u : ℂ) - (δ : ℂ) * I) ^ 2 =
      ((2 * (u ^ 2 - δ ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [I_sq]
    ring
  have hval : (((u : ℂ) + (δ : ℂ) * I) ^ 2)⁻¹ + (((u : ℂ) - (δ : ℂ) * I) ^ 2)⁻¹ =
      ((2 * (u ^ 2 - δ ^ 2) / (u ^ 2 + δ ^ 2) ^ 2 : ℝ) : ℂ) := by
    rw [inv_add_inv hne1 hne2, ← mul_pow, hmul, hsq]
    push_cast
    ring
  rw [e1, e2, hval, Complex.ofReal_re, div_le_div_iff₀ (by positivity) hδ2]
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ δ ^ 2 / 4 - u ^ 2) (sq_nonneg u),
    mul_nonneg (by linarith : (0 : ℝ) ≤ δ ^ 2 / 4 - u ^ 2) hδ2.le, sq_nonneg u]


/-- **The pair splits off the inverse-square sum at any point off the divisor.** -/
theorem tsum_inv_sq_split_pair {z : ℂ} (hz : XiC z ≠ 0) {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂) :
    ∑' q : XiZeroCopy, ((z - xiSpectralPoint q) ^ 2)⁻¹
      = ((z - xiSpectralPoint q₁) ^ 2)⁻¹ + ((z - xiSpectralPoint q₂) ^ 2)⁻¹
        + ∑' q : XiZeroCopy, (if q = q₁ ∨ q = q₂ then 0 else ((z - xiSpectralPoint q) ^ 2)⁻¹) := by
  classical
  have hs := summable_inv_sq_sub_xiSpectralPoint hz
  set f : XiZeroCopy → ℂ := fun q => ((z - xiSpectralPoint q) ^ 2)⁻¹ with hf
  set g : XiZeroCopy → ℂ := fun q => if q = q₁ then 0 else f q with hg
  have hg_summable : Summable g := by
    refine hs.congr_cofinite ?_
    filter_upwards [(Set.finite_singleton q₁).compl_mem_cofinite] with q hq
    have hq' : q ≠ q₁ := fun h => hq (by simp [h])
    simp [hg, hq']
  have step1 : ∑' q, f q = f q₁ + ∑' q, g q := hs.tsum_eq_add_tsum_ite q₁
  have step2 : ∑' q, g q = g q₂ + ∑' q, (if q = q₂ then 0 else g q) :=
    hg_summable.tsum_eq_add_tsum_ite q₂
  have hq21 : q₂ ≠ q₁ := fun h => h12 h.symm
  have hg2 : g q₂ = f q₂ := by simp [hg, hq21]
  have hrest : (fun q => if q = q₂ then 0 else g q)
      = fun q => if q = q₁ ∨ q = q₂ then 0 else f q := by
    funext q
    by_cases hq2 : q = q₂
    · simp [hq2]
    · by_cases hq1 : q = q₁
      · simp [hg, hq1]
      · simp [hg, hq1, hq2]
  rw [step1, step2, hg2, hrest]
  ring

/-- The inverse-square terms at `t` of the copies other than `q₁, q₂`. -/
def offPairInvSq (t : ℝ) (q₁ q₂ q : XiZeroCopy) : ℂ :=
  if q = q₁ ∨ q = q₂ then 0 else (((t : ℂ) - xiSpectralPoint q) ^ 2)⁻¹

theorem norm_offPairInvSq (t : ℝ) (q₁ q₂ q : XiZeroCopy) :
    ‖offPairInvSq t q₁ q₂ q‖ =
      if q = q₁ ∨ q = q₂ then 0 else 1 / ‖(t : ℂ) - xiSpectralPoint q‖ ^ 2 := by
  unfold offPairInvSq
  split_ifs
  · exact norm_zero
  · rw [norm_inv, norm_pow, one_div]

theorem summable_offPairInvSq {t : ℝ} (hXi : XiC (t : ℂ) ≠ 0) (q₁ q₂ : XiZeroCopy) :
    Summable (offPairInvSq t q₁ q₂) := by
  classical
  refine (summable_inv_sq_sub_xiSpectralPoint hXi).congr_cofinite ?_
  filter_upwards [((Set.finite_singleton q₁).union (Set.finite_singleton q₂)).compl_mem_cofinite]
    with q hq
  have hq' : ¬ (q = q₁ ∨ q = q₂) := fun h => hq (by rcases h with h | h <;> simp [h])
  simp only [offPairInvSq, if_neg hq']

/-- The remaining copies contribute at most their inverse-square mass. -/
theorem re_tsum_offPairInvSq_le {t : ℝ} (hXi : XiC (t : ℂ) ≠ 0) {q₁ q₂ : XiZeroCopy} {S : ℝ}
    (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, q ≠ q₁ ∧ q ≠ q₂) →
      ∑ q ∈ F, 1 / ‖(t : ℂ) - xiSpectralPoint q‖ ^ 2 ≤ S) :
    (∑' q, offPairInvSq t q₁ q₂ q).re ≤ S := by
  classical
  have hrs := summable_offPairInvSq hXi q₁ q₂
  have hre_s : Summable fun q => (offPairInvSq t q₁ q₂ q).re :=
    hrs.norm.of_norm_bounded fun q => Complex.abs_re_le_norm _
  have hbound : ∑' q, ‖offPairInvSq t q₁ q₂ q‖ ≤ S := by
    refine hrs.norm.tsum_le_of_sum_le fun F => ?_
    have hF := hS (F.filter fun q => ¬ (q = q₁ ∨ q = q₂)) (by
      intro q hq
      have h := (Finset.mem_filter.mp hq).2
      push Not at h
      exact h)
    have e : ∑ q ∈ F, ‖offPairInvSq t q₁ q₂ q‖ = ∑ q ∈ F.filter fun q => ¬ (q = q₁ ∨ q = q₂),
        1 / ‖(t : ℂ) - xiSpectralPoint q‖ ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [norm_offPairInvSq]
      by_cases hq : q = q₁ ∨ q = q₂
      · rw [if_pos hq, if_neg (not_not.mpr hq)]
      · rw [if_neg hq, if_pos hq]
    rw [e]
    exact hF
  calc (∑' q, offPairInvSq t q₁ q₂ q).re = ∑' q, (offPairInvSq t q₁ q₂ q).re :=
        Complex.re_tsum hrs
    _ ≤ ∑' q, ‖offPairInvSq t q₁ q₂ q‖ :=
        hre_s.tsum_le_tsum (fun q => Complex.re_le_norm _) hrs.norm
    _ ≤ S := hbound

/-- **First Laguerre failure on a neighbourhood of an off-line ordinate.**  Let `γ ∓ δ i` be two
distinct zero copies, `|t − γ| ≤ |δ|/2`, `ΞC(t) ≠ 0`, and let the remaining copies carry
inverse-square mass at most `S` at `t`, with `δ² S < 24/25`.  Then the first Laguerre expression,
which is the second slice coefficient, has negative real part at `t`. -/
theorem laguerre_re_neg_near_offLine_pair {γ δ t : ℝ} (hδ : δ ≠ 0)
    {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂)
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) - (δ : ℂ) * I)
    (h2 : xiSpectralPoint q₂ = (γ : ℂ) + (δ : ℂ) * I)
    (ht : |t - γ| ≤ |δ| / 2) (hXi : XiC (t : ℂ) ≠ 0) {S : ℝ}
    (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, q ≠ q₁ ∧ q ≠ q₂) →
      ∑ q ∈ F, 1 / ‖(t : ℂ) - xiSpectralPoint q‖ ^ 2 ≤ S)
    (hsmall : δ ^ 2 * S < 24 / 25) :
    (deriv XiC t ^ 2 - XiC t * deriv (deriv XiC) t).re < 0 := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hrest := re_tsum_offPairInvSq_le hXi hS
  have hpair := re_inv_sq_pair_le (γ := γ) (t := t) hδ ht
  rw [← h1, ← h2, Complex.add_re] at hpair
  have hsplit := tsum_inv_sq_split_pair hXi h12
  have hXi' : Xi t ≠ 0 := by
    intro h
    apply hXi
    rw [XiC_ofReal, h]
    simp
  have hpos : 0 < Xi t ^ 2 := by positivity
  have hS' : S < 24 / 25 / δ ^ 2 := by rw [lt_div_iff₀ hδ2]; linarith
  have hneg : (∑' q : XiZeroCopy, (((t : ℂ) - xiSpectralPoint q) ^ 2)⁻¹).re < 0 := by
    rw [hsplit, Complex.add_re, Complex.add_re]
    change _ + _ + (∑' q, offPairInvSq t q₁ q₂ q).re < 0
    have : -(24 / 25) / δ ^ 2 = -(24 / 25 / δ ^ 2) := by ring
    linarith
  rw [laguerre_XiC_eq_tsum_inv_sq hXi, XiC_ofReal]
  have hcast : ((Xi t : ℂ)) ^ 2 = ((Xi t ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg hpos hneg

/-- **Slice form.**  Under the same hypotheses the second slice coefficient is negative. -/
theorem xiSliceCoeff_two_re_neg_near_offLine_pair {γ δ t : ℝ} (hδ : δ ≠ 0)
    {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂)
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) - (δ : ℂ) * I)
    (h2 : xiSpectralPoint q₂ = (γ : ℂ) + (δ : ℂ) * I)
    (ht : |t - γ| ≤ |δ| / 2) (hXi : XiC (t : ℂ) ≠ 0) {S : ℝ}
    (hS : ∀ F : Finset XiZeroCopy, (∀ q ∈ F, q ≠ q₁ ∧ q ≠ q₂) →
      ∑ q ∈ F, 1 / ‖(t : ℂ) - xiSpectralPoint q‖ ^ 2 ≤ S)
    (hsmall : δ ^ 2 * S < 24 / 25) :
    (xiSliceCoeff t 2).re < 0 := by
  rw [xiSliceCoeff_two_eq_laguerre]
  exact laguerre_re_neg_near_offLine_pair hδ h12 h1 h2 ht hXi hS hsmall

end

end RHTower
