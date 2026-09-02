import GaloisForLFunctions.RHTower.XiHadamardGrowth
import GaloisForLFunctions.RHTower.CanonicalProductE1LogDeriv

/-!
# The Laguerre expression of `Ξ` as an inverse-square sum over its zeros

For the centered completed zeta function `ΞC` (an even entire function of order one with the
unconditional Hadamard product `ΞC = ΞC(0) · ∏_q E₁(z / a_q)` over the multiplicity copies `q` of
its zeros `a_q`), the first Laguerre expression satisfies, at every non-zero `z`,

`ΞC'(z)² − ΞC(z)·ΞC''(z) = ΞC(z)² · ∑_q (z − a_q)⁻²`.

The proof differentiates the Mittag-Leffler expansion of the logarithmic derivative term by term:
on a small disc around `z` the terms `(w − a_q)⁻¹ + a_q⁻¹ = w / (a_q (w − a_q))` are bounded by a
summable family, so the derivative of the sum is the sum of the derivatives.

At a real point `γ` the identity exhibits the contribution of a conjugate pair of zeros
`γ ∓ δ i`: it is `−2/δ²`, negative and singular as the pair approaches the real axis, while every
real zero contributes a positive term.  Consequently, wherever the first Laguerre inequality holds
at `γ`, the remaining zeros must supply at least `2/δ²`.
-/

open Complex Filter Topology Metric

namespace RHTower

noncomputable section

/-- One Mittag-Leffler term of the logarithmic derivative of the Xi canonical product. -/
def xiMittagLefflerTerm (q : XiZeroCopy) (w : ℂ) : ℂ :=
  (w - xiSpectralPoint q)⁻¹ + (xiSpectralPoint q)⁻¹

theorem xiMittagLefflerTerm_eq (q : XiZeroCopy) {w : ℂ} (hw : w ≠ xiSpectralPoint q) :
    xiMittagLefflerTerm q w = w / (xiSpectralPoint q * (w - xiSpectralPoint q)) := by
  have h1 : w - xiSpectralPoint q ≠ 0 := sub_ne_zero.mpr hw
  have h2 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  rw [xiMittagLefflerTerm]
  field_simp
  ring

/-- A point off the divisor is distinct from every spectral point. -/
theorem xiSpectralPoint_ne_of_XiC_ne_zero' {z : ℂ} (hz : XiC z ≠ 0) (q : XiZeroCopy) :
    z ≠ xiSpectralPoint q :=
  fun h => hz (h ▸ XiC_xiSpectralPoint_eq_zero q)

/-- Off the divisor, the logarithmic derivative of `ΞC` is the Mittag-Leffler sum. -/
theorem logDeriv_XiC_eq_tsum {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv XiC z = ∑' q : XiZeroCopy, xiMittagLefflerTerm q z := by
  have hfun : XiC = fun w => XiC 0 * xiCanonicalProduct w := by
    funext w
    exact congrFun XiC_eq_constant_mul_canonicalProduct w
  rw [hfun, logDeriv_const_mul _ _ XiC_zero_ne, xiCanonicalProduct]
  exact logDeriv_canonicalProductE1Indexed xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable (xiSpectralPoint_ne_of_XiC_ne_zero' hz)

/-- The derivative of one Mittag-Leffler term. -/
theorem hasDerivAt_xiMittagLefflerTerm (q : XiZeroCopy) {w : ℂ} (hw : w ≠ xiSpectralPoint q) :
    HasDerivAt (xiMittagLefflerTerm q) (-((w - xiSpectralPoint q) ^ 2)⁻¹) w := by
  have hd : HasDerivAt (fun u : ℂ => u - xiSpectralPoint q) 1 w :=
    (hasDerivAt_id w).sub_const _
  have hinv := (hd.inv (sub_ne_zero.mpr hw)).add_const (xiSpectralPoint q)⁻¹
  have hrw : -(1 : ℂ) / (w - xiSpectralPoint q) ^ 2 = -((w - xiSpectralPoint q) ^ 2)⁻¹ := by
    rw [neg_div, one_div]
  rw [hrw] at hinv
  exact hinv

/-- **Termwise differentiation of the Mittag-Leffler sum.**  At a point off the divisor the
derivative of the logarithmic derivative of `ΞC` is minus the inverse-square sum over the zeros,
and that sum converges. -/
theorem hasSum_neg_inv_sq_deriv_logDeriv_XiC {z : ℂ} (hz : XiC z ≠ 0) :
    HasSum (fun q : XiZeroCopy => -((z - xiSpectralPoint q) ^ 2)⁻¹) (deriv (logDeriv XiC) z) := by
  classical
  -- the open set where `ΞC` does not vanish, and a disc around `z` inside it
  have hUopen : IsOpen {w : ℂ | XiC w ≠ 0} :=
    isOpen_ne_fun XiC_differentiable.continuous continuous_const
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hUopen z hz
  set R : ℝ := ‖z‖ + d / 2 with hRdef
  have hRpos : 0 < R := by positivity
  have hd2 : 0 < d / 2 := by positivity
  -- every spectral point is at distance at least `d` from `z`
  have hfar : ∀ q : XiZeroCopy, d ≤ ‖z - xiSpectralPoint q‖ := by
    intro q
    by_contra hlt
    push Not at hlt
    have hmem : xiSpectralPoint q ∈ ball z d := by
      rw [mem_ball, dist_eq_norm, norm_sub_rev]
      exact hlt
    exact hball hmem (XiC_xiSpectralPoint_eq_zero q)
  -- the finitely many small spectral points
  have hcof : ∀ᶠ q in cofinite, 2 * R ≤ ‖xiSpectralPoint q‖ :=
    eventually_norm_ge_of_summable_inv_sq xiSpectralPoint_ne_zero
      xiSpectralPoint_inv_sq_summable (by positivity)
  have hfin : {q : XiZeroCopy | ‖xiSpectralPoint q‖ < 2 * R}.Finite := by
    have := Filter.eventually_cofinite.mp hcof
    exact this.subset fun q hq => by
      simp only [Set.mem_setOf_eq] at hq ⊢
      exact not_le.mpr hq
  -- the summable majorant
  set u : XiZeroCopy → ℝ := fun q =>
    2 * R * (1 / ‖xiSpectralPoint q‖ ^ 2)
      + (if ‖xiSpectralPoint q‖ < 2 * R then 2 * R / (d / 2 * ‖xiSpectralPoint q‖) else 0)
    with hudef
  have hu : Summable u := by
    refine (xiSpectralPoint_inv_sq_summable.mul_left (2 * R)).add ?_
    refine summable_of_ne_finset_zero (s := hfin.toFinset) fun q hq => ?_
    have hq' : ¬ ‖xiSpectralPoint q‖ < 2 * R := by
      intro h
      exact hq (hfin.mem_toFinset.mpr h)
    simp [hq']
  -- every point of the disc of radius `d/2` is at distance at least `d/2` from every spectral point
  have hdist : ∀ q : XiZeroCopy, ∀ w ∈ ball z (d / 2), d / 2 ≤ ‖w - xiSpectralPoint q‖ := by
    intro q w hw
    have hwz : ‖w - z‖ < d / 2 := by
      rw [mem_ball, dist_eq_norm] at hw
      exact hw
    have h1 := hfar q
    have h2 := norm_sub_le_norm_sub_add_norm_sub z w (xiSpectralPoint q)
    rw [norm_sub_rev z w] at h2
    linarith
  -- the bound on the disc of radius `d/2`
  have hbound : ∀ q : XiZeroCopy, ∀ w ∈ ball z (d / 2), ‖xiMittagLefflerTerm q w‖ ≤ u q := by
    intro q w hw
    have hwz : ‖w - z‖ < d / 2 := by
      rw [mem_ball, dist_eq_norm] at hw
      exact hw
    have hwR : ‖w‖ ≤ R := by
      have := norm_sub_le_norm_sub_add_norm_sub w z 0
      simp only [sub_zero] at this
      rw [hRdef]
      linarith
    have haq : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    have hwq : d / 2 ≤ ‖w - xiSpectralPoint q‖ := hdist q w hw
    have hwq0 : w ≠ xiSpectralPoint q := by
      intro h
      rw [h, sub_self, norm_zero] at hwq
      linarith
    have hwqpos : 0 < ‖w - xiSpectralPoint q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwq0)
    rw [xiMittagLefflerTerm_eq q hwq0, norm_div, norm_mul]
    rw [div_le_iff₀ (mul_pos haq hwqpos)]
    by_cases hsmall : ‖xiSpectralPoint q‖ < 2 * R
    · -- small spectral point: use the disc distance
      have hu' : u q = 2 * R * (1 / ‖xiSpectralPoint q‖ ^ 2)
          + 2 * R / (d / 2 * ‖xiSpectralPoint q‖) := by simp [hudef, hsmall]
      rw [hu']
      have hA : 0 ≤ 2 * R * (1 / ‖xiSpectralPoint q‖ ^ 2) * (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖) := by
        positivity
      have hB : ‖w‖ ≤ 2 * R / (d / 2 * ‖xiSpectralPoint q‖) * (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        calc ‖w‖ * (d / 2 * ‖xiSpectralPoint q‖)
            ≤ R * (‖w - xiSpectralPoint q‖ * ‖xiSpectralPoint q‖) := by
              have := mul_le_mul hwR hwq (by positivity) hRpos.le
              nlinarith [haq]
          _ = 2 * R * (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖) / 2 := by ring
          _ ≤ 2 * R * (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖) := by
              have : 0 ≤ 2 * R * (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖) := by positivity
              linarith
      nlinarith [hA, hB]
    · -- large spectral point: `‖w − a‖ ≥ ‖a‖ / 2`
      push Not at hsmall
      have hu' : u q = 2 * R * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        have : ¬ ‖xiSpectralPoint q‖ < 2 * R := not_lt.mpr hsmall
        simp [hudef, this]
      rw [hu']
      have hhalf : ‖xiSpectralPoint q‖ / 2 ≤ ‖w - xiSpectralPoint q‖ := by
        have := norm_sub_norm_le (xiSpectralPoint q) w
        rw [norm_sub_rev] at this
        linarith
      rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      calc ‖w‖ * ‖xiSpectralPoint q‖ ^ 2
          ≤ R * ‖xiSpectralPoint q‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hwR (by positivity)
        _ = 2 * R * (‖xiSpectralPoint q‖ * (‖xiSpectralPoint q‖ / 2)) := by ring
        _ ≤ 2 * R * (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hhalf haq.le
  -- differentiability of the terms on the disc
  have hdiff : ∀ q : XiZeroCopy, DifferentiableOn ℂ (xiMittagLefflerTerm q) (ball z (d / 2)) := by
    intro q w hw
    have hwq : w ≠ xiSpectralPoint q := by
      intro h
      have := hdist q w hw
      rw [h, sub_self, norm_zero] at this
      linarith
    exact (hasDerivAt_xiMittagLefflerTerm q hwq).differentiableAt.differentiableWithinAt
  have hzball : z ∈ ball z (d / 2) := mem_ball_self hd2
  have hsum := hasSum_deriv_of_summable_norm hu hdiff isOpen_ball hbound hzball
  -- identify the derivative of the sum with the derivative of `logDeriv ΞC`
  have hev : logDeriv XiC =ᶠ[𝓝 z] fun w => ∑' q : XiZeroCopy, xiMittagLefflerTerm q w := by
    filter_upwards [isOpen_ball.mem_nhds hzball] with w hw
    have hw' : XiC w ≠ 0 := hball (ball_subset_ball (by linarith) hw)
    exact logDeriv_XiC_eq_tsum hw'
  rw [hev.deriv_eq]
  refine hsum.congr_fun fun q => ?_
  exact (hasDerivAt_xiMittagLefflerTerm q (xiSpectralPoint_ne_of_XiC_ne_zero' hz q)).deriv.symm

/-- The inverse-square sum over the zeros converges at every point off the divisor. -/
theorem summable_inv_sq_sub_xiSpectralPoint {z : ℂ} (hz : XiC z ≠ 0) :
    Summable (fun q : XiZeroCopy => ((z - xiSpectralPoint q) ^ 2)⁻¹) :=
  (hasSum_neg_inv_sq_deriv_logDeriv_XiC hz).summable.neg.congr fun q => by simp

/-- **The Laguerre identity for `ΞC`.**  Off the divisor,
`ΞC'(z)² − ΞC(z)·ΞC''(z) = ΞC(z)² · ∑_q (z − a_q)⁻²`. -/
theorem laguerre_XiC_eq_tsum_inv_sq {z : ℂ} (hz : XiC z ≠ 0) :
    deriv XiC z ^ 2 - XiC z * deriv (deriv XiC) z
      = XiC z ^ 2 * ∑' q : XiZeroCopy, ((z - xiSpectralPoint q) ^ 2)⁻¹ := by
  have hsum := hasSum_neg_inv_sq_deriv_logDeriv_XiC hz
  have htsum : deriv (logDeriv XiC) z
      = -∑' q : XiZeroCopy, ((z - xiSpectralPoint q) ^ 2)⁻¹ := by
    rw [← hsum.tsum_eq, tsum_neg]
  have hdXi : DifferentiableAt ℂ XiC z := XiC_differentiable z
  have hddXi : DifferentiableAt ℂ (deriv XiC) z :=
    ((XiC_differentiable.analyticAt z).deriv).differentiableAt
  have hlog : logDeriv XiC = deriv XiC / XiC := by
    funext w
    rfl
  have hderiv : deriv (logDeriv XiC) z
      = (deriv (deriv XiC) z * XiC z - deriv XiC z * deriv XiC z) / XiC z ^ 2 := by
    rw [hlog]
    exact deriv_div hddXi hdXi hz
  rw [hderiv] at htsum
  have hsq : XiC z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h := (div_eq_iff hsq).mp htsum
  linear_combination -h

/-- **The contribution of a conjugate pair.**  If `γ ∓ δ i` are zeros (as two distinct
multiplicity copies) and `ΞC(γ) ≠ 0`, the inverse-square sum at the real point `γ` is
`−2/δ²` plus the sum over the remaining copies. -/
theorem tsum_inv_sq_sub_xiSpectralPoint_pair {γ δ : ℝ} (hδ : δ ≠ 0)
    {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂)
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) - (δ : ℂ) * I)
    (h2 : xiSpectralPoint q₂ = (γ : ℂ) + (δ : ℂ) * I)
    (hγ : XiC (γ : ℂ) ≠ 0) :
    ∑' q : XiZeroCopy, (((γ : ℂ) - xiSpectralPoint q) ^ 2)⁻¹
      = -(2 / (δ : ℂ) ^ 2)
        + ∑' q : XiZeroCopy,
            (if q = q₁ ∨ q = q₂ then 0 else (((γ : ℂ) - xiSpectralPoint q) ^ 2)⁻¹) := by
  classical
  have hs := summable_inv_sq_sub_xiSpectralPoint hγ
  set f : XiZeroCopy → ℂ := fun q => (((γ : ℂ) - xiSpectralPoint q) ^ 2)⁻¹ with hf
  set g : XiZeroCopy → ℂ := fun q => if q = q₁ then 0 else f q with hg
  have hg_summable : Summable g := by
    refine hs.congr_cofinite ?_
    have hfin : ({q₁} : Set XiZeroCopy).Finite := Set.finite_singleton q₁
    filter_upwards [hfin.compl_mem_cofinite] with q hq
    have hq' : q ≠ q₁ := fun h => hq (by simp [h])
    simp [hg, hq']
  have step1 : ∑' q, f q = f q₁ + ∑' q, g q := hs.tsum_eq_add_tsum_ite q₁
  have step2 : ∑' q, g q = g q₂ + ∑' q, (if q = q₂ then 0 else g q) :=
    hg_summable.tsum_eq_add_tsum_ite q₂
  have hg2 : g q₂ = f q₂ := by
    have : q₂ ≠ q₁ := fun h => h12 h.symm
    simp [hg, this]
  have hrest : (fun q => if q = q₂ then 0 else g q)
      = fun q => if q = q₁ ∨ q = q₂ then 0 else f q := by
    funext q
    by_cases hq2 : q = q₂
    · simp [hq2]
    · by_cases hq1 : q = q₁
      · simp [hg, hq1]
      · simp [hg, hq1, hq2]
  have hpair : f q₁ + f q₂ = -(2 / (δ : ℂ) ^ 2) := by
    have hδ' : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ
    have hsq1 : ((γ : ℂ) - xiSpectralPoint q₁) ^ 2 = -(δ : ℂ) ^ 2 := by
      rw [h1]
      ring_nf
      rw [I_sq]
      ring
    have hsq2 : ((γ : ℂ) - xiSpectralPoint q₂) ^ 2 = -(δ : ℂ) ^ 2 := by
      rw [h2]
      ring_nf
      rw [I_sq]
      ring
    simp only [hf, hsq1, hsq2]
    field_simp
    ring
  calc ∑' q, f q = f q₁ + (g q₂ + ∑' q, (if q = q₂ then 0 else g q)) := by rw [step1, step2]
    _ = (f q₁ + f q₂) + ∑' q, (if q = q₁ ∨ q = q₂ then 0 else f q) := by
        rw [hg2, hrest]; ring
    _ = -(2 / (δ : ℂ) ^ 2) + ∑' q, (if q = q₁ ∨ q = q₂ then 0 else f q) := by rw [hpair]

/-- **Real form at a real point.**  With `ΞC(γ) = Ξ(γ)` real, the real part of the Laguerre
expression at `γ` is `Ξ(γ)²` times `−2/δ²` plus the real part of the remaining inverse-square
sum. -/
theorem laguerre_XiC_re_pair {γ δ : ℝ} (hδ : δ ≠ 0)
    {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂)
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) - (δ : ℂ) * I)
    (h2 : xiSpectralPoint q₂ = (γ : ℂ) + (δ : ℂ) * I)
    (hγ : XiC (γ : ℂ) ≠ 0) :
    (deriv XiC γ ^ 2 - XiC γ * deriv (deriv XiC) γ).re
      = Xi γ ^ 2 * (-(2 / δ ^ 2)
          + (∑' q : XiZeroCopy,
              (if q = q₁ ∨ q = q₂ then 0 else (((γ : ℂ) - xiSpectralPoint q) ^ 2)⁻¹)).re) := by
  rw [laguerre_XiC_eq_tsum_inv_sq hγ, tsum_inv_sq_sub_xiSpectralPoint_pair hδ h12 h1 h2 hγ,
    XiC_ofReal]
  have hcast : ((Xi γ : ℂ)) ^ 2 = ((Xi γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.re_ofReal_mul, Complex.add_re, Complex.neg_re]
  congr 2
  have : (2 / (δ : ℂ) ^ 2) = ((2 / δ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_re]

/-- **The inner band.**  Wherever the first Laguerre inequality holds at a real point `γ` with
`Ξ(γ) ≠ 0`, a conjugate pair of zeros `γ ∓ δ i` forces the remaining zeros to contribute at
least `2/δ²` to the inverse-square sum at `γ`. -/
theorem two_div_sq_le_of_laguerre_nonneg {γ δ : ℝ} (hδ : δ ≠ 0)
    {q₁ q₂ : XiZeroCopy} (h12 : q₁ ≠ q₂)
    (h1 : xiSpectralPoint q₁ = (γ : ℂ) - (δ : ℂ) * I)
    (h2 : xiSpectralPoint q₂ = (γ : ℂ) + (δ : ℂ) * I)
    (hγ : XiC (γ : ℂ) ≠ 0)
    (hL : 0 ≤ (deriv XiC γ ^ 2 - XiC γ * deriv (deriv XiC) γ).re) :
    2 / δ ^ 2 ≤ (∑' q : XiZeroCopy,
        (if q = q₁ ∨ q = q₂ then 0 else (((γ : ℂ) - xiSpectralPoint q) ^ 2)⁻¹)).re := by
  rw [laguerre_XiC_re_pair hδ h12 h1 h2 hγ] at hL
  have hXi : Xi γ ≠ 0 := by
    intro h
    apply hγ
    rw [XiC_ofReal, h]
    simp
  have hpos : 0 < Xi γ ^ 2 := by positivity
  have := nonneg_of_mul_nonneg_right hL hpos
  linarith

end

end RHTower
