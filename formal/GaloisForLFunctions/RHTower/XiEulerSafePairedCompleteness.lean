import GaloisForLFunctions.RHTower.XiCauchyTransformCompleteness
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# The orientation sector is complete on an absolute-Euler paired quadrant

Both poles of a Schwarz-paired Cauchy vector attached to a point of the open quadrant
`Re w > 1/2`, `Im w > 0` lie in the absolute Euler convergence region, so the pair is regular for
the Xi divisor.  Schwarz conjugation fixes the paired vector, and the real pairing of a fixed
fibre-constant vector against the pair is twice the real part of its Cauchy transform.

Vanishing of that real pairing on the whole quadrant therefore kills the Cauchy transform, hence
every multiplicity fibre sum, hence the vector itself.  No exterior threshold, high-frequency
cutoff, or low-frequency band is used.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- Centered spectral coordinate of an absolute-Euler pole. -/
def xiEulerCentered (w : ℂ) : ℂ := -Complex.I * w

theorem XiC_xiEulerCentered (w : ℂ) : XiC (xiEulerCentered w) = xi (1 / 2 + w) := by
  rw [XiC, xiEulerCentered]
  congr 1
  linear_combination (-w) * Complex.I_sq

theorem XiC_xiEulerCentered_ne_zero {w : ℂ} (hw : 1 / 2 < w.re) :
    XiC (xiEulerCentered w) ≠ 0 := by
  rw [XiC_xiEulerCentered]
  refine xi_ne_zero_of_one_lt_re ?_
  simp only [Complex.add_re, Complex.div_re]
  norm_num
  linarith

theorem xiEulerCentered_conj (w : ℂ) :
    xiEulerCentered ((starRingEnd ℂ) w) = -(starRingEnd ℂ) (xiEulerCentered w) := by
  rw [xiEulerCentered, xiEulerCentered]
  simp only [map_mul, map_neg, Complex.conj_I]
  ring

/-- **General Schwarz law for Cauchy vectors.**  Schwarz conjugation sends the Cauchy vector at a
regular pole to minus the Cauchy vector at the reflected pole. -/
theorem xiWeilSchwarzLp_cauchy (z : XiCRegularPoint)
    (hz : XiC (-(starRingEnd ℂ) (z : ℂ)) ≠ 0) :
    xiWeilSchwarzLp (xiWeilCauchyLp z) =
      -xiWeilCauchyLp ⟨-(starRingEnd ℂ) (z : ℂ), hz⟩ := by
  apply Subtype.ext
  funext q
  rw [xiWeilSchwarzLp_apply]
  change (starRingEnd ℂ) ((xiSpectralPoint (xiZeroCopyConjEquiv q) - (z : ℂ))⁻¹) =
    -((xiSpectralPoint q - (-(starRingEnd ℂ) (z : ℂ)))⁻¹)
  rw [xiSpectralPoint_copyConj]
  simp only [map_inv₀, map_sub, map_neg, Complex.conj_conj]
  rw [← inv_neg]
  congr 1
  ring

/-! ## The Schwarz-paired absolute-Euler vector -/

/-- The Schwarz-paired Cauchy vector of an absolute-Euler pole. -/
def xiEulerPairedCauchyLp (w : ℂ) (h₁ : XiC (xiEulerCentered w) ≠ 0)
    (h₂ : XiC (-(starRingEnd ℂ) (xiEulerCentered w)) ≠ 0) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilCauchyLp ⟨xiEulerCentered w, h₁⟩ -
    xiWeilCauchyLp ⟨-(starRingEnd ℂ) (xiEulerCentered w), h₂⟩

/-- **The paired vector is Schwarz fixed.** -/
theorem xiWeilSchwarzLp_eulerPaired (w : ℂ) (h₁ : XiC (xiEulerCentered w) ≠ 0)
    (h₂ : XiC (-(starRingEnd ℂ) (xiEulerCentered w)) ≠ 0) :
    xiWeilSchwarzLp (xiEulerPairedCauchyLp w h₁ h₂) = xiEulerPairedCauchyLp w h₁ h₂ := by
  have hrefl : -(starRingEnd ℂ) (-(starRingEnd ℂ) (xiEulerCentered w)) =
      xiEulerCentered w := by
    simp
  have h1 := xiWeilSchwarzLp_cauchy ⟨xiEulerCentered w, h₁⟩ h₂
  have h2 := xiWeilSchwarzLp_cauchy ⟨-(starRingEnd ℂ) (xiEulerCentered w), h₂⟩
    (by rw [hrefl]; exact h₁)
  rw [xiEulerPairedCauchyLp, xiWeilSchwarzLp_sub, h1, h2]
  have hcast : (⟨-(starRingEnd ℂ) (-(starRingEnd ℂ) (xiEulerCentered w)),
      (by rw [hrefl]; exact h₁ : XiC (-(starRingEnd ℂ) (-(starRingEnd ℂ)
        (xiEulerCentered w))) ≠ 0)⟩ : XiCRegularPoint) =
      ⟨xiEulerCentered w, h₁⟩ := by
    apply Subtype.ext
    exact hrefl
  rw [hcast]
  abel

/-! ## Real pairing against a Schwarz-fixed vector -/

theorem inner_schwarzFixed_reflectedCauchy {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hv : xiWeilSchwarzLp v = v) (z : XiCRegularPoint)
    (hz : XiC (-(starRingEnd ℂ) (z : ℂ)) ≠ 0) :
    inner ℂ v (xiWeilCauchyLp ⟨-(starRingEnd ℂ) (z : ℂ), hz⟩) =
      -inner ℂ (xiWeilCauchyLp z) v := by
  have hJ := xiWeilSchwarzLp_cauchy z hz
  have hcoord : ∀ q : XiZeroCopy,
      (xiWeilCauchyLp ⟨-(starRingEnd ℂ) (z : ℂ), hz⟩ : XiZeroCopy → ℂ) q =
        -(starRingEnd ℂ) ((xiWeilCauchyLp z : XiZeroCopy → ℂ) (xiZeroCopyConjEquiv q)) := by
    intro q
    have h := congrArg (fun x : lp (fun _ : XiZeroCopy => ℂ) 2 =>
      (x : XiZeroCopy → ℂ) q) hJ
    simp only [xiWeilSchwarzLp_apply] at h
    have hneg : ((-xiWeilCauchyLp ⟨-(starRingEnd ℂ) (z : ℂ), hz⟩ :
        lp (fun _ : XiZeroCopy => ℂ) 2) : XiZeroCopy → ℂ) q =
        -((xiWeilCauchyLp ⟨-(starRingEnd ℂ) (z : ℂ), hz⟩ :
          lp (fun _ : XiZeroCopy => ℂ) 2) : XiZeroCopy → ℂ) q := Complex.ext rfl rfl
    rw [hneg] at h
    linear_combination h
  have hvcoord : ∀ q : XiZeroCopy,
      (starRingEnd ℂ) ((v : XiZeroCopy → ℂ) q) =
        (v : XiZeroCopy → ℂ) (xiZeroCopyConjEquiv q) := by
    intro q
    have h := congrArg (fun x : lp (fun _ : XiZeroCopy => ℂ) 2 =>
      (x : XiZeroCopy → ℂ) q) hv
    simp only [xiWeilSchwarzLp_apply] at h
    rw [← h]
    simp
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, ← tsum_neg]
  rw [← (xiZeroCopyConjEquiv).tsum_eq (fun q : XiZeroCopy =>
    -(inner ℂ ((xiWeilCauchyLp z : XiZeroCopy → ℂ) q) ((v : XiZeroCopy → ℂ) q)))]
  refine tsum_congr (fun q => ?_)
  rw [hcoord q]
  simp only [RCLike.inner_apply]
  rw [← hvcoord q]
  ring

theorem XiC_neg_conj_xiEulerCentered_ne_zero {w : ℂ} (hw : 1 / 2 < w.re) :
    XiC (-(starRingEnd ℂ) (xiEulerCentered w)) ≠ 0 := by
  have hval : -(starRingEnd ℂ) (xiEulerCentered w) = xiEulerCentered ((starRingEnd ℂ) w) := by
    rw [xiEulerCentered_conj]
  rw [hval]
  refine XiC_xiEulerCentered_ne_zero ?_
  simpa using hw

/-- The real pairing of a Schwarz-fixed vector against the paired Cauchy vector is twice the real
part of its Cauchy transform. -/
theorem re_inner_eulerPaired {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hv : xiWeilSchwarzLp v = v) (w : ℂ) (h₁ : XiC (xiEulerCentered w) ≠ 0)
    (h₂ : XiC (-(starRingEnd ℂ) (xiEulerCentered w)) ≠ 0) :
    (inner ℂ v (xiEulerPairedCauchyLp w h₁ h₂)).re =
      2 * (xiCauchyTransform v (xiEulerCentered w)).re := by
  have hsplit : inner ℂ v (xiEulerPairedCauchyLp w h₁ h₂) =
      inner ℂ v (xiWeilCauchyLp ⟨xiEulerCentered w, h₁⟩) -
        inner ℂ v (xiWeilCauchyLp ⟨-(starRingEnd ℂ) (xiEulerCentered w), h₂⟩) := by
    rw [xiEulerPairedCauchyLp, inner_sub_right]
  rw [hsplit, inner_schwarzFixed_reflectedCauchy hv ⟨xiEulerCentered w, h₁⟩ h₂,
    sub_neg_eq_add, xiCauchyTransform_eq_inner v ⟨xiEulerCentered w, h₁⟩]
  have hsym : (inner ℂ (xiWeilCauchyLp ⟨xiEulerCentered w, h₁⟩) v).re =
      (inner ℂ v (xiWeilCauchyLp ⟨xiEulerCentered w, h₁⟩)).re := by
    rw [← inner_conj_symm v (xiWeilCauchyLp ⟨xiEulerCentered w, h₁⟩), Complex.conj_re]
  simp only [Complex.add_re]
  rw [hsym]
  ring

/-- Fibre-constant divisor vectors. -/
def XiFiberConstant (v : lp (fun _ : XiZeroCopy => ℂ) 2) : Prop :=
  ∀ q q' : XiZeroCopy, q.1 = q'.1 → (v : XiZeroCopy → ℂ) q = (v : XiZeroCopy → ℂ) q'

theorem eq_zero_of_fiberConstant_of_fiberSum_eq_zero
    {v : lp (fun _ : XiZeroCopy => ℂ) 2} (hfib : XiFiberConstant v)
    (hsum : ∀ ρ : XiDivisorSupport, xiWeilFiberSum (fun q => (v : XiZeroCopy → ℂ) q) ρ = 0) :
    v = 0 := by
  apply lp.ext
  funext q
  have h := hsum q.1
  rw [xiWeilFiberSum] at h
  have hconst : ∀ q' ∈ xiZeroCopyFiber q.1, (v : XiZeroCopy → ℂ) q' =
      (v : XiZeroCopy → ℂ) q := by
    intro q' hq'
    exact hfib q' q (by rw [mem_xiZeroCopyFiber.mp hq'])
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_xiZeroCopyFiber, nsmul_eq_mul] at h
  have hpos : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) ((q.1 : ℂ))) := by
    have := xi_divisor_pos_on_support q.1
    omega
  have hne : ((Int.toNat ((MeromorphicOn.divisor xi Set.univ) ((q.1 : ℂ))) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have := (mul_eq_zero.mp h).resolve_left hne
  simpa using this

/-- **Absolute-Euler paired completeness.**  A Schwarz-fixed fibre-constant divisor vector whose
real pairing against every absolute-Euler paired Cauchy vector vanishes is zero. -/
theorem eq_zero_of_re_inner_eulerPaired_eq_zero
    {v : lp (fun _ : XiZeroCopy => ℂ) 2}
    (hv : xiWeilSchwarzLp v = v) (hfib : XiFiberConstant v)
    (h : ∀ (w : ℂ) (hw1 : 1 / 2 < w.re) (_hw2 : 0 < w.im),
      (inner ℂ v (xiEulerPairedCauchyLp w (XiC_xiEulerCentered_ne_zero hw1)
        (XiC_neg_conj_xiEulerCentered_ne_zero hw1))).re = 0) :
    v = 0 := by
  set z₀ : ℂ := 1 - Complex.I with hz₀
  have hquad : ∀ z ∈ ball z₀ (1 / 4 : ℝ),
      1 / 2 < (Complex.I * z).re ∧ 0 < (Complex.I * z).im := by
    intro z hz
    rw [mem_ball, Complex.dist_eq] at hz
    have hre : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    have him : |(z - z₀).im| ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
    have hre' : |z.re - 1| < 1 / 4 := by
      have : (z - z₀).re = z.re - 1 := by rw [hz₀]; simp
      rw [this] at hre; linarith
    have him' : |z.im + 1| < 1 / 4 := by
      have : (z - z₀).im = z.im + 1 := by rw [hz₀]; simp
      rw [this] at him; linarith
    rw [abs_lt] at hre' him'
    constructor
    · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
      linarith [him'.2]
    · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul]
      linarith [hre'.1]
  have hcentered : ∀ z ∈ ball z₀ (1 / 4 : ℝ), xiEulerCentered (Complex.I * z) = z := by
    intro z _
    rw [xiEulerCentered]
    linear_combination (-z) * Complex.I_sq
  have hballfree : ball z₀ (1 / 4 : ℝ) ⊆ {z : ℂ | XiC z ≠ 0} := by
    intro z hz
    obtain ⟨hq1, _⟩ := hquad z hz
    have := XiC_xiEulerCentered_ne_zero hq1
    rwa [hcentered z hz] at this
  have hre : ∀ z ∈ ball z₀ (1 / 4 : ℝ), (xiCauchyTransform v z).re = 0 := by
    intro z hz
    obtain ⟨hq1, hq2⟩ := hquad z hz
    have hval := h (Complex.I * z) hq1 hq2
    rw [re_inner_eulerPaired hv] at hval
    rw [hcentered z hz] at hval
    linarith
  refine eq_zero_of_fiberConstant_of_fiberSum_eq_zero hfib (fun ρ => ?_)
  exact xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball v
    (by norm_num) hballfree hre ρ

end

end RHTower
