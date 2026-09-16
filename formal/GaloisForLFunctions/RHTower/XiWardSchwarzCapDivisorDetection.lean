import GaloisForLFunctions.RHTower.XiWardSchwarzCapSourcePairing

/-!
# Canonical lower-cap detection of every right-half Xi zero

The source-defined transverse scan is not merely a convenient generic family.
It meets every centered Xi divisor point arising from a zero with real part
strictly greater than one half.  Thus a uniform lower-cap zero-free or
minimum-modulus shortcut would already be RH-bearing.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Every right-half Xi divisor point lies on the literal canonical lower cap
at the inverse transverse parameter. -/
theorem xiWardLowerCapPoint_eq_xiSpectralPoint_of_right
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re) :
    ∃ s : ℝ,
      xiWardLowerCapPoint s (xiSpectralPoint q).re = xiSpectralPoint q := by
  let a : ℝ := (q.1 : ℂ).re - 1 / 2
  have hqstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : a ∈ Set.Ioo (0 : ℝ) (1 / 2) := by
    dsimp [a]
    constructor <;> linarith [hqstrip.2]
  refine ⟨xiWardTransverseCoordinate a, ?_⟩
  apply Complex.ext
  · simp [xiWardLowerCapPoint]
  · rw [xiWardLowerCapPoint]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero]
    rw [xiWardTransverseLevel_coordinate ha, xiSpectralPoint_im_eq]
    dsimp [a]
    ring

/-- A right-half Xi zero produces a literal zero of `XiC` on the canonical
lower-cap foliation. -/
theorem xiWardLowerCap_hits_rightXiZeroCopy
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re) :
    ∃ s x : ℝ,
      XiC (xiWardLowerCapPoint s x) = 0 := by
  obtain ⟨s, hs⟩ := xiWardLowerCapPoint_eq_xiSpectralPoint_of_right q hq
  refine ⟨s, (xiSpectralPoint q).re, ?_⟩
  rw [hs]
  exact XiC_xiSpectralPoint_eq_zero q

/-- Premise-free packaged form: the canonical lower-cap foliation detects
every right-half Xi zero. -/
theorem xiWardLowerCap_detects_rightXiZeroCopies :
    ∀ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re →
      ∃ s x : ℝ, XiC (xiWardLowerCapPoint s x) = 0 := by
  intro q hq
  exact xiWardLowerCap_hits_rightXiZeroCopy q hq

end

end RHTower
