import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFixedSourceDefect
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalNonstationarySource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceRealBand

/-! The complete physical source identified with its fixed, absolutely convergent defect integral. -/
namespace RHTower.D4BMJointSource
open Complex Set
noncomputable section
set_option autoImplicit false

/-- The complete original source is the finite part of one fixed rational weight. -/
theorem physicalFundamentalSourceMoment_fixed_weight (q : XiZeroCopy) (a : ℂ) :
    fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a=
      2*a^(2 : ℕ)*nonstationaryMoment nonstationarySourceNumerator 8 (physicalFundamentalFrequency q true) := by
  have hs := physicalNonstationaryFrequency_strip q
  have hw := physicalFundamentalFrequency_strip q true
  have hw1 : physicalFundamentalFrequency q true+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hi
    exact hw.1 hi
  rw [physicalFundamentalSourceMoment_nonstationary,nonstationarySourceConstant,nonstationarySourceQuadratic,
    nonstationarySourceNumerator_moment _ (by linarith [hs.1]) hw1]

/-- Exact normalization: no finite part remains on the right, and the rational kernel is independent of q. -/
theorem physicalFundamentalSourceMoment_fixed_defect (q : XiZeroCopy) (a : ℂ) :
    (physicalFundamentalFrequency q true+1)*
      fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a=
      2*a^(2 : ℕ)*((86/625:ℂ)-nonstationarySourceDefect (physicalFundamentalFrequency q true)) := by
  have hs := physicalNonstationaryFrequency_strip q
  have hw := physicalFundamentalFrequency_strip q true
  have hw1 : physicalFundamentalFrequency q true+1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im] at hi
    exact hw.1 hi
  rw [physicalFundamentalSourceMoment_fixed_weight]
  calc
    _ = 2*a^(2 : ℕ)*((physicalFundamentalFrequency q true+1)*
        nonstationaryMoment nonstationarySourceNumerator 8 (physicalFundamentalFrequency q true)) := by ring
    _ = _ := by rw [nonstationarySourceNumerator_normalized _ (by linarith [hs.1]) hw1]

/-- Every nonzero original amplitude survives uniformly in an entire band of Xi heights. -/
theorem physicalFundamentalSourceMoment_low_height_ne_zero :
    ∃ h : ℝ, 0 < h ∧ ∀ q : XiZeroCopy, |(q.1:ℂ).im| ≤ h → ∀ a : ℂ, a ≠ 0 →
      fundamentalSourceMoment (physicalFundamentalFrequency q true) (D4BMModularCore.physicalRate q true) a ≠ 0 := by
  obtain ⟨δ,hδ,h⟩ := nonstationarySourceDefect_uniform_real_band
  refine ⟨2*δ,by positivity,?_⟩
  intro q hq a ha hm
  have hs := physicalNonstationaryFrequency_strip q
  have hi : |(physicalFundamentalFrequency q true).im| ≤ δ := by
    rw [physicalFundamentalFrequency_eq]
    norm_num [Complex.div_im,abs_div,abs_neg]
    linarith
  have hd := h _ ⟨hs.1.le,hs.2.le⟩ hi
  have he := physicalFundamentalSourceMoment_fixed_defect q a
  rw [hm,mul_zero] at he
  have hprod : 2*a^(2 : ℕ)*((86/625:ℂ)-nonstationarySourceDefect (physicalFundamentalFrequency q true)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) (sub_ne_zero.mpr hd.symm)
  exact hprod he.symm

end
end RHTower.D4BMJointSource
