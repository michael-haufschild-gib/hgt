import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion
import GaloisForLFunctions.RHTower.XiWeilResolventSource
import GaloisForLFunctions.RHTower.SeamStripRamification

/-!
# The explicit two-pole CCM source form

The Xi-Weil square of a regular two-pole Cauchy packet is exactly a four-term
divided-difference form in the meromorphically continued prime--archimedean
relative trace.  This is the source-side form on which the remaining CCM
positivity problem lives.
-/

open Complex

namespace RHTower

noncomputable section

/-- The continued prime--archimedean divided-difference kernel. -/
def ccmContinuedCauchyKernel (z w : ℂ) : ℂ :=
  (continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) w) -
    continuedPrimeArchSourceRelativeTrace z) /
      (z - (starRingEnd ℂ) w)

/-- The explicit rank-two CCM source energy. -/
def ccmTwoPoleSourceEnergy (z w a b : ℂ) : ℂ :=
  a * (starRingEnd ℂ) a * ccmContinuedCauchyKernel z z +
  a * (starRingEnd ℂ) b * ccmContinuedCauchyKernel z w +
  b * (starRingEnd ℂ) a * ccmContinuedCauchyKernel w z +
  b * (starRingEnd ℂ) b * ccmContinuedCauchyKernel w w

def ccmTwoPoleCoeff (z : ℂ) (a b : ℂ) (u : ℂ) : ℂ :=
  if u = z then a else b

/-- Natural pole-free domain for both a pole and its reflected source point. -/
def CCMContinuedCauchyDomain (z : ℂ) : Prop :=
  0 < (1 / 2 + z * I).re ∧
  1 / 2 + z * I ≠ 1 ∧
  riemannZeta (1 / 2 + z * I) ≠ 0 ∧
  0 < (1 / 2 + (starRingEnd ℂ) z * I).re ∧
  1 / 2 + (starRingEnd ℂ) z * I ≠ 1 ∧
  riemannZeta (1 / 2 + (starRingEnd ℂ) z * I) ≠ 0

/-- Schwarz reality in the centered Xi coordinate. -/
theorem XiC_conj (z : ℂ) :
    XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (XiC z) := by
  rw [XiC, XiC]
  have harg : 1 / 2 + (starRingEnd ℂ) z * I =
      1 - (starRingEnd ℂ) (1 / 2 + z * I) := by
    apply Complex.ext <;> simp <;> ring
  rw [harg, xi_one_sub, xi_conj]

/-- A regular point with the same imaginary centered coordinate as an actual Xi
divisor point belongs to the full continued source domain.  Real pole motion
therefore preserves both open-strip source evaluations. -/
theorem ccmContinuedCauchyDomain_of_regular_same_spectral_im
    (q : XiZeroCopy) {z : ℂ} (hz : XiC z ≠ 0)
    (him : z.im = (xiSpectralPoint q).im) :
    CCMContinuedCauchyDomain z := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hsre : (1 / 2 + z * I).re = (q.1 : ℂ).re := by
    simp [xiSpectralPoint] at him ⊢
    linarith
  have htsre : (1 / 2 + (starRingEnd ℂ) z * I).re = 1 - (q.1 : ℂ).re := by
    simp [xiSpectralPoint] at him ⊢
    linarith
  have hs0 : 0 < (1 / 2 + z * I).re := hsre.symm ▸ hstrip.1
  have hs1 : (1 / 2 + z * I).re < 1 := hsre.symm ▸ hstrip.2
  have ht0 : 0 < (1 / 2 + (starRingEnd ℂ) z * I).re := by
    rw [htsre]
    linarith
  have ht1 : (1 / 2 + (starRingEnd ℂ) z * I).re < 1 := by
    rw [htsre]
    linarith
  have htz : XiC ((starRingEnd ℂ) z) ≠ 0 := by
    rw [XiC_conj]
    intro h
    apply hz
    have := congrArg (starRingEnd ℂ) h
    simpa using this
  refine ⟨hs0, ?_, ?_, ht0, ?_, ?_⟩
  · intro h
    rw [h] at hs1
    norm_num at hs1
  · intro hzero
    apply hz
    exact (xi_zero_iff_zeta_zero_of_mem_strip hs0 hs1).mpr hzero
  · intro h
    rw [h] at ht1
    norm_num at ht1
  · intro hzero
    apply htz
    exact (xi_zero_iff_zeta_zero_of_mem_strip ht0 ht1).mpr hzero

lemma xiWeilCauchyPacket_pair_eq_two
    {z w a b : ℂ} (hz : XiC z ≠ 0) (hw : XiC w ≠ 0) (hzw : z ≠ w) :
    xiWeilCauchyPacket {z, w} (ccmTwoPoleCoeff z a b) =
      xiWeilTwoCauchyPacket
        ⟨z, hz⟩ ⟨w, hw⟩ a b := by
  funext x
  simp [xiWeilCauchyPacket, ccmTwoPoleCoeff, xiWeilTwoCauchyPacket,
    hzw, Ne.symm hzw]

/-- Exact equality between the Xi-Weil square and the explicit continued
prime--archimedean rank-two source form. -/
theorem xiWeilPolarization_twoCauchy_eq_continuedSourceEnergy
    {z w a b : ℂ}
    (hzdom : CCMContinuedCauchyDomain z)
    (hwdom : CCMContinuedCauchyDomain w)
    (hzw : z ≠ w)
    (hzz : z ≠ (starRingEnd ℂ) z)
    (hzwc : z ≠ (starRingEnd ℂ) w)
    (hwzc : w ≠ (starRingEnd ℂ) z)
    (hww : w ≠ (starRingEnd ℂ) w) :
    xiWeilPolarization
        (xiWeilTwoCauchyPacket
          ⟨z, XiC_ne_zero_of_continuedPrimeArch_domain hzdom.1 hzdom.2.1 hzdom.2.2.1⟩
          ⟨w, XiC_ne_zero_of_continuedPrimeArch_domain hwdom.1 hwdom.2.1 hwdom.2.2.1⟩
          a b)
        (xiWeilTwoCauchyPacket
          ⟨z, XiC_ne_zero_of_continuedPrimeArch_domain hzdom.1 hzdom.2.1 hzdom.2.2.1⟩
          ⟨w, XiC_ne_zero_of_continuedPrimeArch_domain hwdom.1 hwdom.2.1 hwdom.2.2.1⟩
          a b) =
      ccmTwoPoleSourceEnergy z w a b := by
  let hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hzdom.1 hzdom.2.1 hzdom.2.2.1
  let hwXi : XiC w ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hwdom.1 hwdom.2.1 hwdom.2.2.1
  have hsource := xiWeilPolarization_cauchyPacket_eq_continuedPrimeArchSource
    (s := {z, w}) (t := {z, w})
    (c := ccmTwoPoleCoeff z a b) (d := ccmTwoPoleCoeff z a b)
    (hzpos := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.1
      · exact hwdom.1)
    (hz1 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.1
      · exact hwdom.2.1)
    (hzzeta := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.1
      · exact hwdom.2.2.1)
    (hwpos := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.2.1
      · exact hwdom.2.2.2.1)
    (hw1 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.2.2.1
      · exact hwdom.2.2.2.2.1)
    (hwzeta := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hzdom.2.2.2.2.2
      · exact hwdom.2.2.2.2.2)
    (hsep := by
      intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact hzz
      · exact hzwc
      · exact hwzc
      · exact hww)
  rw [xiWeilCauchyPacket_pair_eq_two hzXi hwXi hzw] at hsource
  rw [hsource]
  simp [ccmTwoPoleSourceEnergy, ccmContinuedCauchyKernel, ccmTwoPoleCoeff,
    hzw, Ne.symm hzw]
  ring

end
end RHTower
