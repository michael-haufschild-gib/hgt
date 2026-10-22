import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureHolomorphicSectorCoercivity
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmAdjacentFeatureKreinIndexSeparator
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.RectangleLocalWeightedCauchyResidue
import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureLatticePrimeGammaBudget

/-!
# Critical-line thin-strip source projector

For every bounded spectral-height window, local finiteness of the Xi divisor supplies a positive
transverse width containing no off-line zero.  On that thinner rectangle, the square of the
real-centered critical feature is holomorphic because its fixed poles lie at imaginary height
`+-1`.  The normalized contour of the continued pole--Gamma--von-Mangoldt trace therefore equals
the exact multiplicity-weighted critical-line feature energy in the window.

The contour definition contains no zero enumeration or divisor-fitted coefficient.  Divisor
local finiteness is used only in the proof that a suitable positive width exists.  This replaces
the earlier Abel/exterior critical-line projector at finite height.  It does not prove the
remaining height-local `4 / 25` arithmetic ceiling.
-/

open Complex Filter intervalIntegral Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Pole-free domain of the squared real-centered critical-feature weight. -/
def criticalFeaturePoleFreeDomain (t : ℝ) : Set ℂ :=
  {z | z ≠ (t : ℂ) - I ∧ z ≠ (t : ℂ) + I}

theorem isOpen_criticalFeaturePoleFreeDomain (t : ℝ) :
    IsOpen (criticalFeaturePoleFreeDomain t) := by
  rw [criticalFeaturePoleFreeDomain]
  exact (isOpen_compl_singleton.inter isOpen_compl_singleton)

theorem analyticOnNhd_criticalFeatureCauchyKernelTest_sq
    (t : ℝ) :
    AnalyticOnNhd ℂ (fun z => criticalFeatureCauchyKernelTest t z ^ (2 : ℕ))
      (criticalFeaturePoleFreeDomain t) := by
  intro z hz
  rw [criticalFeaturePoleFreeDomain, Set.mem_setOf_eq] at hz
  unfold criticalFeatureCauchyKernelTest criticalHardyLowerCauchyTest
    criticalHardyUpperCauchyTest xiWeilCauchyTest
  simp only [criticalHardyLowerPoint_coe, criticalHardyUpperPoint_coe]
  have hlow : z - ((t : ℂ) - I) ≠ 0 := sub_ne_zero.mpr hz.1
  have hupp : z - ((t : ℂ) + I) ≠ 0 := sub_ne_zero.mpr hz.2
  exact ((analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).inv hlow)).add
    (analyticAt_const.mul
      ((analyticAt_id.sub analyticAt_const).inv hupp))).pow 2

/-- Local-weight Guinand--Weil rectangle extraction.  Unlike the older global theorem, the
weight need only be analytic on one open neighbourhood of the rectangle. -/
theorem rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum_local
    {g : ℂ → ℂ} {V : Set ℂ} (hVopen : IsOpen V)
    (hg : AnalyticOnNhd ℂ g V)
    {z₁ z₂ : ℂ}
    (hrect : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ V)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * g w := by
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_xiC_closedRectangle_factorization z₁ z₂
  let U₀ : Set ℂ := {z : ℂ | h z ≠ 0}
  let U : Set ℂ := U₀ ∩ V
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hU₀open : IsOpen U₀ := by
    change IsOpen (h ⁻¹' {0}ᶜ)
    exact isOpen_compl_singleton.preimage hhcont
  have hUopen : IsOpen U := hU₀open.inter hVopen
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro z hz
    exact ⟨hhK z hz, hrect hz⟩
  have hin : ∀ w ∈ xiCClosedRectangleZeros z₁ z₂,
      z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_xiCClosedRectangleZeros.mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    have hwreU := hwre
    have hwimU := hwim
    rw [uIcc_of_le hre.le] at hwre
    rw [uIcc_of_le him.le] at hwim
    have hrel : z₁.re < w.re := by
      have hne : z₁.re ≠ w.re := by
        intro heq
        have hedge : (z₁.re : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (hleft w.im hwimU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.1 hne
    have hrer : w.re < z₂.re := by
      have hne : w.re ≠ z₂.re := by
        intro heq
        have hedge : (z₂.re : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (hright w.im hwimU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.2 hne
    have himl : z₁.im < w.im := by
      have hne : z₁.im ≠ w.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₁.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (hbot w.re hwreU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.1 hne
    have himr : w.im < z₂.im := by
      have hne : w.im ≠ z₂.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₂.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := XiC_ne_zero_of_admissible (htop w.re hwreU)
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.2 hne
    exact ⟨hrel, hrer, himl, himr⟩
  have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    (xiCClosedRectangleZeros z₁ z₂) (fun w => w) m hUopen
      (hg.mono inter_subset_right) hin hsub
      (hhan.mono (fun _ _ => Set.mem_univ _))
      (fun z hz => hz.1) (fun z _ => hfact z)
  rw [rectIntegral_congr
      (g₂ := fun z => g z * logDeriv XiC z)
      (fun z hz => by
        congr 1
        exact (continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
          hz.re_pos hz.ne_one hz.zeta_ne).trans
          (logDeriv_XiC_eq_relativeResolventTrace
            (XiC_ne_zero_of_admissible hz)).symm)
      hbot htop hright hleft]
  calc
    rectIntegral (fun z => g z * logDeriv XiC z) z₁ z₂ =
        2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
          (m w : ℂ) * g w := hres
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * g w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      rw [hm w hw]

def xiThinStripLowerCorner (A delta : ℝ) : ℂ :=
  (A : ℂ) - (delta : ℂ) * I

def xiThinStripUpperCorner (B delta : ℝ) : ℂ :=
  (B : ℂ) + (delta : ℂ) * I

theorem xiThinStrip_rectangle_subset_criticalFeaturePoleFreeDomain
    (t A B delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta < 1) :
    (uIcc (xiThinStripLowerCorner A delta).re
        (xiThinStripUpperCorner B delta).re ×ℂ
      uIcc (xiThinStripLowerCorner A delta).im
        (xiThinStripUpperCorner B delta).im) ⊆
      criticalFeaturePoleFreeDomain t := by
  intro z hz
  have him := (Complex.mem_reProdIm.mp hz).2
  have himcorners :
      (xiThinStripLowerCorner A delta).im = -delta ∧
        (xiThinStripUpperCorner B delta).im = delta := by
    simp [xiThinStripLowerCorner, xiThinStripUpperCorner, Complex.mul_im]
  rw [himcorners.1, himcorners.2,
    uIcc_of_le (neg_le_self hdelta0)] at him
  change -delta ≤ z.im ∧ z.im ≤ delta at him
  rw [criticalFeaturePoleFreeDomain, Set.mem_setOf_eq]
  constructor
  · intro hzlow
    have hi := congrArg Complex.im hzlow
    simp at hi
    linarith
  · intro hzupp
    have hi := congrArg Complex.im hzupp
    simp at hi
    linarith

def criticalFeatureThinStripSourceContour
    (t A B delta : ℝ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun z => criticalFeatureCauchyKernelTest t z ^ (2 : ℕ) *
        continuedPrimeArchSourceRelativeTrace z)
      (xiThinStripLowerCorner A delta)
      (xiThinStripUpperCorner B delta)

private theorem sq_eq_normSq_of_im_eq_zero {z : ℂ} (hz : z.im = 0) :
    z ^ (2 : ℕ) = (Complex.normSq z : ℂ) := by
  apply Complex.ext <;> simp [pow_two, Complex.normSq_apply, hz]

theorem criticalFeatureThinStripSourceContour_eq_lineEnergy
    {t A B delta : ℝ} (hAB : A < B)
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hbot : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) - (delta : ℂ) * I))
    (htop : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) + (delta : ℂ) * I))
    (hright : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((A : ℂ) + y * I))
    (hisolate : ∀ w ∈ xiCClosedRectangleZeros
        (xiThinStripLowerCorner A delta)
        (xiThinStripUpperCorner B delta), w.im = 0) :
    criticalFeatureThinStripSourceContour t A B delta =
      ∑ w ∈ xiCClosedRectangleZeros
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta),
        ((analyticOrderAt XiC w).toNat : ℂ) *
          (Complex.normSq (criticalFeatureCauchyKernelTest t w) : ℂ) := by
  have hre : (xiThinStripLowerCorner A delta).re <
      (xiThinStripUpperCorner B delta).re := by
    simpa [xiThinStripLowerCorner, xiThinStripUpperCorner] using hAB
  have him : (xiThinStripLowerCorner A delta).im <
      (xiThinStripUpperCorner B delta).im := by
    simp [xiThinStripLowerCorner, xiThinStripUpperCorner, Complex.mul_im]
    linarith
  have hbot' : ∀ x ∈ uIcc
      (xiThinStripLowerCorner A delta).re
      (xiThinStripUpperCorner B delta).re,
      XiExplicitAdmissible
        ((x : ℂ) + (xiThinStripLowerCorner A delta).im * I) := by
    simpa [xiThinStripLowerCorner, xiThinStripUpperCorner, sub_eq_add_neg,
      mul_assoc] using hbot
  have htop' : ∀ x ∈ uIcc
      (xiThinStripLowerCorner A delta).re
      (xiThinStripUpperCorner B delta).re,
      XiExplicitAdmissible
        ((x : ℂ) + (xiThinStripUpperCorner B delta).im * I) := by
    simpa [xiThinStripLowerCorner, xiThinStripUpperCorner, mul_assoc] using htop
  have hright' : ∀ y ∈ uIcc
      (xiThinStripLowerCorner A delta).im
      (xiThinStripUpperCorner B delta).im,
      XiExplicitAdmissible
        (((xiThinStripUpperCorner B delta).re : ℂ) + y * I) := by
    simpa [xiThinStripLowerCorner, xiThinStripUpperCorner, Complex.mul_im]
      using hright
  have hleft' : ∀ y ∈ uIcc
      (xiThinStripLowerCorner A delta).im
      (xiThinStripUpperCorner B delta).im,
      XiExplicitAdmissible
        (((xiThinStripLowerCorner A delta).re : ℂ) + y * I) := by
    simpa [xiThinStripLowerCorner, xiThinStripUpperCorner, Complex.mul_im]
      using hleft
  have hres :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum_local
      (isOpen_criticalFeaturePoleFreeDomain t)
      (analyticOnNhd_criticalFeatureCauchyKernelTest_sq t)
      (xiThinStrip_rectangle_subset_criticalFeaturePoleFreeDomain
        t A B delta hdelta0.le (hdeltaHalf.trans (by norm_num)))
      hre him hbot' htop' hright' hleft'
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [criticalFeatureThinStripSourceContour, hres,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  have hwim : w.im = 0 := hisolate w hw
  have hwstrip : |w.im| < 1 / 2 := by rw [hwim]; norm_num
  have heq :
      HedenmalmThetaSource.criticalEvaluation
          w hwstrip
          (HedenmalmThetaSource.criticalFeature (t : ℂ) (by norm_num)) =
        criticalFeatureCauchyKernelTest t w := by
    rw [criticalEvaluation_realCriticalFeature_eq_hardyCauchySum]
    rfl
  have hFim : (criticalFeatureCauchyKernelTest t w).im = 0 := by
    rw [← heq]
    exact criticalEvaluation_realCriticalFeature_im_eq_zero_of_im_eq_zero
      t hwstrip hwim
  exact sq_eq_normSq_of_im_eq_zero hFim

private theorem exists_positive_im_isolation_radius
    (S : Finset ℂ) {cap : ℝ} (hcap : 0 < cap) :
    ∃ delta : ℝ, 0 < delta ∧ delta < cap ∧
      ∀ z ∈ S, |z.im| < delta → z.im = 0 := by
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨cap / 2, by linarith, by linarith, ?_⟩
      simp
  | @insert a S ha ih =>
      obtain ⟨delta, hdelta0, hdeltacap, hiso⟩ := ih
      by_cases haim : a.im = 0
      · refine ⟨delta, hdelta0, hdeltacap, ?_⟩
        intro z hz hzsmall
        rw [Finset.mem_insert] at hz
        rcases hz with hza | hz
        · have hza' : z = a := by simpa using hza
          subst z
          exact haim
        · exact hiso z hz hzsmall
      · let eta : ℝ := min delta (|a.im| / 2)
        have habs : 0 < |a.im| := abs_pos.mpr haim
        have heta0 : 0 < eta := by
          dsimp only [eta]
          exact lt_min hdelta0 (by positivity)
        have hetacap : eta < cap :=
          (min_le_left delta (|a.im| / 2)).trans_lt hdeltacap
        refine ⟨eta, heta0, hetacap, ?_⟩
        intro z hz hzsmall
        rw [Finset.mem_insert] at hz
        rcases hz with hza | hz
        · have hza' : z = a := by simpa using hza
          subst z
          exfalso
          have hlt : |a.im| < |a.im| / 2 :=
            hzsmall.trans_le (min_le_right delta (|a.im| / 2))
          linarith
        · exact hiso z hz
            (hzsmall.trans_le (min_le_left delta (|a.im| / 2)))

/-- Local finiteness gives an unconditional positive strip width containing no off-line Xi zero
inside a fixed bounded height window. -/
theorem exists_xiThinStrip_isolating_criticalLine
    {A B delta₀ : ℝ} (_hAB : A < B) (hdelta₀ : 0 < delta₀) :
    ∃ delta : ℝ, 0 < delta ∧ delta < delta₀ ∧ delta < 1 / 2 ∧
      ∀ w ∈ xiCClosedRectangleZeros
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta),
        w.im = 0 := by
  let S : Finset ℂ := xiCClosedRectangleZeros
    (xiThinStripLowerCorner A delta₀)
    (xiThinStripUpperCorner B delta₀)
  let cap : ℝ := min delta₀ (1 / 2)
  have hcap : 0 < cap := lt_min hdelta₀ (by norm_num)
  obtain ⟨eta, heta0, hetacap, hiso⟩ :=
    exists_positive_im_isolation_radius S hcap
  let delta : ℝ := eta / 2
  have hdelta0 : 0 < delta := by dsimp only [delta]; linarith
  have hdelta_eta : delta < eta := by dsimp only [delta]; linarith
  have hdelta_delta₀ : delta < delta₀ := by
    have hcaple : cap ≤ delta₀ := min_le_left _ _
    exact hdelta_eta.trans (hetacap.trans_le hcaple)
  have hdelta_half : delta < 1 / 2 := by
    have hcaple : cap ≤ 1 / 2 := min_le_right _ _
    exact hdelta_eta.trans (hetacap.trans_le hcaple)
  refine ⟨delta, hdelta0, hdelta_delta₀, hdelta_half, ?_⟩
  intro w hw
  have hwdata := mem_xiCClosedRectangleZeros.mp hw
  have hwinner := Complex.mem_reProdIm.mp hwdata.1
  have hwre : w.re ∈ uIcc A B := by
    simpa [xiThinStripLowerCorner, xiThinStripUpperCorner] using hwinner.1
  have hwim : w.im ∈ Set.Icc (-delta) delta := by
    simpa [xiThinStripLowerCorner, xiThinStripUpperCorner, Complex.mul_im,
      uIcc_of_le (neg_le_self hdelta0.le)] using hwinner.2
  have hwouter : w ∈ S := by
    apply mem_xiCClosedRectangleZeros.mpr
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hwdata.2⟩
    · simpa [S, xiThinStripLowerCorner, xiThinStripUpperCorner] using hwre
    · rw [show (xiThinStripLowerCorner A delta₀).im = -delta₀ by
          simp [xiThinStripLowerCorner, Complex.mul_im],
        show (xiThinStripUpperCorner B delta₀).im = delta₀ by
          simp [xiThinStripUpperCorner, Complex.mul_im],
        uIcc_of_le (neg_le_self hdelta₀.le)]
      change -delta₀ ≤ w.im ∧ w.im ≤ delta₀
      change -delta ≤ w.im ∧ w.im ≤ delta at hwim
      constructor <;> linarith
  apply hiso w hwouter
  have habs : |w.im| ≤ delta := (abs_le).mpr hwim
  exact habs.trans_lt hdelta_eta

/-- Every bounded height window with zero-free vertical sides admits a thinner admissible source
rectangle containing only critical-line Xi zeros.  Width is independent of feature center. -/
theorem exists_xiThinStrip_admissible_isolating_criticalLine
    {A B delta₀ : ℝ} (hAB : A < B) (hdelta₀ : 0 < delta₀)
    (hright₀ : ∀ y ∈ uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft₀ : ∀ y ∈ uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((A : ℂ) + y * I)) :
    ∃ delta : ℝ, 0 < delta ∧ delta < delta₀ ∧ delta < 1 / 2 ∧
      (∀ x ∈ uIcc A B,
        XiExplicitAdmissible ((x : ℂ) - (delta : ℂ) * I)) ∧
      (∀ x ∈ uIcc A B,
        XiExplicitAdmissible ((x : ℂ) + (delta : ℂ) * I)) ∧
      (∀ y ∈ uIcc (-delta) delta,
        XiExplicitAdmissible ((B : ℂ) + y * I)) ∧
      (∀ y ∈ uIcc (-delta) delta,
        XiExplicitAdmissible ((A : ℂ) + y * I)) ∧
      ∀ w ∈ xiCClosedRectangleZeros
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta),
        w.im = 0 := by
  obtain ⟨delta, hdelta0, hdeltalt, hdeltahalf, hisolate⟩ :=
    exists_xiThinStrip_isolating_criticalLine hAB hdelta₀
  have hbot : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) - (delta : ℂ) * I) := by
    intro x hx
    apply SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half
    · simpa [Complex.mul_im, abs_neg, abs_of_pos hdelta0] using hdeltahalf
    · intro hzero
      let w : ℂ := (x : ℂ) - (delta : ℂ) * I
      have hw : w ∈ xiCClosedRectangleZeros
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta) := by
        apply mem_xiCClosedRectangleZeros.mpr
        refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hzero⟩
        · simpa [w, xiThinStripLowerCorner, xiThinStripUpperCorner] using hx
        · simp [w, xiThinStripLowerCorner, xiThinStripUpperCorner,
            Complex.mul_im, hdelta0.le]
      have hwim := hisolate w hw
      dsimp only [w] at hwim
      simp [Complex.mul_im] at hwim
      linarith
  have htop : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) + (delta : ℂ) * I) := by
    intro x hx
    apply SlabFullWidthAdmissibility.XiExplicitAdmissible_of_abs_im_lt_half
    · simpa [Complex.mul_im, abs_of_pos hdelta0] using hdeltahalf
    · intro hzero
      let w : ℂ := (x : ℂ) + (delta : ℂ) * I
      have hw : w ∈ xiCClosedRectangleZeros
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta) := by
        apply mem_xiCClosedRectangleZeros.mpr
        refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, hzero⟩
        · simpa [w, xiThinStripLowerCorner, xiThinStripUpperCorner] using hx
        · simp [w, xiThinStripLowerCorner, xiThinStripUpperCorner,
            Complex.mul_im, hdelta0.le]
      have hwim := hisolate w hw
      dsimp only [w] at hwim
      simp [Complex.mul_im] at hwim
      linarith
  have hsmallSubset : uIcc (-delta) delta ⊆ uIcc (-delta₀) delta₀ := by
    rw [uIcc_of_le (neg_le_self hdelta0.le),
      uIcc_of_le (neg_le_self hdelta₀.le)]
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  have hright : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((B : ℂ) + y * I) := by
    intro y hy
    exact hright₀ y (hsmallSubset hy)
  have hleft : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((A : ℂ) + y * I) := by
    intro y hy
    exact hleft₀ y (hsmallSubset hy)
  exact ⟨delta, hdelta0, hdeltalt, hdeltahalf,
    hbot, htop, hright, hleft, hisolate⟩

/-- Every bounded height window with zero-free vertical sides admits a thinner source rectangle
whose normalized pole--Gamma--von-Mangoldt contour is exactly critical-line feature energy in that
window.  Width is chosen before applying the argument principle. -/
theorem exists_criticalFeatureThinStripSourceContour_eq_lineEnergy
    {t A B delta₀ : ℝ} (hAB : A < B) (hdelta₀ : 0 < delta₀)
    (hright₀ : ∀ y ∈ uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft₀ : ∀ y ∈ uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((A : ℂ) + y * I)) :
    ∃ delta : ℝ, 0 < delta ∧ delta < delta₀ ∧ delta < 1 / 2 ∧
      criticalFeatureThinStripSourceContour t A B delta =
        ∑ w ∈ xiCClosedRectangleZeros
            (xiThinStripLowerCorner A delta)
            (xiThinStripUpperCorner B delta),
          ((analyticOrderAt XiC w).toNat : ℂ) *
            (Complex.normSq (criticalFeatureCauchyKernelTest t w) : ℂ) := by
  obtain ⟨delta, hdelta0, hdeltalt, hdeltahalf,
      hbot, htop, hright, hleft, hisolate⟩ :=
    exists_xiThinStrip_admissible_isolating_criticalLine
      hAB hdelta₀ hright₀ hleft₀
  refine ⟨delta, hdelta0, hdeltalt, hdeltahalf, ?_⟩
  exact criticalFeatureThinStripSourceContour_eq_lineEnergy
    hAB hdelta0 hdeltahalf hbot htop hright hleft hisolate

def finiteCriticalLineFeatureEnergy
    (t A B delta : ℝ) : ℝ :=
  ∑ w ∈ xiCClosedRectangleZeros
      (xiThinStripLowerCorner A delta)
      (xiThinStripUpperCorner B delta),
    ((analyticOrderAt XiC w).toNat : ℝ) *
      Complex.normSq (criticalFeatureCauchyKernelTest t w)

theorem re_criticalFeatureThinStripSourceContour_eq_finiteCriticalLineFeatureEnergy
    {t A B delta : ℝ} (hAB : A < B)
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hbot : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) - (delta : ℂ) * I))
    (htop : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) + (delta : ℂ) * I))
    (hright : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((A : ℂ) + y * I))
    (hisolate : ∀ w ∈ xiCClosedRectangleZeros
        (xiThinStripLowerCorner A delta)
        (xiThinStripUpperCorner B delta), w.im = 0) :
    (criticalFeatureThinStripSourceContour t A B delta).re =
      finiteCriticalLineFeatureEnergy t A B delta := by
  have h := criticalFeatureThinStripSourceContour_eq_lineEnergy
    (t := t) hAB hdelta0 hdeltaHalf hbot htop hright hleft hisolate
  have hre := congrArg Complex.re h
  rw [finiteCriticalLineFeatureEnergy]
  change Complex.reCLM (criticalFeatureThinStripSourceContour t A B delta) =
    Complex.reCLM (∑ w ∈ xiCClosedRectangleZeros
      (xiThinStripLowerCorner A delta) (xiThinStripUpperCorner B delta),
        ((analyticOrderAt XiC w).toNat : ℂ) *
          (Complex.normSq (criticalFeatureCauchyKernelTest t w) : ℂ)) at hre
  rw [map_sum] at hre
  simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, mul_zero, sub_zero,
    Nat.cast_ofNat] using hre

def criticalFeatureThinStripCorrectedLatticeBudget
    (K : Finset ℤ) (A B delta : ℝ) : ℝ :=
  ∑ k ∈ K, ((criticalFeaturePrimeGammaSourceDiagonal (k : ℝ)).re -
    (criticalFeatureThinStripSourceContour (k : ℝ) A B delta).re)

theorem criticalFeatureThinStripCorrectedLatticeBudget_eq_finiteLineSubtraction
    (K : Finset ℤ) {A B delta : ℝ} (hAB : A < B)
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hbot : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) - (delta : ℂ) * I))
    (htop : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) + (delta : ℂ) * I))
    (hright : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((A : ℂ) + y * I))
    (hisolate : ∀ w ∈ xiCClosedRectangleZeros
        (xiThinStripLowerCorner A delta)
        (xiThinStripUpperCorner B delta), w.im = 0) :
    criticalFeatureThinStripCorrectedLatticeBudget K A B delta =
      ∑ k ∈ K, ((criticalFeaturePrimeGammaSourceDiagonal (k : ℝ)).re -
        finiteCriticalLineFeatureEnergy (k : ℝ) A B delta) := by
  rw [criticalFeatureThinStripCorrectedLatticeBudget]
  apply Finset.sum_congr rfl
  intro k hk
  rw [re_criticalFeatureThinStripSourceContour_eq_finiteCriticalLineFeatureEnergy
    hAB hdelta0 hdeltaHalf hbot htop hright hleft hisolate]

theorem finiteCriticalLineFeatureEnergy_eq_zeroCopySum
    (t A B delta : ℝ) :
    finiteCriticalLineFeatureEnergy t A B delta =
      ∑ q ∈ xiZeroCopyClosedRectangle
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta),
        Complex.normSq
          (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) := by
  have hgroup := sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
    (fun z => (Complex.normSq (criticalFeatureCauchyKernelTest t z) : ℂ))
    (xiThinStripLowerCorner A delta) (xiThinStripUpperCorner B delta)
  have hgroup' :
      (∑ q ∈ xiZeroCopyClosedRectangle
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta),
        (Complex.normSq
          (criticalFeatureCauchyKernelTest t (xiSpectralPoint q)) : ℂ)) =
      ∑ w ∈ xiCClosedRectangleZeros
          (xiThinStripLowerCorner A delta)
          (xiThinStripUpperCorner B delta),
        ((analyticOrderAt XiC w).toNat : ℂ) *
          (Complex.normSq (criticalFeatureCauchyKernelTest t w) : ℂ) := by
    rw [hgroup]
    apply Finset.sum_congr rfl
    intro w hw
    rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat
      (mem_xiCClosedRectangleZeros.mp hw).2]
  rw [finiteCriticalLineFeatureEnergy]
  exact_mod_cast hgroup'.symm

theorem finiteCriticalLineFeatureEnergy_le_criticalLineTrace
    {t A B delta : ℝ}
    (hisolate : ∀ w ∈ xiCClosedRectangleZeros
        (xiThinStripLowerCorner A delta)
        (xiThinStripUpperCorner B delta), w.im = 0) :
    finiteCriticalLineFeatureEnergy t A B delta ≤
      criticalLineCriticalFeatureEnergyTrace t := by
  rw [finiteCriticalLineFeatureEnergy_eq_zeroCopySum]
  let S := xiZeroCopyClosedRectangle
    (xiThinStripLowerCorner A delta) (xiThinStripUpperCorner B delta)
  have hline : ∀ q ∈ S, (q.1 : ℂ).re = 1 / 2 := by
    intro q hq
    have hqrect := mem_xiZeroCopyClosedRectangle.mp hq
    have hw : xiSpectralPoint q ∈ xiCClosedRectangleZeros
        (xiThinStripLowerCorner A delta)
        (xiThinStripUpperCorner B delta) := by
      apply mem_xiCClosedRectangleZeros.mpr
      exact ⟨hqrect, XiC_xiSpectralPoint_eq_zero q⟩
    have him : (xiSpectralPoint q).im = 0 := hisolate _ hw
    rw [xiSpectralPoint_im_eq] at him
    linarith
  have heq :
      (∑ q ∈ S, Complex.normSq
        (criticalFeatureCauchyKernelTest t (xiSpectralPoint q))) =
      ∑ q ∈ S, criticalLineCriticalFeatureEnergy t q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [criticalLineCriticalFeatureEnergy, if_pos (hline q hq)]
  rw [heq]
  exact (criticalLineCriticalFeatureEnergy_summable t).sum_le_tsum S
    (fun q _ => by
      rw [criticalLineCriticalFeatureEnergy]
      split_ifs
      · exact Complex.normSq_nonneg _
      · exact le_rfl)

theorem criticalFeaturePrimeGammaOffLineLatticeBudget_le_thinStripCorrected
    (K : Finset ℤ) {A B delta : ℝ} (hAB : A < B)
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hbot : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) - (delta : ℂ) * I))
    (htop : ∀ x ∈ uIcc A B,
      XiExplicitAdmissible ((x : ℂ) + (delta : ℂ) * I))
    (hright : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc (-delta) delta,
      XiExplicitAdmissible ((A : ℂ) + y * I))
    (hisolate : ∀ w ∈ xiCClosedRectangleZeros
        (xiThinStripLowerCorner A delta)
        (xiThinStripUpperCorner B delta), w.im = 0) :
    criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
      criticalFeatureThinStripCorrectedLatticeBudget K A B delta := by
  rw [criticalFeaturePrimeGammaOffLineLatticeBudget,
    criticalFeatureThinStripCorrectedLatticeBudget_eq_finiteLineSubtraction
      K hAB hdelta0 hdeltaHalf hbot htop hright hleft hisolate]
  simp only [criticalFeaturePrimeGammaOffLineExcess]
  apply Finset.sum_le_sum
  intro k hk
  linarith [finiteCriticalLineFeatureEnergy_le_criticalLineTrace
    (t := (k : ℝ)) hisolate]

/-- Source-only finite-height majorant for the corrected divisor budget.  One width works for the
whole feature lattice because isolation and boundary admissibility are center-independent. -/
theorem exists_thinStripCorrectedLattice_sourceMajorant
    (K : Finset ℤ) {A B delta₀ : ℝ} (hAB : A < B) (hdelta₀ : 0 < delta₀)
    (hright₀ : ∀ y ∈ uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((B : ℂ) + y * I))
    (hleft₀ : ∀ y ∈ uIcc (-delta₀) delta₀,
      XiExplicitAdmissible ((A : ℂ) + y * I)) :
    ∃ delta : ℝ, 0 < delta ∧ delta < delta₀ ∧ delta < 1 / 2 ∧
      criticalFeaturePrimeGammaOffLineLatticeBudget K ≤
        criticalFeatureThinStripCorrectedLatticeBudget K A B delta ∧
      criticalFeatureThinStripCorrectedLatticeBudget K A B delta =
        ∑ k ∈ K, ((criticalFeaturePrimeGammaSourceDiagonal (k : ℝ)).re -
          finiteCriticalLineFeatureEnergy (k : ℝ) A B delta) := by
  obtain ⟨delta, hdelta0, hdeltalt, hdeltahalf,
      hbot, htop, hright, hleft, hisolate⟩ :=
    exists_xiThinStrip_admissible_isolating_criticalLine
      hAB hdelta₀ hright₀ hleft₀
  refine ⟨delta, hdelta0, hdeltalt, hdeltahalf, ?_, ?_⟩
  · exact criticalFeaturePrimeGammaOffLineLatticeBudget_le_thinStripCorrected
      K hAB hdelta0 hdeltahalf hbot htop hright hleft hisolate
  · exact criticalFeatureThinStripCorrectedLatticeBudget_eq_finiteLineSubtraction
      K hAB hdelta0 hdeltahalf hbot htop hright hleft hisolate


end
end RHTower
