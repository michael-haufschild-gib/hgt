import GaloisForLFunctions.RHTower.RectangleLocalWeightedCauchyResidue
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.XiMassAnalyticTest

/-!
# Exact finite Xi contour law for the analytic mass test

The principal mass test is analytic only on its maximal branch strip.  The local weighted
argument principle nevertheless applies to every closed Xi rectangle contained in that strip.
This module identifies its contour exactly with the enclosed analytic-multiplicity sum and then
with the existing multiplicity-copy carrier.
-/

open Complex Filter intervalIntegral Set

namespace RHTower

noncomputable section

private theorem massContourEdgePoint_re (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).re = x := by simp

private theorem massContourEdgePoint_im (x c : ℝ) :
    ((x : ℂ) + (c : ℂ) * I).im = c := by simp

/-- A mass test on a branch-strip rectangle extracts every enclosed centered Xi zero with exact
analytic multiplicity.  Boundary nonvanishing is stated directly; no source continuation or RH
assumption enters. -/
theorem rectIntegral_xiMassAnalyticTest_mul_logDeriv_eq_closedRectangleZeroSum
    {a : ℝ} (ha : 0 < a) (τ : ℂ) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hstrip : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ xiMassStrip a)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => xiMassAnalyticTest a τ z * logDeriv XiC z) z₁ z₂ =
      2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * xiMassAnalyticTest a τ w := by
  classical
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_xiC_closedRectangle_factorization z₁ z₂
  let U : Set ℂ := {z : ℂ | h z ≠ 0} ∩ xiMassStrip a
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hUopen : IsOpen U := by
    exact (isOpen_compl_singleton.preimage hhcont).inter (isOpen_xiMassStrip a)
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    intro z hz
    exact ⟨hhK z hz, hstrip hz⟩
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
        have hneXi := hleft w.im hwimU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.1 hne
    have hrer : w.re < z₂.re := by
      have hne : w.re ≠ z₂.re := by
        intro heq
        have hedge : (z₂.re : ℂ) + w.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := hright w.im hwimU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwre.2 hne
    have himl : z₁.im < w.im := by
      have hne : z₁.im ≠ w.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₁.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := hbot w.re hwreU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.1 hne
    have himr : w.im < z₂.im := by
      have hne : w.im ≠ z₂.im := by
        intro heq
        have hedge : (w.re : ℂ) + z₂.im * I = w := by
          apply Complex.ext <;> simp [heq]
        have hneXi := htop w.re hwreU
        rw [hedge] at hneXi
        exact hneXi hwzero
      exact lt_of_le_of_ne hwim.2 hne
    exact ⟨hrel, hrer, himl, himr⟩
  have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    (xiCClosedRectangleZeros z₁ z₂) (fun w => w) m hUopen
      (fun z hz => analyticOnNhd_xiMassAnalyticTest ha τ z hz.2) hin hsub
      (fun z _ => hhan z (Set.mem_univ z)) (fun _ hz => hz.1)
      (fun z _ => hfact z)
  calc
    rectIntegral (fun z => xiMassAnalyticTest a τ z * logDeriv XiC z) z₁ z₂ =
        2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
          (m w : ℂ) * xiMassAnalyticTest a τ w := by
      simpa only using hres
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * xiMassAnalyticTest a τ w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      rw [hm w hw]

/-- The same exact finite contour law in the project's multiplicity-copy carrier. -/
theorem rectIntegral_xiMassAnalyticTest_mul_logDeriv_eq_xiZeroCopyClosedRectangleSum
    {a : ℝ} (ha : 0 < a) (τ : ℂ) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hstrip : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ xiMassStrip a)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₁.im * I) ≠ 0)
    (htop : ∀ x ∈ uIcc z₁.re z₂.re, XiC ((x : ℂ) + z₂.im * I) ≠ 0)
    (hright : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₂.re : ℂ) + y * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im, XiC ((z₁.re : ℂ) + y * I) ≠ 0) :
    rectIntegral (fun z => xiMassAnalyticTest a τ z * logDeriv XiC z) z₁ z₂ =
      2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiMassAnalyticTest a τ (xiSpectralPoint q) := by
  calc
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * xiMassAnalyticTest a τ w :=
      rectIntegral_xiMassAnalyticTest_mul_logDeriv_eq_closedRectangleZeroSum
        ha τ hre him hstrip hbot htop hright hleft
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * xiMassAnalyticTest a τ w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      have hzero : XiC w = 0 := (mem_xiCClosedRectangleZeros.mp hw).2
      rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hzero]
    _ = _ := by
      rw [sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum]

end

end RHTower
