import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularVerticalResolvent
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomEdge
import GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling

/-!
# Full sharp rectangular Guinand--Weil formula

The sharp rectangular test has only piecewise-linear Fourier regularity.  The bottom edge is
already absolutely integrable, while the preceding vertical-resolvent theorem supplies cofinal
vanishing without a zero-separation hypothesis.  This module combines those values with the exact
finite Xi factorization on symmetric rectangles.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- Exact argument-principle extraction on a symmetric depth-one rectangle whose right edge
avoids all Xi spectral real coordinates.  Evenness of `XiC` then also clears the left edge. -/
theorem rectIntegral_rectangularLogDeriv_symmetric_eq_xiZeroCopy_sum
    (L a R : ℝ) (hR : 0 < R)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    rectIntegral
        (fun z => xiRectangularTwoEdgeTransform L a z ^ 2 * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I) =
      2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
          xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - I)
  let z₂ : ℂ := (((R : ℝ) : ℂ) + I)
  let g : ℂ → ℂ := fun z => xiRectangularTwoEdgeTransform L a z ^ 2
  obtain ⟨m, h, hhan, hm, hhK, hfact⟩ :=
    exists_xiC_closedRectangle_factorization z₁ z₂
  let U : Set ℂ := {z : ℂ | h z ≠ 0}
  have hhcont : Continuous h := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hhan z (Set.mem_univ z)).continuousAt
  have hUopen : IsOpen U := by
    change IsOpen (h ⁻¹' {0}ᶜ)
    exact isOpen_compl_singleton.preimage hhcont
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U :=
    fun z hz => hhK z hz
  have hz₁re : z₁.re = -R := by simp [z₁]
  have hz₂re : z₂.re = R := by simp [z₂]
  have hz₁im : z₁.im = -1 := by simp [z₁]
  have hz₂im : z₂.im = 1 := by simp [z₂]
  have hin : ∀ w ∈ xiCClosedRectangleZeros z₁ z₂,
      z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im := by
    intro w hw
    obtain ⟨hwK, hwzero⟩ := mem_xiCClosedRectangleZeros.mp hw
    obtain ⟨hwre, hwim⟩ := Complex.mem_reProdIm.mp hwK
    rw [uIcc_of_le (by simp [hz₁re, hz₂re]; linarith)] at hwre
    rw [uIcc_of_le (by simp [hz₁im, hz₂im])] at hwim
    have hwstrip := xiC_zero_im_mem_openHalf hwzero
    have hreRight : w.re < z₂.re := by
      apply lt_of_le_of_ne hwre.2
      intro heq
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy w).mp hwzero
      apply havoid q
      rw [hz₂re] at heq
      have hqre := congrArg Complex.re hq
      linarith
    have hreLeft : z₁.re < w.re := by
      apply lt_of_le_of_ne hwre.1
      intro heq
      have hnegzero : XiC (-w) = 0 := by rw [XiC_even, hwzero]
      obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (-w)).mp hnegzero
      apply havoid q
      rw [hz₁re] at heq
      have hqre := congrArg Complex.re hq
      simp only [neg_re] at hqre
      linarith
    exact ⟨hreLeft, hreRight, by rw [hz₁im]; linarith,
      by rw [hz₂im]; linarith⟩
  have hres := rectIntegral_mul_logDeriv_boxCount
    (xiCClosedRectangleZeros z₁ z₂) (fun w => w) m
    (xiRectangularTwoEdgeTransform_sq_analyticOnNhd L a)
    hUopen hin hsub (fun z _ => hhan z (Set.mem_univ z))
    (fun _ hz => hz) (fun z _ => hfact z)
  calc
    rectIntegral
        (fun z => xiRectangularTwoEdgeTransform L a z ^ 2 * logDeriv XiC z)
        (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I) =
      2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (m w : ℂ) * g w := by
      simpa only [z₁, z₂, g] using hres
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * g w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      have hwzero : XiC w = 0 := (mem_xiCClosedRectangleZeros.mp hw).2
      rw [hm w hw, xiSpectralMultiplicity_eq_analyticOrderAt_toNat hwzero]
    _ = 2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        g (xiSpectralPoint q) := by
      rw [sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum]
    _ = 2 * Real.pi * I *
        ∑ q ∈ xiZeroCopyClosedRectangle
          (((-R : ℝ) : ℂ) - I) (((R : ℝ) : ℂ) + I),
          xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ 2 := by
      rfl

end

end RHTower
