import GaloisForLFunctions.RHTower.XiCenteredRealShiftCauchyPairExactCorrection
import GaloisForLFunctions.RHTower.XiCriticalLineThinStripSourceProjector

/-!
# Pole-safe inner landing for the rational Xi Cauchy pair

The rational EGC kernel has prescribed poles at `z = w ± eps`.  Treating it
as an entire test on an inner source rectangle would silently lose their
residues.  This module isolates the complementary, pole-safe regime: when
the two prescribed poles are outside the inner rectangle, its normalized
continued prime--archimedean contour is exactly the finite multiplicity-copy
Cauchy row.  Thus a later nested construction can use this lemma on every
outer boundary point after proving geometric pole avoidance, while the
separate two-pole correction handles the regime in which shifts enter a
contour.
-/

open Complex Filter intervalIntegral Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Domain on which a Cauchy pair test with observation point `w` has neither
of its prescribed poles. -/
def meromorphicCauchyPairPoleFreeDomain (eps : ℝ) (w : ℂ) : Set ℂ :=
  {z | z - w - (eps : ℂ) ≠ 0 ∧ z - w + (eps : ℂ) ≠ 0}

theorem isOpen_meromorphicCauchyPairPoleFreeDomain (eps : ℝ) (w : ℂ) :
    IsOpen (meromorphicCauchyPairPoleFreeDomain eps w) := by
  have hminus : IsOpen {z : ℂ | z - w - (eps : ℂ) ≠ 0} := by
    change IsOpen ((fun z : ℂ => z - w - (eps : ℂ)) ⁻¹' ({0}ᶜ : Set ℂ))
    exact isOpen_compl_singleton.preimage
      ((continuous_id.sub continuous_const).sub continuous_const)
  have hplus : IsOpen {z : ℂ | z - w + (eps : ℂ) ≠ 0} := by
    change IsOpen ((fun z : ℂ => z - w + (eps : ℂ)) ⁻¹' ({0}ᶜ : Set ℂ))
    exact isOpen_compl_singleton.preimage
      ((continuous_id.sub continuous_const).add continuous_const)
  exact hminus.inter hplus

/-- In its pole-free domain, the prescribed rational pair kernel is analytic
in the inner contour variable. -/
theorem analyticOnNhd_meromorphicCauchyPairKernel_left
    (eps : ℝ) (w : ℂ) :
    AnalyticOnNhd ℂ (fun z => meromorphicCauchyPairKernel eps z w)
      (meromorphicCauchyPairPoleFreeDomain eps w) := by
  intro z hz
  rw [meromorphicCauchyPairPoleFreeDomain, Set.mem_setOf_eq] at hz
  have hden : (z - w) ^ 2 - (eps : ℂ) ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hz.2 hz.1
  unfold meromorphicCauchyPairKernel
  exact ((analyticAt_id.sub analyticAt_const).pow 2).div
    (((analyticAt_id.sub analyticAt_const).pow 2).sub (analyticAt_const.pow 2)) hden

/-- Normalized inner continued-source contour for a rational pair row.  The
observation pole locations are prescribed by `eps` and `w`, before any Xi
divisor expansion. -/
def normalizedMeromorphicCauchyPairInnerSourceContour
    (eps : ℝ) (w z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun z => meromorphicCauchyPairKernel eps z w *
        continuedPrimeArchSourceRelativeTrace z)
      z₁ z₂

/-- **Pole-safe inner source landing.**  If the two prescribed Cauchy poles
are outside an admissible inner rectangle, the normalized source contour is
exactly its finite Xi multiplicity-copy Cauchy row.  No zero-dependent pole
placement, simplicity assumption, or limit interchange occurs. -/
theorem normalizedMeromorphicCauchyPairInnerSourceContour_eq_xiZeroCopy_sum
    {eps : ℝ} {w z₁ z₂ : ℂ}
    (hrect : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆
      meromorphicCauchyPairPoleFreeDomain eps w)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    normalizedMeromorphicCauchyPairInnerSourceContour eps w z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        meromorphicCauchyPairKernel eps (xiSpectralPoint q) w := by
  have hres :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum_local
      (isOpen_meromorphicCauchyPairPoleFreeDomain eps w)
      (analyticOnNhd_meromorphicCauchyPairKernel_left eps w)
      hrect hre him hbot htop hright hleft
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  have hconvert :
      (∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
          ((analyticOrderAt XiC z).toNat : ℂ) *
            meromorphicCauchyPairKernel eps z w) =
        ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          meromorphicCauchyPairKernel eps (xiSpectralPoint q) w := by
    calc
      (∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
          ((analyticOrderAt XiC z).toNat : ℂ) *
            meromorphicCauchyPairKernel eps z w) =
          ∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
            (xiSpectralMultiplicity z : ℂ) *
              meromorphicCauchyPairKernel eps z w := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzero : XiC z = 0 := (mem_xiCClosedRectangleZeros.mp hz).2
        rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hzero]
      _ = ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          meromorphicCauchyPairKernel eps (xiSpectralPoint q) w :=
        (sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
          (fun z => meromorphicCauchyPairKernel eps z w) z₁ z₂).symm
  rw [normalizedMeromorphicCauchyPairInnerSourceContour, hres,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul, hconvert]

end

end RHTower
