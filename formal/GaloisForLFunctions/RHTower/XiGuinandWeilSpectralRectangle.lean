import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# Cofinal finite-stage Xi Guinand--Weil source law

This module identifies the analytic-order zero sum delivered by rectangle residues with the
multiplicity-copy carrier used by the formal Xi Weil criteria.  Every finite packet of divisor
copies then lies in an admissible rectangle on which the continued prime--archimedean source
contour equals the full copied spectral value sum.
-/

open Complex Filter intervalIntegral Set

namespace RHTower

noncomputable section

/-- All multiplicity copies whose centered spectral point lies in the closed rectangle. -/
def xiZeroCopyClosedRectangle (z₁ z₂ : ℂ) : Finset XiZeroCopy :=
  (xiCClosedRectangleZeros z₁ z₂).biUnion fun w =>
    (finite_xiSpectralPoint_fiber w).toFinset

@[simp] theorem mem_xiZeroCopyClosedRectangle {z₁ z₂ : ℂ} {q : XiZeroCopy} :
    q ∈ xiZeroCopyClosedRectangle z₁ z₂ ↔
      xiSpectralPoint q ∈
        (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
  constructor
  · intro hq
    obtain ⟨w, hw, hqw⟩ := Finset.mem_biUnion.mp hq
    have hpoint : xiSpectralPoint q = w := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hqw
    rw [hpoint]
    exact (mem_xiCClosedRectangleZeros.mp hw).1
  · intro hq
    apply Finset.mem_biUnion.mpr
    refine ⟨xiSpectralPoint q, ?_, ?_⟩
    · exact mem_xiCClosedRectangleZeros.mpr
        ⟨hq, XiC_xiSpectralPoint_eq_zero q⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- Grouping the copied Xi divisor by its distinct spectral points exactly recovers analytic
multiplicity. -/
theorem sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
    (g : ℂ → ℂ) (z₁ z₂ : ℂ) :
    ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, g (xiSpectralPoint q) =
      ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * g w := by
  classical
  let Z := xiCClosedRectangleZeros z₁ z₂
  let F : ℂ → Finset XiZeroCopy := fun w =>
    (finite_xiSpectralPoint_fiber w).toFinset
  have hdisj : (Z : Set ℂ).PairwiseDisjoint F := by
    intro w hw v hv hwv
    change Disjoint (F w) (F v)
    rw [Finset.disjoint_left]
    intro q hqw hqv
    have hqw' : xiSpectralPoint q = w := by
      simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hqw
    have hqv' : xiSpectralPoint q = v := by
      simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hqv
    exact hwv (hqw'.symm.trans hqv')
  rw [xiZeroCopyClosedRectangle, show xiCClosedRectangleZeros z₁ z₂ = Z from rfl,
    show (fun w => (finite_xiSpectralPoint_fiber w).toFinset) = F from rfl,
    Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro w hw
  calc
    ∑ q ∈ F w, g (xiSpectralPoint q) = ∑ _q ∈ F w, g w := by
      apply Finset.sum_congr rfl
      intro q hq
      have hpoint : xiSpectralPoint q = w := by
        simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
      rw [hpoint]
    _ = (F w).card • g w := Finset.sum_const (g w)
    _ = (xiSpectralMultiplicity w : ℂ) * g w := by
      simp [F, xiSpectralMultiplicity]

/-- On an admissible rectangle, the continued prime--archimedean source contour is exactly the
finite sum over all enclosed multiplicity copies in the existing Xi spectral carrier. -/
theorem rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
      2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        g (xiSpectralPoint q) := by
  calc
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        ((analyticOrderAt XiC w).toNat : ℂ) * g w :=
      rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
        hg hre him hbot htop hright hleft
    _ = 2 * Real.pi * I * ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * g w := by
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      have hzero : XiC w = 0 := (mem_xiCClosedRectangleZeros.mp hw).2
      rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hzero]
    _ = _ := by
      rw [sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum]

/-- **Cofinal finite-stage Guinand--Weil source law.**  Every prescribed finite packet of Xi
multiplicity copies is contained in an admissible rectangle on which the continued source contour
equals the full copied spectral sum over that rectangle. -/
theorem exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing
    (t : Finset XiZeroCopy) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (∀ q ∈ t, q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
      rectIntegral (fun z => g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
        2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          g (xiSpectralPoint q) := by
  obtain ⟨z₁, z₂, hre, him, hpacket, hbot, htop, hright, hleft⟩ :=
    exists_admissible_rectangle_containing_xiZeroCopy_finset t
  refine ⟨z₁, z₂, hre, him, ?_, ?_⟩
  · intro q hq
    rw [mem_xiZeroCopyClosedRectangle]
    apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le hre.le, uIcc_of_le him.le]
    exact ⟨⟨(hpacket q hq).1.le, (hpacket q hq).2.1.le⟩,
      ⟨(hpacket q hq).2.2.1.le, (hpacket q hq).2.2.2.le⟩⟩
  · exact rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
      hg hre him hbot htop hright hleft

/-- The cofinal source law specialized to the squared rectangular two-edge Xi test that produces
the sharp dyadic prime window.  Analytic regularity of the test is discharged internally. -/
theorem exists_admissible_rectIntegral_rectangularSource_eq_xiZeroCopy_sum_containing
    (t : Finset XiZeroCopy) (L a : ℝ) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      (∀ q ∈ t, q ∈ xiZeroCopyClosedRectangle z₁ z₂) ∧
      rectIntegral (fun z => xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ) *
          continuedPrimeArchSourceRelativeTrace z) z₁ z₂ =
        2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ) :=
  exists_admissible_rectIntegral_source_eq_xiZeroCopy_sum_containing t
    (xiRectangularTwoEdgeTransform_sq_analyticOnNhd L a)

/-- **Full rectangular Weil value as a cofinal source-contour limit.**  For every positive error
tolerance, an automatically admissible finite rectangle has normalized continued-source contour
within that tolerance of the complete rectangular Xi-Weil polarization.  Thus the passage from
finite rectangle residues to the full absolutely summable divisor value needs no extra hypothesis. -/
theorem exists_admissible_rectangularSource_normalizedContour_approximates_weil
    (L a : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      dist ((2 * Real.pi * I)⁻¹ *
          rectIntegral (fun z => xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ) *
            continuedPrimeArchSourceRelativeTrace z) z₁ z₂)
        (xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
          (xiRectangularTwoEdgeTransform L a)) < epsilon := by
  let f : XiZeroCopy → ℂ := fun q =>
    xiRectangularTwoEdgeTransform L a (xiSpectralPoint q) ^ (2 : ℕ)
  have hsum : Summable f := xiRectangularTwoEdgeTransform_sq_summable L a
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨t, ht⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hcontains, hcontour⟩ :=
    exists_admissible_rectIntegral_rectangularSource_eq_xiZeroCopy_sum_containing
      t L a
  refine ⟨z₁, z₂, hre, him, ?_⟩
  have hpacket : t ≤ xiZeroCopyClosedRectangle z₁ z₂ := by
    intro q hq
    exact hcontains q hq
  have hnear := ht (xiZeroCopyClosedRectangle z₁ z₂) hpacket
  rw [Metric.mem_ball] at hnear
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [hcontour, xiWeilPolarization_rectangular_eq_tsum_sq]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  simpa only [f] using hnear

end

end RHTower
