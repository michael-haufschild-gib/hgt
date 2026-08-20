/-
# The shift lattice lies in the asymmetric-functional-equation regular set

The regularity hypothesis of the cusp--spectrum radius law asks for pair-analyticity of the
completed value at `s₀ - k/d` and at its reflection, together with Gamma-pole-freeness.  All three
depend only on the *height* of the point, and the shift lattice is horizontal: every `s₀ - k/d` has
the same imaginary part as `s₀`.  So a single height inequality on `s₀` puts the whole lattice
inside the regular set, and Step 3 of the radius law loses its last hypothesis.

The corpus already had the height criterion but stated it with a positive-real-part side condition;
that condition was only excluding the reflected continuation pole at `1`, which a nonzero height
already excludes.  Removing it is what makes the criterion usable on a lattice running to the left.

Main results:
* `selbergVerticalPoint_reflection_ne_one_of_im_ne_zero` — a nonzero height excludes the reflected
  pole, with no condition on the real part.
* `ExtendedSelbergClass.mem_asymmetricFERegularSet_of_height` — **the height criterion, with no
  real-part hypothesis**.
* `ExtendedSelbergClass.shiftLattice_mem_asymmetricFERegularSet` — **the whole shift lattice is
  regular**.
* `ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_height`,
  `ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate_of_height` — **Step 3 of the
  cusp--spectrum radius law with the regularity hypothesis discharged**.
-/
import GaloisForLFunctions.RHTower.SelbergRankOneSineFactor
import GaloisForLFunctions.RHTower.SelbergClass.GammaTailRegularity

open Filter Topology Complex

namespace RHTower

noncomputable section

/-- A nonzero height excludes the reflected continuation pole, whatever the real part. -/
theorem selbergVerticalPoint_reflection_ne_one_of_im_ne_zero {sigma t : ℝ} (ht : t ≠ 0) :
    1 - star (selbergVerticalPoint sigma t) ≠ 1 := by
  rw [selbergVerticalPoint_reflection]
  intro h
  have him := congrArg Complex.im h
  simp [selbergVerticalPoint] at him
  exact ht him

theorem analyticAt_selbergCompletedValue_verticalTail_reflection_of_im_ne_zero
    (G : SelbergGammaData) (A : SelbergAnalyticContinuation) {sigma t : ℝ}
    (ht : t ≠ 0) (htail : G.verticalTailCondition t) :
    AnalyticAt ℂ (selbergCompletedValue G A) (1 - star (selbergVerticalPoint sigma t)) := by
  rw [selbergVerticalPoint_reflection]
  have hpoint : selbergVerticalPoint (1 - sigma) t ≠ 1 := by
    rw [← selbergVerticalPoint_reflection]
    exact selbergVerticalPoint_reflection_ne_one_of_im_ne_zero (sigma := sigma) ht
  exact analyticAt_selbergCompletedValue_verticalTail G A htail hpoint

theorem ExtendedSelbergClass.mem_completedFEContourSafeSet_of_im_ne_zero
    (F : ExtendedSelbergClass) {sigma t : ℝ} (ht : t ≠ 0)
    (hpoint : selbergVerticalPoint sigma t ≠ 1)
    (htail : F.gammaData.verticalTailCondition t) :
    selbergVerticalPoint sigma t ∈ F.completedFEContourSafeSet := by
  constructor
  · exact analyticAt_selbergCompletedValue_verticalTail F.gammaData F.continuation htail hpoint
  · exact analyticAt_selbergCompletedValue_verticalTail_reflection_of_im_ne_zero
      F.gammaData F.continuation ht htail

theorem SelbergGammaData.gammaTailHeight_nonneg (G : SelbergGammaData) :
    0 ≤ G.gammaTailHeight := by
  unfold SelbergGammaData.gammaTailHeight
  exact Finset.sum_nonneg fun j _ ↦ div_nonneg (abs_nonneg _) (G.lambda_pos j).le

/-- **The height criterion for asymmetric-functional-equation regularity, with no hypothesis on
the real part.** -/
theorem ExtendedSelbergClass.mem_asymmetricFERegularSet_of_height
    (F : ExtendedSelbergClass) {sigma t : ℝ} (ht : F.gammaData.gammaTailHeight < |t|) :
    selbergVerticalPoint sigma t ∈ F.asymmetricFERegularSet := by
  have htne : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    exact absurd ht (not_lt.mpr F.gammaData.gammaTailHeight_nonneg)
  constructor
  · exact F.mem_completedFEContourSafeSet_of_im_ne_zero htne
      (selbergVerticalPoint_ne_one_of_gammaTailHeight_lt_abs F.gammaData ht)
      (F.gammaData.verticalTailCondition_of_gammaTailHeight_lt_abs ht)
  · exact F.gammaData.mem_asymmetricPoleFreeSet_verticalTail
      (F.gammaData.verticalTailCondition_of_gammaTailHeight_lt_abs ht)

/-- The shift lattice is horizontal. -/
theorem selbergShiftPoint_eq (s₀ : ℂ) (d : ℝ) (k : ℕ) :
    s₀ - (k : ℂ) / (d : ℂ) = selbergVerticalPoint (s₀.re - (k : ℝ) / d) s₀.im := by
  have hdiv : ((k : ℂ)) / (d : ℂ) = (((k : ℝ) / d : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hdiv]
  apply Complex.ext <;> simp [selbergVerticalPoint]

/-- **The whole shift lattice is regular** once the base height clears the Gamma-tail bound. -/
theorem ExtendedSelbergClass.shiftLattice_mem_asymmetricFERegularSet
    (F : ExtendedSelbergClass) {s₀ : ℂ}
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|) (k : ℕ) :
    (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ)) ∈ F.asymmetricFERegularSet := by
  rw [selbergShiftPoint_eq s₀ F.gammaData.degree k]
  exact F.mem_asymmetricFERegularSet_of_height hheight

/-- **Step 3 of the cusp--spectrum radius law, with the regularity hypothesis discharged.** -/
theorem ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_height (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) {s₀ : ℂ} (ha1 : (F.coeff 1 : ℂ) ≠ 0)
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hfreq : ∃ᶠ k : ℕ in atTop,
      c₀ ≤ ‖F.gammaData.asymmetricS (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) :=
  F.limsup_norm_shift_rpow_inv hd s₀ ha1
    (Filter.Eventually.of_forall (F.shiftLattice_mem_asymmetricFERegularSet hheight)) hc₀ hfreq

/-- **Step 3 in every degree, for a rank-one presentation, with every hypothesis on the analytic
continuation discharged.** -/
theorem ExtendedSelbergClass.limsup_norm_shift_rpow_inv_of_halfRate_of_height
    (F : ExtendedSelbergClass) (hd : 0 < F.gammaData.degree) {s₀ : ℂ}
    (ha1 : (F.coeff 1 : ℂ) ≠ 0)
    (hrate : ∀ j, F.gammaData.lambda j = F.gammaData.degree / 2)
    (hheight : F.gammaData.gammaTailHeight < |s₀.im|) :
    limsup (fun k : ℕ =>
        (‖F (s₀ - (k : ℂ) / (F.gammaData.degree : ℂ))‖ / (k.factorial : ℝ)) ^ (1 / (k : ℝ)))
      atTop
      = F.gammaData.conductor ^ (1 / F.gammaData.degree)
        / (2 * Real.pi * F.gammaData.degree) :=
  F.limsup_norm_shift_rpow_inv_of_halfRate hd s₀ ha1 hrate
    (Filter.Eventually.of_forall (F.shiftLattice_mem_asymmetricFERegularSet hheight))

end

end RHTower
