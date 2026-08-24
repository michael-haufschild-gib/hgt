import GaloisForLFunctions.RHTower.XiShiftEulerRationalSampleWitness
import GaloisForLFunctions.RHTower.CCMRectangularDirichletLandau
import GaloisForLFunctions.RHTower.XiRealBoundaryDivisorMeasure
import GaloisForLFunctions.HTGeometry.DivisorPairing
import GaloisForLFunctions.HTGeometry.RationalFiniteAvoidance

/-!
# Rational shifted-Xi negative-inertia witnesses

For a fixed positive-transverse Xi zero, numerator cancellation can occur at only finitely many
shifts in a compact interval.  Indeed, reflected numerator evaluation follows an injective affine
line through the complex plane, while the Xi zero set is finite on its compact image.  Rational
density therefore supplies an uncancelled positive rational shift below that zero.

Combining this shift selection with Gaussian-rational Euler-region locality gives an exact,
unconditional RH-failure criterion: RH fails precisely when some positive rational shift admits an
uncancelled shifted pole and a finite Gaussian-rational Pick matrix of positive negative inertia.
-/

open Complex Set Topology Filter
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Affine Xi argument obtained by evaluating the shifted numerator at the reflection of a pole. -/
def xiShiftReflectedZeroMap (lambda : ℂ) (omega : ℝ) : ℂ :=
  -lambda - (2 * omega : ℂ) * I

/-- Evaluation at a reflected shifted-Xi pole is evaluation of `XiC` along the affine reflected
zero line. -/
theorem suzukiCanonicalE_neg_xiShiftPoleCoordinate_eq_XiC
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) =
      XiC (xiShiftReflectedZeroMap (xiSpectralPoint q.1) omega) := by
  rw [suzukiCanonicalE_eq_XiC_shift, xiShiftPoleCoordinate]
  congr 1
  simp only [xiShiftReflectedZeroMap]
  ring

/-- Distinct real shifts visit distinct points on the reflected Xi line. -/
theorem xiShiftReflectedZeroMap_injective (lambda : ℂ) :
    Function.Injective (xiShiftReflectedZeroMap lambda) := by
  intro x y hxy
  have him := congrArg Complex.im hxy
  simp only [xiShiftReflectedZeroMap, sub_im, neg_im, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, mul_one, add_zero] at him
  norm_num at him
  linarith

/-- On every bounded real shift interval, only finitely many shifts make the reflected numerator
vanish. -/
theorem finite_xiShiftReflectedZeroMap_zeros_Icc
    (lambda : ℂ) (a b : ℝ) :
    {omega ∈ Set.Icc a b | XiC (xiShiftReflectedZeroMap lambda omega) = 0}.Finite := by
  let S : Set ℂ := xiShiftReflectedZeroMap lambda '' Set.Icc a b
  have hmapContinuous : Continuous (xiShiftReflectedZeroMap lambda) := by
    change Continuous (fun omega : ℝ => -lambda - (2 * omega : ℂ) * I)
    fun_prop
  have hScompact : IsCompact S := isCompact_Icc.image hmapContinuous
  have hzeros : (S ∩ {z : ℂ | XiC z = 0}).Finite :=
    finite_zeros_of_isCompact isOpen_univ
      XiC_differentiable.differentiableOn
      (fun z _ => XiRealBoundary.not_XiC_eventuallyEq_zero z)
      hScompact (Set.subset_univ S)
  have hpre :
      (xiShiftReflectedZeroMap lambda ⁻¹' (S ∩ {z : ℂ | XiC z = 0})).Finite :=
    hzeros.preimage (xiShiftReflectedZeroMap_injective lambda).injOn
  refine hpre.subset ?_
  intro omega homega
  exact ⟨⟨omega, homega.1, rfl⟩, homega.2⟩

/-- Every positive-transverse Xi zero admits a positive rational shift below its transverse
coordinate at which its reflected numerator does not cancel its shifted denominator pole. -/
theorem exists_rational_shift_uncancelled_of_xiRightZeroCopy
    (q₀ : XiRightZeroCopy) :
    ∃ omega : ℝ,
      0 < omega ∧
      omega < (I * xiSpectralPoint q₀.1).re ∧
      (∃ r : ℚ, omega = (r : ℝ)) ∧
      ∃ q : XiShiftRightZeroCopy omega,
        q.1 = q₀.1 ∧
        suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0 := by
  let a : ℝ := (I * xiSpectralPoint q₀.1).re
  let B : Set ℝ :=
    {omega ∈ Set.Icc (0 : ℝ) a |
      XiC (xiShiftReflectedZeroMap (xiSpectralPoint q₀.1) omega) = 0}
  have hB : B.Finite := by
    simpa only [B, a] using
      finite_xiShiftReflectedZeroMap_zeros_Icc (xiSpectralPoint q₀.1) 0 a
  obtain ⟨omega, homega, hnotF, r, hr⟩ :=
    exists_ratCast_mem_Ioo_not_mem_finset q₀.2 hB.toFinset
  have hnotB : omega ∉ B := by
    simpa only [Set.Finite.mem_toFinset] using hnotF
  have hXi :
      XiC (xiShiftReflectedZeroMap (xiSpectralPoint q₀.1) omega) ≠ 0 := by
    intro hzero
    exact hnotB ⟨⟨le_of_lt homega.1, le_of_lt homega.2⟩, hzero⟩
  let q : XiShiftRightZeroCopy omega := ⟨q₀.1, homega.2⟩
  refine ⟨omega, homega.1, homega.2, ⟨r, hr⟩, q, rfl, ?_⟩
  rw [suzukiCanonicalE_neg_xiShiftPoleCoordinate_eq_XiC]
  exact hXi

/-- A fully arithmetic finite witness for failure of RH: positive rational shift, uncancelled
shifted pole, and positive negative inertia on Gaussian-rational Euler-region nodes. -/
def XiShiftEulerRationalNegativeWitness : Prop :=
  ∃ (omega : ℝ),
    0 < omega ∧
    (∃ r : ℚ, omega = (r : ℝ)) ∧
    ∃ (q : XiShiftRightZeroCopy omega),
      suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0 ∧
      ∃ (N : ℕ) (w : Fin N → xiShiftEulerGaussianRationalSet omega),
        0 < hermNegIndex (Matrix.of fun i j =>
          eulerXiShiftPick omega (w j).1 (w i).1)

/-- RH fails exactly when a positive rational shift has an uncancelled pole detected by a finite
Gaussian-rational Euler Pick matrix.  This is a closed theorem with no analytic or arithmetic
premise. -/
theorem not_riemannHypothesis_iff_xiShiftEulerRationalNegativeWitness :
    ¬RiemannHypothesis ↔ XiShiftEulerRationalNegativeWitness := by
  constructor
  · intro hRH
    obtain ⟨q₀⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    obtain ⟨omega, homega, _, hrat, q, _, huncancel⟩ :=
      exists_rational_shift_uncancelled_of_xiRightZeroCopy q₀
    obtain ⟨N, w, hneg⟩ :=
      exists_gaussianRational_eulerXiShiftPick_sample_negIndex_pos_of_uncancelled
        homega q huncancel
    exact ⟨omega, homega, hrat, q, huncancel, N, w, hneg⟩
  · rintro ⟨omega, homega, _, q, _, _, _, _⟩ hRH
    letI := isEmpty_xiRightZeroCopy_of_riemannHypothesis hRH
    exact isEmptyElim (α := XiRightZeroCopy) ⟨q.1, homega.trans q.2⟩

end

end RHTower
