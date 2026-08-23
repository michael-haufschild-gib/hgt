import GaloisForLFunctions.RHTower.XiWeilHardyCriticalFiberSamplingFloor

/-!
# Zero-deflated prime--Gamma trace at a Hardy critical fiber

The fixed-fiber sampling floor is not merely an abstract Hilbert projection.  Add the rational
correction

`multiplicity(ρ) * ((xiSpectralPointSupport ρ - z)⁻¹ - xiSpectralPointSupport ρ⁻¹)`

to the continued prime--Gamma relative trace and form its reflected divided difference.  A direct
resolvent identity shows that the new kernel is the original CCM source kernel minus exactly the
rank-one contribution of the complete `ρ` fiber.

For a critical-line fiber the rational term is Hermitian, so every separated packet's deflated
source energy is its original source energy minus the multiplicity-weighted squared Cauchy sample.
Consequently RH is equivalent to nonnegativity of this single zero-deflated source response on all
separated packets.  Hardy's theorem supplies the deflation point unconditionally.

This converts residual Weil positivity into a concrete passivity/Nevanlinna target for one explicit
rationally corrected source trace.  No passivity of that trace is asserted here.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Continued prime--Gamma relative trace with one complete Xi multiplicity fiber deflated.  The
constant term preserves the relative-trace normalization at `z = 0`. -/
def ccmFixedFiberDeflatedRelativeTrace
    (ρ : XiDivisorSupport) (z : ℂ) : ℂ :=
  continuedPrimeArchSourceRelativeTrace z +
    ((xiZeroCopyFiber ρ).card : ℂ) *
      ((xiSpectralPointSupport ρ - z)⁻¹ -
        (xiSpectralPointSupport ρ)⁻¹)

/-- Reflected divided-difference kernel of the fixed-fiber-deflated source trace. -/
def ccmFixedFiberDeflatedCauchyKernel
    (ρ : XiDivisorSupport) (z w : ℂ) : ℂ :=
  (ccmFixedFiberDeflatedRelativeTrace ρ ((starRingEnd ℂ) w) -
      ccmFixedFiberDeflatedRelativeTrace ρ z) /
    (z - (starRingEnd ℂ) w)

/-- The relative-resolvent contribution of a complete multiplicity fiber. -/
theorem sum_xiRelativeResolventTerm_xiZeroCopyFiber
    (ρ : XiDivisorSupport) (z : ℂ) :
    ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q =
      ((xiZeroCopyFiber ρ).card : ℂ) *
        ((xiSpectralPointSupport ρ)⁻¹ -
          (xiSpectralPointSupport ρ - z)⁻¹) := by
  calc
    ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q =
        ∑ _q ∈ xiZeroCopyFiber ρ,
          ((xiSpectralPointSupport ρ)⁻¹ -
            (xiSpectralPointSupport ρ - z)⁻¹) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [xiRelativeResolventTerm]
      have hρ : q.1 = ρ := mem_xiZeroCopyFiber.mp hq
      simp only [xiSpectralPoint_eq_support, hρ]
    _ = _ := by simp; ring

/-- On the source/Xi comparison domain, the corrected trace is literally the full Xi relative
resolvent trace with the complete `ρ` fiber removed. -/
theorem ccmFixedFiberDeflatedRelativeTrace_eq_xiTrace_sub_fiber
    (ρ : XiDivisorSupport) {z : ℂ}
    (hspos : 0 < (1 / 2 + z * Complex.I).re)
    (hs1 : 1 / 2 + z * Complex.I ≠ 1)
    (hzeta : riemannZeta (1 / 2 + z * Complex.I) ≠ 0) :
    ccmFixedFiberDeflatedRelativeTrace ρ z =
      xiRelativeResolventTrace z -
        ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q := by
  rw [ccmFixedFiberDeflatedRelativeTrace,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta,
    sum_xiRelativeResolventTerm_xiZeroCopyFiber]
  ring

/-- Zero deflation subtracts exactly the selected fiber's rank-one Cauchy kernel. -/
theorem ccmFixedFiberDeflatedCauchyKernel_eq_sub_rankOne
    (ρ : XiDivisorSupport) {z w : ℂ}
    (hz : z ≠ xiSpectralPointSupport ρ)
    (hw : (starRingEnd ℂ) w ≠ xiSpectralPointSupport ρ)
    (hzw : z ≠ (starRingEnd ℂ) w) :
    ccmFixedFiberDeflatedCauchyKernel ρ z w =
      ccmContinuedCauchyKernel z w -
        ((xiZeroCopyFiber ρ).card : ℂ) *
          (xiSpectralPointSupport ρ - z)⁻¹ *
          (xiSpectralPointSupport ρ - (starRingEnd ℂ) w)⁻¹ := by
  rw [ccmFixedFiberDeflatedCauchyKernel,
    ccmFixedFiberDeflatedRelativeTrace, ccmFixedFiberDeflatedRelativeTrace,
    ccmContinuedCauchyKernel]
  field_simp [sub_ne_zero.mpr hz.symm, sub_ne_zero.mpr hw.symm,
    sub_ne_zero.mpr hzw]
  ring

/-- The finite quadratic value of the selected rank-one correction is the multiplicity times the
squared modulus of the packet's Cauchy sample. -/
theorem fixedFiber_rankOne_packet_sum_eq
    (ρ : XiDivisorSupport) (P : XiSeparatedContinuedCauchyPacket)
    (hα : (starRingEnd ℂ) (xiSpectralPointSupport ρ) =
      xiSpectralPointSupport ρ) :
    let _ := P.fintypeIndex
    ∑ i, ∑ j, P.coeff i * (starRingEnd ℂ) (P.coeff j) *
        (((xiZeroCopyFiber ρ).card : ℂ) *
          (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹ *
          (xiSpectralPointSupport ρ -
            (starRingEnd ℂ) (P.pole j : ℂ))⁻¹) =
      ((xiZeroCopyFiber ρ).card : ℂ) *
        ((Complex.normSq
          (∑ i, P.coeff i *
            (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹) : ℝ) : ℂ) := by
  letI := P.fintypeIndex
  dsimp
  have hconj : ∀ j,
      (xiSpectralPointSupport ρ - (starRingEnd ℂ) (P.pole j : ℂ))⁻¹ =
        (starRingEnd ℂ)
          ((xiSpectralPointSupport ρ - (P.pole j : ℂ))⁻¹) := by
    intro j
    rw [map_inv₀, map_sub, hα]
  have hstep :
      ∑ i, ∑ j, P.coeff i * (starRingEnd ℂ) (P.coeff j) *
          (((xiZeroCopyFiber ρ).card : ℂ) *
            (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹ *
            (xiSpectralPointSupport ρ -
              (starRingEnd ℂ) (P.pole j : ℂ))⁻¹) =
        ((xiZeroCopyFiber ρ).card : ℂ) *
          (∑ i, P.coeff i *
            (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹) *
          (starRingEnd ℂ)
            (∑ j, P.coeff j *
              (xiSpectralPointSupport ρ - (P.pole j : ℂ))⁻¹) := by
    calc
      ∑ i, ∑ j, P.coeff i * (starRingEnd ℂ) (P.coeff j) *
          (((xiZeroCopyFiber ρ).card : ℂ) *
            (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹ *
            (xiSpectralPointSupport ρ -
              (starRingEnd ℂ) (P.pole j : ℂ))⁻¹) =
          ((xiZeroCopyFiber ρ).card : ℂ) *
            ∑ i, ∑ j,
              (P.coeff i *
                (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹) *
              (starRingEnd ℂ)
                (P.coeff j *
                  (xiSpectralPointSupport ρ - (P.pole j : ℂ))⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hconj j, map_mul]
        ring
      _ = ((xiZeroCopyFiber ρ).card : ℂ) *
          ((∑ i, P.coeff i *
              (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹) *
            ∑ j, (starRingEnd ℂ)
              (P.coeff j *
                (xiSpectralPointSupport ρ - (P.pole j : ℂ))⁻¹)) := by
        rw [Finset.sum_mul_sum]
      _ = _ := by rw [map_sum]; ring
  rw [hstep]
  rw [show ((xiZeroCopyFiber ρ).card : ℂ) *
      (∑ i, P.coeff i *
        (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹) *
      (starRingEnd ℂ)
        (∑ j, P.coeff j *
          (xiSpectralPointSupport ρ - (P.pole j : ℂ))⁻¹) =
      ((xiZeroCopyFiber ρ).card : ℂ) *
        ((∑ i, P.coeff i *
          (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹) *
        (starRingEnd ℂ)
          (∑ j, P.coeff j *
            (xiSpectralPointSupport ρ - (P.pole j : ℂ))⁻¹)) by ring,
    Complex.mul_conj]

/-- Explicit deflated source energy of a separated continued-Cauchy packet. -/
def XiSeparatedContinuedCauchyPacket.fixedFiberDeflatedSourceEnergy
    (P : XiSeparatedContinuedCauchyPacket) (ρ : XiDivisorSupport) : ℝ := by
  letI := P.fintypeIndex
  exact (∑ i, ∑ j,
    P.coeff i * (starRingEnd ℂ) (P.coeff j) *
      ccmFixedFiberDeflatedCauchyKernel ρ
        (P.pole i : ℂ) (P.pole j : ℂ)).re

/-- On a reflection-fixed fiber, deflated energy is original source energy minus its exact sampling
floor. -/
theorem XiSeparatedContinuedCauchyPacket.fixedFiberDeflatedSourceEnergy_eq
    (P : XiSeparatedContinuedCauchyPacket) (ρ : XiDivisorSupport)
    (hα : (starRingEnd ℂ) (xiSpectralPointSupport ρ) =
      xiSpectralPointSupport ρ) :
    P.fixedFiberDeflatedSourceEnergy ρ =
      P.sourceEnergy -
        ((xiZeroCopyFiber ρ).card : ℝ) *
          Complex.normSq (P.evaluation (xiFirstZeroCopy ρ)) := by
  letI := P.fintypeIndex
  have hzero : XiC (xiSpectralPointSupport ρ) = 0 := by
    simpa only [xiSpectralPoint_eq_support, xiFirstZeroCopy_fst] using
      XiC_xiSpectralPoint_eq_zero (xiFirstZeroCopy ρ)
  have hpole : ∀ i, (P.pole i : ℂ) ≠ xiSpectralPointSupport ρ := by
    intro i h
    apply (P.pole i).1.property
    rw [h]
    exact hzero
  have hpoleConj : ∀ j,
      (starRingEnd ℂ) (P.pole j : ℂ) ≠ xiSpectralPointSupport ρ := by
    intro j h
    have hz : XiC ((starRingEnd ℂ) (P.pole j : ℂ)) = 0 := by
      rw [h]
      exact hzero
    rw [XiC_conj] at hz
    apply (P.pole j).1.property
    have hz' := congrArg (starRingEnd ℂ) hz
    simpa using hz'
  have hcomplex :
      ∑ i, ∑ j,
          P.coeff i * (starRingEnd ℂ) (P.coeff j) *
            ccmFixedFiberDeflatedCauchyKernel ρ
              (P.pole i : ℂ) (P.pole j : ℂ) =
        (∑ i, ∑ j,
          P.coeff i * (starRingEnd ℂ) (P.coeff j) *
            ccmContinuedCauchyKernel (P.pole i : ℂ) (P.pole j : ℂ)) -
        ∑ i, ∑ j,
          P.coeff i * (starRingEnd ℂ) (P.coeff j) *
            (((xiZeroCopyFiber ρ).card : ℂ) *
              (xiSpectralPointSupport ρ - (P.pole i : ℂ))⁻¹ *
              (xiSpectralPointSupport ρ -
                (starRingEnd ℂ) (P.pole j : ℂ))⁻¹) := by
    simp_rw [ccmFixedFiberDeflatedCauchyKernel_eq_sub_rankOne ρ
      (hpole _) (hpoleConj _) (P.separated _ _), mul_sub,
      Finset.sum_sub_distrib]
  rw [XiSeparatedContinuedCauchyPacket.fixedFiberDeflatedSourceEnergy,
    hcomplex, Complex.sub_re,
    fixedFiber_rankOne_packet_sum_eq ρ P hα]
  change _ = P.sourceEnergy - _
  rw [P.evaluation_firstZeroCopy_eq ρ]
  change _ = continuedCauchyPacketSourceEnergy P.coeff P.pole - _
  unfold continuedCauchyPacketSourceEnergy
  simp

/-- Critical-fiber zero-deflated passivity is exactly RH. -/
theorem riemannHypothesis_iff_fixedCriticalFiber_deflatedSourceEnergy_nonnegative
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔
      ∀ P : XiSeparatedContinuedCauchyPacket,
        0 ≤ P.fixedFiberDeflatedSourceEnergy ρ := by
  have hαim : (xiSpectralPointSupport ρ).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  have hα : (starRingEnd ℂ) (xiSpectralPointSupport ρ) =
      xiSpectralPointSupport ρ := by
    apply Complex.ext
    · simp
    · simp [hαim]
  constructor
  · intro hRH P
    have hfloor :=
      (riemannHypothesis_iff_fixedFiber_samplingFloor ρ).mp hRH P
    rw [P.fixedFiberDeflatedSourceEnergy_eq ρ hα]
    linarith
  · intro hall
    apply (riemannHypothesis_iff_fixedFiber_samplingFloor ρ).mpr
    intro P
    have hres := hall P
    rw [P.fixedFiberDeflatedSourceEnergy_eq ρ hα] at hres
    linarith

/-- Hardy supplies an unconditional critical fiber whose zero-deflated source passivity is
equivalent to RH. -/
theorem exists_hardyCriticalFiber_deflatedSourceEnergy_criterion :
    ∃ ρ : XiDivisorSupport,
      (ρ : ℂ).re = 1 / 2 ∧
        (RiemannHypothesis ↔
          ∀ P : XiSeparatedContinuedCauchyPacket,
            0 ≤ P.fixedFiberDeflatedSourceEnergy ρ) := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  exact ⟨ρ, hρ,
    riemannHypothesis_iff_fixedCriticalFiber_deflatedSourceEnergy_nonnegative ρ hρ⟩

end

end RHTower
