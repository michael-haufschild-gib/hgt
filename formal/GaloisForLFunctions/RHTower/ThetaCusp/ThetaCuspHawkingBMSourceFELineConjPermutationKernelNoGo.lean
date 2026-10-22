import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFERealCocycleReflectionOrbitExtinction
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianLineWronskianGreenComparison

/-!
# Line-conjugate permutation survivor for the literal source-FE Ward law

The full FE--Schwarz quartet supplies a canonical cross-orbit pairing which is symmetric,
reflection-real, algebraically nondegenerate, and source-FE covariant without RH.  Thus arbitrary
fixed-kernel nondegeneracy cannot replace selection of the local physical Peierls pairing.

`[NEW] [CANONICAL SURVIVOR] [NONDEGENERATE KERNEL] [PRODUCER NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

@[simp]
theorem hbXiPeierlsLineConj_apply_apply (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv (xiZeroCopyLineConjEquiv q) = q :=
  DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply q

theorem hbXiPeierls_copyConj_reflect_comm (q : XiZeroCopy) :
    xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv q) =
      xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q) := by
  have h := hbXiPeierlsLineConj_apply_apply (xiZeroCopyConjEquiv q)
  simpa [xiZeroCopyLineConjEquiv, Equiv.trans_apply] using
    congrArg xiZeroCopyReflectEquiv h

theorem hbXiPeierls_lineConj_reflect_comm (q : XiZeroCopy) :
    xiZeroCopyReflectEquiv (xiZeroCopyLineConjEquiv q) =
      xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q) := by
  simp only [xiZeroCopyLineConjEquiv, Equiv.trans_apply,
    xiZeroCopyReflectEquiv_apply_apply]
  rw [hbXiPeierls_copyConj_reflect_comm,
    xiZeroCopyReflectEquiv_apply_apply]

/-- The literal helicity factor respects Schwarz conjugation. -/
theorem d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_copyConj
    (q : XiZeroCopy) :
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) := by
  have hlambda :
      d4ThetaTeukolskyQuadraticChiralAngularEigenvalue
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
        (starRingEnd ℂ)
          (d4ThetaTeukolskyQuadraticChiralAngularEigenvalue (xiSpectralPoint q)) := by
    rw [d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
      d4ThetaTeukolskyQuadraticChiralAngularEigenvalue_eq,
      xiSpectralPoint_copyConj]
    simp only [map_add, map_div₀, map_ofNat, map_pow, map_one]
    ring
  rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq, hlambda]
  apply Complex.ext <;> simp

/-- The literal unit Einstein carrier respects Schwarz conjugation. -/
theorem d4ThetaHawkingSelfDualUnitCarrier_copyConj (q : XiZeroCopy) :
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1
        (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      (starRingEnd ℂ)
        (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint q)) := by
  rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
    show ((xiZeroCopyConjEquiv q).1 : ℂ) =
      (starRingEnd ℂ) (q.1 : ℂ) from deningerDivisorThetaEigen_conjEquiv q]
  simp only [one_pow, one_mul, map_mul, map_add, map_one, map_div₀, map_ofNat, map_pow]

/-- Literal BM unit source is Schwarz-real on divisor copies. -/
theorem d4BMXiSecondHarmonicUnitSource_copyConj (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) := by
  rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_copyConj,
    d4ThetaHawkingSelfDualUnitCarrier_copyConj, map_mul]

/-- Critical-line conjugation sends the literal source to the conjugate reflected source. -/
theorem d4BMXiSecondHarmonicUnitSource_lineConj (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ)
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
          (xiZeroCopyReflectEquiv q)) := by
  calc
    d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 (xiZeroCopyLineConjEquiv q) =
        d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
          (xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv q)) := by
      rw [xiZeroCopyLineConjEquiv, Equiv.trans_apply,
        hbXiPeierls_copyConj_reflect_comm]
    _ = _ := d4BMXiSecondHarmonicUnitSource_copyConj (xiZeroCopyReflectEquiv q)

/-- Schwarz conjugation of the literal source induces conjugation of its FE cocycle. -/
theorem hbXiPeierlsUnitSourceFECocycle_copyConj (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) := by
  by_cases hq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0
  · have hSq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
        (xiZeroCopyConjEquiv q) = 0 := by
      rw [d4BMXiSecondHarmonicUnitSource_copyConj, hq, map_zero]
    simp [hbXiPeierlsUnitSourceFECocycle, hq, hSq]
  · have hSq : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
        (xiZeroCopyConjEquiv q) ≠ 0 := by
      rw [d4BMXiSecondHarmonicUnitSource_copyConj]
      exact (map_ne_zero (starRingEnd ℂ)).mpr hq
    rw [hbXiPeierlsUnitSourceFECocycle, if_neg hSq,
      hbXiPeierlsUnitSourceFECocycle, if_neg hq, map_div₀,
      d4BMXiSecondHarmonicUnitSource_copyConj]
    have hnum :
        d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
            (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)) =
          (starRingEnd ℂ)
            (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
              (xiZeroCopyReflectEquiv q)) := by
      rw [← hbXiPeierls_copyConj_reflect_comm]
      exact d4BMXiSecondHarmonicUnitSource_copyConj (xiZeroCopyReflectEquiv q)
    rw [hnum]

/-- Critical-line conjugation gives the reciprocal FE cocycle. -/
theorem hbXiPeierlsUnitSourceFECocycle_lineConj_mul (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceFECocycle (xiZeroCopyLineConjEquiv q) *
        hbXiPeierlsUnitSourceFECocycle q = 1 := by
  have hinv := hbXiPeierlsUnitSourceFECocycle_involutive (xiZeroCopyConjEquiv q)
  rw [hbXiPeierlsUnitSourceFECocycle_copyConj] at hinv
  simpa [xiZeroCopyLineConjEquiv, Equiv.trans_apply] using hinv

/-- Canonical permutation kernel supported on critical-line conjugate pairs. -/
def hbXiPeierlsLineConjPermutationKernel (q r : XiZeroCopy) : ℂ :=
  if r = xiZeroCopyLineConjEquiv q then 1 else 0

@[simp]
theorem hbXiPeierlsLineConjPermutationKernel_apply_lineConj (q : XiZeroCopy) :
    hbXiPeierlsLineConjPermutationKernel q (xiZeroCopyLineConjEquiv q) = 1 := by
  simp [hbXiPeierlsLineConjPermutationKernel]

theorem hbXiPeierlsLineConjPermutationKernel_ne_zero_iff (q r : XiZeroCopy) :
    hbXiPeierlsLineConjPermutationKernel q r ≠ 0 ↔
      r = xiZeroCopyLineConjEquiv q := by
  simp [hbXiPeierlsLineConjPermutationKernel]

theorem hbXiPeierlsLineConjPermutationKernel_symmetric (q r : XiZeroCopy) :
    hbXiPeierlsLineConjPermutationKernel q r =
      hbXiPeierlsLineConjPermutationKernel r q := by
  have hiff : r = xiZeroCopyLineConjEquiv q ↔
      q = xiZeroCopyLineConjEquiv r := by
    constructor
    · intro h
      subst r
      exact (hbXiPeierlsLineConj_apply_apply q).symm
    · intro h
      subst q
      exact (hbXiPeierlsLineConj_apply_apply r).symm
  simp only [hbXiPeierlsLineConjPermutationKernel]
  rw [if_congr hiff rfl rfl]

theorem hbXiPeierlsLineConjPermutationKernel_reflectionReal :
    HBXiPeierlsReflectionRealKernel hbXiPeierlsLineConjPermutationKernel := by
  intro q r
  have hiff :
      xiZeroCopyReflectEquiv r =
          xiZeroCopyLineConjEquiv (xiZeroCopyReflectEquiv q) ↔
        r = xiZeroCopyLineConjEquiv q := by
    constructor
    · intro h
      apply xiZeroCopyReflectEquiv.injective
      rw [h, ← hbXiPeierls_lineConj_reflect_comm]
    · intro h
      subst r
      exact hbXiPeierls_lineConj_reflect_comm q
  simp only [hbXiPeierlsLineConjPermutationKernel]
  rw [if_congr hiff rfl rfl]
  by_cases h : r = xiZeroCopyLineConjEquiv q <;> simp [h]

theorem hbXiPeierlsLineConjPermutationKernel_kernelWard :
    HBXiPeierlsUnitSourceFEKernelWard hbXiPeierlsLineConjPermutationKernel := by
  intro q r
  rw [hbXiPeierlsLineConjPermutationKernel_reflectionReal q r]
  by_cases h : r = xiZeroCopyLineConjEquiv q
  · subst r
    rw [hbXiPeierlsLineConjPermutationKernel, if_pos rfl, map_one, one_mul]
    simpa [mul_comm] using hbXiPeierlsUnitSourceFECocycle_lineConj_mul q
  · rw [hbXiPeierlsLineConjPermutationKernel, if_neg h, map_zero, zero_mul, zero_mul]

/-- The canonical line-conjugate kernel form is source-FE covariant unconditionally. -/
theorem hbXiPeierlsLineConjPermutationKernel_packetTransport
    (x y : HBXiPeierlsPacket) :
    hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel
        (hbXiPeierlsUnitSourceFEPacketTransport x)
        (hbXiPeierlsUnitSourceFEPacketTransport y) =
      (starRingEnd ℂ)
        (hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel x y) :=
  hbXiPeierlsKernelForm_packetTransport_of_kernelWard
    hbXiPeierlsLineConjPermutationKernel
    hbXiPeierlsLineConjPermutationKernel_kernelWard x y

/-- Testing the second slot at the line-conjugate basis vector reads the original coefficient. -/
@[simp]
theorem hbXiPeierlsLineConjPermutationKernelForm_single_right
    (x : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel x
        (Finsupp.single (xiZeroCopyLineConjEquiv q) 1) = x q := by
  classical
  simp [hbXiPeierlsKernelForm, hbXiPeierlsLineConjPermutationKernel, eq_comm]

/-- Testing the first slot at the line-conjugate basis vector reads the original coefficient. -/
@[simp]
theorem hbXiPeierlsLineConjPermutationKernelForm_single_left
    (y : HBXiPeierlsPacket) (q : XiZeroCopy) :
    hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel
        (Finsupp.single (xiZeroCopyLineConjEquiv q) 1) y = y q := by
  classical
  simp [hbXiPeierlsKernelForm, hbXiPeierlsLineConjPermutationKernel, eq_comm]

/-- The canonical cross-orbit form has trivial left radical on finite packets. -/
theorem hbXiPeierlsLineConjPermutationKernelForm_leftRadical_iff
    (x : HBXiPeierlsPacket) :
    (∀ y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel x y = 0) ↔
      x = 0 := by
  constructor
  · intro h
    apply Finsupp.ext
    intro q
    simpa using h (Finsupp.single (xiZeroCopyLineConjEquiv q) 1)
  · rintro rfl
    simp

/-- The canonical cross-orbit form has trivial right radical on finite packets. -/
theorem hbXiPeierlsLineConjPermutationKernelForm_rightRadical_iff
    (y : HBXiPeierlsPacket) :
    (∀ x : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm hbXiPeierlsLineConjPermutationKernel x y = 0) ↔
      y = 0 := by
  constructor
  · intro h
    apply Finsupp.ext
    intro q
    simpa using h (Finsupp.single (xiZeroCopyLineConjEquiv q) 1)
  · rintro rfl
    simp

/-- Away from the critical line, line conjugation leaves the two-point FE orbit. -/
theorem hbXiPeierlsLineConj_ne_self_and_ne_reflect_of_tilt
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    xiZeroCopyLineConjEquiv q ≠ q ∧
      xiZeroCopyLineConjEquiv q ≠ xiZeroCopyReflectEquiv q := by
  constructor
  · intro h
    apply htilt
    have hfst := congrArg (fun r : XiZeroCopy => (r.1 : ℂ).re) h
    change (1 - (starRingEnd ℂ) (q.1 : ℂ)).re = (q.1 : ℂ).re at hfst
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hfst
    linarith
  · intro h
    have hfst := congrArg (fun r : XiZeroCopy => (r.1 : ℂ).im) h
    change (1 - (starRingEnd ℂ) (q.1 : ℂ)).im =
      (1 - (q.1 : ℂ)).im at hfst
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im] at hfst
    exact xi_divisor_support_im_ne_zero q.1 (by linarith)

/-- HC53's within-orbit extinction is sharp: the canonical Ward survivor has zero full tilted
FE-orbit block while retaining trivial global radicals. -/
theorem hbXiPeierlsLineConjPermutationKernel_reflectionOrbitBlock_eq_zero_of_tilt
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    hbXiPeierlsLineConjPermutationKernel q q = 0 ∧
      hbXiPeierlsLineConjPermutationKernel q (xiZeroCopyReflectEquiv q) = 0 ∧
      hbXiPeierlsLineConjPermutationKernel (xiZeroCopyReflectEquiv q) q = 0 ∧
      hbXiPeierlsLineConjPermutationKernel (xiZeroCopyReflectEquiv q)
        (xiZeroCopyReflectEquiv q) = 0 :=
  kernel_reflectionOrbitBlock_eq_zero_of_kernelWard_of_reflectionReal_of_tilt
    hbXiPeierlsLineConjPermutationKernel
    hbXiPeierlsLineConjPermutationKernel_kernelWard
    hbXiPeierlsLineConjPermutationKernel_reflectionReal q htilt

end

end RHTower
