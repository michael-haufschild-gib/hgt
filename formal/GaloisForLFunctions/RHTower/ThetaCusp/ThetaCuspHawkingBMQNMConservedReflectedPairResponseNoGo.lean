import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFEQNMGeneratorLocalityNoGo

/-!
# QNM-conserved reflected-pair response no-go

The strongest known algebraic escape from the literal BM response obstruction is a
division-free compensator that reads the functional-equation-reflected Xi copy. This file proves
that stationary QNM time conservation excludes the entire reflected-pair mechanism, not only that
example.

QNM-generator conservation forces every packet kernel to be spectral-fibre local. Away from the
critical wall a copy and its functional-equation reflection have different support, so their kernel
coefficient is zero. On the wall the literal BM source amplitude is zero. Consequently the complete
source--kernel--radial response charge induced by a reflected-pair coefficient vanishes on every Xi
copy.

This kills the proposed chain

`stationary reflected-pair response -> nontrivial BM cancellation -> shared Ward zero ->
HB/FZZ-P/RBH/PW-B -> RH`.

Any surviving nontrivial reflected-pair producer must break QNM time conservation or cease to arise
from a finite-packet bilinear kernel coefficient.
-/

open Complex

namespace RHTower

noncomputable section

/-- QNM-generator conservation forbids every reflected cross-fibre coefficient off the critical
wall. -/
theorem hbXiPeierlsQNMGeneratorWard_reflectionCoefficient_eq_zero_of_offLine
    (m : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsQNMGeneratorWard m K)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    K q (xiZeroCopyReflectEquiv q) = 0 := by
  have hlocal : HBXiPeierlsSpectralFibreLocalKernel K :=
    (hbXiPeierlsQNMGeneratorWard_iff_spectralLocal m K).mp hward
  by_contra hcoeff
  have hsupport : q.1 = (xiZeroCopyReflectEquiv q).1 :=
    hlocal q (xiZeroCopyReflectEquiv q) hcoeff
  have hre := congrArg (fun r : XiDivisorSupport => (r : ℂ).re) hsupport
  rw [xiZeroCopyReflect_re_eq_one_sub] at hre
  apply hoff
  linarith

/-- Composite BM response charge induced by the reflected-pair coefficient of a packet kernel. -/
def hbXiPeierlsQNMKernelReflectionResponseCharge
    (n : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q *
    K q (xiZeroCopyReflectEquiv q) *
      d4BMXiPlusPlusComplementaryExponent n q

/-- QNM time conservation forces the induced reflected-pair response charge to vanish on every Xi
copy: spectral locality kills it off wall, and source extinction kills it on wall. -/
theorem hbXiPeierlsQNMKernelReflectionResponseCharge_eq_zero
    (m n : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsQNMGeneratorWard m K) (q : XiZeroCopy) :
    hbXiPeierlsQNMKernelReflectionResponseCharge n K q = 0 := by
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · have hsource : d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q = 0 :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    rw [hbXiPeierlsQNMKernelReflectionResponseCharge, hsource]
    simp only [zero_mul]
  · have hkernel :=
      hbXiPeierlsQNMGeneratorWard_reflectionCoefficient_eq_zero_of_offLine
        m K hward q hline
    rw [hbXiPeierlsQNMKernelReflectionResponseCharge, hkernel]
    simp only [mul_zero, zero_mul]

/-- Proposed nontrivial stationary reflected-pair producer. -/
def HBXiPeierlsQNMConservedNontrivialReflectedPairResponseProducer : Prop :=
  ∃ (m n : ℕ) (K : XiZeroCopy → XiZeroCopy → ℂ) (q : XiZeroCopy),
    HBXiPeierlsQNMGeneratorWard m K ∧
    hbXiPeierlsQNMKernelReflectionResponseCharge n K q ≠ 0

/-- Premise-free certificate: no QNM-conserved packet kernel can produce a nonzero reflected-pair
BM response charge. -/
theorem hbXiPeierlsQNMConservedNontrivialReflectedPairResponseProducerRouteKilled :
    ¬ HBXiPeierlsQNMConservedNontrivialReflectedPairResponseProducer := by
  rintro ⟨m, n, K, q, hward, hnonzero⟩
  exact hnonzero
    (hbXiPeierlsQNMKernelReflectionResponseCharge_eq_zero m n K hward q)

end

end RHTower
