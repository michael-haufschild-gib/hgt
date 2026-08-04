import GaloisForLFunctions.RHTower.CCMRationalFiniteBruhatCyclicHaarPacket
import GaloisForLFunctions.RHTower.CCMRationalAdelicPureTensorStrongPhysical
import GaloisForLFunctions.RHTower.CCMRationalAdelicEpsilonOne

/-!
# Haar-derived dual cancellation for genuine adelic pure tensors

The second CCM endpoint of a pure tensor is a product of its archimedean and
finite Haar integrals.  If the archimedean factor vanishes, Fourier evaluation
at zero vanishes after denominator dilation.  If the finite factor vanishes,
cyclic Haar quadrature kills sum of residue weights.  Thus endpoint product
vanishing always gives exact dual Poisson cancellation.
-/

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped RestrictedProduct algebraMap Classical BigOperators FourierTransform

namespace GaloisForLFunctions
namespace RHTower

/-- Exact Fourier-zero scaling for positive denominator dilation. -/
theorem fourier_ccmRationalPositiveDenominatorDilation_zero_eq
    (f : CCMRationalArchimedeanSchwartz)
    (D : ℕ) (hD : 0 < D) :
    (𝓕 (ccmRationalPositiveDenominatorDilation f D hD)) 0 =
      (D : ℝ) • ccmRationalArchimedeanSchwartzIntegral f := by
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hD
  change (𝓕 (ccmRationalArchimedeanDilation f (D : ℝ)⁻¹
    (inv_ne_zero (ne_of_gt hDR)))) 0 = _
  rw [fourier_ccmRationalArchimedeanDilation f (inv_pos.mpr hDR)]
  simp only [zero_div]
  rw [fourier_ccmRationalArchimedean_zero_eq_integral,
    ← ccmRationalArchimedeanSchwartzIntegral_apply]
  simp only [Complex.real_smul]
  congr 1
  norm_cast
  field_simp

/-- Vanishing archimedean Haar endpoint kills Fourier zero mode after every
positive denominator dilation. -/
theorem fourier_ccmRationalPositiveDenominatorDilation_zero_of_integral_eq_zero
    (f : CCMRationalArchimedeanSchwartz)
    (D : ℕ) (hD : 0 < D)
    (hzero : ccmRationalArchimedeanSchwartzIntegral f = 0) :
    (𝓕 (ccmRationalPositiveDenominatorDilation f D hD)) 0 = 0 := by
  rw [fourier_ccmRationalPositiveDenominatorDilation_zero_eq f D hD,
    hzero, smul_zero]

/-- **Endpoint zero-mode conservation law.** Product of packet weight sum and
Fourier zero mode is exactly packet period times pure-tensor `ε₁`.  Denominator
Jacobians cancel identically. -/
theorem ccmRationalAdelicPureTensor_dualZeroMode_eq_period_nsmul_epsilonOne
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit)
    (Q : CCMRationalFiniteBruhatCyclicHaarPacket phi b) :
    (∑ r : Fin Q.period, Q.weight r) *
        (𝓕 (ccmRationalPositiveDenominatorDilation
          f Q.denominator Q.denominator_pos)) 0 =
      Q.period •
        (ccmRationalArchimedeanSchwartzIntegral f *
          ccmRationalFiniteBruhatIntegral phi) := by
  rw [Q.weightSum_eq,
    fourier_ccmRationalPositiveDenominatorDilation_zero_eq
      f Q.denominator Q.denominator_pos]
  simp only [Complex.real_smul, nsmul_eq_mul]
  push_cast
  have hD : (Q.denominator : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt Q.denominator_pos)
  field_simp [hD]

/-- **Haar-derived dual endpoint law.** For every pure tensor and genuine
profinite class-space coordinate, `ε₁ = 0` supplies a periodic trace packet
whose dual Poisson zero mode vanishes. -/
theorem ccmRationalAdelicPureTensor_exists_periodicTracePacket_dualZero_of_epsilonOne
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit)
    (hendpoint :
      ccmRationalAdelicBruhatIntegral (f ⊗ₜ[ℂ] phi) = 0) :
    ∃ P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b.1,
      (∑ r : Fin P.period, P.weight r) *
        (𝓕 (ccmRationalPositiveDenominatorDilation
          f P.denominator P.denominator_pos)) 0 = 0 := by
  obtain ⟨Q⟩ := ccmRationalFiniteBruhat_exists_cyclicHaarPacket phi b
  let P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b.1 :=
    { denominator := Q.denominator
      denominator_pos := Q.denominator_pos
      period := Q.period
      period_neZero := Q.period_neZero
      weight := Q.weight
      finiteCoefficient := Q.finiteCoefficient
      trace_eq := fun bInf => by
        rw [ccmRationalAdelicBruhatPureTensorOrbitSum_eq_integerSum
          f phi bInf b.1 Q.denominator Q.denominator_pos
          Q.rationalDenominator]
        rw [ccmRationalPeriodicWeightedTrace]
        apply tsum_congr
        intro n
        rw [← Q.finiteCoefficient n]
        rw [ccmRationalPositiveDenominatorDilation_apply]
        rw [mul_comm]
        congr 1
        ring_nf }
  refine ⟨P, ?_⟩
  have hprod :
      ccmRationalArchimedeanSchwartzIntegral f *
        ccmRationalFiniteBruhatIntegral phi = 0 := by
    simpa using hendpoint
  have hexact :=
    ccmRationalAdelicPureTensor_dualZeroMode_eq_period_nsmul_epsilonOne
      f phi b Q
  rw [hprod, nsmul_zero] at hexact
  simpa [P] using hexact

/-- Both literal CCM endpoints imply strong all-derivative, all-weight decay
of the genuine `ℚˣ` pure-tensor class-space trace. -/
theorem ccmRationalAdelicPureTensor_exists_unitLogTrace_strongLogDecay_of_endpoints
    (f : CCMRationalArchimedeanSchwartz)
    (phi : CCMRationalFiniteBruhatSchwartz)
    (b : CCMRationalProfiniteUnit)
    (hzero : ccmRationalAdelicBruhatZeroEval (f ⊗ₜ[ℂ] phi) = 0)
    (hone : ccmRationalAdelicBruhatIntegral (f ⊗ₜ[ℂ] phi) = 0) :
    ∃ P : CCMRationalAdelicPureTensorPeriodicTracePacket f phi b.1,
      (fun t : ℝ => ∑' q : CCMRationalUnit,
        ccmRationalAdelicBruhatPureTensorOrbit
          f phi (Real.exp t) b.1 (q : ℚ)) =
          @ccmRationalPeriodicWeightedLogTrace
            P.period P.period_neZero P.weight
            (ccmRationalPositiveDenominatorDilation
              f P.denominator P.denominator_pos) ∧
        RHTower.DeningerMeyerStrongLogDecay
          (fun t : ℝ => ∑' q : CCMRationalUnit,
            ccmRationalAdelicBruhatPureTensorOrbit
              f phi (Real.exp t) b.1 (q : ℚ)) := by
  obtain ⟨P, hdual⟩ :=
    ccmRationalAdelicPureTensor_exists_periodicTracePacket_dualZero_of_epsilonOne
      f phi b hone
  have hraw : f 0 * phi.1 0 = 0 := by simpa using hzero
  exact ⟨P, P.unitLogTrace_eq f phi b.1 hraw,
    P.unitLogTrace_strongLogDecay f phi b.1 hraw hdual⟩

end RHTower
end GaloisForLFunctions
