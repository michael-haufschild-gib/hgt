import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPeierlsArbitraryIncidenceRealizationNoGo

/-!
# Universal HB copywise-unit-phase darkness no-go

The universal HB Peierls cubic cut is unchanged by an arbitrary copy-dependent
unit complex phase on the plus branch together with its conjugate phase on the
minus branch. No continuity, measurability, or compatibility between copies is
assumed. Consequently, phase or sheet selection alone cannot make an off-line
Xi-zero copy dark.

This closes the phase-only repair branch of the shared proposed route

`source polarization -> BM darkness -> Ward charge zero -> HB/FZZ-P/RBH/PW-B -> RH`.

Any surviving source repair must change magnitude, carrier, propagator, or
source incidence rather than only phase/sheet.
-/

open Complex

namespace RHTower

noncomputable section

/-- Arbitrary copywise unit rephasing leaves the universal HB BM cubic cut
exactly unchanged. -/
theorem hbUniversalPeierls_copywiseUnitPhase_BM_cubicCut_eq
    (phase : XiZeroCopy -> ℂ)
    (hphase : ∀ q : XiZeroCopy, Complex.normSq (phase q) = 1)
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
        hbUniversalPeierlsPairing hbUniversalPeierlsQuadraticResidual
        (hbUniversalPeierlsPropagator
          (hbUniversalPeierlsBMTarget n amplitude q))
        (phase q • hbUniversalPeierlsPlusBranch)
        ((starRingEnd ℂ (phase q)) • hbUniversalPeierlsMinusBranch) =
      2 * hbUniversalPeierlsBMTarget n amplitude q := by
  rw [d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_smul_conj,
    hbUniversalPeierls_cubicCut_eq]
  norm_num [hphase q]

/-- With nonzero amplitude in the physical parameter range, a copywise
unit-rephased universal HB BM cut is dark exactly on the critical line. -/
theorem hbUniversalPeierls_copywiseUnitPhase_BM_cubicCut_eq_zero_iff_line
    (phase : XiZeroCopy -> ℂ)
    (hphase : ∀ q : XiZeroCopy, Complex.normSq (phase q) = 1)
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
        hbUniversalPeierlsPairing hbUniversalPeierlsQuadraticResidual
        (hbUniversalPeierlsPropagator
          (hbUniversalPeierlsBMTarget n amplitude q))
        (phase q • hbUniversalPeierlsPlusBranch)
        ((starRingEnd ℂ (phase q)) • hbUniversalPeierlsMinusBranch) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [hbUniversalPeierls_copywiseUnitPhase_BM_cubicCut_eq phase hphase,
    mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or]
  exact hbUniversalPeierlsBMTarget_eq_zero_iff ha n q hz0 hz1

/-- Proposed phase-only repair: arbitrary unit phase choices make some
off-critical-line universal HB copy dark. -/
def HBUniversalCopywiseUnitPhaseOffLineDarknessRepair : Prop :=
  ∃ phase : XiZeroCopy -> ℂ,
    (∀ q : XiZeroCopy, Complex.normSq (phase q) = 1) ∧
    ∃ (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) (z : ℝ),
      amplitude ≠ 0 ∧ 0 < z ∧ z < 1 ∧ (q.1 : ℂ).re ≠ 1 / 2 ∧
      d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
          hbUniversalPeierlsPairing hbUniversalPeierlsQuadraticResidual
          (hbUniversalPeierlsPropagator
            (hbUniversalPeierlsBMTarget n amplitude q))
          (phase q • hbUniversalPeierlsPlusBranch)
          ((starRingEnd ℂ (phase q)) • hbUniversalPeierlsMinusBranch) = 0

/-- Arbitrary copywise unit-phase or sheet selection cannot darken an off-line
universal HB copy. -/
theorem hbUniversalCopywiseUnitPhaseOffLineDarknessRepairRouteKilled :
    ¬ HBUniversalCopywiseUnitPhaseOffLineDarknessRepair := by
  rintro ⟨phase, hphase, n, amplitude, q, z, ha, hz0, hz1, hoff, hdark⟩
  exact hoff
    ((hbUniversalPeierls_copywiseUnitPhase_BM_cubicCut_eq_zero_iff_line
      phase hphase ha n q hz0 hz1).mp hdark)

end

end RHTower
