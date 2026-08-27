import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicPeierlsPolarizedLanding

/-!
# HB Peierls arbitrary-incidence realization no-go

A fixed two-dimensional complex carrier with coordinate pairing, componentwise
symmetric quadratic residual, and target-scaled symplectic propagator realizes
every complex polarized Peierls incidence. It satisfies symmetry, cubic cyclicity,
and Peierls skewness unconditionally.

Instantiating the target by the BM boundary concomitant manufactures the complete
conditional HB landing copywise for every Xi divisor. A single fixed propagator
realizes all copies exactly when that boundary target is globally constant.

Thus abstract Peierls algebra is nonselective; literal global Einstein--Teukolsky
source semantics must supply the remaining incidence and compatibility.

`[NEW] [UNIVERSAL REALIZATION] [PRODUCER NO-GO] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Fixed two-dimensional complex field/residual carrier for universal Peierls incidence. -/
abbrev HBUniversalPeierlsCarrier := ℂ × ℂ

/-- Complex-bilinear coordinate pairing. -/
def hbUniversalPeierlsPairing :
    HBUniversalPeierlsCarrier →ₗ[ℂ]
      HBUniversalPeierlsCarrier →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun x y : HBUniversalPeierlsCarrier => x.1 * y.1 + x.2 * y.2)
    (by intro x y z; simp; ring)
    (by intro c x y; simp; ring)
    (by intro x y z; simp; ring)
    (by intro c x y; simp; ring)

/-- Componentwise product, the polarization of a diagonal cubic potential. -/
def hbUniversalPeierlsQuadraticResidual :
    HBUniversalPeierlsCarrier →ₗ[ℂ]
      HBUniversalPeierlsCarrier →ₗ[ℂ] HBUniversalPeierlsCarrier :=
  LinearMap.mk₂ ℂ
    (fun x y : HBUniversalPeierlsCarrier => (x.1 * y.1, x.2 * y.2))
    (by intro x y z; ext <;> simp <;> ring)
    (by intro c x y; ext <;> simp <;> ring)
    (by intro x y z; ext <;> simp <;> ring)
    (by intro c x y; ext <;> simp <;> ring)

/-- Target-scaled standard complex symplectic rotation. -/
def hbUniversalPeierlsPropagator (T : ℂ) :
    HBUniversalPeierlsCarrier →ₗ[ℂ] HBUniversalPeierlsCarrier where
  toFun f := (-T * f.2, T * f.1)
  map_add' f g := by ext <;> simp <;> ring
  map_smul' c f := by ext <;> simp <;> ring

/-- Fixed branches whose quadratic residuals form a unit symplectic cell. -/
def hbUniversalPeierlsPlusBranch : HBUniversalPeierlsCarrier := (2, 0)

def hbUniversalPeierlsMinusBranch : HBUniversalPeierlsCarrier := (0, 1)

theorem hbUniversalPeierlsQuadraticResidual_symmetric
    (x y : HBUniversalPeierlsCarrier) :
    hbUniversalPeierlsQuadraticResidual x y =
      hbUniversalPeierlsQuadraticResidual y x := by
  ext <;> simp [hbUniversalPeierlsQuadraticResidual] <;> ring

theorem hbUniversalPeierlsPairing_quadraticResidual_cyclic
    (x y z : HBUniversalPeierlsCarrier) :
    hbUniversalPeierlsPairing x (hbUniversalPeierlsQuadraticResidual y z) =
      hbUniversalPeierlsPairing z (hbUniversalPeierlsQuadraticResidual x y) := by
  simp [hbUniversalPeierlsPairing, hbUniversalPeierlsQuadraticResidual]
  ring

theorem hbUniversalPeierlsSourcePairing_eq
    (T : ℂ) (f g : HBUniversalPeierlsCarrier) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
        (hbUniversalPeierlsPropagator T) f g =
      T * (f.1 * g.2 - f.2 * g.1) := by
  simp [d4GaugeFixedTeukolskyPeierlsSourcePairing,
    hbUniversalPeierlsPairing, hbUniversalPeierlsPropagator]
  ring

theorem hbUniversalPeierlsSourcePairing_skew
    (T : ℂ) (f g : HBUniversalPeierlsCarrier) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
        (hbUniversalPeierlsPropagator T) f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
        (hbUniversalPeierlsPropagator T) g f := by
  rw [hbUniversalPeierlsSourcePairing_eq, hbUniversalPeierlsSourcePairing_eq]
  ring

theorem hbUniversalPeierlsPlusResidual_eq :
    d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
        hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch =
      (2, 0) := by
  ext <;> norm_num [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
    hbUniversalPeierlsQuadraticResidual, hbUniversalPeierlsPlusBranch]

theorem hbUniversalPeierlsMinusResidual_eq :
    d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
        hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch =
      (0, 1 / 2) := by
  ext <;> norm_num [d4GaugeFixedTeukolskyQuadraticPlusPlusResidual,
    hbUniversalPeierlsQuadraticResidual, hbUniversalPeierlsMinusBranch]

/-- Every complex target is realized as the polarized quadratic-source incidence. -/
theorem hbUniversalPeierls_incidence_eq (T : ℂ) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
        (hbUniversalPeierlsPropagator T)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
          hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
          hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) = T := by
  rw [hbUniversalPeierlsPlusResidual_eq, hbUniversalPeierlsMinusResidual_eq,
    hbUniversalPeierlsSourcePairing_eq]
  ring

/-- The complete phase-normalized cubic cut realizes twice the arbitrary target. -/
theorem hbUniversalPeierls_cubicCut_eq (T : ℂ) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut
        hbUniversalPeierlsPairing hbUniversalPeierlsQuadraticResidual
        (hbUniversalPeierlsPropagator T)
        hbUniversalPeierlsPlusBranch hbUniversalPeierlsMinusBranch = 2 * T := by
  rw [d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized
    hbUniversalPeierlsPairing hbUniversalPeierlsQuadraticResidual
    (hbUniversalPeierlsPropagator T)
    hbUniversalPeierlsPlusBranch hbUniversalPeierlsMinusBranch
    hbUniversalPeierlsQuadraticResidual_symmetric
    hbUniversalPeierlsPairing_quadraticResidual_cyclic
    (hbUniversalPeierlsSourcePairing_skew T),
    hbUniversalPeierls_incidence_eq]

/-- BM boundary-concomitant target inserted into the universal Peierls model. -/
def hbUniversalPeierlsBMTarget
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q

/-- The missing HB source-incidence premise is realizable for every copywise BM target. -/
theorem hbUniversalPeierls_BM_incidence_eq
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
        (hbUniversalPeierlsPropagator
          (hbUniversalPeierlsBMTarget n amplitude q))
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
          hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
        (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
          hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) =
      d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q := by
  exact hbUniversalPeierls_incidence_eq
    (hbUniversalPeierlsBMTarget n amplitude q)

/-- Exact global-compatibility law: one fixed universal propagator realizes every BM copy exactly
when the complete boundary-concomitant target is constant across the Xi divisor. -/
theorem hbUniversalPeierls_fixedPropagator_BM_incidence_iff
    (T : ℂ) (n : ℕ) (amplitude : ℂ) :
    (∀ q : XiZeroCopy,
      d4GaugeFixedTeukolskyPeierlsSourcePairing hbUniversalPeierlsPairing
          (hbUniversalPeierlsPropagator T)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsPlusBranch)
          (d4GaugeFixedTeukolskyQuadraticPlusPlusResidual
            hbUniversalPeierlsQuadraticResidual hbUniversalPeierlsMinusBranch) =
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q) ↔
      ∀ q : XiZeroCopy,
        d4BMXiSecondHarmonicSourceScaledBoundaryConcomitant n amplitude q = T := by
  constructor
  · intro h q
    have hq := h q
    rw [hbUniversalPeierls_incidence_eq] at hq
    exact hq.symm
  · intro h q
    rw [hbUniversalPeierls_incidence_eq, h q]

/-- The BM target itself vanishes exactly on the critical line. -/
theorem hbUniversalPeierlsBMTarget_eq_zero_iff
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    hbUniversalPeierlsBMTarget n amplitude q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hcand := d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_eq_zero_iff
    ha n q hz0 hz1
  rw [d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_eq_two_mul_boundaryConcomitant
    n amplitude q hz0 hz1] at hcand
  simpa [hbUniversalPeierlsBMTarget] using hcand

/-- Copywise target fitting makes the complete abstract causal cut equal the BM candidate with no
additional premise: all structural Peierls axioms are satisfied by the fixed two-dimensional
carrier, while only the propagator scalar depends on the requested incidence. -/
theorem hbUniversalPeierls_BM_cokernelCausalCut_eq_candidate
    (n : ℕ) (amplitude : ℂ) (q : XiZeroCopy)
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut
        (hbUniversalPeierlsPairing hbUniversalPeierlsMinusBranch)
        hbUniversalPeierlsQuadraticResidual 0
        (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
        (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
        0 0 hbUniversalPeierlsPlusBranch hbUniversalPeierlsMinusBranch =
      d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate
        n amplitude q z := by
  apply d4BMXiSecondHarmonicCokernelCausalCut_eq_PeierlsPolarizedCandidate
    hbUniversalPeierlsPairing hbUniversalPeierlsQuadraticResidual 0
    (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
    (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
    (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
    0 0 hbUniversalPeierlsPlusBranch hbUniversalPeierlsMinusBranch
    n amplitude q hz0 hz1
  · simp
  · simp
  · exact hbUniversalPeierlsQuadraticResidual_symmetric
  · exact hbUniversalPeierlsPairing_quadraticResidual_cyclic
  · exact hbUniversalPeierlsSourcePairing_skew
      (hbUniversalPeierlsBMTarget n amplitude q)
  · exact hbUniversalPeierls_BM_incidence_eq n amplitude q

/-- The target-fitted abstract model manufactures the HB wall receiver copywise. This is a no-go,
not an RH proof: the propagator was scaled by the requested divisor-dependent BM target. -/
theorem hbUniversalPeierls_BM_retardedSection_eq_advancedSection_iff_criticalLine
    {amplitude : ℂ} (ha : amplitude ≠ 0)
    (n : ℕ) (q : XiZeroCopy) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
        (hbUniversalPeierlsPairing hbUniversalPeierlsMinusBranch)
        hbUniversalPeierlsQuadraticResidual 0
        (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
        (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
        hbUniversalPeierlsPlusBranch hbUniversalPeierlsMinusBranch =
      d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelSection
        (hbUniversalPeierlsPairing hbUniversalPeierlsMinusBranch)
        hbUniversalPeierlsQuadraticResidual 0 0 0
        hbUniversalPeierlsPlusBranch hbUniversalPeierlsMinusBranch ↔
      (q.1 : ℂ).re = 1 / 2 := by
  apply d4BMXiSecondHarmonic_retardedSection_eq_advancedSection_iff_criticalLine
    hbUniversalPeierlsPairing hbUniversalPeierlsQuadraticResidual 0
    (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
    (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
    (hbUniversalPeierlsPropagator (hbUniversalPeierlsBMTarget n amplitude q))
    0 0 hbUniversalPeierlsPlusBranch hbUniversalPeierlsMinusBranch
    ha n q hz0 hz1
  · simp
  · simp
  · exact hbUniversalPeierlsQuadraticResidual_symmetric
  · exact hbUniversalPeierlsPairing_quadraticResidual_cyclic
  · exact hbUniversalPeierlsSourcePairing_skew
      (hbUniversalPeierlsBMTarget n amplitude q)
  · exact hbUniversalPeierls_BM_incidence_eq n amplitude q

end

end RHTower
