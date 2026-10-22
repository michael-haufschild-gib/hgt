import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicHermitianSourceOrientationNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingCubicPeierlsPolarization

/-!
# HB source-fixed Peierls reflection rigidity

For one divisor-independent cyclic/skew Peierls theory, Schwarz reflection of the two linear
branch families is already enough to produce bioriented compatibility: reflection swaps the
branches, while cubic Peierls polarization changes sign under that swap.  The resulting causal cut
is therefore reflection-odd without an additional global compatibility premise.

The reflected sum of the literal unit-seed Birmingham--Mokhtari candidates is exactly twice the
Hermitian-source reflection current.  Its zero locus is the critical line.  Consequently, if one
source-fixed Schwarz-covariant Peierls theory realizes both oriented BM incidences at a divisor,
that divisor is critical; if it realizes every divisor, RH follows.

This removes biorientation/global compatibility as an independent HB proof burden.  The remaining
producer problem is the literal augmented Einstein--Teukolsky source-incidence identity itself.

`[NEW] [SOURCE-FIXED] [BIORIENTED RIGIDITY] [RH REDUCTION] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- The reflected sum of literal unit-seed BM candidates is twice the Hermitian-source
reflection current. -/
theorem d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_reflection_add_eq_two_mul_hermitianCurrent
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n 1 q (1 / 2) +
        d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n 1
          (xiZeroCopyReflectEquiv q) (1 / 2) =
      2 * d4BMXiSecondHarmonicHermitianSourceReflectionCurrent n q := by
  unfold d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate
    d4BMXiSecondHarmonicHermitianSourceReflectionCurrent
    d4BMXiSecondHarmonicHermitianSourceWeight
    d4BMXiReflectionComplexWeightedRegularComplementaryCurrent
    d4BMXiSecondHarmonicPolarizedSourceAmplitude
  repeat rw [Complex.normSq_mul]
  push_cast
  ring

variable {X Y : Type*}
  [AddCommGroup X] [Module ℂ X]
  [AddCommGroup Y] [Module ℂ Y]

/-- A single cyclic/skew Peierls theory evaluated on Schwarz-swapped branch families has a
reflection-odd cubic cut. -/
theorem d4GaugeFixedTeukolskySourceFixedPeierlsCubicCut_reflection_odd
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p m : XiZeroCopy → X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f)
    (hp : ∀ q, p (xiZeroCopyReflectEquiv q) = m q)
    (hm : ∀ q, m (xiZeroCopyReflectEquiv q) = p q)
    (q : XiZeroCopy) :
    d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta
        (p (xiZeroCopyReflectEquiv q)) (m (xiZeroCopyReflectEquiv q)) =
      -d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta (p q) (m q) := by
  rw [hp q, hm q]
  exact d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_swap
    pairing B Delta (p q) (m q) hB hcyclic hskew

/-- Source-fixed Schwarz-covariant Peierls incidence with the literal BM candidate forces the
chosen Xi fibre onto the critical line. -/
theorem d4BMXiSourceFixedPeierls_BM_incidence_forces_criticalLine
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p m : XiZeroCopy → X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f)
    (hp : ∀ q, p (xiZeroCopyReflectEquiv q) = m q)
    (hm : ∀ q, m (xiZeroCopyReflectEquiv q) = p q)
    (n : ℕ) (q : XiZeroCopy)
    (hincidence :
      d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta (p q) (m q) =
        d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n 1 q (1 / 2))
    (hincidenceReflect :
      d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta
          (p (xiZeroCopyReflectEquiv q)) (m (xiZeroCopyReflectEquiv q)) =
        d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n 1
          (xiZeroCopyReflectEquiv q) (1 / 2)) :
    (q.1 : ℂ).re = 1 / 2 := by
  apply (d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff n q).mp
  have hodd := d4GaugeFixedTeukolskySourceFixedPeierlsCubicCut_reflection_odd
    pairing B Delta p m hB hcyclic hskew hp hm q
  have hsum :
      d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n 1 q (1 / 2) +
          d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n 1
            (xiZeroCopyReflectEquiv q) (1 / 2) = 0 := by
    rw [← hincidence, ← hincidenceReflect, hodd]
    ring
  have htwo :
      2 * d4BMXiSecondHarmonicHermitianSourceReflectionCurrent n q = 0 := by
    rw [←
      d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_reflection_add_eq_two_mul_hermitianCurrent]
    exact hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Global source-fixed Schwarz-covariant Peierls incidence with literal BM data implies RH. -/
theorem d4BMXiSourceFixedPeierls_global_BM_incidence_forces_rh
    (pairing : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ)
    (B : X →ₗ[ℂ] X →ₗ[ℂ] Y) (Delta : Y →ₗ[ℂ] X)
    (p m : XiZeroCopy → X)
    (hB : ∀ x y, B x y = B y x)
    (hcyclic : ∀ x y z, pairing x (B y z) = pairing z (B x y))
    (hskew : ∀ f g, d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta f g =
      -d4GaugeFixedTeukolskyPeierlsSourcePairing pairing Delta g f)
    (hp : ∀ q, p (xiZeroCopyReflectEquiv q) = m q)
    (hm : ∀ q, m (xiZeroCopyReflectEquiv q) = p q)
    (n : ℕ)
    (hincidence : ∀ q : XiZeroCopy,
      d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut pairing B Delta (p q) (m q) =
        d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate n 1 q (1 / 2)) :
    RiemannHypothesis := by
  apply (forall_d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff_rh n).mp
  intro q
  apply (d4BMXiSecondHarmonicHermitianSourceReflectionCurrent_eq_zero_iff n q).mpr
  exact d4BMXiSourceFixedPeierls_BM_incidence_forces_criticalLine
    pairing B Delta p m hB hcyclic hskew hp hm n q (hincidence q)
      (hincidence (xiZeroCopyReflectEquiv q))

end

end RHTower
