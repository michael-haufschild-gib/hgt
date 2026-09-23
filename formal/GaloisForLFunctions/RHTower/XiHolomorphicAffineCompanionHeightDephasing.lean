import GaloisForLFunctions.RHTower.XiHolomorphicAffineCompanionFibreDeterminant
import GaloisForLFunctions.RHTower.XiWardCubicIntegerHarmonicDephasing

/-!
# Source-generated height dephasing of the affine-companion second compound

The complex-weight affine moment determinant has the usual ordered-pair expansion.  Multiplying
each pair minor by the integer-harmonic source correlation removes unequal ordinates in the limit.
The survivor is the exact equal-ordinate second compound needed by the phase-safe fibre theorem.

This module proves the finite source/dephasing connector.  It does not prove an arithmetic upper
bound for the resulting four-leg trace.
-/

open scoped BigOperators
open Complex Filter Topology Finset

namespace RHTower

noncomputable section

/-- Power moment of a finite configuration with genuinely complex weights. -/
def complexWeightedAffineMoment {ι : Type*}
    (s : Finset ι) (c z : ι → ℂ) (k : ℕ) : ℂ :=
  ∑ i ∈ s, c i * z i ^ k

/-- Central two-by-two affine moment determinant with complex weights. -/
def complexWeightedAffineCentralDet {ι : Type*}
    (s : Finset ι) (c z : ι → ℂ) : ℂ :=
  complexWeightedAffineMoment s c z 0 * complexWeightedAffineMoment s c z 2 -
    complexWeightedAffineMoment s c z 1 ^ (2 : ℕ)

/-- Complex-weight Cauchy--Binet identity.  Positivity is not asserted. -/
theorem two_mul_complexWeightedAffineCentralDet_eq_pair_sum
    {ι : Type*} (s : Finset ι) (c z : ι → ℂ) :
    2 * complexWeightedAffineCentralDet s c z =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * (z i - z j) ^ (2 : ℕ) := by
  have hexpand : ∀ i ∈ s,
      ∑ j ∈ s, c i * c j * (z i - z j) ^ (2 : ℕ) =
        c i * z i ^ (2 : ℕ) * complexWeightedAffineMoment s c z 0 -
          2 * (c i * z i) * complexWeightedAffineMoment s c z 1 +
          c i * complexWeightedAffineMoment s c z 2 := by
    intro i _hi
    rw [complexWeightedAffineMoment, complexWeightedAffineMoment,
      complexWeightedAffineMoment, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _hj => ?_
    ring
  rw [Finset.sum_congr rfl hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  have h0 : ∑ i ∈ s, c i = complexWeightedAffineMoment s c z 0 := by
    rw [complexWeightedAffineMoment]
    exact Finset.sum_congr rfl fun i _hi => by ring
  have h1 : ∑ i ∈ s, 2 * (c i * z i) =
      2 * complexWeightedAffineMoment s c z 1 := by
    rw [complexWeightedAffineMoment, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _hi => by ring
  have h2 : ∑ i ∈ s, c i * z i ^ (2 : ℕ) =
      complexWeightedAffineMoment s c z 2 := rfl
  rw [h0, h1, h2, complexWeightedAffineCentralDet]
  ring

/-- One ordered affine-companion exterior coefficient. -/
def complexWeightedAffinePairCoefficient {ι : Type*}
    (c z : ι → ℂ) (p : ι × ι) : ℂ :=
  (1 / 2 : ℂ) * c p.1 * c p.2 * (z p.1 - z p.2) ^ (2 : ℕ)

/-- Finite second-compound trace with source-native integer-harmonic ordinate dephasing. -/
def finiteAffineCompanionIntegerHarmonicTrace {ι : Type*}
    (s : Finset ι) (gamma : ι → ℝ) (c z : ι → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ s.product s,
    complexWeightedAffinePairCoefficient c z p *
      integerHarmonicOrdinateKernel (gamma p.1 - gamma p.2) N

/-- Equal-ordinate exterior trace retained after source-native dephasing. -/
def finiteAffineCompanionOrdinateFibreTrace {ι : Type*}
    (s : Finset ι) (gamma : ι → ℝ) (c z : ι → ℂ) : ℂ :=
  ∑ p ∈ s.product s with gamma p.1 = gamma p.2,
    complexWeightedAffinePairCoefficient c z p

/-- Integer source translations project the complex-weight affine second compound exactly onto
equal-ordinate fibres. -/
theorem tendsto_finiteAffineCompanionIntegerHarmonicTrace
    {ι : Type*} (s : Finset ι) (gamma : ι → ℝ) (c z : ι → ℂ) :
    Tendsto (finiteAffineCompanionIntegerHarmonicTrace s gamma c z) atTop
      (nhds (finiteAffineCompanionOrdinateFibreTrace s gamma c z)) := by
  classical
  rw [finiteAffineCompanionOrdinateFibreTrace]
  simp only [Finset.sum_filter]
  unfold finiteAffineCompanionIntegerHarmonicTrace
  apply tendsto_finsetSum
  intro p hp
  have hphase := tendsto_integerHarmonicOrdinateKernel
    (gamma p.1 - gamma p.2)
  have hscaled := hphase.const_mul (complexWeightedAffinePairCoefficient c z p)
  by_cases hgamma : gamma p.1 = gamma p.2
  · have hzero : gamma p.1 - gamma p.2 = 0 := sub_eq_zero.mpr hgamma
    rw [hzero] at hscaled
    rw [if_pos hgamma, hzero]
    simpa using hscaled
  · rw [if_neg hgamma]
    have hne : gamma p.1 - gamma p.2 ≠ 0 := sub_ne_zero.mpr hgamma
    simp only [if_neg hne, mul_zero] at hscaled
    simpa only [if_neg hne, mul_zero] using hscaled

end

end RHTower
