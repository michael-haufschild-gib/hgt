import GaloisForLFunctions.RHTower.SuzukiApertureBoundedCoordinate
import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The coalescing defect on any bounded-coordinate aperture

Theorem E in the model Suzuki's operator actually uses.  The two parity energies of the movable
deficiency base are the real parts of resolvent quadratic forms of `cosh(cX)` and `sinh(cX)`; as the
base collapses the even profile tends to the constant source vector and the normalized odd profile
to the position source vector, so the defect gap is exactly twice the squared base times the
position-to-constant resolvent quotient.

Nothing in the statement mentions the aperture model: any finite measure space with a bounded real
coordinate carries it, and the Suzuki interval is one.
-/

open MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  (B : BoundedCoordinate Ω μ)

/-- `(44)`: the even resolvent energy of the movable deficiency base. -/
def coalescingEvenEnergy (R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : ℝ) : ℝ :=
  (inner ℂ (B.coshVecC c) (R (B.coshVecC c)) : ℂ).re

/-- `(44)`: the odd resolvent energy of the movable deficiency base. -/
def coalescingOddEnergy (R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (c : ℝ) : ℝ :=
  (inner ℂ (B.sinhVecC c) (R (B.sinhVecC c)) : ℂ).re

/-- `(45)`: the intrinsic source tangent, the position-to-constant resolvent quotient. -/
def positionResolventTangent (R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : ℝ :=
  (inner ℂ (B.monomialC 1) (R (B.monomialC 1)) : ℂ).re /
    (inner ℂ (B.monomialC 0) (R (B.monomialC 0)) : ℂ).re

/-- **Theorem E `(46)`, model-free.**  The coalescing defect gap is twice the squared base times the
position-resolvent quotient. -/
theorem tendsto_one_sub_coalescingDefect_rate (R : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hR : 0 < (inner ℂ (B.monomialC 0) (R (B.monomialC 0)) : ℂ).re) :
    Tendsto (fun c : ℝ =>
        (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle (coalescingEvenEnergy B R c)
          (coalescingOddEnergy B R c)) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (positionResolventTangent B R)) := by
  have hcosh := B.tendsto_coshVecC
  have hsinh := B.tendsto_inv_smul_sinhVecC
  have hE : Tendsto (fun c : ℝ => coalescingEvenEnergy B R c) (𝓝[>] (0 : ℝ))
      (𝓝 ((inner ℂ (B.monomialC 0) (R (B.monomialC 0)) : ℂ).re)) :=
    (Complex.continuous_re.tendsto _).comp
      (hcosh.inner ((R.continuous.tendsto _).comp hcosh))
  have hOsq : Tendsto (fun c : ℝ => coalescingOddEnergy B R c / c ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 ((inner ℂ (B.monomialC 1) (R (B.monomialC 1)) : ℂ).re)) := by
    have h : Tendsto (fun c : ℝ =>
        (inner ℂ (c⁻¹ • B.sinhVecC c) (R (c⁻¹ • B.sinhVecC c)) : ℂ).re)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((inner ℂ (B.monomialC 1) (R (B.monomialC 1)) : ℂ).re)) :=
      (Complex.continuous_re.tendsto _).comp
        (hsinh.inner ((R.continuous.tendsto _).comp hsinh))
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcpos : (0 : ℝ) < c := mem_Ioi.mp hc
    have hmap : R (c⁻¹ • B.sinhVecC c) = c⁻¹ • R (B.sinhVecC c) :=
      (R.restrictScalars ℝ).map_smul c⁻¹ (B.sinhVecC c)
    rw [coalescingOddEnergy, hmap,
      show (c⁻¹ • B.sinhVecC c) = ((c⁻¹ : ℝ) : ℂ) • B.sinhVecC c from
        (Complex.coe_smul _ _).symm,
      show (c⁻¹ • R (B.sinhVecC c)) = ((c⁻¹ : ℝ) : ℂ) • R (B.sinhVecC c) from
        (Complex.coe_smul _ _).symm,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    field_simp
  have hc2 : Tendsto (fun c : ℝ => c ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => c ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have hO : Tendsto (fun c : ℝ => coalescingOddEnergy B R c) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hc2.mul hOsq
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcpos : (0 : ℝ) < c := mem_Ioi.mp hc
    field_simp
  have hsum : Tendsto (fun c : ℝ =>
        coalescingEvenEnergy B R c + coalescingOddEnergy B R c) (𝓝[>] (0 : ℝ))
      (𝓝 ((inner ℂ (B.monomialC 0) (R (B.monomialC 0)) : ℂ).re)) := by
    have h := hE.add hO
    rwa [add_zero] at h
  have hne : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      coalescingEvenEnergy B R c + coalescingOddEnergy B R c ≠ 0 :=
    hsum.eventually (eventually_ne_nhds (ne_of_gt hR))
  have hlim := hOsq.div hsum (ne_of_gt hR)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hne] with c hc hden
  have hcpos : (0 : ℝ) < c := mem_Ioi.mp hc
  simp only [Pi.div_apply, GaloisForLFunctions.RHTower.suzukiDefectAngle]
  field_simp
  ring

/-! ## Suzuki's literal interval -/

attribute [local instance] Measure.Subtype.measureSpace

/-- **Theorem E on Suzuki's literal interval space.**  The model gap is closed: the coalescing
tangent law holds verbatim for bounded operators on `SuzukiApertureIntervalL2`. -/
theorem tendsto_one_sub_suzukiIntervalDefect_rate {a : ℝ} (ha : 0 ≤ a)
    (R : SuzukiApertureIntervalL2 a →L[ℂ] SuzukiApertureIntervalL2 a)
    (hR : 0 < (inner ℂ ((suzukiApertureCoordinate ha).monomialC 0)
        (R ((suzukiApertureCoordinate ha).monomialC 0)) : ℂ).re) :
    Tendsto (fun c : ℝ =>
        (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          (coalescingEvenEnergy (suzukiApertureCoordinate ha) R c)
          (coalescingOddEnergy (suzukiApertureCoordinate ha) R c)) / (2 * c ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (positionResolventTangent (suzukiApertureCoordinate ha) R)) :=
  tendsto_one_sub_coalescingDefect_rate (suzukiApertureCoordinate ha) R hR

end RHTower
