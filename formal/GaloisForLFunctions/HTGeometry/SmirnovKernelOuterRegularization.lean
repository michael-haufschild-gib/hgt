import GaloisForLFunctions.HTGeometry.SchurOneSubOuter
import GaloisForLFunctions.HTGeometry.HardyMultiplierModelSpaceProduct

/-!
# Outer regularization of a nonzero Smirnov Toeplitz kernel

The two canonical inner factors in a Toeplitz-kernel boundary factorization can be transferred to
an outer numerator by multiplying with `1 - theta`.  The resulting symbol is, up to one constant
unit, the phase reflection of a quotient whose numerator and denominator are both outer.
-/

open Complex MeasureTheory Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Phase reflection is multiplicative for nonzero Smirnov quotients. -/
theorem DiskSmirnovBoundary.phaseReflectionSymbol_mul_ae
    (F G : DiskSmirnovBoundary)
    (hFn : ∃ z ∈ ball (0 : ℂ) 1, F.numerator.fn z ≠ 0)
    (hGn : ∃ z ∈ ball (0 : ℂ) 1, G.numerator.fn z ≠ 0) :
    (F.mul G).phaseReflectionSymbol =ᵐ[volume]
      fun x => F.phaseReflectionSymbol x * G.phaseReflectionSymbol x := by
  filter_upwards [F.boundary_mul_ae G, F.boundary_ne_zero_ae hFn,
    G.boundary_ne_zero_ae hGn] with x hmul hF hG
  have hFG : (F.mul G).boundary x ≠ 0 := by rw [hmul]; exact mul_ne_zero hF hG
  rw [DiskSmirnovBoundary.phaseReflectionSymbol,
    DiskSmirnovBoundary.phaseReflectionSymbol,
    DiskSmirnovBoundary.phaseReflectionSymbol,
    if_neg hFG, if_neg hF, if_neg hG, hmul, map_mul]
  field_simp

/-- Product of two canonical inner factors, with its exact unit analytic bound. -/
def SmirnovToeplitzKernelElement.combinedInner {U : ℝ → ℂ}
    (K : SmirnovToeplitzKernelElement U)
    (hR : ∃ z ∈ ball (0 : ℂ) 1, K.reflected.numerator.fn z ≠ 0) :
    DiskMultiplier :=
  (K.forward.innerFactor K.forward_nonzero).mul
    (K.reflected.innerFactor hR)

theorem SmirnovToeplitzKernelElement.combinedInner_bd {U : ℝ → ℂ}
    (K : SmirnovToeplitzKernelElement U)
    (hR : ∃ z ∈ ball (0 : ℂ) 1, K.reflected.numerator.fn z ≠ 0) :
    (K.combinedInner hR).bd = 1 := by
  simp [SmirnovToeplitzKernelElement.combinedInner, DiskMultiplier.mul,
    DiskSmirnovBoundary.innerFactor, diskMultiplierInnerFactor_bd]

theorem SmirnovToeplitzKernelElement.combinedInner_schur {U : ℝ → ℂ}
    (K : SmirnovToeplitzKernelElement U)
    (hR : ∃ z ∈ ball (0 : ℂ) 1, K.reflected.numerator.fn z ≠ 0)
    (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖(K.combinedInner hR).fn z‖ ≤ 1 := by
  simpa [K.combinedInner_bd hR] using (K.combinedInner hR).bd_le z hz

theorem SmirnovToeplitzKernelElement.combinedInner_line_unit_ae {U : ℝ → ℂ}
    (K : SmirnovToeplitzKernelElement U)
    (hR : ∃ z ∈ ball (0 : ℂ) 1, K.reflected.numerator.fn z ≠ 0) :
    ∀ᵐ x ∂volume, ‖diskMultiplierLineBoundary (K.combinedInner hR) x‖ = 1 := by
  filter_upwards [diskMultiplierLineBoundary_mul_ae
      (K.forward.innerFactor K.forward_nonzero)
      (K.reflected.innerFactor hR),
    ae_norm_diskMultiplierLineBoundary_innerFactor_eq_one
      K.forward.numerator K.forward_nonzero,
    ae_norm_diskMultiplierLineBoundary_innerFactor_eq_one
      K.reflected.numerator hR] with x hmul hF hRunit
  have hF' : ‖diskMultiplierLineBoundary
      (K.forward.innerFactor K.forward_nonzero) x‖ = 1 := by
    simpa [DiskSmirnovBoundary.innerFactor] using hF
  have hRunit' : ‖diskMultiplierLineBoundary
      (K.reflected.innerFactor hR) x‖ = 1 := by
    simpa [DiskSmirnovBoundary.innerFactor] using hRunit
  change ‖diskMultiplierLineBoundary
      ((K.forward.innerFactor K.forward_nonzero).mul
        (K.reflected.innerFactor hR)) x‖ = 1
  rw [hmul, norm_mul, hF', hRunit', one_mul]

/-- A nonzero kernel for a unimodular symbol makes that symbol, up to a constant unit, the phase
reflection of an outer Smirnov quotient.  No boundary-analytic or finite-Blaschke assumption is
used. -/
theorem SmirnovToeplitzKernelElement.exists_outerSmirnov_phaseReflection
    {U : ℝ → ℂ} (K : SmirnovToeplitzKernelElement U)
    (hU : ∀ᵐ x ∂volume, ‖U x‖ = 1) :
    ∃ (d : ℂ) (Q : DiskSmirnovBoundary),
      ‖d‖ = 1 ∧ IsOuterDiskMultiplier Q.numerator ∧
        U =ᵐ[volume] fun x => d * Q.phaseReflectionSymbol x := by
  obtain ⟨hR, c, hc, hfactor⟩ := K.exists_innerOuter_boundary_factorization hU
  let I := K.combinedInner hR
  let H := K.reflected.outerPart hR
  have hIschur : ∀ z ∈ ball (0 : ℂ) 1, ‖I.fn z‖ ≤ 1 :=
    fun z hz => K.combinedInner_schur hR z hz
  have hIunit : ∀ᵐ x ∂volume, ‖diskMultiplierLineBoundary I x‖ = 1 :=
    K.combinedInner_line_unit_ae hR
  have hHouter : IsOuterDiskMultiplier H.numerator :=
    K.reflected.outerPart_numerator_outer hR
  by_cases hIone : ∀ z ∈ ball (0 : ℂ) 1, I.fn z = 1
  · let Q := H
    refine ⟨(starRingEnd ℂ) c, Q, ?_, hHouter, ?_⟩
    · simpa using hc
    have hIline : diskMultiplierLineBoundary I =ᵐ[volume] fun _ => 1 := by
      have hcongr : diskMultiplierLineBoundary I =ᵐ[volume]
          diskMultiplierLineBoundary DiskMultiplier.one :=
        diskMultiplierLineBoundary_congr_ae (by
          intro z hz
          simpa [DiskMultiplier.one] using hIone z hz)
      exact hcongr.trans diskMultiplierLineBoundary_one_ae
    filter_upwards [hfactor, diskMultiplierLineBoundary_mul_ae
      (K.forward.innerFactor K.forward_nonzero)
      (K.reflected.innerFactor hR), hIline] with x hfac hImul hI
    change U x = (starRingEnd ℂ) c * H.phaseReflectionSymbol x
    calc
      U x = U x * diskMultiplierLineBoundary I x := by rw [hI, mul_one]
      _ = U x * (diskMultiplierLineBoundary
          (K.forward.innerFactor K.forward_nonzero) x *
            diskMultiplierLineBoundary (K.reflected.innerFactor hR) x) := by
              congr 1
      _ = U x * diskMultiplierLineBoundary
          (K.forward.innerFactor K.forward_nonzero) x *
            diskMultiplierLineBoundary (K.reflected.innerFactor hR) x := by rw [mul_assoc]
      _ = (starRingEnd ℂ) c * H.phaseReflectionSymbol x := hfac
  · push Not at hIone
    obtain ⟨z0, hz0, hIz0⟩ := hIone
    let A := (DiskMultiplier.const 1).sub I
    have hAouter : IsOuterDiskMultiplier A :=
      isOuterDiskMultiplier_one_sub_of_schur I hIschur ⟨z0, hz0, hIz0⟩
    let Q := H.mul (DiskSmirnovBoundary.ofMultiplier A)
    have hQouter : IsOuterDiskMultiplier Q.numerator := by
      exact hHouter.mul hAouter
    refine ⟨-(starRingEnd ℂ) c, Q, ?_, hQouter, ?_⟩
    · simpa using hc
    have hAphase := diskMultiplierPhaseReflectionSymbol_one_sub_ae
      I hIschur hIunit ⟨z0, hz0, hIz0⟩
    have hQphase := H.phaseReflectionSymbol_mul_ae
      (DiskSmirnovBoundary.ofMultiplier A)
      hHouter.exists_nonzero hAouter.exists_nonzero
    have hAof : (DiskSmirnovBoundary.ofMultiplier A).phaseReflectionSymbol
        =ᵐ[volume] diskMultiplierPhaseReflectionSymbol A := by
      filter_upwards [DiskSmirnovBoundary.boundary_ofMultiplier_ae A] with x hx
      rw [DiskSmirnovBoundary.phaseReflectionSymbol,
        diskMultiplierPhaseReflectionSymbol, hx]
    have hImul := diskMultiplierLineBoundary_mul_ae
      (K.forward.innerFactor K.forward_nonzero)
      (K.reflected.innerFactor hR)
    filter_upwards [hfactor, hAphase, hQphase, hAof, hImul, hIunit, hU]
      with x hfac hA hQ hAofx hImulx hIunitx hUx
    rw [hQ, hAofx, hA]
    have hI : diskMultiplierLineBoundary I x =
        diskMultiplierLineBoundary (K.forward.innerFactor K.forward_nonzero) x *
          diskMultiplierLineBoundary (K.reflected.innerFactor hR) x := hImulx
    have hfacI : U x * diskMultiplierLineBoundary I x =
        (starRingEnd ℂ) c * H.phaseReflectionSymbol x := by
      calc
        U x * diskMultiplierLineBoundary I x =
            U x * (diskMultiplierLineBoundary
              (K.forward.innerFactor K.forward_nonzero) x *
                diskMultiplierLineBoundary (K.reflected.innerFactor hR) x) := by rw [hI]
        _ = U x * diskMultiplierLineBoundary
              (K.forward.innerFactor K.forward_nonzero) x *
                diskMultiplierLineBoundary (K.reflected.innerFactor hR) x := by rw [mul_assoc]
        _ = (starRingEnd ℂ) c * H.phaseReflectionSymbol x := hfac
    have hIconj : diskMultiplierLineBoundary I x *
        (starRingEnd ℂ) (diskMultiplierLineBoundary I x) = 1 := by
      rw [RCLike.mul_conj, hIunitx]
      norm_num
    calc
      U x = U x * (diskMultiplierLineBoundary I x *
          (starRingEnd ℂ) (diskMultiplierLineBoundary I x)) := by rw [hIconj, mul_one]
      _ = (U x * diskMultiplierLineBoundary I x) *
          (starRingEnd ℂ) (diskMultiplierLineBoundary I x) := by ring
      _ = ((starRingEnd ℂ) c * H.phaseReflectionSymbol x) *
          (starRingEnd ℂ) (diskMultiplierLineBoundary I x) := by rw [hfacI]
      _ = -(starRingEnd ℂ) c *
          (H.phaseReflectionSymbol x *
            (-(starRingEnd ℂ) (diskMultiplierLineBoundary I x))) := by ring

end

end GaloisForLFunctions.HTGeometry
