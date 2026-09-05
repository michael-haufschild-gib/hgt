import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaLameResidual
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaParameterRegions
import Mathlib.Tactic

/-!
# Failure of the printed Lamé field throughout physical region I

The residual audit says a nondegenerate, nonzero-modulus `dn` field is exact only at `q₀=1`.
Physical region I instead forces `0<q₀<1/2`.  Thus every nonconstant interior region-I candidate
has nonzero printed residual, even though its Lamé spectral parameter is real.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Physical region-I parameters away from the constant-curvature `m=0` degeneration. -/
abbrev NonzeroPhysicalRegionI :=
  {P : PhysicalRegionI // P.val.modulus ≠ 0}

noncomputable def NonzeroPhysicalRegionI.modulusUnit
    (P : NonzeroPhysicalRegionI) : ℝˣ :=
  Units.mk0 P.val.val.modulus P.property

noncomputable def NonzeroPhysicalRegionI.lameScale
    (P : NonzeroPhysicalRegionI) : PositiveLameScale :=
  ⟨P.val.val.q₀, P.val.property.1⟩

theorem nonzeroPhysicalRegionI_q₀_ne_one (P : NonzeroPhysicalRegionI) :
    (P.val.val.q₀ : ℝ) ≠ 1 := by
  have hb := physicalRegionI_bounds P.val
  linarith [hb.2.2.2]

/-- Every nondegenerate printed `dn` candidate in physical region I has nonzero NLS residual. -/
theorem physicalRegionI_printedLameResidual_ne_zero
    (P : NonzeroPhysicalRegionI)
    (J : NondegenerateJacobiLamePoint P.val.val.modulus) :
    printedLameReducedResidual P.val.val.modulus P.lameScale J.sn J.dn ≠ 0 := by
  have hclass := printedLameReducedResidual_eq_zero_iff P.modulusUnit P.lameScale J
  intro hzero
  have hzero' :
      printedLameReducedResidual (P.modulusUnit : ℝ) P.lameScale J.sn J.dn = 0 := by
    exact hzero
  have hq := hclass.mp hzero'
  exact nonzeroPhysicalRegionI_q₀_ne_one P hq

/-- The corrected elastica amplitude and printed `dn` amplitude differ at every nondegenerate
region-I point. -/
theorem physicalRegionI_elasticaAmplitude_ne_dnSq
    (P : NonzeroPhysicalRegionI)
    (J : NondegenerateJacobiLamePoint P.val.val.modulus) :
    1 - P.val.val.modulus / (P.val.val.q₀ : ℝ) * J.sn ^ 2 ≠ J.dn ^ 2 := by
  have hdiff := elasticaAmplitudeSq_sub_dnSq P.val.val.modulus P.lameScale J.toJacobiLamePoint
  have hm : P.val.val.modulus ≠ 0 := P.property
  have hq : (P.val.val.q₀ : ℝ) ≠ 0 := P.val.val.q₀.ne_zero
  have hqone := nonzeroPhysicalRegionI_q₀_ne_one P
  change
    (1 - P.val.val.modulus / (P.val.val.q₀ : ℝ) * J.sn ^ 2) - J.dn ^ 2 =
      P.val.val.modulus * ((P.val.val.q₀ : ℝ) - 1) /
        (P.val.val.q₀ : ℝ) * J.sn ^ 2 at hdiff
  intro heq
  have hleft :
      (1 - P.val.val.modulus / (P.val.val.q₀ : ℝ) * J.sn ^ 2) - J.dn ^ 2 = 0 := by
    rw [heq, sub_self]
  rw [hleft] at hdiff
  have hfactor :
      P.val.val.modulus * ((P.val.val.q₀ : ℝ) - 1) /
          (P.val.val.q₀ : ℝ) * J.sn ^ 2 ≠ 0 := by
    exact mul_ne_zero
      (div_ne_zero (mul_ne_zero hm (sub_ne_zero.mpr hqone)) hq)
      (pow_ne_zero 2 J.sn_ne_zero)
  exact hfactor hdiff.symm

/-- Spectral reality does not repair the nonlinear amplitude mismatch. -/
theorem physicalRegionI_realSpectrum_but_nonzeroResidual
    (P : NonzeroPhysicalRegionI)
    (J : NondegenerateJacobiLamePoint P.val.val.modulus) :
    1 / 2 < lameEpsilonSq P.val.val ∧
      printedLameReducedResidual P.val.val.modulus P.lameScale J.sn J.dn ≠ 0 :=
  ⟨physicalRegionI_lameEpsilonSq_gt_half P.val,
    physicalRegionI_printedLameResidual_ne_zero P J⟩

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
