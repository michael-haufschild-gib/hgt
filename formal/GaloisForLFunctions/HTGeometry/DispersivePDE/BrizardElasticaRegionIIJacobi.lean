import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiAlternativeCurvature
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaJacobiSdGlobal
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaParameterRegions
import Mathlib.Tactic

/-!
# Real Jacobi `sd` curvature in paper Region II

The paper's imaginary-argument `sn` formula becomes a real `sd` profile with complementary
classical modulus `n'=1/(1-m)` and positive scale `-q₀/(1-m)`.  This module constructs that
profile globally and proves its first- and second-order curvature equations.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def regionIIComplementModulus (P : PhysicalRegionII) : ClassicalModulus := by
  have hm := (physicalRegionII_bounds P).1
  have hden : 0 < 1 - P.val.modulus := by linarith
  refine ⟨1 / (1 - P.val.modulus), one_div_pos.mpr hden, ?_⟩
  rw [div_lt_iff₀ hden]
  linarith

@[simp] theorem regionIIComplementModulus_val (P : PhysicalRegionII) :
    (regionIIComplementModulus P : ℝ) = 1 / (1 - P.val.modulus) := rfl

noncomputable def regionIIRealScale (P : PhysicalRegionII) : ℝ :=
  -(P.val.q₀ : ℝ) * (regionIIComplementModulus P : ℝ)

theorem regionIIRealScale_pos (P : PhysicalRegionII) :
    0 < regionIIRealScale P := by
  rw [regionIIRealScale]
  exact mul_pos (neg_pos.mpr P.property.1)
    (regionIIComplementModulus P).property.1

theorem regionIIRealScale_eq (P : PhysicalRegionII) :
    regionIIRealScale P = -(P.val.q₀ : ℝ) / (1 - P.val.modulus) := by
  rw [regionIIRealScale, regionIIComplementModulus_val]
  ring

noncomputable def regionIIRealScaleUnit (P : PhysicalRegionII) : ℝˣ :=
  Units.mk0 (regionIIRealScale P) (ne_of_gt (regionIIRealScale_pos P))

@[simp] theorem regionIIRealScaleUnit_val (P : PhysicalRegionII) :
    (regionIIRealScaleUnit P : ℝ) = regionIIRealScale P := rfl

/-- The transformed modulus `n=1-n'=-m/(1-m)` from Appendix A. -/
noncomputable def regionIITransformedModulus (P : PhysicalRegionII) : ℝ :=
  1 - (regionIIComplementModulus P : ℝ)

theorem regionIITransformedModulus_eq (P : PhysicalRegionII) :
    regionIITransformedModulus P =
      -P.val.modulus / (1 - P.val.modulus) := by
  rw [regionIITransformedModulus, regionIIComplementModulus_val]
  field_simp [ne_of_gt (show 0 < 1 - P.val.modulus by
    linarith [(physicalRegionII_bounds P).1])]
  ring

theorem regionIITransformedModulus_pos (P : PhysicalRegionII) :
    0 < regionIITransformedModulus P := by
  rw [regionIITransformedModulus_eq]
  exact div_pos (neg_pos.mpr (lt_trans (physicalRegionII_bounds P).1 (by norm_num)))
    (by linarith [(physicalRegionII_bounds P).1])

theorem regionII_sdGammaSq (P : PhysicalRegionII) :
    sdGammaSq (regionIIComplementModulus P : ℝ) (regionIIRealScaleUnit P) =
      gammaSq P.val := by
  rw [sdGammaSq, gammaSq, regionIIComplementModulus_val,
    regionIIRealScaleUnit_val, regionIIRealScale_eq]
  have hgap : 1 - P.val.modulus ≠ 0 := by
    linarith [(physicalRegionII_bounds P).1]
  field_simp [P.val.q₀.ne_zero, hgap]
  ring

theorem regionII_sdNuSq (P : PhysicalRegionII) :
    sdNuSq (regionIIComplementModulus P : ℝ) (regionIIRealScaleUnit P) =
      nuSq P.val := by
  rw [sdNuSq, nuSq, regionII_sdGammaSq, gammaSq,
    regionIIComplementModulus_val, regionIIRealScaleUnit_val, regionIIRealScale_eq]
  have hgap : 1 - P.val.modulus ≠ 0 := by
    linarith [(physicalRegionII_bounds P).1]
  field_simp [P.val.q₀.ne_zero, hgap]
  ring

noncomputable def regionIIJacobiSquaredCurvature
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) : ℝ :=
  sdSquaredCurvature (regionIIRealScaleUnit P) J x

noncomputable def regionIIJacobiSquaredCurvatureVelocity
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) : ℝ :=
  sdSquaredCurvatureVelocity J x

theorem regionIIJacobiSquaredCurvature_explicit
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiSquaredCurvature P J x / regionIIRealScale P =
      1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
        jacobiSd J x ^ 2 := by
  rw [regionIIJacobiSquaredCurvature, sdSquaredCurvature,
    regionIIRealScaleUnit_val, regionIITransformedModulus,
    regionIIRealScale]
  have hq : (P.val.q₀ : ℝ) ≠ 0 := P.val.q₀.ne_zero
  have hr : (regionIIComplementModulus P : ℝ) ≠ 0 :=
    ne_of_gt (regionIIComplementModulus P).property.1
  field_simp [hq, hr]
  ring

theorem regionIIJacobiSquaredCurvature_pos
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    0 < regionIIJacobiSquaredCurvature P J x := by
  have hscale := regionIIRealScale_pos P
  have hn := regionIITransformedModulus_pos P
  have hq := neg_pos.mpr P.property.1
  have hsd := sq_nonneg (jacobiSd J x)
  have hratio : 0 < regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) :=
    div_pos hn hq
  have hright : 0 < 1 + regionIITransformedModulus P / (-(P.val.q₀ : ℝ)) *
      jacobiSd J x ^ 2 := by positivity
  have hquot : 0 < regionIIJacobiSquaredCurvature P J x / regionIIRealScale P := by
    rw [regionIIJacobiSquaredCurvature_explicit]
    exact hright
  rcases div_pos_iff.mp hquot with h | h
  · exact h.1
  · exact False.elim (not_lt_of_ge hscale.le h.2)

theorem regionIIJacobiSquaredCurvature_hasDerivAt
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    HasDerivAt (regionIIJacobiSquaredCurvature P J)
      (regionIIJacobiSquaredCurvatureVelocity P J x) x := by
  exact sdSquaredCurvature_hasDerivAt (regionIIRealScaleUnit P) J
    (classicalJacobiDnRegularPoint (regionIIComplementModulus P) J x)

theorem regionIIJacobiSquaredCurvature_zero
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIJacobiSquaredCurvature P J 0 = regionIIRealScale P := by
  exact sdSquaredCurvature_zero (regionIIRealScaleUnit P) J

theorem regionIIJacobiSquaredCurvatureVelocity_zero
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIJacobiSquaredCurvatureVelocity P J 0 = 0 := by
  exact sdSquaredCurvatureVelocity_zero J

/-- Paper equation (62) after its Region II imaginary-to-real transformation. -/
theorem regionIIJacobiSquaredCurvature_equation
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiSquaredCurvatureVelocity P J x ^ 2 =
      dimensionlessCurvatureRHSWithSquares (regionIIRealScale P)
        (gammaSq P.val) (nuSq P.val)
        (regionIIJacobiSquaredCurvature P J x) := by
  have h := sdSquaredCurvature_equation (regionIIRealScaleUnit P) J
    (classicalJacobiDnRegularPoint (regionIIComplementModulus P) J x)
  simpa only [regionIIJacobiSquaredCurvature,
    regionIIJacobiSquaredCurvatureVelocity, regionIIRealScaleUnit_val,
    regionII_sdGammaSq, regionII_sdNuSq, classicalJacobiDnRegularPoint] using h

noncomputable def regionIIJacobiSquaredCurvatureAcceleration
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) : ℝ :=
  2 * (regionIIComplementModulus P : ℝ) *
    (1 - (regionIIComplementModulus P : ℝ)) *
      (jacobiSdVelocity J x ^ 2 + jacobiSd J x * jacobiSdAcceleration J x)

theorem regionIIJacobiSquaredCurvatureVelocity_hasDerivAt
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    HasDerivAt (regionIIJacobiSquaredCurvatureVelocity P J)
      (regionIIJacobiSquaredCurvatureAcceleration P J x) x := by
  have hprod := (jacobiSd_hasDerivAt_global (regionIIComplementModulus P) J x).mul
    (jacobiSdVelocity_hasDerivAt_global (regionIIComplementModulus P) J x)
  have h := hprod.const_mul
    (2 * (regionIIComplementModulus P : ℝ) *
      (1 - (regionIIComplementModulus P : ℝ)))
  change HasDerivAt
    (fun y => -2 * (-(regionIIComplementModulus P : ℝ) *
      (1 - (regionIIComplementModulus P : ℝ))) *
        jacobiSd J y * jacobiSdVelocity J y)
    (regionIIJacobiSquaredCurvatureAcceleration P J x) x
  have hderiv :
      2 * (regionIIComplementModulus P : ℝ) *
          (1 - (regionIIComplementModulus P : ℝ)) *
          (jacobiSdVelocity J x * jacobiSdVelocity J x +
            jacobiSd J x * jacobiSdAcceleration J x) =
        regionIIJacobiSquaredCurvatureAcceleration P J x := by
    rw [regionIIJacobiSquaredCurvatureAcceleration]
    ring
  apply (h.congr_deriv hderiv).congr_of_eventuallyEq
  filter_upwards with y
  simp only [Pi.mul_apply]
  ring

theorem regionIIJacobiSquaredCurvature_secondOrderEquation
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) (x : ℝ) :
    regionIIJacobiSquaredCurvatureAcceleration P J x =
      -6 * regionIIJacobiSquaredCurvature P J x ^ 2 -
        4 * gammaSq P.val * regionIIRealScale P *
          regionIIJacobiSquaredCurvature P J x +
        2 * (1 + nuSq P.val + gammaSq P.val) * regionIIRealScale P ^ 2 := by
  rw [regionIIJacobiSquaredCurvatureAcceleration,
    jacobiSd_firstIntegral_global, jacobiSdAcceleration,
    regionIIJacobiSquaredCurvature, sdSquaredCurvature,
    ← regionII_sdGammaSq P, ← regionII_sdNuSq P,
    sdNuSq, sdGammaSq, regionIIRealScaleUnit_val]
  field_simp [ne_of_gt (regionIIRealScale_pos P)]
  ring

theorem regionIIJacobiSquaredCurvatureAcceleration_zero
    (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    regionIIJacobiSquaredCurvatureAcceleration P J 0 =
      2 * (regionIIComplementModulus P : ℝ) *
        (1 - (regionIIComplementModulus P : ℝ)) := by
  rw [regionIIJacobiSquaredCurvatureAcceleration, jacobiSdVelocity_zero,
    jacobiSd_zero, jacobiSdAcceleration_zero]
  ring

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
