import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaPhaseSecantBounds
import GaloisForLFunctions.HTGeometry.MonotonePhaseLevelCount
import Mathlib.Tactic

/-!
# Jacobi phase as a global coordinate

A continuous strictly increasing phase with a positive global secant floor is onto the real line.
The quantitative phase bounds therefore upgrade every physical Jacobi phase to a bijection and a
canonical real-coordinate equivalence.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

structure CoercivePhase where
  phase : ℝ → ℝ
  slopeFloor : ℝ
  slopeFloor_pos : 0 < slopeFloor
  phase_zero : phase 0 = 0
  continuous : Continuous phase
  strictMono : StrictMono phase
  lower_secant : ∀ I : OrderedArclengthPair,
    slopeFloor * (I.right - I.left) ≤ phase I.right - phase I.left

theorem CoercivePhase.surjective (F : CoercivePhase) : Function.Surjective F.phase := by
  intro y
  let R : ℝ := (|y| + 1) / F.slopeFloor
  have hR : 0 < R := div_pos (by positivity) F.slopeFloor_pos
  let Ileft : OrderedArclengthPair := ⟨-R, 0, by linarith⟩
  let Iright : OrderedArclengthPair := ⟨0, R, hR.le⟩
  have hl := F.lower_secant Ileft
  have hr := F.lower_secant Iright
  have hscale : F.slopeFloor * R = |y| + 1 := by
    change F.slopeFloor * ((|y| + 1) / F.slopeFloor) = |y| + 1
    field_simp [ne_of_gt F.slopeFloor_pos]
  have hlow : F.phase (-R) ≤ y := by
    change F.slopeFloor * (0 - -R) ≤ F.phase 0 - F.phase (-R) at hl
    rw [F.phase_zero] at hl
    have hy := neg_abs_le y
    nlinarith
  have hhigh : y ≤ F.phase R := by
    change F.slopeFloor * (R - 0) ≤ F.phase R - F.phase 0 at hr
    rw [F.phase_zero] at hr
    have hy := le_abs_self y
    nlinarith
  obtain ⟨x, _, hx⟩ := GaloisForLFunctions.HTGeometry.exists_mem_Icc_eq
    (show -R ≤ R by linarith) F.continuous.continuousOn ⟨hlow, hhigh⟩
  exact ⟨x, hx⟩

theorem CoercivePhase.bijective (F : CoercivePhase) : Function.Bijective F.phase :=
  ⟨F.strictMono.injective, F.surjective⟩

noncomputable def CoercivePhase.equiv (F : CoercivePhase) : ℝ ≃ ℝ :=
  Equiv.ofBijective F.phase F.bijective

theorem CoercivePhase.existsUnique_level (F : CoercivePhase) (y : ℝ) :
    ∃! x : ℝ, F.phase x = y := by
  obtain ⟨x, hx⟩ := F.surjective y
  exact ⟨x, hx, fun z hz => F.strictMono.injective (hz.trans hx.symm)⟩

noncomputable def regionINonnegativeCoercivePhase
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) : CoercivePhase where
  phase := physicalJacobiPhase k₀ P.val J
  slopeFloor := (k₀ : ℝ) * (physicalGamma P.val + physicalNu P.val) / 2
  slopeFloor_pos := div_pos
    (mul_pos k₀.property (add_pos (physicalGamma_pos P.val) (physicalNu_pos P.val)))
    (by norm_num)
  phase_zero := physicalJacobiPhase_zero k₀ P.val J
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (physicalJacobiPhase_hasDerivAt k₀ P.val J x).continuousAt
  strictMono := physicalJacobiPhase_strictMono k₀ P.val J
  lower_secant := fun I => (regionINonnegativePhase_secant_bounds k₀ P J I).1

noncomputable def regionINegativeCoercivePhase
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) : CoercivePhase where
  phase := physicalJacobiPhase k₀ P.val J
  slopeFloor := (k₀ : ℝ) *
    (physicalGamma P.val + physicalNu P.val / regionIAmplitudeEndpoint P.val) / 2
  slopeFloor_pos := div_pos
    (mul_pos k₀.property
      (add_pos (physicalGamma_pos P.val)
        (div_pos (physicalNu_pos P.val) (regionIAmplitudeEndpoint_pos P.val))))
    (by norm_num)
  phase_zero := physicalJacobiPhase_zero k₀ P.val J
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (physicalJacobiPhase_hasDerivAt k₀ P.val J x).continuousAt
  strictMono := physicalJacobiPhase_strictMono k₀ P.val J
  lower_secant := fun I => (regionINegativePhase_secant_bounds k₀ P J I).1

noncomputable def regionIICoercivePhase
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) : CoercivePhase where
  phase := regionIIPhysicalPhase k₀ P J
  slopeFloor := (k₀ : ℝ) * regionIIGamma P / 2 +
    ((k₀ : ℝ) * regionIINu P / 2) / regionIIAmplitudeUpper P
  slopeFloor_pos := add_pos
    (div_pos (mul_pos k₀.property (regionIIGamma_pos P)) (by norm_num))
    (div_pos
      (div_pos (mul_pos k₀.property (regionIINu_pos P)) (by norm_num))
      (regionIIAmplitudeUpper_pos P))
  phase_zero := regionIIPhysicalPhase_zero k₀ P J
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (regionIIPhysicalPhase_hasDerivAt k₀ P J x).continuousAt
  strictMono := regionIIPhysicalPhase_strictMono k₀ P J
  lower_secant := fun I => (regionIIPhase_secant_bounds k₀ P J I).1

theorem regionINonnegativePhase_surjective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    Function.Surjective (physicalJacobiPhase k₀ P.val J) :=
  (regionINonnegativeCoercivePhase k₀ P J).surjective

theorem regionINegativePhase_surjective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    Function.Surjective (physicalJacobiPhase k₀ P.val J) :=
  (regionINegativeCoercivePhase k₀ P J).surjective

theorem regionIIPhase_surjective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    Function.Surjective (regionIIPhysicalPhase k₀ P J) :=
  (regionIICoercivePhase k₀ P J).surjective

theorem regionINonnegativePhase_bijective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINonnegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    Function.Bijective (physicalJacobiPhase k₀ P.val J) :=
  ⟨physicalJacobiPhase_injective k₀ P.val J,
    regionINonnegativePhase_surjective k₀ P J⟩

theorem regionINegativePhase_bijective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionINegativeModulus)
    (J : JacobiEllipticSystem P.val.val.modulus) :
    Function.Bijective (physicalJacobiPhase k₀ P.val J) :=
  ⟨physicalJacobiPhase_injective k₀ P.val J,
    regionINegativePhase_surjective k₀ P J⟩

theorem regionIIPhase_bijective
    (k₀ : PositiveCurvatureScale) (P : PhysicalRegionII)
    (J : JacobiEllipticSystem (regionIIComplementModulus P : ℝ)) :
    Function.Bijective (regionIIPhysicalPhase k₀ P J) :=
  ⟨regionIIPhysicalPhase_injective k₀ P J, regionIIPhase_surjective k₀ P J⟩

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
