import GaloisForLFunctions.RHTower.RealCoronaLocalDetectabilityFracture
import GaloisForLFunctions.HTGeometry.MaximalRealDiagonalSelfAdjoint
import GaloisForLFunctions.RHTower.DeningerArithmeticOrientedHilbertHodge
import GaloisForLFunctions.RHTower.XiOrdinateEndpointObstruction

/-!
# Complete Xi-divisor local-detectability fracture

The absolute centered Xi divisor defines an unconditional self-adjoint maximal diagonal operator.
Its spectrum escapes every bound.  The canonical functional-equation orientation nevertheless
commutes with it exactly, so the associated first commutator and orientation-odd component vanish.
-/

noncomputable section

open Filter HilbertSchmidt
open GaloisForLFunctions.RHTower

namespace RHTower

/-- Absolute centered spectral coordinate of a multiplicity copy of the complete Xi divisor. -/
def xiCompleteDivisorEnergy (q : XiZeroCopy) : ℝ := ‖xiSpectralPoint q‖

/-- Unconditional self-adjoint maximal diagonal attached to every multiplicity copy of the Xi
divisor. -/
def xiCompleteDivisorDirac : XiDivisorL2 →ₗ.[ℂ] XiDivisorL2 :=
  maximalRealDiagonal xiCompleteDivisorEnergy

theorem xiCompleteDivisorDirac_isSelfAdjoint :
    IsSelfAdjoint xiCompleteDivisorDirac :=
  maximalRealDiagonal_isSelfAdjoint xiCompleteDivisorEnergy

/-- Coordinatewise canonical orientation on the completed Xi divisor. -/
def xiCompleteDivisorOrientation : Module.End ℂ XiDivisorL2 where
  toFun := fun a =>
    ⟨fun q => deningerArithmeticFEOrientation q * a q,
      (lp.memℓp a).mono' fun q => by
        rw [norm_mul, norm_deningerArithmeticFEOrientation, one_mul]⟩
  map_add' := by
    intro a b
    ext q
    change deningerArithmeticFEOrientation q * (a q + b q) =
      deningerArithmeticFEOrientation q * a q +
        deningerArithmeticFEOrientation q * b q
    ring
  map_smul' := by
    intro c a
    ext q
    change deningerArithmeticFEOrientation q * (c * a q) =
      c * (deningerArithmeticFEOrientation q * a q)
    ring

@[simp] theorem xiCompleteDivisorOrientation_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    xiCompleteDivisorOrientation a q =
      deningerArithmeticFEOrientation q * a q := rfl

theorem xiCompleteDivisorOrientation_sq :
    xiCompleteDivisorOrientation * xiCompleteDivisorOrientation = 1 := by
  apply LinearMap.ext
  intro a
  ext q
  change deningerArithmeticFEOrientation q *
      (deningerArithmeticFEOrientation q * a q) = a q
  rw [← mul_assoc, deningerArithmeticFEOrientation_sq, one_mul]

theorem norm_xiCompleteDivisorOrientation (a : XiDivisorL2) :
    ‖xiCompleteDivisorOrientation a‖ = ‖a‖ := by
  have hsq : ‖xiCompleteDivisorOrientation a‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro q
    rw [xiCompleteDivisorOrientation_apply, norm_mul,
      norm_deningerArithmeticFEOrientation, one_mul]
  nlinarith [norm_nonneg (xiCompleteDivisorOrientation a), norm_nonneg a]

/-- The orientation preserves the maximal domain because it changes no coordinate norm. -/
theorem xiCompleteDivisorOrientation_mem_domain
    (x : xiCompleteDivisorDirac.domain) :
    xiCompleteDivisorOrientation (x : XiDivisorL2) ∈
      xiCompleteDivisorDirac.domain := by
  change Memℓp
    (fun q : XiZeroCopy =>
      (xiCompleteDivisorEnergy q : ℂ) *
        xiCompleteDivisorOrientation (x : XiDivisorL2) q) 2
  exact x.property.mono' fun q => by
    rw [xiCompleteDivisorOrientation_apply]
    simp only [norm_mul, norm_deningerArithmeticFEOrientation, one_mul]
    exact le_rfl

/-- The complete divisor commutes with canonical functional-equation orientation. -/
theorem xiCompleteDivisorDirac_orientation_commutes
    (x : xiCompleteDivisorDirac.domain) :
    xiCompleteDivisorDirac
        ⟨xiCompleteDivisorOrientation (x : XiDivisorL2),
          xiCompleteDivisorOrientation_mem_domain x⟩ =
      xiCompleteDivisorOrientation (xiCompleteDivisorDirac x) := by
  ext q
  change (xiCompleteDivisorEnergy q : ℂ) *
      (deningerArithmeticFEOrientation q * (x : XiDivisorL2) q) =
    deningerArithmeticFEOrientation q *
      ((xiCompleteDivisorEnergy q : ℂ) * (x : XiDivisorL2) q)
  ring

/-- The complete-divisor first commutator with the grading is identically zero. -/
theorem xiCompleteDivisor_orientationCommutator_eq_zero
    (x : xiCompleteDivisorDirac.domain) :
    linearPMapOrientationCommutator xiCompleteDivisorDirac
      xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_domain x = 0 := by
  rw [linearPMapOrientationCommutator_apply,
    xiCompleteDivisorDirac_orientation_commutes]
  exact sub_self _

/-- The orientation-odd, locally detecting part of the complete divisor vanishes exactly. -/
theorem xiCompleteDivisor_orientationOdd_eq_zero
    (x : xiCompleteDivisorDirac.domain) :
    linearPMapOrientationOdd xiCompleteDivisorDirac
      xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_domain x = 0 := by
  have hs := LinearMap.congr_fun xiCompleteDivisorOrientation_sq
    (xiCompleteDivisorDirac x)
  change xiCompleteDivisorOrientation
      (xiCompleteDivisorOrientation (xiCompleteDivisorDirac x)) =
    xiCompleteDivisorDirac x at hs
  rw [linearPMapOrientationOdd_apply,
    xiCompleteDivisorDirac_orientation_commutes, hs]
  simp

/-- The entire complete divisor lies in the orientation-even sector. -/
theorem xiCompleteDivisor_orientationEven_eq
    (x : xiCompleteDivisorDirac.domain) :
    linearPMapOrientationEven xiCompleteDivisorDirac
      xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_domain x =
        xiCompleteDivisorDirac x := by
  have hs := LinearMap.congr_fun xiCompleteDivisorOrientation_sq
    (xiCompleteDivisorDirac x)
  change xiCompleteDivisorOrientation
      (xiCompleteDivisorOrientation (xiCompleteDivisorDirac x)) =
    xiCompleteDivisorDirac x at hs
  rw [linearPMapOrientationEven_apply,
    xiCompleteDivisorDirac_orientation_commutes, hs]
  module

/-- Canonical basis vector in the maximal complete-divisor domain. -/
def xiCompleteDivisorEigenvector (q : XiZeroCopy) :
    xiCompleteDivisorDirac.domain :=
  ⟨lpBasis XiZeroCopy q,
    lpBasis_mem_maximalRealDiagonalDomain xiCompleteDivisorEnergy q⟩

theorem xiCompleteDivisorDirac_eigenvector (q : XiZeroCopy) :
    xiCompleteDivisorDirac (xiCompleteDivisorEigenvector q) =
      (xiCompleteDivisorEnergy q : ℂ) •
        (xiCompleteDivisorEigenvector q : XiDivisorL2) := by
  ext r
  classical
  change (xiCompleteDivisorEnergy r : ℂ) * (lpBasis XiZeroCopy q) r =
    (xiCompleteDivisorEnergy q : ℂ) * (lpBasis XiZeroCopy q) r
  by_cases hr : r = q
  · subst r
    rfl
  · rw [lpBasis_apply, lp.single_apply_ne _ _ _ hr]
    simp

/-- The complete Xi-divisor Dirac operator is genuinely unbounded, unconditionally. -/
theorem xiCompleteDivisorDirac_genuinelyUnbounded :
    IsGenuinelyUnboundedLinearPMap xiCompleteDivisorDirac := by
  rintro ⟨C, hC, hbound⟩
  have hev : ∀ᶠ q : XiZeroCopy in cofinite,
      C < xiCompleteDivisorEnergy q :=
    tendsto_norm_xiSpectralPoint_cofinite.eventually
      (eventually_gt_atTop C)
  rcases hev.exists with ⟨q, hq⟩
  have hb := hbound (xiCompleteDivisorEigenvector q)
  have hnorm : ‖(xiCompleteDivisorEigenvector q : XiDivisorL2)‖ = 1 := by
    simpa [xiCompleteDivisorEigenvector] using
      (lpBasis XiZeroCopy).orthonormal.norm_eq_one q
  rw [xiCompleteDivisorDirac_eigenvector, norm_smul, hnorm, mul_one] at hb
  simp only [xiCompleteDivisorEnergy, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_one] at hb
  exact (not_lt_of_ge hb) hq

/-- **Complete-divisor local-detectability no-go.**  The grading is perfectly Lipschitz (zero
commutator), but its detecting odd component is zero while the full self-adjoint divisor operator
is genuinely unbounded. -/
theorem xiCompleteDivisor_localDetectabilityFracture :
    HasLinearPMapBoundOnDomain
        (linearPMapOrientationCommutator xiCompleteDivisorDirac
          xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_domain) ∧
      IsGenuinelyUnboundedLinearPMap xiCompleteDivisorDirac ∧
      (∀ x : xiCompleteDivisorDirac.domain,
        linearPMapOrientationOdd xiCompleteDivisorDirac
          xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_domain x = 0) := by
  refine ⟨⟨0, le_rfl, fun x => ?_⟩,
    xiCompleteDivisorDirac_genuinelyUnbounded,
    xiCompleteDivisor_orientationOdd_eq_zero⟩
  rw [xiCompleteDivisor_orientationCommutator_eq_zero, norm_zero, zero_mul]

end RHTower

