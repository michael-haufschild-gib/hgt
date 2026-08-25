import GaloisForLFunctions.RHTower.XiHypertranscendentalModularResidueTransgression
import GaloisForLFunctions.RHTower.XiHedenmalmJordanNormalCollision
import GaloisForLFunctions.RHTower.XiTransverseQuasiUnipotentSeparation

/-!
# The centered Xi affine residue requires a Real polarization

The reflection-balanced completed current is

`-(s - 1/2) * ξ'(s) / ξ(s)`.

At an Xi divisor point `rho` of multiplicity `m`, its residue is the nonzero vector
`-((rho - 1/2) * m)`.  Critical-line placement does not annihilate this vector: it removes only
its real component, leaving the nonzero multiplicity-weighted height in the imaginary component.

This forces a change of scalar language.  The real-linear quotient `Complex.reLm` has exactly the
imaginary axis as kernel.  Moreover, every nonzero real-linear scalar observer with that kernel is
a scalar multiple of `Complex.reLm`.  In contrast, a complex-linear observer which kills even one
actual centered Xi residue is the zero observer, because that nonzero residue spans the local
one-dimensional complex carrier.

Thus RH is a Real/Hermitian polarization law for surviving complex residues, not holomorphic
annihilation of the completed divisor current.  The exact falsifier is an off-line divisor: its
residue remains nonzero but leaves the imaginary-axis real form and its transverse character is
not quasi-unipotent.  The global landing statement is equivalent to RH; this file does not produce
that landing from the arithmetic source.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Multiplicity-exact residue of the centered affine completed-Xi current at one divisor point. -/
def xiCenteredAffineResidueVector (rho : XiDivisorSupport) : ℂ :=
  -(((rho : ℂ) - 1 / 2) * (xiSupportMultiplicity rho : ℂ))

/-- Horizontal component of the centered residue. -/
theorem xiCenteredAffineResidueVector_re (rho : XiDivisorSupport) :
    (xiCenteredAffineResidueVector rho).re =
      -((rho : ℂ).re - 1 / 2) * (xiSupportMultiplicity rho : ℝ) := by
  simp [xiCenteredAffineResidueVector, Complex.mul_re]
  ring

/-- Longitudinal component is exact multiplicity-weighted height. -/
theorem xiCenteredAffineResidueVector_im (rho : XiDivisorSupport) :
    (xiCenteredAffineResidueVector rho).im =
      -(rho : ℂ).im * (xiSupportMultiplicity rho : ℝ) := by
  simp [xiCenteredAffineResidueVector, Complex.mul_im]

/-- The transverse residue coordinate is the cofinal source-shell entropy with exact
multiplicity. -/
theorem xiCenteredAffineResidueVector_re_eq_multiplicity_mul_shellTransferEntropy
    (rho : XiDivisorSupport) :
    (xiCenteredAffineResidueVector rho).re =
      (xiSupportMultiplicity rho : ℝ) * shellTransferEntropy (rho : ℂ) := by
  rw [xiCenteredAffineResidueVector_re, shellTransferEntropy_eq]
  ring

/-- Vanishing of only the horizontal residue coordinate is exactly critical-line placement. -/
theorem xiCenteredAffineResidueVector_re_eq_zero_iff (rho : XiDivisorSupport) :
    (xiCenteredAffineResidueVector rho).re = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiCenteredAffineResidueVector_re]
  have hm : (xiSupportMultiplicity rho : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (xiSupportMultiplicity_pos rho))
  constructor
  · intro h
    have hneg : -((rho : ℂ).re - 1 / 2) = 0 :=
      (mul_eq_zero.mp h).resolve_right hm
    have : (rho : ℂ).re - 1 / 2 = 0 := neg_eq_zero.mp hneg
    linarith
  · intro h
    rw [h]
    ring

/-- The longitudinal residue coordinate never vanishes at an Xi divisor point. -/
theorem xiCenteredAffineResidueVector_im_ne_zero (rho : XiDivisorSupport) :
    (xiCenteredAffineResidueVector rho).im ≠ 0 := by
  rw [xiCenteredAffineResidueVector_im]
  exact mul_ne_zero (neg_ne_zero.mpr (xi_divisor_support_im_ne_zero rho))
    (by exact_mod_cast (Nat.ne_of_gt (xiSupportMultiplicity_pos rho)))

/-- The completed current retains a nonzero residue even on the critical line. -/
theorem xiCenteredAffineResidueVector_ne_zero (rho : XiDivisorSupport) :
    xiCenteredAffineResidueVector rho ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  exact xiCenteredAffineResidueVector_im_ne_zero rho (by simpa using him)

/-- The real form selected by vanishing horizontal charge. -/
def complexImaginaryAxis : Submodule ℝ ℂ :=
  LinearMap.ker Complex.reLm

theorem mem_complexImaginaryAxis_iff (z : ℂ) :
    z ∈ complexImaginaryAxis ↔ z.re = 0 := by
  rfl

/-- One Xi residue lands in the real form exactly on the critical line. -/
theorem xiCenteredAffineResidueVector_mem_imaginaryAxis_iff
    (rho : XiDivisorSupport) :
    xiCenteredAffineResidueVector rho ∈ complexImaginaryAxis ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [mem_complexImaginaryAxis_iff,
    xiCenteredAffineResidueVector_re_eq_zero_iff]

/-- The real-polarized residue landing is the same rank-one transverse quotient whose finite-order
monodromy is tested by quasi-unipotence. -/
theorem xiCenteredAffineResidueVector_mem_imaginaryAxis_iff_transverseQuasiUnipotent
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport) :
    xiCenteredAffineResidueVector rho ∈ complexImaginaryAxis ↔
      XiTransverseQuasiUnipotent n rho := by
  exact (xiCenteredAffineResidueVector_mem_imaginaryAxis_iff rho).trans
    (xiTransverseQuasiUnipotent_iff_re_eq_half hn rho).symm

/-- The vector above is the genuine residue of the reflection-balanced completed-Xi current. -/
theorem tendsto_xiExceptionalAffineDivisorCurrent_centeredResidueVector
    (rho : XiDivisorSupport) :
    Tendsto
      (fun s => (s - (rho : ℂ)) * xiExceptionalAffineDivisorCurrent s)
      (𝓝[≠] (rho : ℂ))
      (𝓝 (xiCenteredAffineResidueVector rho)) := by
  have horder : meromorphicOrderAt xi (rho : ℂ) =
      ((xiSupportMultiplicity rho : ℤ) : WithTop ℤ) := by
    rw [(xi_analyticOnNhd_univ (rho : ℂ) (Set.mem_univ _)).meromorphicOrderAt_eq]
    rw [xiSupportMultiplicity_eq_analyticOrderAt_toNat]
    rw [show analyticOrderAt xi (rho : ℂ) =
        ((analyticOrderAt xi (rho : ℂ)).toNat : ℕ∞) by
      exact (ENat.coe_toNat (xi_orderAt_ne_top (rho : ℂ))).symm]
    simp
  simpa [xiCenteredAffineResidueVector] using
    xiExceptionalAffineDivisorCurrent_residue horder

/-! ## Scalar-language rigidity -/

/-- A complex-linear observer which vanishes on the imaginary real form is identically zero. -/
theorem complexLinearMap_eq_zero_of_vanishes_on_imaginaryAxis
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (L : ℂ →ₗ[ℂ] W)
    (hvanish : ∀ z : ℂ, z ∈ complexImaginaryAxis → L z = 0) :
    L = 0 := by
  have hI : L Complex.I = 0 :=
    hvanish Complex.I (by simp [complexImaginaryAxis])
  have h1 : L 1 = 0 := by
    calc
      L 1 = L ((-Complex.I) • (Complex.I : ℂ)) := by norm_num
      _ = (-Complex.I) • L Complex.I := by rw [L.map_smul]
      _ = 0 := by rw [hI, smul_zero]
  apply LinearMap.ext
  intro z
  calc
    L z = L (z • (1 : ℂ)) := by simp
    _ = z • L 1 := by rw [L.map_smul]
    _ = 0 := by rw [h1, smul_zero]
    _ = (0 : ℂ →ₗ[ℂ] W) z := rfl

/-- Strong local no-go: killing one actual nonzero Xi residue already kills every complex-linear
observer on the one-dimensional residue carrier. -/
theorem complexLinearMap_eq_zero_of_kills_xiCenteredAffineResidue
    {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (L : ℂ →ₗ[ℂ] W) (rho : XiDivisorSupport)
    (hkill : L (xiCenteredAffineResidueVector rho) = 0) :
    L = 0 := by
  apply LinearMap.ext
  intro z
  let r := xiCenteredAffineResidueVector rho
  have hr : r ≠ 0 := xiCenteredAffineResidueVector_ne_zero rho
  calc
    L z = L ((z / r) • r) := by rw [smul_eq_mul, div_mul_cancel₀ z hr]
    _ = (z / r) • L r := by rw [L.map_smul]
    _ = 0 := by rw [show L r = 0 from hkill, smul_zero]
    _ = (0 : ℂ →ₗ[ℂ] W) z := rfl

/-- Every real-linear scalar observer which kills the imaginary axis is a scalar multiple of the
real-part quotient. -/
theorem realLinearMap_eq_smul_reLm_of_vanishes_on_imaginaryAxis
    (L : ℂ →ₗ[ℝ] ℝ)
    (hvanish : ∀ z : ℂ, z ∈ complexImaginaryAxis → L z = 0) :
    L = (L 1) • Complex.reLm := by
  have hI : L Complex.I = 0 :=
    hvanish Complex.I (by simp [complexImaginaryAxis])
  apply LinearMap.ext
  intro z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hz, L.map_add, L.map_smul, L.map_smul, hI]
  simp
  ring

/-- Hence every nonzero real-linear scalar observer vanishing on the required real form has exactly
that real form as kernel. -/
theorem realLinearMap_ker_eq_imaginaryAxis_of_nonzero_of_vanishes
    (L : ℂ →ₗ[ℝ] ℝ) (hL : L ≠ 0)
    (hvanish : ∀ z : ℂ, z ∈ complexImaginaryAxis → L z = 0) :
    LinearMap.ker L = complexImaginaryAxis := by
  have hclass :=
    realLinearMap_eq_smul_reLm_of_vanishes_on_imaginaryAxis L hvanish
  have hL1 : L 1 ≠ 0 := by
    intro hzero
    apply hL
    rw [hclass, hzero]
    simp
  ext z
  change L z = 0 ↔ z.re = 0
  rw [hclass]
  simp [hL1]

/-! ## Global phase and falsifier -/

/-- RH is exactly Real-polarized landing of every nonzero actual centered affine residue. -/
theorem riemannHypothesis_iff_all_xiCenteredAffineResidues_nonzero_realPolarized :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        xiCenteredAffineResidueVector rho ≠ 0 ∧
          xiCenteredAffineResidueVector rho ∈ complexImaginaryAxis := by
  constructor
  · intro hRH rho
    exact ⟨xiCenteredAffineResidueVector_ne_zero rho,
      (xiCenteredAffineResidueVector_mem_imaginaryAxis_iff rho).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)⟩
  · intro h
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro rho hzero
    let q : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    exact (xiCenteredAffineResidueVector_mem_imaginaryAxis_iff q).1 (h q).2

/-- Exact hostile falsifier: an off-line divisor retains its nonzero complex residue, but the
residue leaves the required real form and the transverse quotient loses quasi-unipotence. -/
theorem xiOffLine_falsifies_centeredAffineResidueRealPolarization
    {n : ℕ} (hn : 2 ≤ n) (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    xiCenteredAffineResidueVector rho ≠ 0 ∧
      xiCenteredAffineResidueVector rho ∉ complexImaginaryAxis ∧
      ¬ XiTransverseQuasiUnipotent n rho := by
  exact ⟨xiCenteredAffineResidueVector_ne_zero rho,
    (xiCenteredAffineResidueVector_mem_imaginaryAxis_iff rho).not.mpr hoff,
    (xiTransverseQuasiUnipotent_iff_re_eq_half hn rho).not.mpr hoff⟩

/-- Critical-line placement kills only transverse real charge: the residue and its longitudinal
height coordinate remain nonzero. -/
theorem xiCriticalLine_centeredAffineResidue_survives_in_realPolarization
    (rho : XiDivisorSupport) (hline : (rho : ℂ).re = 1 / 2) :
    xiCenteredAffineResidueVector rho ≠ 0 ∧
      xiCenteredAffineResidueVector rho ∈ complexImaginaryAxis ∧
      (xiCenteredAffineResidueVector rho).im ≠ 0 := by
  exact ⟨xiCenteredAffineResidueVector_ne_zero rho,
    (xiCenteredAffineResidueVector_mem_imaginaryAxis_iff rho).2 hline,
    xiCenteredAffineResidueVector_im_ne_zero rho⟩

end

end RHTower
