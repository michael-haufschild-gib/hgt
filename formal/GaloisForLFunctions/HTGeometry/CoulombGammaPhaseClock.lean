import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection

/-!
# The Coulomb Gamma phase as a unitary hypertranscendental clock

For angular momentum `ell`, the Coulomb partial-wave scattering phase is

`exp(2 i sigma_ell(eta)) = Gamma(ell+1+i eta) / Gamma(ell+1-i eta)`.

This module proves two complementary facts about that exact observable.  On the physical real
Sommerfeld parameter it has unit modulus, obeys parameter reflection, and adjacent partial waves
differ only by an elementary rational phase.  In the complex Sommerfeld coordinate its
meromorphic continuation has oriented Gamma charge two and is hypertranscendental.  Thus bounded
phase-only observation does not imply finite differential complexity: the complexity is in the
clock's value structure, not in a temporal evolution law.

The physics formula is equation (1) of Barata--Canto--Hussein,
*The Coulomb Phase Shift Revisited*, arXiv:0912.3189.  The identification is external to Lean;
all Gamma identities and differential-algebraic conclusions below are internal.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance coulombGammaPhaseDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance coulombGammaPhaseIntAlgebraAnalytic :
    Algebra ℤ (analyticSubring Set.univ) := Ring.toIntAlgebra _

local instance coulombGammaPhaseIntAlgebraMero :
    Algebra ℤ (meroField Set.univ) := Ring.toIntAlgebra _

local instance coulombGammaPhaseIntAlgebraRatFunc :
    Algebra ℤ (RatFunc ℂ) := Ring.toIntAlgebra _

local instance coulombGammaPhaseDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance coulombGammaPhaseRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance coulombGammaPhaseRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance coulombGammaPhaseDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance coulombGammaPhaseCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The complexified Coulomb partial-wave phase in the Sommerfeld coordinate `z`:
`Gamma(z+ell+1) / Gamma(-z+ell+1)`. -/
def coulombPhaseMero (ell : ℕ) : meroField Set.univ :=
  gammaShiftMero ((ell + 1 : ℕ) : ℂ) /
    gammaNegativeShiftMero ((ell + 1 : ℕ) : ℂ)

/-- The Coulomb phase is a one-orbit oriented Gamma product with charge two.  One cell carries
the negative-slope denominator with exponent `-1`; the other carries the positive-slope
numerator, separated by the integer shift `2*ell+1`. -/
theorem coulombPhaseMero_eq_orientedProduct (ell : ℕ) :
    coulombPhaseMero ell =
      gammaOrientedProductMero
        (fun _ : Fin 1 => -(ell : ℂ))
        (fun _ : Fin 1 => ![0, 2 * ell + 1])
        (fun _ : Fin 1 => ![0, 1])
        (fun _ : Fin 1 => ![-1, 0]) := by
  simp [coulombPhaseMero, gammaOrientedProductMero, div_eq_mul_inv]
  ring

/-- **Coulomb-phase differential boundary.**  Every complexified Coulomb partial-wave phase is
hypertranscendental over the rational function field.  Euler reflection places both Gamma
contributions on one translation orbit and their oriented charge is `1 - (-1) = 2`. -/
theorem hypertranscendentalOver_coulombPhaseMero (ell : ℕ) :
    HypertranscendentalOver (RatFunc ℂ) (coulombPhaseMero ell) := by
  rw [coulombPhaseMero_eq_orientedProduct]
  let b : Fin 1 → ℂ := fun _ => -(ell : ℂ)
  let nn : Fin 1 → Fin 2 → ℕ := fun _ => ![0, 2 * ell + 1]
  let p : Fin 1 → Fin 2 → ℤ := fun _ => ![0, 1]
  let n : Fin 1 → Fin 2 → ℤ := fun _ => ![-1, 0]
  have h :=
    (hypertranscendentalOver_mul_gammaOrientedProductMero_iff_exists_charge_ne_zero
      b nn p n 1 one_ne_zero
      (by simpa using
        (HTGeometry.differentialAlgebraicOver_algebraMap
          (F := RatFunc ℂ) (E := meroField Set.univ) 1))
      (fun c c' hcc => (hcc (Subsingleton.elim c c')).elim)).2
      (by
        refine ⟨0, ?_⟩
        norm_num [gammaOrientedOrbitCharge, p, n])
  simpa [b, nn, p, n] using h

/-- The actual Coulomb partial-wave scattering phase on a real Sommerfeld parameter. -/
def coulombPhaseValue (ell : ℕ) (eta : ℝ) : ℂ :=
  Complex.Gamma (((ell + 1 : ℕ) : ℂ) + Complex.I * (eta : ℂ)) /
    Complex.Gamma (((ell + 1 : ℕ) : ℂ) - Complex.I * (eta : ℂ))

/-- **Physical unitarity.**  The Coulomb partial-wave phase has unit modulus for every real
Sommerfeld parameter, even though its complex continuation is hypertranscendental. -/
theorem norm_coulombPhaseValue (ell : ℕ) (eta : ℝ) :
    ‖coulombPhaseValue ell eta‖ = 1 := by
  have hden : Complex.Gamma (((ell + 1 : ℕ) : ℂ) - Complex.I * (eta : ℂ)) =
      starRingEnd ℂ (Complex.Gamma
        (((ell + 1 : ℕ) : ℂ) + Complex.I * (eta : ℂ))) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp
    ring
  have hGamma : Complex.Gamma
      (((ell + 1 : ℕ) : ℂ) + Complex.I * (eta : ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp
    positivity
  rw [coulombPhaseValue, hden]
  rw [norm_div, norm_conj, div_self (norm_ne_zero_iff.mpr hGamma)]

/-- Adjacent partial waves differ by the elementary unit-modulus rational phase
`(ell+1+i*eta)/(ell+1-i*eta)`.  Thus changing angular momentum modifies only a finite
observable gauge and does not remove the Gamma source. -/
theorem coulombPhaseValue_succ (ell : ℕ) (eta : ℝ) :
    coulombPhaseValue (ell + 1) eta =
      ((((ell + 1 : ℕ) : ℂ) + Complex.I * (eta : ℂ)) /
        (((ell + 1 : ℕ) : ℂ) - Complex.I * (eta : ℂ))) *
          coulombPhaseValue ell eta := by
  let zp : ℂ := ((ell + 1 : ℕ) : ℂ) + Complex.I * (eta : ℂ)
  let zm : ℂ := ((ell + 1 : ℕ) : ℂ) - Complex.I * (eta : ℂ)
  have hzp : zp ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [zp] at hre
    have hpos : (0 : ℝ) < (ell : ℝ) + 1 := by positivity
    linarith
  have hzm : zm ≠ 0 := by
    intro hz
    have hre := congrArg Complex.re hz
    simp [zm] at hre
    have hpos : (0 : ℝ) < (ell : ℝ) + 1 := by positivity
    linarith
  have hGm : Complex.Gamma zm ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [zm]
    positivity
  have hp := Complex.Gamma_add_one zp hzp
  have hm := Complex.Gamma_add_one zm hzm
  rw [coulombPhaseValue, coulombPhaseValue]
  have hpArg : (((ell + 1 + 1 : ℕ) : ℂ) + Complex.I * (eta : ℂ)) = zp + 1 := by
    simp [zp]
    ring
  have hmArg : (((ell + 1 + 1 : ℕ) : ℂ) - Complex.I * (eta : ℂ)) = zm + 1 := by
    simp [zm]
    ring
  rw [hpArg, hmArg]
  change Complex.Gamma (zp + 1) / Complex.Gamma (zm + 1) =
    (zp / zm) * (Complex.Gamma zp / Complex.Gamma zm)
  rw [hp, hm]
  field_simp [hzm, hGm]

/-- Parameter reflection reverses the observed Coulomb phase. -/
theorem coulombPhaseValue_neg (ell : ℕ) (eta : ℝ) :
    coulombPhaseValue ell (-eta) = (coulombPhaseValue ell eta)⁻¹ := by
  rw [coulombPhaseValue, coulombPhaseValue, inv_div]
  congr 1 <;> push_cast <;> ring

end

end GaloisForLFunctions
