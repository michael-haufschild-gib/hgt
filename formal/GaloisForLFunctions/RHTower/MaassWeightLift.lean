import GaloisForLFunctions.RHTower.MaassSmoothDifferentialOperators
import GaloisForLFunctions.RHTower.RealPrincipalSeriesDerivedDirections

import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Differential actions on the actual Maass weight lift

The standard weight lift embeds smooth upper-half-plane functions into functions on SL(2,R).
Differentiation along diagonal, compact, and compact-conjugated diagonal right translations
recovers the actual raising and lowering operators at every group element.
-/

open UpperHalfPlane Complex
namespace GaloisForLFunctions.RHTower.MaassSmooth
noncomputable section

/-- The literal weight `2m` lift to the real special linear group. -/
def weightLift (m : ℤ) (f : FunctionSpace) (g : SL2R) : ℂ :=
  f (g • UpperHalfPlane.I) * realSphericalKTypeCharacter m (realIwasawaK g)

@[simp] theorem weightLift_zero (m : ℤ) : weightLift m 0 = 0 := by
  funext g
  change (0 : ℂ) * _ = 0
  exact zero_mul _

@[simp] theorem weightLift_smul (m : ℤ) (c : ℂ) (f : FunctionSpace) :
    weightLift m (c • f) = c • weightLift m f := by
  funext g
  change (c * f (g • UpperHalfPlane.I)) * _ = c * (f (g • UpperHalfPlane.I) * _)
  exact mul_assoc _ _ _

private theorem iwasawaK_right (g : SL2R) (k : upperHalfPlaneStabilizer) :
    realIwasawaK (g * (k : SL2R)) = realIwasawaK g * k := by
  apply Subtype.ext
  simp [realIwasawaK, orbitSectionCocycle, mul_smul,
    MulAction.mem_stabilizer_iff.mp k.property, mul_assoc]

/-- Right compact translation acts by the actual weight character. -/
theorem weightLift_right (m : ℤ) (f : FunctionSpace) (g : SL2R)
    (k : upperHalfPlaneStabilizer) :
    weightLift m f (g * (k : SL2R)) =
      weightLift m f g * realSphericalKTypeCharacter m k := by
  simp only [weightLift, iwasawaK_right, map_mul, mul_smul,
    MulAction.mem_stabilizer_iff.mp k.property, mul_assoc]

private theorem character_borel (m : ℤ) (b : realUpperBorel) (g : SL2R) :
    realSphericalKTypeCharacter m (realIwasawaK ((b : SL2R) * g)) =
      realSphericalKTypeCharacter m (realIwasawaK g) := by
  rw [realIwasawaK_mul, map_mul, realSphericalM_KTypeCharacter, one_mul]

private theorem section_borel (z : ℍ) : z.toSL2R ∈ realUpperBorel := by
  rw [realUpperBorel_mem_iff]
  simp

/-- The lift recovers the original function on the standard section. -/
@[simp] theorem weightLift_section (m : ℤ) (f : FunctionSpace) (z : ℍ) :
    weightLift m f z.toSL2R = f z := by
  have hc := character_borel m ⟨z.toSL2R, section_borel z⟩ 1
  simp only [mul_one] at hc
  have hi : realIwasawaK (1 : SL2R) = 1 := by
    simpa using realIwasawaK_of_K 1
  simp [weightLift, hc, hi]

/-- Lifting loses no source function. -/
theorem weightLift_injective (m : ℤ) : Function.Injective (weightLift m) := by
  intro f h he
  apply Subtype.ext
  funext z
  simpa using congrFun he z.toSL2R

private theorem section_smul (z w : ℍ) :
    ((z.toSL2R • w : ℍ) : ℂ) = (z.re : ℂ) + (z.im : ℂ) * (w : ℂ) := by
  have hs : (Real.sqrt z.im : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr z.im_pos
  have hs2 : (Real.sqrt z.im : ℂ) ^ 2 = (z.im : ℂ) := by
    exact_mod_cast Real.sq_sqrt z.im_pos.le
  rw [coe_specialLinearGroup_apply]
  simp only [coe_toSL2R]
  change ((Real.sqrt z.im : ℂ) * (w : ℂ) + ((z.re / Real.sqrt z.im : ℝ) : ℂ)) /
    ((0 : ℂ) * (w : ℂ) + ((1 / Real.sqrt z.im : ℝ) : ℂ)) = _
  simp only [Complex.ofReal_div, Complex.ofReal_one, zero_mul, zero_add]
  field_simp [hs]
  linear_combination (w : ℂ) * hs2

private theorem diagonal_orbit (t : ℝ) :
    (((realPositiveDiagonalBorel t : SL2R) • UpperHalfPlane.I : ℍ) : ℂ) =
      (Real.exp (2*t) : ℂ) * Complex.I := by
  rw [coe_specialLinearGroup_apply]
  simp [realPositiveDiagonalBorel, Real.exp_neg, Real.exp_add,
    show 2*t = t+t by ring, div_eq_mul_inv]
  ring

private theorem diagonal_orbit_deriv :
    HasDerivAt
      (fun t : ℝ => (((realPositiveDiagonalBorel (-t) : SL2R) • UpperHalfPlane.I : ℍ) : ℂ))
      (-2 * Complex.I) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul (-2)).exp).ofReal_comp.mul_const Complex.I
  simpa [diagonal_orbit, mul_neg] using h

private theorem rotation_diagonal_orbit_deriv (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => ((((k : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R)) •
        UpperHalfPlane.I : ℍ) : ℂ))
      (-4 * ((k : SL2R) 1 0 : ℂ) * ((k : SL2R) 1 1 : ℂ) +
        (2 * (((k : SL2R) 1 0 : ℂ)^(2 : ℕ) - ((k : SL2R) 1 1 : ℂ)^(2 : ℕ))) * Complex.I) 0 := by
  have hk := (UpperHalfPlane.hasStrictFDerivAt_smul ((k : SL2R).mapGL ℝ)
    UpperHalfPlane.I).hasFDerivAt
  have h := hk.comp_hasDerivAt_of_eq 0 diagonal_orbit_deriv (by simp)
  have hn : ((k : SL2R) 1 0 : ℂ)^(2 : ℕ) + ((k : SL2R) 1 1 : ℂ)^(2 : ℕ) = 1 := by
    exact_mod_cast sphericalK_lower_row_normSq k
  let c : ℂ := ((k : SL2R) 1 0 : ℂ)
  let d : ℂ := ((k : SL2R) 1 1 : ℂ)
  have hinv : (d + Complex.I*c)⁻¹ = d - Complex.I*c := by
    apply inv_eq_of_mul_eq_one_right
    ring_nf
    rw [Complex.I_sq]
    linear_combination hn
  convert! h using 1
  · funext t
    simp [mul_smul]
    rfl
  · have hj : UpperHalfPlane.smulFDeriv ((k : SL2R).mapGL ℝ) UpperHalfPlane.I
        (-2 * Complex.I) = (-2 * Complex.I) / (d + Complex.I*c)^(2 : ℕ) := by
      simp [UpperHalfPlane.smulFDeriv, UpperHalfPlane.σ, UpperHalfPlane.denom,
        c, d, mul_comm, add_comm, div_eq_mul_inv]
    rw [hj, div_eq_mul_inv, ← inv_pow, hinv]
    change -4*c*d + 2*(c^(2 : ℕ)-d^(2 : ℕ))*Complex.I = _
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_three]
    ring

private theorem section_rotation_orbit_deriv (z : ℍ) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => (((z.toSL2R * (k : SL2R) *
        (realPositiveDiagonalBorel (-t) : SL2R)) • UpperHalfPlane.I : ℍ) : ℂ))
      ((z.im : ℂ) * (-4 * ((k : SL2R) 1 0 : ℂ) * ((k : SL2R) 1 1 : ℂ) +
        (2 * (((k : SL2R) 1 0 : ℂ)^(2 : ℕ) - ((k : SL2R) 1 1 : ℂ)^(2 : ℕ))) * Complex.I)) 0 := by
  have h := ((rotation_diagonal_orbit_deriv k).const_mul (z.im : ℂ)).const_add (z.re : ℂ)
  convert! h using 1
  funext t
  rw [mul_assoc, mul_smul, section_smul]

private theorem source_orbit_deriv (f : FunctionSpace) (z : ℍ)
    (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => f ((z.toSL2R * (k : SL2R) *
        (realPositiveDiagonalBorel (-t) : SL2R)) • UpperHalfPlane.I))
      ((-4 * (z.im : ℂ) * ((k : SL2R) 1 0 : ℂ) * ((k : SL2R) 1 1 : ℂ)) *
        directional 1 f z +
       (2 * (z.im : ℂ) * (((k : SL2R) 1 0 : ℂ)^(2 : ℕ) - ((k : SL2R) 1 1 : ℂ)^(2 : ℕ))) *
        directional Complex.I f z) 0 := by
  have h := (differentiableAt f z).hasFDerivAt.comp_hasDerivAt_of_eq 0
    (section_rotation_orbit_deriv z k) (by
      simp [mul_smul, MulAction.mem_stabilizer_iff.mp k.property])
  convert! h using 1
  · funext t
    simp [Function.comp_def]
  · let a : ℝ := -4 * z.im * (k : SL2R) 1 0 * (k : SL2R) 1 1
    let b : ℝ := 2 * z.im * ((k : SL2R) 1 0 ^ 2 - (k : SL2R) 1 1 ^ 2)
    have hv : (z.im : ℂ) * (-4 * ((k : SL2R) 1 0 : ℂ) * ((k : SL2R) 1 1 : ℂ) +
        (2 * (((k : SL2R) 1 0 : ℂ)^(2 : ℕ) - ((k : SL2R) 1 1 : ℂ)^(2 : ℕ))) * Complex.I) =
        a • (1 : ℂ) + b • Complex.I := by
      simp [a, b, Complex.real_smul]
      ring
    rw [hv, map_add, map_smul, map_smul]
    simp [a, b, Complex.real_smul, directional_apply]

private theorem character_diagonal_deriv (m : ℤ) (z : ℍ)
    (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => realSphericalKTypeCharacter m (realIwasawaK
        (z.toSL2R * (k : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R))))
      (-4 * (m : ℂ) * Complex.I * ((k : SL2R) 1 0 : ℂ) * ((k : SL2R) 1 1 : ℂ) *
        realSphericalKTypeCharacter m k) 0 := by
  have h := hasDerivAt_compactRealPrincipalSeries_diagonal_KType 0 m k
  have hn := h.scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).neg) (by simp)
  have hf : (fun t : ℝ => realSphericalKTypeCharacter m (realIwasawaK
      (z.toSL2R * (k : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R)))) =
      (fun t : ℝ => ((compactRealPrincipalSeries 0 (realPositiveDiagonalBorel (-t) : SL2R))
        (realCompactKType 0 m)).1 k) := by
    funext t
    rw [mul_assoc, character_borel m ⟨z.toSL2R, section_borel z⟩]
    rw [compactRealPrincipalSeries_diagonal_KType_apply]
    simp [realSphericalKTypeCharacter_apply, realIwasawaK_phase_rotation_diagonal]
  rw [hf]
  convert! hn using 1
  simp

private theorem weighted_phase_identity (m : ℤ) (c d p y fx fy u : ℂ)
    (hp : p ≠ 0) (hphase : p = d + Complex.I*c) (hnorm : c^(2 : ℕ)+d^(2 : ℕ) = 1) :
    (Complex.I*y*fx-y*fy-(m : ℂ)*u) * p^(2*(m+1)) +
      (-Complex.I*y*fx-y*fy+(m : ℂ)*u) * p^(2*(m-1)) =
      ((-4*y*c*d)*fx + (2*y*(c^(2 : ℕ)-d^(2 : ℕ)))*fy - 4*(m : ℂ)*Complex.I*c*d*u) * p^(2*m) := by
  have hinv : p⁻¹ = d-Complex.I*c := by
    apply inv_eq_of_mul_eq_one_right
    rw [hphase]
    ring_nf
    rw [Complex.I_sq]
    linear_combination hnorm
  have hpos : p^(2 : ℤ) = (d+Complex.I*c)^(2 : ℕ) := by rw [hphase]; rfl
  have hneg : p^(-2 : ℤ) = (d-Complex.I*c)^(2 : ℕ) := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow, hinv]
  rw [show 2*(m+1) = 2*m+2 by ring, zpow_add₀ hp,
    show 2*(m-1) = 2*m+(-2) by ring, zpow_add₀ hp, hpos, hneg]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem weightLift_section_rotation_diagonal (m : ℤ) (f : FunctionSpace)
    (z : ℍ) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => weightLift m f
        (z.toSL2R * (k : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R)))
      (weightLift (m+1) (raise m f) (z.toSL2R * (k : SL2R)) +
        weightLift (m-1) (lower m f) (z.toSL2R * (k : SL2R))) 0 := by
  have h := (source_orbit_deriv f z k).mul (character_diagonal_deriv m z k)
  convert! h using 1
  · simp only [weightLift_right, weightLift_section]
    simp only [realPositiveDiagonalBorel_zero, neg_zero, OneMemClass.coe_one, mul_one, mul_smul,
      MulAction.mem_stabilizer_iff.mp k.property, toSL2R_smul_I]
    have hc : realSphericalKTypeCharacter m (realIwasawaK (z.toSL2R * (k : SL2R))) =
        realSphericalKTypeCharacter m k := by
      rw [character_borel m ⟨z.toSL2R, section_borel z⟩, realIwasawaK_of_K]
    rw [hc]
    have hphase : realSphericalKPhase k =
        ((k : SL2R) 1 1 : ℂ) + Complex.I * ((k : SL2R) 1 0 : ℂ) := by
      rcases upperHalfPlaneStabilizer_matrix_relations k with ⟨h10, h11⟩
      simp [realSphericalKPhase, h10, h11]
      ring
    have hnorm : ((k : SL2R) 1 0 : ℂ)^(2 : ℕ) + ((k : SL2R) 1 1 : ℂ)^(2 : ℕ) = 1 := by
      exact_mod_cast sphericalK_lower_row_normSq k
    have hi := weighted_phase_identity m _ _ _ (z.im : ℂ)
      (directional 1 f z) (directional Complex.I f z) (f z)
      (realSphericalKPhase_ne_zero k) hphase hnorm
    change (Complex.I * ((z.im : ℂ) * directional 1 f z) -
      (z.im : ℂ) * directional Complex.I f z - (m : ℂ)*f z) * _ +
      (- (Complex.I * ((z.im : ℂ) * directional 1 f z)) -
      (z.im : ℂ) * directional Complex.I f z + (m : ℂ)*f z) * _ = _
    simp only [realSphericalKTypeCharacter_apply]
    linear_combination hi

/-- The actual inverse diagonal right translation differentiates to raising plus lowering. -/
theorem weightLift_diagonal_hasDerivAt (m : ℤ) (f : FunctionSpace) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => weightLift m f (g * (realPositiveDiagonalBorel (-t) : SL2R)))
      (weightLift (m+1) (raise m f) g + weightLift (m-1) (lower m f) g) 0 := by
  have hg : (g • UpperHalfPlane.I).toSL2R * (realIwasawaK g : SL2R) = g :=
    realIwasawaB_mul_realIwasawaK g
  simpa only [hg] using weightLift_section_rotation_diagonal m f
    (g • UpperHalfPlane.I) (realIwasawaK g)

/-- Compact right translation differentiates to the actual weight operator. -/
theorem weightLift_rotation_hasDerivAt (m : ℤ) (f : FunctionSpace) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => weightLift m f (g * (realSphericalRotation t : SL2R)))
      ((2*(m : ℂ)*Complex.I) * weightLift m f g) 0 := by
  have h := (hasDerivAt_realSphericalKTypeCharacter_rotation m 0).const_mul (weightLift m f g)
  simpa [weightLift_right, mul_comm, mul_left_comm, mul_assoc] using h

/-- Compact conjugation rotates the two noncompact differential directions. -/
theorem weightLift_conjugateDiagonal_hasDerivAt (m : ℤ) (f : FunctionSpace)
    (g : SL2R) (q : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => weightLift m f
        (g * ((q : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R) * (q : SL2R)⁻¹)))
      (realSphericalKTypeCharacter 1 q * weightLift (m+1) (raise m f) g +
        realSphericalKTypeCharacter (-1) q * weightLift (m-1) (lower m f) g) 0 := by
  have h := (weightLift_diagonal_hasDerivAt m f (g * (q : SL2R))).mul_const
    (realSphericalKTypeCharacter m q⁻¹)
  convert! h using 1
  · funext t
    simpa only [mul_assoc, InvMemClass.coe_inv] using
      weightLift_right m f (g * (q : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R)) q⁻¹
  · rw [weightLift_right, weightLift_right]
    have hc : realSphericalKTypeCharacter m q * realSphericalKTypeCharacter m q⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hm : realSphericalKTypeCharacter (m-1) q =
        realSphericalKTypeCharacter m q * realSphericalKTypeCharacter (-1) q := by
      simpa only [sub_eq_add_neg] using realSphericalKTypeCharacter_add m (-1) q
    rw [realSphericalKTypeCharacter_add, hm]
    linear_combination -(realSphericalKTypeCharacter 1 q * weightLift (m+1) (raise m f) g +
      realSphericalKTypeCharacter (-1) q * weightLift (m-1) (lower m f) g) * hc

/-- The quarter-rotation conjugate differentiates to `i` times raising minus lowering. -/
theorem weightLift_quarterDiagonal_hasDerivAt (m : ℤ) (f : FunctionSpace) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => weightLift m f
        (g * ((realSphericalRotation (Real.pi/4) : SL2R) *
          (realPositiveDiagonalBorel (-t) : SL2R) *
          (realSphericalRotation (Real.pi/4) : SL2R)⁻¹)))
      (Complex.I * (weightLift (m+1) (raise m f) g -
        weightLift (m-1) (lower m f) g)) 0 := by
  convert! weightLift_conjugateDiagonal_hasDerivAt m f g
    (realSphericalRotation (Real.pi/4)) using 1
  rw [realSphericalKTypeCharacter_one_quarter, realSphericalKTypeCharacter_neg_one_quarter]
  ring

end
end GaloisForLFunctions.RHTower.MaassSmooth
