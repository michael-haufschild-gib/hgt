import GaloisForLFunctions.RHTower.RealPrincipalSeriesDiagonalKTypeDerivative
import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactKDerivative

/-!
# Actual real infinitesimal directions of the compact principal series

Finite Fourier sums inherit the diagonal and rotation derivatives. Compact conjugation gives
the second noncompact direction, and the three resulting operators express the shifted Casimir.
-/

namespace GaloisForLFunctions.RHTower
noncomputable section


/-- Differentiating the inverse diagonal flow on any finite Fourier vector. -/
theorem negativeDiagonal_matches_spherical_E_add_F_finite
    (s : ℝ) (v : SphericalKFiniteModel) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ =>
        (compactRealPrincipalSeries (1 - s)
          (realPositiveDiagonalBorel (-t) : SL2R)
          (realCompactKFiniteEmbedding (1 - s) v)).1 k)
      ((realCompactKFiniteEmbedding (1 - s)
        ((sphericalPrincipalE (s : ℂ) + sphericalPrincipalF (s : ℂ)) v)).1 k) 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simpa using (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  | add v w hv hw =>
      simpa only [map_add, AddMemClass.coe_add, Pi.add_apply, Pi.add_def] using hv.add hw
  | single m z => exact negativeDiagonal_matches_spherical_E_add_F s m z k

theorem compactRealPrincipalSeries_K_apply (σ : ℝ) (q : upperHalfPlaneStabilizer)
    (φ : realCompactPictureSpace σ) (k : upperHalfPlaneStabilizer) :
    (compactRealPrincipalSeries σ (q : SL2R) φ).1 k = φ.1 (k * q) := by
  rw [compactRealPrincipalSeries_apply]
  change realUpperBorelRpowCharacter σ (realIwasawaB ((k * q : upperHalfPlaneStabilizer) : SL2R)) *
    φ.1 (realIwasawaK ((k * q : upperHalfPlaneStabilizer) : SL2R)) = _
  rw [realIwasawaB_of_K, realIwasawaK_of_K, map_one, one_mul]

theorem realSphericalKTypeCharacter_add (m n : ℤ) (q : upperHalfPlaneStabilizer) :
    realSphericalKTypeCharacter (m+n) q =
      realSphericalKTypeCharacter m q * realSphericalKTypeCharacter n q := by
  simp only [realSphericalKTypeCharacter_apply, mul_add]
  exact zpow_add₀ (realSphericalKPhase_ne_zero q) _ _

theorem sphericalKTypeRepresentation_E (s : ℂ) (q : upperHalfPlaneStabilizer)
    (v : SphericalKFiniteModel) :
    sphericalKTypeRepresentation q (sphericalPrincipalE s v) =
      realSphericalKTypeCharacter 1 q • sphericalPrincipalE s (sphericalKTypeRepresentation q v) := by
  have he : (sphericalKTypeRepresentation q).comp (sphericalPrincipalE s) =
      realSphericalKTypeCharacter 1 q • (sphericalPrincipalE s).comp (sphericalKTypeRepresentation q) := by
    apply Finsupp.lhom_ext
    intro m z
    change sphericalKTypeAction q (sphericalPrincipalE s (Finsupp.single m z)) = _
    simp only [sphericalPrincipalE_single, sphericalKTypeAction_single, LinearMap.smul_apply,
      LinearMap.comp_apply]
    change Finsupp.single (m+1) _ =
      realSphericalKTypeCharacter 1 q • sphericalPrincipalE s (sphericalKTypeAction q (Finsupp.single m z))
    rw [sphericalKTypeAction_single, sphericalPrincipalE_single, Finsupp.smul_single]
    congr 1
    rw [realSphericalKTypeCharacter_add]
    simp only [smul_eq_mul]
    ring
  exact LinearMap.congr_fun he v

theorem sphericalKTypeRepresentation_F (s : ℂ) (q : upperHalfPlaneStabilizer)
    (v : SphericalKFiniteModel) :
    sphericalKTypeRepresentation q (sphericalPrincipalF s v) =
      realSphericalKTypeCharacter (-1) q • sphericalPrincipalF s (sphericalKTypeRepresentation q v) := by
  have he : (sphericalKTypeRepresentation q).comp (sphericalPrincipalF s) =
      realSphericalKTypeCharacter (-1) q • (sphericalPrincipalF s).comp (sphericalKTypeRepresentation q) := by
    apply Finsupp.lhom_ext
    intro m z
    change sphericalKTypeAction q (sphericalPrincipalF s (Finsupp.single m z)) = _
    simp only [sphericalPrincipalF_single, sphericalKTypeAction_single, LinearMap.smul_apply,
      LinearMap.comp_apply]
    change Finsupp.single (m-1) _ =
      realSphericalKTypeCharacter (-1) q • sphericalPrincipalF s (sphericalKTypeAction q (Finsupp.single m z))
    rw [sphericalKTypeAction_single, sphericalPrincipalF_single, Finsupp.smul_single]
    congr 1
    rw [sub_eq_add_neg, realSphericalKTypeCharacter_add]
    simp only [smul_eq_mul]
    ring
  exact LinearMap.congr_fun he v

/-- Rotation differentiation on every finite Fourier vector. -/
theorem compactRotation_matches_spherical_I_H_finite
    (s : ℝ) (v : SphericalKFiniteModel) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => (compactRealPrincipalSeries (1-s) (realSphericalRotation t : SL2R)
        (realCompactKFiniteEmbedding (1-s) v)).1 k)
      (Complex.I * (realCompactKFiniteEmbedding (1-s) (sphericalPrincipalH v)).1 k) 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simpa using (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  | add v w hv hw =>
      simpa only [map_add, AddMemClass.coe_add, Pi.add_apply, Pi.add_def, mul_add] using hv.add hw
  | single m z =>
      simpa only [compactSphericalPrincipalH_equiv_apply,
        sphericalModelCompactKFiniteEquiv_apply_coe] using
        compactRotation_hasDerivAt_eq_I_H_single s m z k

/-- Conjugating the actual diagonal flow gives both noncompact weight directions. -/
theorem compactConjugateDiagonal_hasDerivAt (s : ℝ) (q : upperHalfPlaneStabilizer)
    (v : SphericalKFiniteModel) (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ =>
        (compactRealPrincipalSeries (1-s)
          ((q : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R) * (q : SL2R)⁻¹)
          (realCompactKFiniteEmbedding (1-s) v)).1 k)
      ((realCompactKFiniteEmbedding (1-s)
        (realSphericalKTypeCharacter 1 q • sphericalPrincipalE (s : ℂ) v +
          realSphericalKTypeCharacter (-1) q • sphericalPrincipalF (s : ℂ) v)).1 k) 0 := by
  have he (w : SphericalKFiniteModel) (r : upperHalfPlaneStabilizer) :
      compactRealPrincipalSeries (1-s) (r : SL2R) (realCompactKFiniteEmbedding (1-s) w) =
        realCompactKFiniteEmbedding (1-s) (sphericalKTypeRepresentation r w) :=
    (LinearMap.congr_fun (realCompactKFiniteEmbedding_intertwines_K (1-s) r) w).symm
  have hi : sphericalKTypeRepresentation q (sphericalKTypeRepresentation q⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hd := negativeDiagonal_matches_spherical_E_add_F_finite s
    (sphericalKTypeRepresentation q⁻¹ v) (k*q)
  have hvalue :
      (realCompactKFiniteEmbedding (1-s)
        ((sphericalPrincipalE (s : ℂ) + sphericalPrincipalF (s : ℂ))
          (sphericalKTypeRepresentation q⁻¹ v))).1 (k*q) =
      (realCompactKFiniteEmbedding (1-s)
        (realSphericalKTypeCharacter 1 q • sphericalPrincipalE (s : ℂ) v +
          realSphericalKTypeCharacter (-1) q • sphericalPrincipalF (s : ℂ) v)).1 k := by
    rw [← compactRealPrincipalSeries_K_apply, he]
    simp only [LinearMap.add_apply, map_add, sphericalKTypeRepresentation_E,
      sphericalKTypeRepresentation_F, hi]
  rw [hvalue] at hd
  convert hd using 1
  funext t
  rw [map_mul, map_mul]
  simp only [Module.End.mul_apply]
  rw [show (q : SL2R)⁻¹ = ((q⁻¹ : upperHalfPlaneStabilizer) : SL2R) from rfl,
    he, compactRealPrincipalSeries_K_apply]

theorem realSphericalKTypeCharacter_one_quarter :
    realSphericalKTypeCharacter 1 (realSphericalRotation (Real.pi/4)) = Complex.I := by
  rw [realSphericalKTypeCharacter_rotation]
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

theorem realSphericalKTypeCharacter_neg_one_quarter :
    realSphericalKTypeCharacter (-1) (realSphericalRotation (Real.pi/4)) = -Complex.I := by
  rw [realSphericalKTypeCharacter_rotation]
  convert Complex.exp_neg_pi_div_two_mul_I using 1
  congr 1
  push_cast
  ring

/-- The quarter-turn conjugated inverse diagonal has derivative `i(E-F)`. -/
theorem compactQuarterDiagonal_hasDerivAt (s : ℝ) (v : SphericalKFiniteModel)
    (k : upperHalfPlaneStabilizer) :
    HasDerivAt
      (fun t : ℝ => (compactRealPrincipalSeries (1-s)
        ((realSphericalRotation (Real.pi/4) : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R) *
          (realSphericalRotation (Real.pi/4) : SL2R)⁻¹)
        (realCompactKFiniteEmbedding (1-s) v)).1 k)
      (Complex.I * (realCompactKFiniteEmbedding (1-s)
        ((sphericalPrincipalE (s : ℂ) - sphericalPrincipalF (s : ℂ)) v)).1 k) 0 := by
  have hd := compactConjugateDiagonal_hasDerivAt s (realSphericalRotation (Real.pi/4)) v k
  simpa only [realSphericalKTypeCharacter_one_quarter, realSphericalKTypeCharacter_neg_one_quarter,
    neg_smul, ← sub_eq_add_neg, ← smul_sub, map_smul, LinearMap.sub_apply, SetLike.val_smul, Pi.smul_apply,
    smul_eq_mul] using hd

/-- The real noncompact and compact infinitesimal generators. -/
def sphericalDerivedA (s : ℂ) : Module.End ℂ SphericalKFiniteModel :=
  sphericalPrincipalE s + sphericalPrincipalF s

def sphericalDerivedB (s : ℂ) : Module.End ℂ SphericalKFiniteModel :=
  Complex.I • (sphericalPrincipalE s - sphericalPrincipalF s)

def sphericalDerivedC : Module.End ℂ SphericalKFiniteModel :=
  Complex.I • sphericalPrincipalH

/-- Raising and lowering are recovered from the two actual noncompact directions. -/
theorem sphericalPrincipalE_eq_derived (s : ℂ) :
    sphericalPrincipalE s = (1/2 : ℂ) • (sphericalDerivedA s - Complex.I • sphericalDerivedB s) := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro m
  simp only [sphericalDerivedA, sphericalDerivedB, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  linear_combination (sphericalPrincipalE s v m - sphericalPrincipalF s v m) / 2 * Complex.I_sq

theorem sphericalPrincipalF_eq_derived (s : ℂ) :
    sphericalPrincipalF s = (1/2 : ℂ) • (sphericalDerivedA s + Complex.I • sphericalDerivedB s) := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro m
  simp only [sphericalDerivedA, sphericalDerivedB, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  linear_combination -(sphericalPrincipalE s v m - sphericalPrincipalF s v m) / 2 * Complex.I_sq

/-- The shifted Casimir in the real infinitesimal basis. -/
theorem sphericalPrincipalLaplacian_eq_derived (s : ℂ) :
    sphericalPrincipalLaplacian s = (-1/4 : ℂ) •
      ((sphericalDerivedA s).comp (sphericalDerivedA s) +
       (sphericalDerivedB s).comp (sphericalDerivedB s) - sphericalDerivedC.comp sphericalDerivedC) := by
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro m
  have hc := congrArg (fun T : Module.End ℂ SphericalKFiniteModel => T v m)
    (sphericalPrincipalE_comm_F s)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finsupp.sub_apply] at hc
  simp only [sphericalPrincipalLaplacian, sphericalPrincipalCasimir,
    sphericalDerivedA, sphericalDerivedB, sphericalDerivedC,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.id_apply, map_add, map_sub, map_smul,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  linear_combination hc / 2 +
    (sphericalPrincipalE s (sphericalPrincipalE s v) m -
      sphericalPrincipalE s (sphericalPrincipalF s v) m -
      sphericalPrincipalF s (sphericalPrincipalE s v) m +
      sphericalPrincipalF s (sphericalPrincipalF s v) m -
      sphericalPrincipalH (sphericalPrincipalH v) m) / 4 * Complex.I_sq

end
end GaloisForLFunctions.RHTower
