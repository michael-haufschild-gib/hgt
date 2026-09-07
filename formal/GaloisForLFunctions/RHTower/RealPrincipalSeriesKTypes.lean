import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactPicture
import GaloisForLFunctions.RHTower.RealSphericalHarishChandra
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Finite spherical K-types in the compact principal-series picture

The stabilizer of `I` in `SL(2, ℝ)` is identified explicitly with the complex unit circle.
Its even Fourier characters are proved pairwise distinct and linearly independent.  Because the
intersection of the upper Borel with this stabilizer is `{ ±1 }`, every even character satisfies
the compact-picture twisting law.  Their finite linear combinations therefore give an injective
linear map from the explicit spherical Harish-Chandra model into the compact principal series.

This supplies the algebraic K-finite bridge.  A later smooth model is still needed to derive the
raising and lowering operators from differentiated right translation.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Matrices stabilizing `I` have rotation form in their off-diagonal entries. -/
theorem upperHalfPlaneStabilizer_matrix_relations (k : upperHalfPlaneStabilizer) :
    (k : SL2R) 1 0 = -(k : SL2R) 0 1 ∧
      (k : SL2R) 1 1 = (k : SL2R) 0 0 := by
  have hkfix : (k : SL2R) • UpperHalfPlane.I = UpperHalfPlane.I :=
    MulAction.mem_stabilizer_iff.mp k.property
  have hcoe := congr_arg (fun z : UpperHalfPlane ↦ (z : ℂ)) hkfix
  rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoe
  have hden : (((k : SL2R) 1 0 : ℂ) * (UpperHalfPlane.I : ℂ) +
      ((k : SL2R) 1 1 : ℂ)) ≠ 0 := by
    simpa [UpperHalfPlane.denom] using
      UpperHalfPlane.denom_ne_zero ((k : SL2R).mapGL ℝ) UpperHalfPlane.I
  have hmul := (div_eq_iff hden).mp hcoe
  have hre := congr_arg Complex.re hmul
  have him := congr_arg Complex.im hmul
  norm_num at hre him
  constructor <;> linarith

/-- Unit-circle phase of a rotation in the stabilizer of `I`. -/
def realSphericalKPhase (k : upperHalfPlaneStabilizer) : ℂ :=
  ((k : SL2R) 0 0 : ℂ) - Complex.I * ((k : SL2R) 0 1 : ℂ)

@[simp]
theorem realSphericalKPhase_one : realSphericalKPhase 1 = 1 := by
  simp [realSphericalKPhase]

@[simp]
theorem realSphericalKPhase_mul (k l : upperHalfPlaneStabilizer) :
    realSphericalKPhase (k * l) = realSphericalKPhase k * realSphericalKPhase l := by
  rcases upperHalfPlaneStabilizer_matrix_relations k with ⟨hk10, hk11⟩
  rcases upperHalfPlaneStabilizer_matrix_relations l with ⟨hl10, hl11⟩
  have hl10c : ((((l : SL2R) 1 0 : ℝ) : ℂ)) = -((((l : SL2R) 0 1 : ℝ) : ℂ)) := by
    exact_mod_cast hl10
  have hl11c : ((((l : SL2R) 1 1 : ℝ) : ℂ)) = ((((l : SL2R) 0 0 : ℝ) : ℂ)) := by
    exact_mod_cast hl11
  change
    ((((k : SL2R) * (l : SL2R)) 0 0 : ℝ) : ℂ) -
        Complex.I * ((((k : SL2R) * (l : SL2R)) 0 1 : ℝ) : ℂ) =
      realSphericalKPhase k * realSphericalKPhase l
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    realSphericalKPhase]
  push_cast
  rw [hl10c, hl11c]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem realSphericalKPhase_normSq (k : upperHalfPlaneStabilizer) :
    Complex.normSq (realSphericalKPhase k) = 1 := by
  rcases upperHalfPlaneStabilizer_matrix_relations k with ⟨hk10, hk11⟩
  have hdet := (k : SL2R).property
  rw [Matrix.det_fin_two, hk10, hk11] at hdet
  simp [realSphericalKPhase, Complex.normSq_apply]
  nlinarith

/-- The rotation phase as a monoid homomorphism from `K` to the unit circle. -/
def realSphericalKToCircle : upperHalfPlaneStabilizer →* Circle where
  toFun k := ⟨realSphericalKPhase k, by
    apply mem_sphere_zero_iff_norm.2
    rw [Complex.norm_def, realSphericalKPhase_normSq]
    norm_num⟩
  map_one' := Subtype.ext realSphericalKPhase_one
  map_mul' k l := Subtype.ext (realSphericalKPhase_mul k l)

@[simp]
theorem realSphericalKToCircle_coe (k : upperHalfPlaneStabilizer) :
    (realSphericalKToCircle k : ℂ) = realSphericalKPhase k :=
  rfl

/-- Rotation matrix attached to a unit complex number. -/
def realCircleRotation (z : Circle) : SL2R :=
  ⟨!![(z : ℂ).re, -(z : ℂ).im; (z : ℂ).im, (z : ℂ).re], by
    rw [Matrix.det_fin_two]
    have hz := Circle.normSq_coe z
    simp only [Complex.normSq_apply] at hz
    simp
    nlinarith⟩

/-- A rotation matrix fixes `I`, hence belongs to `K`. -/
def realCircleToSphericalK (z : Circle) : upperHalfPlaneStabilizer := by
  refine ⟨realCircleRotation z, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hden : (((realCircleRotation z : SL2R) 1 0 : ℂ) *
      (UpperHalfPlane.I : ℂ) + ((realCircleRotation z : SL2R) 1 1 : ℂ)) ≠ 0 := by
    simpa [UpperHalfPlane.denom] using
      UpperHalfPlane.denom_ne_zero ((realCircleRotation z).mapGL ℝ) UpperHalfPlane.I
  apply (div_eq_iff hden).2
  simp [realCircleRotation]
  ring_nf
  rw [Complex.I_sq]
  ring

@[simp]
theorem realSphericalKToCircle_circleToSphericalK (z : Circle) :
    realSphericalKToCircle (realCircleToSphericalK z) = z := by
  apply Circle.coe_injective
  simp [realSphericalKToCircle, realSphericalKPhase, realCircleToSphericalK,
    realCircleRotation]
  simpa [mul_comm] using Complex.re_add_im (z : ℂ)

@[simp]
theorem realCircleToSphericalK_realSphericalKToCircle
    (k : upperHalfPlaneStabilizer) :
    realCircleToSphericalK (realSphericalKToCircle k) = k := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [realCircleToSphericalK, realCircleRotation, realSphericalKToCircle,
      realSphericalKPhase]
  · simp [realCircleToSphericalK, realCircleRotation, realSphericalKToCircle,
      realSphericalKPhase]
  · simpa [realCircleToSphericalK, realCircleRotation,
      realSphericalKToCircle, realSphericalKPhase] using
      (upperHalfPlaneStabilizer_matrix_relations k).1.symm
  · simpa [realCircleToSphericalK, realCircleRotation,
      realSphericalKToCircle, realSphericalKPhase] using
      (upperHalfPlaneStabilizer_matrix_relations k).2.symm

/-- The stabilizer `K` is explicitly the complex unit circle. -/
def realSphericalKCircleEquiv : upperHalfPlaneStabilizer ≃* Circle :=
  { realSphericalKToCircle with
    invFun := realCircleToSphericalK
    left_inv := realCircleToSphericalK_realSphericalKToCircle
    right_inv := realSphericalKToCircle_circleToSphericalK }

/-- Even Fourier character of the unit circle, indexed by spherical weight `2m`. -/
def evenCircleCharacter (m : ℤ) : Circle →* ℂ where
  toFun z := (z : ℂ) ^ (2 * m)
  map_one' := by simp
  map_mul' z w := by simp [mul_zpow]

@[simp]
theorem evenCircleCharacter_apply (m : ℤ) (z : Circle) :
    evenCircleCharacter m z = (z : ℂ) ^ (2 * m) :=
  rfl

theorem evenCircleCharacter_injective : Function.Injective evenCircleCharacter := by
  intro m n hmn
  by_contra hne
  have hdiff : 2 * (m - n) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hne)
  let θ : ℝ := Real.pi / ((2 * (m - n) : ℤ) : ℝ)
  have heval := DFunLike.congr_fun hmn (Circle.exp θ)
  have hevalCircle : (Circle.exp θ) ^ (2 * m) = (Circle.exp θ) ^ (2 * n) := by
    apply Circle.coe_injective
    simpa using heval
  have hone : (Circle.exp θ) ^ (2 * (m - n)) = 1 := by
    rw [show 2 * (m - n) = 2 * m - 2 * n by ring]
    rw [zpow_sub]
    exact div_eq_one.mpr hevalCircle
  have hpi : (Circle.exp θ) ^ (2 * (m - n)) = Circle.exp Real.pi := by
    rw [← Circle.exp_zsmul]
    congr 1
    rw [zsmul_eq_mul]
    have hdiffR : (((2 * (m - n) : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hdiff
    dsimp [θ]
    field_simp [hdiffR]
  exact Circle.exp_pi_ne_one (hpi.symm.trans hone)

/-- Even `K`-type character of spherical weight `2m`. -/
def realSphericalKTypeCharacter (m : ℤ) : upperHalfPlaneStabilizer →* ℂ :=
  (evenCircleCharacter m).comp realSphericalKToCircle

@[simp]
theorem realSphericalKTypeCharacter_apply (m : ℤ)
    (k : upperHalfPlaneStabilizer) :
    realSphericalKTypeCharacter m k = (realSphericalKPhase k) ^ (2 * m) :=
  rfl

theorem realSphericalKTypeCharacter_injective :
    Function.Injective realSphericalKTypeCharacter := by
  intro m n h
  apply evenCircleCharacter_injective
  ext z
  have hz := DFunLike.congr_fun h (realCircleToSphericalK z)
  simpa [realSphericalKTypeCharacter] using hz

/-- Distinct spherical `K`-type characters are linearly independent. -/
theorem realSphericalKTypeCharacter_linearIndependent :
    LinearIndependent ℂ
      (fun m : ℤ ↦ (realSphericalKTypeCharacter m : upperHalfPlaneStabilizer → ℂ)) :=
  (linearIndependent_monoidHom upperHalfPlaneStabilizer ℂ).comp
    realSphericalKTypeCharacter realSphericalKTypeCharacter_injective

theorem realSphericalM_diagonal_square (m : realSphericalM) :
    ((m : upperHalfPlaneStabilizer) : SL2R) 0 0 ^ 2 = 1 := by
  have hm10 : ((m : upperHalfPlaneStabilizer) : SL2R) 1 0 = 0 := m.property
  rcases upperHalfPlaneStabilizer_matrix_relations (m : upperHalfPlaneStabilizer) with
    ⟨hmrot, hmdiag⟩
  have hm01 : ((m : upperHalfPlaneStabilizer) : SL2R) 0 1 = 0 := by linarith
  have hdet := (((m : upperHalfPlaneStabilizer) : SL2R).property)
  rw [Matrix.det_fin_two, hm10, hm01, hmdiag] at hdet
  simpa [pow_two] using hdet

theorem realSphericalM_borel_character (σ : ℝ) (m : realSphericalM) :
    realUpperBorelRpowCharacter σ (realSphericalMToBorel m) = 1 := by
  have hsq := realSphericalM_diagonal_square m
  have habs : |((m : upperHalfPlaneStabilizer) : SL2R) 0 0| = 1 := by
    nlinarith [sq_abs (((m : upperHalfPlaneStabilizer) : SL2R) 0 0),
      abs_nonneg (((m : upperHalfPlaneStabilizer) : SL2R) 0 0)]
  simp [realUpperBorelRpowCharacter, realSphericalMToBorel, habs]

theorem realSphericalM_circle_square (m : realSphericalM) :
    realSphericalKToCircle (realSphericalMToK m) ^ (2 : ℤ) = 1 := by
  apply Circle.coe_injective
  rw [Circle.coe_zpow]
  change (realSphericalKPhase (realSphericalMToK m)) ^ (2 : ℤ) = 1
  have hm10 : ((m : upperHalfPlaneStabilizer) : SL2R) 1 0 = 0 := m.property
  have hm01 : ((m : upperHalfPlaneStabilizer) : SL2R) 0 1 = 0 := by
    have h := (upperHalfPlaneStabilizer_matrix_relations
      (m : upperHalfPlaneStabilizer)).1
    linarith
  simp [realSphericalKPhase, realSphericalMToK, hm01]
  exact_mod_cast realSphericalM_diagonal_square m

@[simp]
theorem realSphericalM_KTypeCharacter (m : realSphericalM) (n : ℤ) :
    realSphericalKTypeCharacter n (realSphericalMToK m) = 1 := by
  change ((realSphericalKToCircle (realSphericalMToK m) : Circle) : ℂ) ^ (2 * n) = 1
  rw [← Circle.coe_zpow]
  norm_cast
  rw [zpow_mul, realSphericalM_circle_square, one_zpow]
  simp

/-- Spherical weight-`2m` vector in the compact picture. -/
def realCompactKType (σ : ℝ) (m : ℤ) : realCompactPictureSpace σ :=
  ⟨fun k ↦ realSphericalKTypeCharacter m k, by
    intro n k
    change realSphericalKTypeCharacter m (realSphericalMToK n * k) =
      realUpperBorelRpowCharacter σ (realSphericalMToBorel n) *
        realSphericalKTypeCharacter m k
    rw [map_mul, realSphericalM_KTypeCharacter, one_mul,
      realSphericalM_borel_character, one_mul]⟩

@[simp]
theorem realCompactKType_apply (σ : ℝ) (m : ℤ)
    (k : upperHalfPlaneStabilizer) :
    (realCompactKType σ m : upperHalfPlaneStabilizer → ℂ) k =
      realSphericalKTypeCharacter m k :=
  rfl

theorem realCompactKType_linearIndependent (σ : ℝ) :
    LinearIndependent ℂ (realCompactKType σ) := by
  apply LinearIndependent.of_comp (realCompactPictureSpace σ).subtype
  let v : ℤ → (upperHalfPlaneStabilizer → ℂ) :=
    fun m ↦ (realSphericalKTypeCharacter m : upperHalfPlaneStabilizer → ℂ)
  have hv : (realCompactPictureSpace σ).subtype ∘ realCompactKType σ = v := by
    funext m
    ext k
    rfl
  rw [hv]
  exact realSphericalKTypeCharacter_linearIndependent

/-- Injective finite Fourier expansion of the explicit Harish-Chandra model in the compact
picture. -/
def realCompactKFiniteEmbedding (σ : ℝ) :
    SphericalKFiniteModel →ₗ[ℂ] realCompactPictureSpace σ :=
  Finsupp.linearCombination ℂ (realCompactKType σ)

@[simp]
theorem realCompactKFiniteEmbedding_single (σ : ℝ) (m : ℤ) (z : ℂ) :
    realCompactKFiniteEmbedding σ (Finsupp.single m z) =
      z • realCompactKType σ m := by
  simp [realCompactKFiniteEmbedding]

theorem realCompactKFiniteEmbedding_injective (σ : ℝ) :
    Function.Injective (realCompactKFiniteEmbedding σ) := by
  rw [← LinearMap.ker_eq_bot]
  exact (linearIndependent_iff_ker.mp (realCompactKType_linearIndependent σ))

end
end GaloisForLFunctions.RHTower
