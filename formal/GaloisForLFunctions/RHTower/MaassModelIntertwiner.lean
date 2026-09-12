import GaloisForLFunctions.RHTower.MaassAutomorphicDifferentialLadder

/-!
# The actual finite Maass-to-model intertwiner

An exceptional Maass eigenform determines normalized smooth differential ladders with the
standard spherical principal-series coefficients. Their literal lifts give an injective
map from finite spherical coordinates into actual automorphic functions. This map
intertwines compact right translation and differentiation along diagonal, conjugated
diagonal and compact flows.

Its image is the intrinsic differentiated cyclic space of the original Maass vector:
the smallest complex subspace closed under the two generating noncompact derivatives.
The inverse equivalence therefore identifies an actual source space with the existing
model, without assuming differential compatibility or source irreducibility.
-/

open UpperHalfPlane Complex
namespace GaloisForLFunctions.RHTower.MaassSmooth
noncomputable section

/-- The standard raising coefficient for the complementary parameter attached to `lam`. -/
def modelStep (lam : SelbergExceptionalEigenvalue) (m : ℤ) : ℂ :=
  (((2 * lam.complementaryExponent : ℝ) : ℂ) - 1 - 2*(m : ℂ))/2

private theorem modelStep_ne_zero (lam : SelbergExceptionalEigenvalue) (m : ℤ) :
    modelStep lam m ≠ 0 := by
  apply sphericalPrincipalE_coefficient_ne_zero
  rw [abs_lt]
  have h := lam.complementaryExponent_mem_Ioo
  constructor <;> linarith [h.1, h.2]

/-- Product that normalizes the original differential ladder to the compact model basis. -/
def ladderScale (lam : SelbergExceptionalEigenvalue) (n : ℕ) : ℂ :=
  ∏ j ∈ Finset.range n, modelStep lam (j : ℤ)

@[simp] theorem ladderScale_zero (lam : SelbergExceptionalEigenvalue) : ladderScale lam 0 = 1 :=
  Finset.prod_range_zero _

private theorem ladderScale_ne_zero (lam : SelbergExceptionalEigenvalue) (n : ℕ) :
    ladderScale lam n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact modelStep_ne_zero lam j

private theorem ladderScale_succ (lam : SelbergExceptionalEigenvalue) (n : ℕ) :
    ladderScale lam (n+1) = ladderScale lam n * modelStep lam (n : ℤ) :=
  Finset.prod_range_succ _ _

private theorem modelStep_pair (lam : SelbergExceptionalEigenvalue) (n : ℕ) :
    -((lam.1 : ℂ) + (n : ℂ)*((n : ℂ)+1)) =
      modelStep lam (n : ℤ) * modelStep lam (-((n : ℤ)+1)) := by
  have he := lam.eigenvalueOfComplementaryExponent_eq
  unfold eigenvalueOfComplementaryExponent at he
  have hs : ((2 * lam.complementaryExponent : ℝ) : ℂ)^2 = 1-4*(lam.1 : ℂ) := by
    exact_mod_cast (show (2 * lam.complementaryExponent)^2 = 1-4*lam.1 by nlinarith [he])
  unfold modelStep
  push_cast at hs ⊢
  linear_combination -hs/4

/-- The actual raised source with its standard model normalization. -/
def normalizedRaised {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) : FunctionSpace :=
  (ladderScale lam n)⁻¹ • raised (ofMaass f) n

/-- The actual lowered source with its standard model normalization. -/
def normalizedLowered {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) : FunctionSpace :=
  (ladderScale lam n)⁻¹ • lowered (ofMaass f) n

@[simp] theorem normalizedRaised_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : normalizedRaised lam f 0 = ofMaass f := by
  simp [normalizedRaised]

@[simp] theorem normalizedLowered_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : normalizedLowered lam f 0 = ofMaass f := by
  simp [normalizedLowered]

theorem raise_normalizedRaised {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) :
    raise (n : ℤ) (normalizedRaised lam f n) =
      modelStep lam (n : ℤ) • normalizedRaised lam f (n+1) := by
  simp only [normalizedRaised, map_smul, ← raised_succ, smul_smul, ladderScale_succ]
  congr 1
  field_simp [ladderScale_ne_zero, modelStep_ne_zero]

theorem lower_normalizedRaised {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) :
    lower ((n : ℤ)+1) (normalizedRaised lam f (n+1)) =
      modelStep lam (-((n : ℤ)+1)) • normalizedRaised lam f n := by
  simp only [normalizedRaised, map_smul, lower_raised, modelStep_pair, smul_smul, ladderScale_succ]
  congr 1
  field_simp [ladderScale_ne_zero, modelStep_ne_zero]

theorem lower_normalizedLowered {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) :
    lower (-(n : ℤ)) (normalizedLowered lam f n) =
      modelStep lam (n : ℤ) • normalizedLowered lam f (n+1) := by
  simp only [normalizedLowered, map_smul, ← lowered_succ, smul_smul, ladderScale_succ]
  congr 1
  field_simp [ladderScale_ne_zero, modelStep_ne_zero]

theorem raise_normalizedLowered {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) :
    raise (-((n : ℤ)+1)) (normalizedLowered lam f (n+1)) =
      modelStep lam (-((n : ℤ)+1)) • normalizedLowered lam f n := by
  simp only [normalizedLowered, map_smul, raise_lowered, modelStep_pair, smul_smul, ladderScale_succ]
  congr 1
  field_simp [ladderScale_ne_zero, modelStep_ne_zero]

/-- The source functions normalized to the standard spherical principal-series coefficients. -/
def modelSource {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : ℤ → FunctionSpace
  | .ofNat n => normalizedRaised lam f n
  | .negSucc n => normalizedLowered lam f (n+1)

@[simp] theorem modelSource_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : modelSource lam f 0 = ofMaass f :=
  normalizedRaised_zero lam f

/-- The actual source raising operator has exactly the model's coefficient in every weight. -/
theorem raise_modelSource {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) :
    raise m (modelSource lam f m) = modelStep lam m • modelSource lam f (m+1) := by
  cases m with
  | ofNat n => exact raise_normalizedRaised lam f n
  | negSucc n =>
      cases n with
      | zero => simpa [modelSource] using raise_normalizedLowered lam f 0
      | succ n =>
          have hi : Int.negSucc (n+1)+1 = Int.negSucc n := by omega
          rw [hi]
          exact raise_normalizedLowered lam f (n+1)

/-- The actual source lowering operator has exactly the model's coefficient in every weight. -/
theorem lower_modelSource {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) :
    lower m (modelSource lam f m) = modelStep lam (-m) • modelSource lam f (m-1) := by
  cases m with
  | ofNat n =>
      cases n with
      | zero =>
          change lower 0 (normalizedRaised lam f 0) =
            modelStep lam 0 • normalizedLowered lam f 1
          simpa only [normalizedRaised_zero, normalizedLowered_zero, Nat.cast_zero, neg_zero, zero_add] using
            lower_normalizedLowered lam f 0
      | succ n =>
          change lower ((n+1 : ℕ) : ℤ) (normalizedRaised lam f (n+1)) =
            modelStep lam (-((n+1 : ℕ) : ℤ)) • modelSource lam f (((n+1 : ℕ) : ℤ)-1)
          have hi : ((n+1 : ℕ) : ℤ)-1 = n := by omega
          rw [hi]
          exact lower_normalizedRaised lam f n
  | negSucc n => exact lower_normalizedLowered lam f (n+1)

/-- The normalized literal weight lift equals a nonzero rescaling of the automorphic ladder. -/
theorem modelSource_lift {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) :
    weightLift m (modelSource lam f m) =
      (ladderScale lam m.natAbs)⁻¹ • (automorphicLadder f m).1 := by
  cases m with
  | ofNat n => exact weightLift_smul (n : ℤ) _ _
  | negSucc n => exact weightLift_smul (-((n+1 : ℕ) : ℤ)) _ _

/-- The actual automorphic vector attached to a normalized compact basis vector. -/
def modelVector {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) : automorphicFunctionSpace Γ :=
  (ladderScale lam m.natAbs)⁻¹ • automorphicLadder f m

@[simp] theorem modelVector_apply {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) (g : SL2R) :
    (modelVector lam f m).1 g = weightLift m (modelSource lam f m) g :=
  congrFun (modelSource_lift lam f m).symm g

/-- The normalized source family has unique finite coordinates. -/
theorem modelVector_linearIndependent {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : LinearIndependent ℂ (modelVector lam f) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc m hm
  have h : ∑ i ∈ s, (c i * (ladderScale lam i.natAbs)⁻¹) • automorphicLadder f i = 0 := by
    simpa only [modelVector, smul_smul] using hc
  have hm0 := linearIndependent_iff'.mp (automorphicLadder_linearIndependent lam f)
    s (fun i => c i * (ladderScale lam i.natAbs)⁻¹) h m hm
  exact (mul_eq_zero.mp hm0).resolve_right (inv_ne_zero (ladderScale_ne_zero lam m.natAbs))

/-- Map standard finite spherical coordinates to actual automorphic Maass derivatives. -/
def modelToMaass {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : SphericalKFiniteModel →ₗ[ℂ] automorphicFunctionSpace Γ :=
  Finsupp.linearCombination ℂ (modelVector lam f)

@[simp] theorem modelToMaass_single {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) (c : ℂ) :
    modelToMaass lam f (Finsupp.single m c) = c • modelVector lam f m :=
  Finsupp.linearCombination_single ℂ c m

/-- The source-to-model correspondence has no kernel. -/
theorem modelToMaass_injective {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : Function.Injective (modelToMaass lam f) :=
  modelVector_linearIndependent lam f

/-- Diagonal right translation differentiates to the existing model operator on every basis vector. -/
theorem modelVector_diagonal_hasDerivAt {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => (modelVector lam f m).1 (g * (realPositiveDiagonalBorel (-t) : SL2R)))
      (modelStep lam m * (modelVector lam f (m+1)).1 g +
        modelStep lam (-m) * (modelVector lam f (m-1)).1 g) 0 := by
  simpa only [modelVector_apply, raise_modelSource, lower_modelSource,
    weightLift_smul, Pi.smul_apply, smul_eq_mul] using
    weightLift_diagonal_hasDerivAt m (modelSource lam f m) g

/-- The conjugated diagonal acts by the other model differential direction. -/
theorem modelVector_quarterDiagonal_hasDerivAt {Γ : Subgroup SL2R}
    (lam : SelbergExceptionalEigenvalue) (f : MaassCuspEigenform Γ lam.1) (m : ℤ) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => (modelVector lam f m).1
        (g * ((realSphericalRotation (Real.pi/4) : SL2R) *
          (realPositiveDiagonalBorel (-t) : SL2R) *
          (realSphericalRotation (Real.pi/4) : SL2R)⁻¹)))
      (Complex.I * (modelStep lam m * (modelVector lam f (m+1)).1 g -
        modelStep lam (-m) * (modelVector lam f (m-1)).1 g)) 0 := by
  simpa only [modelVector_apply, raise_modelSource, lower_modelSource,
    weightLift_smul, Pi.smul_apply, smul_eq_mul] using
    weightLift_quarterDiagonal_hasDerivAt m (modelSource lam f m) g

/-- The finite-coordinate map intertwines actual diagonal differentiation with `E+F`. -/
theorem modelToMaass_diagonal_hasDerivAt {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (v : SphericalKFiniteModel) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => (modelToMaass lam f v).1 (g * (realPositiveDiagonalBorel (-t) : SL2R)))
      ((modelToMaass lam f
        ((sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ) +
          sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ)) v)).1 g) 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add v w hv hw =>
      simpa only [map_add, AddMemClass.coe_add, Pi.add_apply, Pi.add_def] using hv.add hw
  | single m c =>
      convert! (modelVector_diagonal_hasDerivAt lam f m g).const_mul c using 1 <;>
        simp [modelToMaass_single, modelStep, mul_add, mul_comm, mul_left_comm]

/-- The finite-coordinate map intertwines the conjugated diagonal with `i(E-F)`. -/
theorem modelToMaass_quarterDiagonal_hasDerivAt {Γ : Subgroup SL2R}
    (lam : SelbergExceptionalEigenvalue) (f : MaassCuspEigenform Γ lam.1)
    (v : SphericalKFiniteModel) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => (modelToMaass lam f v).1
        (g * ((realSphericalRotation (Real.pi/4) : SL2R) *
          (realPositiveDiagonalBorel (-t) : SL2R) *
          (realSphericalRotation (Real.pi/4) : SL2R)⁻¹)))
      (Complex.I * (modelToMaass lam f
        ((sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ) -
          sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ)) v)).1 g) 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add v w hv hw =>
      simpa only [map_add, AddMemClass.coe_add, Pi.add_apply, Pi.add_def, mul_add] using hv.add hw
  | single m c =>
      convert! (modelVector_quarterDiagonal_hasDerivAt lam f m g).const_mul c using 1 <;>
        simp [modelToMaass_single, modelStep, mul_sub, mul_comm, mul_left_comm, mul_assoc]

/-- The finite-coordinate map intertwines compact rotation differentiation with `iH`. -/
theorem modelToMaass_rotation_hasDerivAt {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (v : SphericalKFiniteModel) (g : SL2R) :
    HasDerivAt
      (fun t : ℝ => (modelToMaass lam f v).1 (g * (realSphericalRotation t : SL2R)))
      (Complex.I * (modelToMaass lam f (sphericalPrincipalH v)).1 g) 0 := by
  induction v using Finsupp.induction_linear with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add v w hv hw =>
      simpa only [map_add, AddMemClass.coe_add, Pi.add_apply, Pi.add_def, mul_add] using hv.add hw
  | single m c =>
      convert! (weightLift_rotation_hasDerivAt m (modelSource lam f m) g).const_mul c using 1 <;>
        simp [modelVector_apply, mul_comm, mul_left_comm, mul_assoc]

/-- Actual compact right translation agrees with the finite model's compact action. -/
theorem modelToMaass_K {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (v : SphericalKFiniteModel) (k : upperHalfPlaneStabilizer) :
    automorphicRightRegularRepresentation Γ (k : SL2R) (modelToMaass lam f v) =
      modelToMaass lam f (sphericalKTypeAction k v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single m c =>
      apply Subtype.ext
      funext g
      simp [automorphicRightRegularRepresentation_apply, modelVector_apply,
        weightLift_right, mul_comm, mul_assoc]

/-- Normalization does not alter the span of the actual automorphic derivatives. -/
theorem modelToMaass_range {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) :
    LinearMap.range (modelToMaass lam f) = Submodule.span ℂ (Set.range (automorphicLadder f)) := by
  rw [modelToMaass, Finsupp.range_linearCombination]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    change automorphicLadder f m ∈ Submodule.span ℂ (Set.range (modelVector lam f))
    have h : modelVector lam f m ∈ Submodule.span ℂ (Set.range (modelVector lam f)) :=
      Submodule.subset_span ⟨m, rfl⟩
    have h' := Submodule.smul_mem _ (ladderScale lam m.natAbs) h
    simpa only [modelVector, smul_smul, mul_inv_cancel₀ (ladderScale_ne_zero lam m.natAbs),
      one_smul] using h'

/-- The actual finite Maass-to-model map, defined on the span of its automorphic derivatives. -/
def maassToModel {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) :
    LinearMap.range (modelToMaass lam f) ≃ₗ[ℂ] SphericalKFiniteModel :=
  (LinearEquiv.ofInjective (modelToMaass lam f) (modelToMaass_injective lam f)).symm

/-- Mapping back to the actual automorphic space recovers the original vector. -/
@[simp] theorem modelToMaass_maassToModel {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (w : LinearMap.range (modelToMaass lam f)) :
    modelToMaass lam f (maassToModel lam f w) = w.1 :=
  LinearEquiv.ofInjective_symm_apply (modelToMaass lam f) w

/-- Every finite model vector is recovered from its actual Maass realization. -/
@[simp] theorem maassToModel_modelToMaass {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (v : SphericalKFiniteModel) :
    maassToModel lam f ⟨modelToMaass lam f v, LinearMap.mem_range_self _ v⟩ = v :=
  (LinearEquiv.ofInjective (modelToMaass lam f) (modelToMaass_injective lam f)).symm_apply_apply v


/-- The spherical basis vector realizes the specified original Maass function. -/
@[simp] theorem modelToMaass_spherical {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (g : SL2R) :
    (modelToMaass lam f (Finsupp.single 0 1)).1 g = f.1.1 (g • UpperHalfPlane.I) := by
  simp [modelVector_apply, weightLift]

/-- Pointwise derivative of literal right translation along a real curve. -/
def automorphicCurveDerivative {Γ : Subgroup SL2R} (p : ℝ → SL2R)
    (F : automorphicFunctionSpace Γ) : automorphicFunctionSpace Γ := by
  refine ⟨fun g => deriv (fun t : ℝ => F.1 (g*p t)) 0, ?_⟩
  intro γ g
  have h : (fun t : ℝ => F.1 (((γ : SL2R)*g)*p t)) = (fun t => F.1 (g*p t)) := by
    funext t
    simpa only [mul_assoc] using F.property γ (g*p t)
  exact congrArg (fun h : ℝ → ℂ => deriv h 0) h

/-- The actual diagonal derivative equals the transported model operator as an automorphic vector. -/
theorem modelToMaass_diagonal_derivative {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (v : SphericalKFiniteModel) :
    automorphicCurveDerivative (fun t => (realPositiveDiagonalBorel (-t) : SL2R))
        (modelToMaass lam f v) =
      modelToMaass lam f ((sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ) +
        sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ)) v) := by
  apply Subtype.ext
  funext g
  exact (modelToMaass_diagonal_hasDerivAt lam f v g).deriv

/-- The actual quarter-conjugated derivative equals `i(E-F)` as an automorphic vector. -/
theorem modelToMaass_quarterDiagonal_derivative {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (v : SphericalKFiniteModel) :
    automorphicCurveDerivative (fun t => (realSphericalRotation (Real.pi/4) : SL2R) *
        (realPositiveDiagonalBorel (-t) : SL2R) * (realSphericalRotation (Real.pi/4) : SL2R)⁻¹)
        (modelToMaass lam f v) =
      Complex.I • modelToMaass lam f ((sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ) -
        sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ)) v) := by
  apply Subtype.ext
  funext g
  exact (modelToMaass_quarterDiagonal_hasDerivAt lam f v g).deriv

/-- The actual compact derivative equals `iH` as an automorphic vector. -/
theorem modelToMaass_rotation_derivative {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (v : SphericalKFiniteModel) :
    automorphicCurveDerivative (fun t => (realSphericalRotation t : SL2R)) (modelToMaass lam f v) =
      Complex.I • modelToMaass lam f (sphericalPrincipalH v) := by
  apply Subtype.ext
  funext g
  exact (modelToMaass_rotation_hasDerivAt lam f v g).deriv

/-- A complex subspace stable under the two generating noncompact right derivatives. -/
def StableMaassDirections {Γ : Subgroup SL2R} (W : Submodule ℂ (automorphicFunctionSpace Γ)) : Prop :=
  (∀ F ∈ W, automorphicCurveDerivative (fun t => (realPositiveDiagonalBorel (-t) : SL2R)) F ∈ W) ∧
  (∀ F ∈ W, automorphicCurveDerivative (fun t => (realSphericalRotation (Real.pi/4) : SL2R) *
    (realPositiveDiagonalBorel (-t) : SL2R) * (realSphericalRotation (Real.pi/4) : SL2R)⁻¹) F ∈ W)

/-- The actual finite Maass image is stable under both generating differential directions. -/
theorem modelToMaass_range_stable {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) : StableMaassDirections (LinearMap.range (modelToMaass lam f)) := by
  constructor
  · rintro F ⟨v, rfl⟩
    rw [modelToMaass_diagonal_derivative]
    exact LinearMap.mem_range_self _ _
  · rintro F ⟨v, rfl⟩
    rw [modelToMaass_quarterDiagonal_derivative]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

/-- The image is the differentiated cyclic space of the original spherical Maass vector. -/
theorem modelToMaass_range_minimal {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (W : Submodule ℂ (automorphicFunctionSpace Γ))
    (h0 : modelToMaass lam f (Finsupp.single 0 1) ∈ W) (hW : StableMaassDirections W) :
    LinearMap.range (modelToMaass lam f) ≤ W := by
  let E := sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ)
  let F := sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ)
  have hEF (v : SphericalKFiniteModel) (hv : modelToMaass lam f v ∈ W) :
      modelToMaass lam f (E v) ∈ W ∧ modelToMaass lam f (F v) ∈ W := by
    have ha := hW.1 _ hv
    have hb := hW.2 _ hv
    rw [modelToMaass_diagonal_derivative] at ha
    rw [modelToMaass_quarterDiagonal_derivative] at hb
    change modelToMaass lam f ((E+F) v) ∈ W at ha
    change Complex.I • modelToMaass lam f ((E-F) v) ∈ W at hb
    have hdiff : modelToMaass lam f (E v) - modelToMaass lam f (F v) ∈ W := by
      have h := W.smul_mem (-Complex.I) hb
      simpa only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul,
        LinearMap.sub_apply, map_sub] using h
    have hsum : modelToMaass lam f (E v) + modelToMaass lam f (F v) ∈ W := by
      simpa only [LinearMap.add_apply, map_add] using ha
    constructor
    · convert! W.smul_mem (1/2 : ℂ) (W.add_mem hsum hdiff) using 1
      module
    · convert! W.smul_mem (1/2 : ℂ) (W.sub_mem hsum hdiff) using 1
      module
  have hs (m : ℤ) : modelToMaass lam f (Finsupp.single m 1) ∈ W := by
    refine Int.inductionOn' m 0 h0 (fun k _ hk => ?_) (fun k _ hk => ?_)
    · have h := W.smul_mem (modelStep lam k)⁻¹ (hEF _ hk).1
      have hc : (((2*lam.complementaryExponent : ℝ) : ℂ)-1-2*(k : ℂ))/2 =
          modelStep lam k := rfl
      simpa only [E, sphericalPrincipalE_single, hc, modelToMaass_single,
        smul_smul, mul_one, inv_mul_cancel₀ (modelStep_ne_zero lam k), one_smul] using h
    · have h := W.smul_mem (modelStep lam (-k))⁻¹ (hEF _ hk).2
      have hc : (((2*lam.complementaryExponent : ℝ) : ℂ)-1+2*(k : ℂ))/2 =
          modelStep lam (-k) := by simp [modelStep]
      simpa only [F, sphericalPrincipalF_single, hc, modelToMaass_single,
        smul_smul, mul_one, inv_mul_cancel₀ (modelStep_ne_zero lam (-k)), one_smul] using h
  rintro _ ⟨v, rfl⟩
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using W.zero_mem
  | add v w hv hw => simpa only [map_add] using W.add_mem hv hw
  | single m c =>
      simpa only [modelToMaass_single, one_smul] using W.smul_mem c (hs m)

/-- The intrinsic differentiated cyclic space generated by the original Maass function. -/
def maassDifferentialCyclicSpace {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) : Submodule ℂ (automorphicFunctionSpace Γ) :=
  sInf {W | raisedAutomorphic f 0 ∈ W ∧ StableMaassDirections W}

private theorem modelToMaass_generator {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) :
    modelToMaass lam f (Finsupp.single 0 1) = raisedAutomorphic f 0 := by
  apply Subtype.ext
  funext g
  simp [raisedAutomorphic, weightLift]

/-- The model image equals the independently defined differentiated cyclic Maass space. -/
theorem modelToMaass_range_eq_cyclic {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) :
    LinearMap.range (modelToMaass lam f) = maassDifferentialCyclicSpace f := by
  apply le_antisymm
  · apply le_sInf
    intro W hW
    apply modelToMaass_range_minimal lam f W
    · simpa only [modelToMaass_generator] using hW.1
    · exact hW.2
  · apply sInf_le
    exact ⟨⟨Finsupp.single 0 1, modelToMaass_generator lam f⟩, modelToMaass_range_stable lam f⟩

/-- The actual Maass-to-model equivalence on the intrinsic differentiated cyclic source space. -/
def maassDifferentialModelEquiv {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) :
    maassDifferentialCyclicSpace f ≃ₗ[ℂ] SphericalKFiniteModel :=
  (LinearEquiv.ofEq _ _ (modelToMaass_range_eq_cyclic lam f).symm).trans (maassToModel lam f)

/-- Realizing the model coordinates recovers every vector in the intrinsic cyclic source space. -/
@[simp] theorem modelToMaass_differentialModelEquiv {Γ : Subgroup SL2R}
    (lam : SelbergExceptionalEigenvalue) (f : MaassCuspEigenform Γ lam.1)
    (w : maassDifferentialCyclicSpace f) :
    modelToMaass lam f (maassDifferentialModelEquiv lam f w) = w.1 := by
  exact modelToMaass_maassToModel lam f ((LinearEquiv.ofEq _ _
    (modelToMaass_range_eq_cyclic lam f).symm) w)

end
end GaloisForLFunctions.RHTower.MaassSmooth

