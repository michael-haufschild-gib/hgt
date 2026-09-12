import GaloisForLFunctions.RHTower.MaassWeightLift
import GaloisForLFunctions.RHTower.MaassDifferentialLadder

/-! Actual automorphic Maass ladders and uniqueness of their finite weight coordinates. -/

open UpperHalfPlane Complex
namespace GaloisForLFunctions.RHTower.MaassSmooth
noncomputable section

private theorem weightLift_ladder_preserves (Γ : Subgroup SL2R) (m : ℤ) (f : FunctionSpace)
    (hf : weightLift m f ∈ automorphicFunctionSpace Γ) :
    weightLift (m+1) (raise m f) ∈ automorphicFunctionSpace Γ ∧
      weightLift (m-1) (lower m f) ∈ automorphicFunctionSpace Γ := by
  have heq (γ : Γ) (g : SL2R) (p : ℝ → SL2R) :
      (fun t => weightLift m f (((γ : SL2R)*g)*p t)) =
        (fun t => weightLift m f (g*p t)) := by
    funext t
    simpa only [mul_assoc] using hf γ (g*p t)
  have hstep (γ : Γ) (g : SL2R) :
      weightLift (m+1) (raise m f) ((γ : SL2R)*g) = weightLift (m+1) (raise m f) g ∧
      weightLift (m-1) (lower m f) ((γ : SL2R)*g) = weightLift (m-1) (lower m f) g := by
    have ha := weightLift_diagonal_hasDerivAt m f ((γ : SL2R)*g)
    have hb := weightLift_quarterDiagonal_hasDerivAt m f ((γ : SL2R)*g)
    rw [heq] at ha hb
    have ha' := ha.unique (weightLift_diagonal_hasDerivAt m f g)
    have hb' := hb.unique (weightLift_quarterDiagonal_hasDerivAt m f g)
    have hdiff :
        weightLift (m+1) (raise m f) ((γ : SL2R)*g) -
          weightLift (m-1) (lower m f) ((γ : SL2R)*g) =
        weightLift (m+1) (raise m f) g - weightLift (m-1) (lower m f) g :=
      mul_left_cancel₀ Complex.I_ne_zero hb'
    constructor
    · linear_combination (ha' + hdiff)/2
    · linear_combination (ha' - hdiff)/2
  exact ⟨fun γ g => (hstep γ g).1, fun γ g => (hstep γ g).2⟩

private theorem weightLift_ofMaass_mem {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) : weightLift 0 (ofMaass f) ∈ automorphicFunctionSpace Γ := by
  intro γ g
  simp only [weightLift, realSphericalKTypeCharacter_apply, mul_zero, zpow_zero, mul_one,
    ofMaass_apply, mul_smul]
  exact f.1.property γ (g • UpperHalfPlane.I)

/-- Every actual raised Maass function lifts to an automorphic function. -/
theorem raised_automorphic {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (n : ℕ) :
    weightLift (n : ℤ) (raised (ofMaass f) n) ∈ automorphicFunctionSpace Γ := by
  induction n with
  | zero => exact weightLift_ofMaass_mem f
  | succ n ih =>
      simpa only [Nat.cast_add, Nat.cast_one, raised_succ] using
        (weightLift_ladder_preserves Γ (n : ℤ) (raised (ofMaass f) n) ih).1

/-- Every actual lowered Maass function lifts to an automorphic function. -/
theorem lowered_automorphic {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (n : ℕ) :
    weightLift (-(n : ℤ)) (lowered (ofMaass f) n) ∈ automorphicFunctionSpace Γ := by
  induction n with
  | zero => simpa using weightLift_ofMaass_mem f
  | succ n ih =>
      have h := (weightLift_ladder_preserves Γ (-(n : ℤ)) (lowered (ofMaass f) n) ih).2
      convert! h using 1
      simp only [lowered_succ, Nat.cast_add, Nat.cast_one, neg_add_rev]
      congr 1
      omega

/-- The raised ladder as actual automorphic vectors, without an assumed covariance law. -/
def raisedAutomorphic {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (n : ℕ) : automorphicFunctionSpace Γ :=
  ⟨weightLift (n : ℤ) (raised (ofMaass f) n), raised_automorphic f n⟩

/-- The lowered ladder as actual automorphic vectors. -/
def loweredAutomorphic {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (n : ℕ) : automorphicFunctionSpace Γ :=
  ⟨weightLift (-(n : ℤ)) (lowered (ofMaass f) n), lowered_automorphic f n⟩

/-- Exceptional raised automorphic vectors are nonzero at every order. -/
theorem raisedAutomorphic_ne_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) : raisedAutomorphic f n ≠ 0 := by
  intro hz
  apply raised_ne_zero lam f n
  apply weightLift_injective (n : ℤ)
  have h := congrArg (fun v : automorphicFunctionSpace Γ => v.1) hz
  simpa only [raisedAutomorphic, weightLift_zero, ZeroMemClass.coe_zero] using h

/-- Exceptional lowered automorphic vectors are nonzero at every order. -/
theorem loweredAutomorphic_ne_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (n : ℕ) : loweredAutomorphic f n ≠ 0 := by
  intro hz
  apply lowered_ne_zero lam f n
  apply weightLift_injective (-(n : ℤ))
  have h := congrArg (fun v : automorphicFunctionSpace Γ => v.1) hz
  simpa only [loweredAutomorphic, weightLift_zero, ZeroMemClass.coe_zero] using h

/-- Both differential ladders, indexed by their half-weight. -/
def automorphicLadder {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) : ℤ → automorphicFunctionSpace Γ
  | .ofNat n => raisedAutomorphic f n
  | .negSucc n => loweredAutomorphic f (n+1)

/-- Each literal ladder vector has its stated compact weight. -/
theorem automorphicLadder_right {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (m : ℤ) (g : SL2R) (k : upperHalfPlaneStabilizer) :
    (automorphicLadder f m).1 (g * (k : SL2R)) =
      (automorphicLadder f m).1 g * realSphericalKTypeCharacter m k := by
  cases m with
  | ofNat n => exact weightLift_right (n : ℤ) (raised (ofMaass f) n) g k
  | negSucc n => exact weightLift_right (-((n+1 : ℕ) : ℤ)) (lowered (ofMaass f) (n+1)) g k

/-- No vector in the two-sided exceptional automorphic ladder is zero. -/
theorem automorphicLadder_ne_zero {Γ : Subgroup SL2R} (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform Γ lam.1) (m : ℤ) : automorphicLadder f m ≠ 0 := by
  cases m with
  | ofNat n => exact raisedAutomorphic_ne_zero lam f n
  | negSucc n => exact loweredAutomorphic_ne_zero lam f (n+1)

/-- Compact character independence separates all actual automorphic ladder vectors. -/
theorem automorphicLadder_linearIndependent {Γ : Subgroup SL2R}
    (lam : SelbergExceptionalEigenvalue) (f : MaassCuspEigenform Γ lam.1) :
    LinearIndependent ℂ (automorphicLadder f) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc m hm
  have hcoeff (g : SL2R) : c m * (automorphicLadder f m).1 g = 0 := by
    have hchars : ∑ i ∈ s, (c i * (automorphicLadder f i).1 g) •
        (realSphericalKTypeCharacter i : upperHalfPlaneStabilizer → ℂ) = 0 := by
      funext k
      have h := congrArg (fun F : automorphicFunctionSpace Γ => F.1 (g * (k : SL2R))) hc
      simpa [automorphicLadder_right, mul_assoc] using h
    exact linearIndependent_iff'.mp realSphericalKTypeCharacter_linearIndependent
      s (fun i => c i * (automorphicLadder f i).1 g) hchars m hm
  by_contra hcm
  apply automorphicLadder_ne_zero lam f m
  apply Subtype.ext
  funext g
  exact (mul_eq_zero.mp (hcoeff g)).resolve_left hcm

/-- Finite weight coordinates map to the actual differentiated automorphic ladder. -/
def automorphicLadderEmbedding {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) : SphericalKFiniteModel →ₗ[ℂ] automorphicFunctionSpace Γ :=
  Finsupp.linearCombination ℂ (automorphicLadder f)

/-- Finite source coordinates are unique for every exceptional Maass form. -/
theorem automorphicLadderEmbedding_injective {Γ : Subgroup SL2R}
    (lam : SelbergExceptionalEigenvalue) (f : MaassCuspEigenform Γ lam.1) :
    Function.Injective (automorphicLadderEmbedding f) :=
  automorphicLadder_linearIndependent lam f

/-- The coordinate map recovers the specified actual automorphic vector on a basis element. -/
@[simp] theorem automorphicLadderEmbedding_single {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) (m : ℤ) (c : ℂ) :
    automorphicLadderEmbedding f (Finsupp.single m c) = c • automorphicLadder f m :=
  Finsupp.linearCombination_single ℂ c m

end
end GaloisForLFunctions.RHTower.MaassSmooth
