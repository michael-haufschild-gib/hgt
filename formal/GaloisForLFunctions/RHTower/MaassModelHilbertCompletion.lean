import GaloisForLFunctions.RHTower.MaassModelHilbertForm
import Mathlib.Analysis.InnerProductSpace.Completion
import GaloisForLFunctions.HTGeometry.LinearIsometryCompletion

/-!
# The actual Maass map on the canonical Hilbert completion

The canonical complementary-series form defines the norm on finite K-types.
Normalizing the literal Maass map by its proved positive spherical norm gives
an isometry, which extends to the canonical Hilbert completion. This constructs
the Hilbert embedding; invariance of its range and full group equivariance
require the additional orbit argument.
-/

open UpperHalfPlane MeasureTheory

namespace GaloisForLFunctions.RHTower
noncomputable section

/-- Finite K-types equipped with the canonical complementary-series inner product. -/
def ComplementaryKFinite (_lam : SelbergExceptionalEigenvalue) := SphericalKFiniteModel
instance (lam : SelbergExceptionalEigenvalue) : AddCommGroup (ComplementaryKFinite lam) :=
  inferInstanceAs (AddCommGroup SphericalKFiniteModel)
instance (lam : SelbergExceptionalEigenvalue) : Module ℂ (ComplementaryKFinite lam) :=
  inferInstanceAs (Module ℂ SphericalKFiniteModel)

/-- Canonical finite coordinates, as a linear map to the algebraic model. -/
def ComplementaryKFinite.toModel (lam : SelbergExceptionalEigenvalue) :
    ComplementaryKFinite lam →ₗ[ℂ] SphericalKFiniteModel where
  toFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem complementary_parameter_abs (lam : SelbergExceptionalEigenvalue) :
    |2*lam.complementaryExponent| < 1 := by
  have h := lam.complementaryExponent_mem_Ioo
  exact abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

private abbrev complementaryInnerCore (lam : SelbergExceptionalEigenvalue) :
    InnerProductSpace.Core ℂ (ComplementaryKFinite lam) where
  inner v w := sphericalComplementaryHermitianForm (2*lam.complementaryExponent)
    (ComplementaryKFinite.toModel lam v) (ComplementaryKFinite.toModel lam w)
  conj_inner_symm v w :=
    (sphericalComplementaryHermitianForm_positiveDefinite _ (complementary_parameter_abs lam)).1.eq
      (ComplementaryKFinite.toModel lam w) (ComplementaryKFinite.toModel lam v)
  re_inner_nonneg v := by
    by_cases h : v = 0
    · subst v; simp
    · change ComplementaryKFinite.toModel lam v ≠ 0 at h
      exact ((sphericalComplementaryHermitianForm_positiveDefinite _
        (complementary_parameter_abs lam)).2 _ h).le
  add_left v w z := by simp only [map_add, LinearMap.add_apply]
  smul_left v w c := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
  definite v hv := by
    by_contra h
    change ComplementaryKFinite.toModel lam v ≠ 0 at h
    have hp := (sphericalComplementaryHermitianForm_positiveDefinite _
      (complementary_parameter_abs lam)).2 _ h
    rw [hv] at hp
    exact (lt_irrefl 0) hp

instance (lam : SelbergExceptionalEigenvalue) : NormedAddCommGroup (ComplementaryKFinite lam) :=
  (complementaryInnerCore lam).toNormedAddCommGroup
instance (lam : SelbergExceptionalEigenvalue) : InnerProductSpace ℂ (ComplementaryKFinite lam) :=
  InnerProductSpace.ofCore (complementaryInnerCore lam).toCore

/-- Canonical complementary Hilbert space obtained by completing its finite K-types. -/
abbrev ComplementaryHilbert (lam : SelbergExceptionalEigenvalue) :=
  UniformSpace.Completion (ComplementaryKFinite lam)

@[simp] theorem complementaryKFinite_inner (lam : SelbergExceptionalEigenvalue)
    (v w : ComplementaryKFinite lam) : inner ℂ v w =
      sphericalComplementaryHermitianForm (2*lam.complementaryExponent)
        (ComplementaryKFinite.toModel lam v) (ComplementaryKFinite.toModel lam w) := rfl

namespace MaassModelQuotientL2
variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam.1)

theorem modelToLp_spherical_norm_pos :
    0 < ‖modelToLp N lam f (Finsupp.single 0 1)‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he : (Finsupp.single 0 1 : SphericalKFiniteModel) = 0 :=
    modelToLp_injective N lam f (by simpa only [map_zero] using h)
  have he0 := congrArg (fun v : SphericalKFiniteModel => v 0) he
  exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using he0)

theorem modelToLp_norm (v : ComplementaryKFinite lam) :
    ‖modelToLp N lam f (ComplementaryKFinite.toModel lam v)‖ =
      ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ := by
  have h := modelToLp_norm_sq N lam f (ComplementaryKFinite.toModel lam v)
  have hv := @norm_sq_eq_re_inner ℂ (ComplementaryKFinite lam) _ _ _ v
  rw [complementaryKFinite_inner] at hv
  change ‖v‖ ^ 2 = (sphericalComplementaryHermitianForm (2*lam.complementaryExponent)
    (ComplementaryKFinite.toModel lam v) (ComplementaryKFinite.toModel lam v)).re at hv
  rw [← hv] at h
  have hp := mul_nonneg (norm_nonneg (modelToLp N lam f (Finsupp.single 0 1))) (norm_nonneg v)
  nlinarith [norm_nonneg (modelToLp N lam f (ComplementaryKFinite.toModel lam v))]

/-- Normalize the literal Maass map by its actual nonzero spherical norm. -/
def normalizedModelToLp : ComplementaryKFinite lam →ₗ[ℂ]
    Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N+1))) :=
  (‖modelToLp N lam f (Finsupp.single 0 1)‖ : ℂ)⁻¹ •
    (modelToLp N lam f).comp (ComplementaryKFinite.toModel lam)

theorem normalizedModelToLp_norm (v : ComplementaryKFinite lam) :
    ‖normalizedModelToLp N lam f v‖ = ‖v‖ := by
  have h := (modelToLp_spherical_norm_pos N lam f).ne'
  simp only [normalizedModelToLp, LinearMap.smul_apply, LinearMap.comp_apply,
    norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [modelToLp_norm N lam f v, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- The actual normalized finite Maass map is a complex linear isometry. -/
def modelIsometry : ComplementaryKFinite lam →ₗᵢ[ℂ]
    Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N+1))) where
  toLinearMap := normalizedModelToLp N lam f
  norm_map' := normalizedModelToLp_norm N lam f

/-- Hilbert-space isometric embedding extending the original finite Maass model. -/
def completedModelIsometry : ComplementaryHilbert lam →ₗᵢ[ℂ]
    Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N+1))) :=
  HTGeometry.completionExtendₗᵢ (modelIsometry N lam f)

@[simp] theorem completedModelIsometry_coe (v : ComplementaryKFinite lam) :
    completedModelIsometry N lam f (v : ComplementaryHilbert lam) = modelIsometry N lam f v :=
  HTGeometry.completionExtendₗᵢ_coe (modelIsometry N lam f) v

/-- The completed embedding has exactly the closure of the actual finite Maass image as range. -/
theorem completedModelIsometry_range :
    Set.range (completedModelIsometry N lam f) = closure (Set.range (modelIsometry N lam f)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨v, rfl⟩
    induction v using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_closure.preimage (completedModelIsometry N lam f).continuous
    | ih v =>
        rw [completedModelIsometry_coe]
        exact subset_closure ⟨v, rfl⟩
  · apply closure_minimal
    · rintro _ ⟨v, rfl⟩
      exact ⟨(v : ComplementaryHilbert lam), completedModelIsometry_coe N lam f v⟩
    · exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range

end MaassModelQuotientL2
end
end GaloisForLFunctions.RHTower
