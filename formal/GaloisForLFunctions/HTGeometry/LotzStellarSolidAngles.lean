import GaloisForLFunctions.HTGeometry.LotzSignedStellarSubdivision
import GaloisForLFunctions.HTGeometry.LotzGaussianConeValuation

/-!
# Signed stellar subdivision for Gaussian solid angles

Integrating the geometric relation from Lotz, arXiv:2609.09335,
Lemma 3.5 and Proposition 3.6 gives the full signed relation for Gaussian
solid angles. Every exceptional wall is proved null, and every indicator
is proved integrable; callers supply only a basis and nonzero ray coordinates.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory ProbabilityTheory Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- All coordinate and ratio-tie exceptional walls are Gaussian-null. -/
theorem lotzStellarExceptional_gaussian_null (b : Basis ι ℝ E) (a : ι → ℝˣ) :
    stdGaussian E (lotzStellarExceptional b a)=0 := by
  unfold lotzStellarExceptional
  rw [Set.setOf_or,measure_union_null_iff]
  constructor
  · simp only [Set.setOf_exists]
    exact measure_iUnion_null_iff.mpr fun i => lotzGaussian_coordinate_wall b i
  · simp only [Set.setOf_exists]
    apply measure_iUnion_null_iff.mpr
    intro i
    apply measure_iUnion_null_iff.mpr
    intro j
    by_cases hij : i=j
    · simp [hij]
    · simpa [hij] using
        lotzGaussian_pair_wall b a i j

omit [DecidableEq ι] in
/-- Every basis-cone indicator is integrable without an additional analytic premise. -/
theorem lotzBasisConeIndicator_integrable (b : Basis ι ℝ E) :
    Integrable (lotzConeIndicator (lotzBasisCone b)) (stdGaussian E) := by
  change Integrable ((lotzProperBasisCone b : Set E).indicator (fun _ => (1 : ℝ))) _
  exact lotzGaussianCone_integrable (lotzProperBasisCone b)

omit [DecidableEq ι] in
/-- The geometric indicator integrates to the associated Gaussian solid angle. -/
theorem lotzBasisConeIndicator_integral (b : Basis ι ℝ E) :
    (∫ y,lotzConeIndicator (lotzBasisCone b) y ∂stdGaussian E) =
      lotzGaussianConeVal (lotzProperBasisCone b) := by
  change (∫ y,(lotzProperBasisCone b : Set E).indicator (fun _ => (1 : ℝ)) y ∂stdGaussian E) = _
  exact lotzGaussianCone_integral (lotzProperBasisCone b)

variable [Nonempty ι]

/-- Lotz's signed stellar relation holds almost everywhere as an actual cone identity. -/
theorem lotz_signed_stellar_ae (b : Basis ι ℝ E) (a : ι → ℝˣ) :
    (fun y => lotzConeIndicator (lotzBasisCone b) y-
      ∑ j, (if 0 < (a j : ℝ) then (1 : ℝ) else -1)*
        lotzConeIndicator (lotzBasisCone (lotzStellarBasis b a j)) y) =ᵐ[stdGaussian E]
      (fun _ => if ∀ j, (a j : ℝ)<0 then (1 : ℝ) else 0) := by
  have hae : ∀ᵐ y ∂stdGaussian E,y ∈ (lotzStellarExceptional b a)ᶜ :=
    compl_mem_ae_iff.mpr (lotzStellarExceptional_gaussian_null b a)
  exact hae.mono fun y hy => lotz_signed_stellar_subdivision b a hy

/-- Gaussian solid angle obeys the full signed stellar relation, including the exterior correction. -/
theorem lotz_signed_stellar_solid_angle (b : Basis ι ℝ E) (a : ι → ℝˣ) :
    lotzGaussianConeVal (lotzProperBasisCone b)-
      ∑ j, (if 0 < (a j : ℝ) then (1 : ℝ) else -1)*
        lotzGaussianConeVal (lotzProperBasisCone (lotzStellarBasis b a j)) =
      if ∀ j, (a j : ℝ)<0 then (1 : ℝ) else 0 := by
  have hterm (j : ι) : Integrable (fun y => (if 0 < (a j : ℝ) then (1 : ℝ) else -1)*
      lotzConeIndicator (lotzBasisCone (lotzStellarBasis b a j)) y) (stdGaussian E) :=
    (lotzBasisConeIndicator_integrable (lotzStellarBasis b a j)).const_mul _
  have hsum := integrable_finsetSum Finset.univ (fun j _ => hterm j)
  have h := integral_congr_ae (lotz_signed_stellar_ae b a)
  rw [integral_sub (lotzBasisConeIndicator_integrable b) hsum,
    integral_finsetSum _ (fun j _ => hterm j)] at h
  simpa only [integral_const_mul,lotzBasisConeIndicator_integral,integral_const,
    probReal_univ,one_smul] using h

end GaloisForLFunctions.HTGeometry
