import GaloisForLFunctions.HTGeometry.MeasureGramMatrix

/-!
# Complex integral Gram matrices

The conjugate Gram matrix of a family of complex features is positive semidefinite: its quadratic
form is the integral of the squared modulus of the corresponding feature combination.  Pairwise
integrability of the products is what lets the finite sum pass through the integral.

The measure part of the scaled Pick kernel is such a matrix, with the scaled Cauchy kernels at the
nodes as features, so it is positive semidefinite whenever those products are integrable.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Matrix

noncomputable section

open scoped ComplexOrder

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- The conjugate Gram matrix of a finite family of complex features. -/
def complexFeatureGram (μ : Measure Ω) (f : ι → Ω → ℂ) : Matrix ι ι ℂ :=
  fun l m => ∫ ω, f l ω * (starRingEnd ℂ) (f m ω) ∂μ

/-- The feature combination whose squared modulus the quadratic form integrates. -/
def complexFeatureCombination (f : ι → Ω → ℂ) (x : ι → ℂ) (ω : Ω) : ℂ :=
  ∑ l, (starRingEnd ℂ) (x l) * f l ω

omit [MeasurableSpace Ω] in
/-- The squared modulus of a feature combination expands into the pairwise products. -/
theorem complexFeatureCombination_mul_conj (f : ι → Ω → ℂ) (x : ι → ℂ) (ω : Ω) :
    complexFeatureCombination f x ω * (starRingEnd ℂ) (complexFeatureCombination f x ω)
      = ∑ l, ∑ m, (starRingEnd ℂ) (x l) * x m * (f l ω * (starRingEnd ℂ) (f m ω)) := by
  rw [complexFeatureCombination, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, Complex.conj_conj]
  ring

omit [Fintype ι] in
/-- A conjugate Gram matrix is Hermitian. -/
theorem complexFeatureGram_isHermitian (μ : Measure Ω) (f : ι → Ω → ℂ) :
    (complexFeatureGram μ f).IsHermitian := by
  ext l m
  rw [Matrix.conjTranspose_apply]
  show (starRingEnd ℂ) (∫ ω, f m ω * (starRingEnd ℂ) (f l ω) ∂μ)
      = ∫ ω, f l ω * (starRingEnd ℂ) (f m ω) ∂μ
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [map_mul, Complex.conj_conj]
  ring

/-- **The quadratic form of a conjugate Gram matrix is the integral of the squared modulus.** -/
theorem complexFeatureGram_quadratic (μ : Measure Ω) (f : ι → Ω → ℂ)
    (hprod : ∀ l m, Integrable (fun ω => f l ω * (starRingEnd ℂ) (f m ω)) μ) (x : ι → ℂ) :
    star x ⬝ᵥ (complexFeatureGram μ f).mulVec x
      = ∫ ω, complexFeatureCombination f x ω
          * (starRingEnd ℂ) (complexFeatureCombination f x ω) ∂μ := by
  have hterm : ∀ l m, Integrable
      (fun ω => (starRingEnd ℂ) (x l) * x m * (f l ω * (starRingEnd ℂ) (f m ω))) μ :=
    fun l m => (hprod l m).const_mul _
  calc star x ⬝ᵥ (complexFeatureGram μ f).mulVec x
      = ∑ l, ∑ m, (starRingEnd ℂ) (x l) * x m
          * ∫ ω, f l ω * (starRingEnd ℂ) (f m ω) ∂μ := by
        simp only [dotProduct, mulVec, complexFeatureGram, Pi.star_apply,
          RCLike.star_def, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        ring
    _ = ∑ l, ∑ m, ∫ ω, (starRingEnd ℂ) (x l) * x m
          * (f l ω * (starRingEnd ℂ) (f m ω)) ∂μ := by
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
        rw [integral_const_mul]
    _ = ∫ ω, ∑ l, ∑ m, (starRingEnd ℂ) (x l) * x m
          * (f l ω * (starRingEnd ℂ) (f m ω)) ∂μ := by
        rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun m _ => hterm l m]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_finsetSum _ fun m _ => hterm l m]
    _ = ∫ ω, complexFeatureCombination f x ω
          * (starRingEnd ℂ) (complexFeatureCombination f x ω) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (complexFeatureCombination_mul_conj f x ω).symm

/-- **A conjugate Gram matrix of pairwise-integrable features is positive semidefinite.** -/
theorem complexFeatureGram_posSemidef (μ : Measure Ω) (f : ι → Ω → ℂ)
    (hprod : ∀ l m, Integrable (fun ω => f l ω * (starRingEnd ℂ) (f m ω)) μ) :
    (complexFeatureGram μ f).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (complexFeatureGram_isHermitian μ f) fun x => ?_
  rw [complexFeatureGram_quadratic μ f hprod x]
  have hcast : ∀ ω, complexFeatureCombination f x ω
      * (starRingEnd ℂ) (complexFeatureCombination f x ω)
      = ((‖complexFeatureCombination f x ω‖ ^ 2 : ℝ) : ℂ) := by
    intro ω
    rw [Complex.mul_conj, ← Complex.sq_norm]
  have hint : Integrable (fun ω => complexFeatureCombination f x ω
      * (starRingEnd ℂ) (complexFeatureCombination f x ω)) μ := by
    refine Integrable.congr
      (integrable_finsetSum (Finset.univ : Finset ι) fun l _ =>
        integrable_finsetSum (Finset.univ : Finset ι) fun m _ =>
          (hprod l m).const_mul ((starRingEnd ℂ) (x l) * x m)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    exact (complexFeatureCombination_mul_conj f x ω).symm
  have hgint : Integrable (fun ω => ‖complexFeatureCombination f x ω‖ ^ 2) μ := by
    have hre : Integrable (fun ω => (complexFeatureCombination f x ω
        * (starRingEnd ℂ) (complexFeatureCombination f x ω)).re) μ := hint.re
    refine hre.congr (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [hcast ω, Complex.ofReal_re]
  have hval : ∫ ω, complexFeatureCombination f x ω
      * (starRingEnd ℂ) (complexFeatureCombination f x ω) ∂μ
      = ((∫ ω, ‖complexFeatureCombination f x ω‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hcast)]
    exact Complex.ofRealCLM.integral_comp_comm hgint
  rw [hval]
  have hnn : (0 : ℝ) ≤ ∫ ω, ‖complexFeatureCombination f x ω‖ ^ 2 ∂μ :=
    integral_nonneg fun ω => by positivity
  exact_mod_cast hnn

/-- **The scaled measure Gram is positive semidefinite.**  It is the conjugate Gram matrix of the
scaled Cauchy kernels at the nodes above the atoms. -/
theorem measureGram_posSemidef {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ) (y : ℝ)
    (hprod : ∀ l m : Fin d, Integrable (fun t : ℝ =>
      ((y : ℂ) * ((t : ℂ) - upperNode (a l) y)⁻¹) *
        (starRingEnd ℂ) ((y : ℂ) * ((t : ℂ) - upperNode (a m) y)⁻¹)) ν) :
    (measureGram ν a y).PosSemidef :=
  complexFeatureGram_posSemidef ν
    (fun l t => (y : ℂ) * ((t : ℂ) - upperNode (a l) y)⁻¹) hprod

end

end GaloisForLFunctions.HTGeometry
