import GaloisForLFunctions.HTGeometry.LotzStellarCones

/-!
# Gaussian solid angle as a monotone orthogonally invariant cone valuation

Infrastructure for Lotz, arXiv:2609.09335, Proposition 3.6. Gaussian mass
vanishes on every genuine linear hyperplane; degenerate fibers are classified
exactly. Closed-cone solid angle is bounded, monotone, valuative for actual
unions and intersections, and invariant under orthogonal basis changes.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory ProbabilityTheory Module
attribute [local instance] Classical.propDecidable
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every linear fiber has exactly zero or full standard-Gaussian mass, including the degenerate functional. -/
theorem lotz_stdGaussian_fiber (L : StrongDual ℝ E) (c : ℝ) :
    stdGaussian E {x | L x=c} = if L=0 ∧ c=0 then 1 else 0 := by
  by_cases hL : L=0
  · subst L
    by_cases hc : c=0
    · subst c
      simp
    · simp [hc,Ne.symm hc]
  · rw [if_neg (fun h => hL h.1)]
    have hv : (‖L‖^(2 : ℕ)).toNNReal ≠ 0 :=
      ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hL)))
    have hmap : (stdGaussian E).map L = gaussianReal 0 (‖L‖^(2 : ℕ)).toNNReal := by
      rw [IsGaussian.map_eq_gaussianReal L,integral_strongDual_stdGaussian,
        variance_dual_stdGaussian]
    letI := nullSingletonClass_gaussianReal (μ := 0) hv
    have hzero : ((stdGaussian E).map L) {c} = 0 := by
      rw [hmap]
      exact measure_singleton c
    simpa only [Measure.map_apply L.continuous.measurable (measurableSet_singleton c),
      Set.preimage,Set.mem_singleton_iff] using hzero

/-- A hyperplane is Gaussian-null exactly when its defining functional is nonzero. -/
theorem lotz_stdGaussian_kernel_iff (L : StrongDual ℝ E) :
    stdGaussian E {x | L x=0}=0 ↔ L≠0 := by
  rw [lotz_stdGaussian_fiber]
  by_cases h : L=0 <;> simp [h]

/-- Gaussian solid angle of a closed convex cone. -/
def lotzGaussianConeVal (C : ProperCone ℝ E) : ℝ := (stdGaussian E).real (C : Set E)

omit [BorelSpace E] in
theorem lotzGaussianConeVal_nonneg (C : ProperCone ℝ E) : 0 ≤ lotzGaussianConeVal C :=
  ENNReal.toReal_nonneg

theorem lotzGaussianConeVal_le_one (C : ProperCone ℝ E) : lotzGaussianConeVal C ≤ 1 := by
  calc
    lotzGaussianConeVal C ≤ (stdGaussian E).real Set.univ := measureReal_mono (Set.subset_univ _)
    _ = 1 := by simp

theorem lotzGaussianConeVal_monotone : Monotone (lotzGaussianConeVal (E := E)) := by
  intro C D hCD
  exact measureReal_mono hCD

/-- The valuation identity uses the actual union; it does not replace a union by its convex hull. -/
theorem lotzGaussianConeVal_union_inter (C D : ProperCone ℝ E) :
    (stdGaussian E).real ((C : Set E) ∪ (D : Set E)) + lotzGaussianConeVal (C ⊓ D) =
      lotzGaussianConeVal C + lotzGaussianConeVal D := by
  exact measureReal_union_add_inter D.isClosed.measurableSet

/-- The real indicator is integrable for every proper cone, without a side condition. -/
theorem lotzGaussianCone_integrable (C : ProperCone ℝ E) :
    Integrable ((C : Set E).indicator (fun _ => (1 : ℝ))) (stdGaussian E) :=
  (integrable_const 1).indicator C.isClosed.measurableSet

/-- Solid angle is exactly the Gaussian integral of the cone indicator. -/
theorem lotzGaussianCone_integral (C : ProperCone ℝ E) :
    (∫ x, (C : Set E).indicator (fun _ => (1 : ℝ)) x ∂stdGaussian E) =
      lotzGaussianConeVal C := by
  simpa only [smul_eq_mul,mul_one,lotzGaussianConeVal] using integral_indicator_const (μ := stdGaussian E)
    (1 : ℝ) C.isClosed.measurableSet

variable {ι : Type*} [Fintype ι]

/-- Basis coordinates are continuous dual vectors in finite dimension. -/
def lotzCoordinateFunctional (b : Basis ι ℝ E) (i : ι) : StrongDual ℝ E :=
  ⟨b.coord i,(b.coord i).continuous_of_finiteDimensional⟩

omit [MeasurableSpace E] [BorelSpace E] in
theorem lotzCoordinateFunctional_apply (b : Basis ι ℝ E) (i : ι) (x : E) :
    lotzCoordinateFunctional b i x = b.equivFun x i := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem lotzCoordinateFunctional_ne_zero (b : Basis ι ℝ E) (i : ι) :
    lotzCoordinateFunctional b i ≠ 0 := by
  classical
  intro h
  have he := congrArg (fun L : StrongDual ℝ E => L (b i)) h
  simp [lotzCoordinateFunctional_apply,b.equivFun_self] at he

/-- Every coordinate wall has zero Gaussian mass, for every finite-dimensional basis. -/
theorem lotzGaussian_coordinate_wall (b : Basis ι ℝ E) (i : ι) :
    stdGaussian E {x | b.equivFun x i=0}=0 := by
  exact (lotz_stdGaussian_kernel_iff (lotzCoordinateFunctional b i)).mpr
    (lotzCoordinateFunctional_ne_zero b i)

/-- Pair-ratio walls have a natural continuous linear defining functional. -/
def lotzPairFunctional (b : Basis ι ℝ E) (a : ι → ℝˣ) (i j : ι) : StrongDual ℝ E :=
  (a j : ℝ) • lotzCoordinateFunctional b i - (a i : ℝ) • lotzCoordinateFunctional b j

omit [MeasurableSpace E] [BorelSpace E] in
theorem lotzPairFunctional_eq_zero_iff (b : Basis ι ℝ E) (a : ι → ℝˣ) (i j : ι) :
    lotzPairFunctional b a i j=0 ↔ i=j := by
  classical
  constructor
  · intro h
    by_contra hne
    have he := congrArg (fun L : StrongDual ℝ E => L (b i)) h
    simp [lotzPairFunctional,lotzCoordinateFunctional_apply,b.equivFun_self,hne] at he
  · rintro rfl
    simp [lotzPairFunctional]

/-- Ratio coincidences are Gaussian-null exactly off the diagonal in the index set. -/
theorem lotzGaussian_pair_wall (b : Basis ι ℝ E) (a : ι → ℝˣ) (i j : ι) :
    stdGaussian E {x | (a j : ℝ)*b.equivFun x i=(a i : ℝ)*b.equivFun x j} =
      if i=j then 1 else 0 := by
  have h := lotz_stdGaussian_fiber (lotzPairFunctional b a i j) 0
  simp only [lotzPairFunctional_eq_zero_iff,and_true] at h
  simpa only [lotzPairFunctional,
    sub_apply,smul_apply,smul_eq_mul,
    lotzCoordinateFunctional_apply,sub_eq_zero] using h

/-- Gaussian solid angle is invariant under every orthogonal change of basis. -/
theorem lotzGaussian_basis_isometry (b : Basis ι ℝ E) (e : E ≃ₗᵢ[ℝ] E) :
    lotzGaussianConeVal (lotzProperBasisCone (b.map e.toLinearEquiv)) =
      lotzGaussianConeVal (lotzProperBasisCone b) := by
  unfold lotzGaussianConeVal Measure.real
  congr 1
  change (stdGaussian E) (lotzBasisCone (b.map e.toLinearEquiv) : Set E) =
    (stdGaussian E) (lotzBasisCone b : Set E)
  calc
    _ = ((stdGaussian E).map e) (lotzBasisCone (b.map e.toLinearEquiv) : Set E) := by
      rw [stdGaussian_map]
    _ = _ := by
      rw [Measure.map_apply e.continuous.measurable
        (isClosed_lotzBasisCone (b.map e.toLinearEquiv)).measurableSet]
      congr 1
      ext x
      change e x ∈ lotzBasisCone (b.map e.toLinearEquiv) ↔ x ∈ lotzBasisCone b
      simp only [lotzBasisCone_mem,Basis.map_equivFun,LinearEquiv.trans_apply]
      change (∀ i,0 ≤ b.equivFun (e.symm (e x)) i) ↔ ∀ i,0 ≤ b.equivFun x i
      rw [e.symm_apply_apply]

end GaloisForLFunctions.HTGeometry
