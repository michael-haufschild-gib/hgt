import GaloisForLFunctions.HTGeometry.DifferentialVariationalCartanTranslationVector

/-!
# Euclidean norm of the intrinsic Cartan translation vector

Coordinatewise convergence of the normalized Cartan vector upgrades, in finite rank, to
convergence of its literal Euclidean norm.  Comparing this limit with the independently
constructed scalar Fekete limit identifies scalar translation speed exactly with the Euclidean
norm of the intrinsic vector-valued speed.  Consequently, zero scalar speed and zero Cartan vector
are equivalent without any geometric-realization premise.
-/

open Filter Topology
open scoped Differential BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C K : Type*} [Field C] [Field K] [Algebra C K] [Differential K]
  [IsConstantBase C K]

/-- Literal Euclidean norm of the intrinsic vector-valued Cartan translation length. -/
noncomputable def differentialVariationalCartanTranslationVectorEuclideanNorm
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) : ℝ :=
  ‖(WithLp.toLp 2 (differentialVariationalCartanTranslationVector b x σ) :
    EuclideanSpace ℝ (Fin r))‖

/-- Coordinatewise normalized Cartan convergence implies convergence of the literal Euclidean
norm in every finite rank, including rank zero. -/
theorem tendsto_differentialVariationalCartan_normalizedEuclideanNorm
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    Tendsto (fun n : ℕ =>
      ‖(WithLp.toLp 2 (fun i : Fin r =>
        (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
          ((σ ^ n).projectiveBuildingAction b x) : Fin r → ℝ) i / n) :
        EuclideanSpace ℝ (Fin r))‖)
      atTop (nhds (differentialVariationalCartanTranslationVectorEuclideanNorm b x σ)) := by
  have hvec := tendsto_differentialVariationalCartanTranslationVector b x σ
  rw [tendsto_pi_nhds] at hvec
  unfold differentialVariationalCartanTranslationVectorEuclideanNorm
  simp_rw [EuclideanSpace.norm_eq]
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  apply tendsto_finsetSum Finset.univ
  intro i hi
  have hnorm := (hvec i).norm
  simpa only [WithLp.ofLp_toLp, pow_two] using hnorm.mul hnorm

/-- Dividing a vertex displacement by a natural clock equals the Euclidean norm of the
coordinatewise normalized relative-position vector, including clock zero. -/
theorem differentialVariationalProjectiveEuclideanVertexDistance_div_eq_normalizedNorm
    {r : ℕ}
    (x y : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (n : ℕ) :
    DiffOp.differentialVariationalProjectiveEuclideanVertexDistance x y / n =
      ‖(WithLp.toLp 2 (fun i : Fin r =>
        (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) i / n) :
        EuclideanSpace ℝ (Fin r))‖ := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, div_zero]
    rw [show WithLp.toLp 2 (fun _i : Fin r => (0 : ℝ)) = 0 by
      apply PiLp.ext
      intro i
      rfl]
    exact norm_zero.symm
  · unfold DiffOp.differentialVariationalProjectiveEuclideanVertexDistance
    have hvec :
        (WithLp.toLp 2 (fun i : Fin r =>
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) i / n) :
          EuclideanSpace ℝ (Fin r)) =
        ((n : ℝ)⁻¹) •
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y).1 := by
      change WithLp.toLp 2 (fun i : Fin r =>
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) i / n) =
        WithLp.toLp 2 (fun i : Fin r => (n : ℝ)⁻¹ *
          (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x y : Fin r → ℝ) i)
      apply congrArg (WithLp.toLp 2)
      funext i
      rw [div_eq_mul_inv, mul_comm]
    rw [hvec, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (Nat.cast_nonneg n)]
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp

/-- Scalar Euclidean translation speed is exactly the Euclidean norm of the intrinsic Cartan
translation vector. -/
theorem differentialVariationalEuclideanTranslationLength_eq_cartanVectorEuclideanNorm
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalEuclideanTranslationLength b x σ =
      differentialVariationalCartanTranslationVectorEuclideanNorm b x σ := by
  have hscalar := tendsto_differentialVariationalEuclidean_normalizedOrbitDistance b x σ
  have hvector := tendsto_differentialVariationalCartan_normalizedEuclideanNorm b x σ
  have hscalar' : Tendsto (fun n : ℕ =>
      ‖(WithLp.toLp 2 (fun i : Fin r =>
        (DiffOp.differentialVariationalProjectiveEuclideanRelativePosition x
          ((σ ^ n).projectiveBuildingAction b x) : Fin r → ℝ) i / n) :
        EuclideanSpace ℝ (Fin r))‖)
      atTop (nhds (differentialVariationalEuclideanTranslationLength b x σ)) := by
    convert hscalar using 1
    funext n
    exact (differentialVariationalProjectiveEuclideanVertexDistance_div_eq_normalizedNorm
      x ((σ ^ n).projectiveBuildingAction b x) n).symm
  exact tendsto_nhds_unique hscalar' hvector

/-- Zero scalar speed is equivalent to vanishing of the complete intrinsic Cartan vector. -/
theorem differentialVariationalEuclideanTranslationLength_eq_zero_iff_cartanVector_eq_zero
    {r : ℕ} (b : Module.Basis (Fin r) (DiffOp K) (VariationalOreModule C K))
    (x : DiffOp.DifferentialVariationalProjectiveBuildingCarrier K (Fin r))
    (σ : DifferentialFieldAut C K) :
    differentialVariationalEuclideanTranslationLength b x σ = 0 ↔
      differentialVariationalCartanTranslationVector b x σ = 0 := by
  rw [differentialVariationalEuclideanTranslationLength_eq_cartanVectorEuclideanNorm,
    differentialVariationalCartanTranslationVectorEuclideanNorm, norm_eq_zero]
  constructor
  · intro h
    exact WithLp.toLp_injective 2 h
  · intro h
    exact congrArg (WithLp.toLp 2) h

end

end GaloisForLFunctions.HTGeometry
