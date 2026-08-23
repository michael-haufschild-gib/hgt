import GaloisForLFunctions.HTGeometry.ProjectiveAffineChartFullEvaluation

/-!
# Hasse quotient for projective affine-chart evaluation

The disjoint active/inactive row presentation already maps surjectively to the genuine localized
global incidence ring.  Its first-isomorphism quotient gives a precise chartwise local-global
principle: every global incidence class has a local representative, unique modulo the evaluation
kernel.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The genuine localized global incidence ring is the local all-row chart presentation modulo
exactly the relations invisible to global evaluation. -/
noncomputable def projectiveChartFullEvaluationQuotientEquiv
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime] :
    (projectiveChartFullIncidenceRing q n z j exponent p ⧸
      RingHom.ker (projectiveChartFullEvaluation q n z j exponent p).toRingHom) ≃ₐ[
        Localization.AtPrime p]
      projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p :=
  Ideal.quotientKerAlgEquivOfSurjective
    (projectiveChartFullEvaluation_surjective q n z j exponent p)

/-- The first-isomorphism equivalence is induced by full chart evaluation. -/
@[simp] theorem projectiveChartFullEvaluationQuotientEquiv_mk
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (x : projectiveChartFullIncidenceRing q n z j exponent p) :
    projectiveChartFullEvaluationQuotientEquiv q n z j exponent p
        (Ideal.Quotient.mk _ x) =
      projectiveChartFullEvaluation q n z j exponent p x := by
  rfl

/-- Local chart representatives have the same global class exactly when their difference is an
invisible chart relation. -/
theorem projectiveChartFullEvaluation_eq_iff_sub_mem_kernel
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (x y : projectiveChartFullIncidenceRing q n z j exponent p) :
    projectiveChartFullEvaluation q n z j exponent p x =
        projectiveChartFullEvaluation q n z j exponent p y ↔
      x - y ∈ RingHom.ker
        (projectiveChartFullEvaluation q n z j exponent p).toRingHom := by
  change _ ↔ projectiveChartFullEvaluation q n z j exponent p (x - y) = 0
  rw [map_sub, sub_eq_zero]

/-- Every genuine global incidence class has a local all-row chart representative, unique modulo
the invisible chart kernel. -/
theorem projectiveChartFullEvaluation_exists_unique_mod_kernel
    {row κ : Type} [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (j : κ × Fin (q + 1))
    (exponent : κ → (Fin n →₀ ℕ))
    (p : Ideal (projectiveChartCoefficientRing j)) [p.IsPrime]
    (a : projectiveChartBaseChangedGlobalIncidenceRing q n z j exponent p) :
    ∃ x : projectiveChartFullIncidenceRing q n z j exponent p,
      projectiveChartFullEvaluation q n z j exponent p x = a ∧
        ∀ y, projectiveChartFullEvaluation q n z j exponent p y = a ↔
          y - x ∈ RingHom.ker
            (projectiveChartFullEvaluation q n z j exponent p).toRingHom := by
  obtain ⟨x, hx⟩ :=
    projectiveChartFullEvaluation_surjective q n z j exponent p a
  refine ⟨x, hx, fun y => ?_⟩
  rw [← hx, projectiveChartFullEvaluation_eq_iff_sub_mem_kernel]

end


end GaloisForLFunctions.HTGeometry
