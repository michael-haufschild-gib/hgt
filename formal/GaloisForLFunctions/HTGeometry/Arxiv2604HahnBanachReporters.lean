import GaloisForLFunctions.HTGeometry.SeparableBuresCompactTargetBody
import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw
import GaloisForLFunctions.HTGeometry.LorentzConeAdmissibility
import GaloisForLFunctions.HTGeometry.ConstitutiveAsymptoticLawCore
import GaloisForLFunctions.HTGeometry.ObserverFieldEquation
import GaloisForLFunctions.HTGeometry.NestedConvexCapacity
import GaloisForLFunctions.HTGeometry.FiniteBuresComparisonLaw
import GaloisForLFunctions.HTGeometry.ConfocalEnvelopeHull
import GaloisForLFunctions.HTGeometry.ContextOrderPSDHierarchy
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Hahn--Banach reporters for corpus state bodies

Applications of Feinberg--Lavine, arXiv:2604.22717, Theorem 2.1: a state outside a closed convex
admissible body has a continuous real reporter separated from every admissible state by a strict
gap.  The first two results expose reusable reporters for the corpus's infinite Schatten-one and
finite matrix covariance bodies.  The final result is a closed, premise-free Lorentz-cone instance.
-/

noncomputable section

namespace RHTower

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every Schatten-one state excluded from a target covariance body has a strict continuous
reporter certificate. -/
theorem separableBuresTargetBody_strictReporter {V : Set H} {Q : SchattenOneOperator H}
    (hQ : Q ∉ separableBuresCompactTargetBody V) :
    ∃ (reporter : StrongDual ℝ (SchattenOneOperator H)) (threshold : ℝ),
      (∀ M ∈ separableBuresCompactTargetBody V, reporter M < threshold) ∧
        threshold < reporter Q :=
  geometric_hahn_banach_closed_point
    (separableBuresCompactTargetBody_convex V)
    (separableBuresCompactTargetBody_isClosed V) hQ

end RHTower

namespace GaloisForLFunctions.HTGeometry

open Matrix Set
open scoped ComplexOrder MatrixOrder

/-- The Lorentz admissibility set as a pointed cone. -/
def closedLorentzPointedCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PointedCone ℝ (ℝ × E) where
  carrier := closedLorentzAdmissibility
  zero_mem' := by simp [closedLorentzAdmissibility]
  add_mem' := by
    rintro ⟨a, u⟩ ⟨b, v⟩ hu hv
    change ‖u + v‖ ≤ a + b
    exact (norm_add_le u v).trans (add_le_add hu hv)
  smul_mem' := by
    rintro ⟨c, hc⟩ ⟨a, u⟩ hu
    change ‖c • u‖ ≤ c * a
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hu hc

/-- Closed Lorentz admissibility as a proper cone, enabling zero-threshold separation. -/
def closedLorentzProperCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ProperCone ℝ (ℝ × E) :=
  ⟨closedLorentzPointedCone, isClosed_closedLorentzAdmissibility⟩

/-- Positive semidefinite complex matrices as a pointed real cone. -/
def matrixPosSemidefPointedCone (n : ℕ) :
    PointedCone ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {M | M.PosSemidef}
  zero_mem' := Matrix.PosSemidef.zero
  add_mem' := Matrix.PosSemidef.add
  smul_mem' := by
    intro c M hM
    exact hM.smul c.property

/-- Positive semidefinite matrices as a proper real cone. -/
def matrixPosSemidefProperCone (n : ℕ) :
    ProperCone ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨matrixPosSemidefPointedCone n, isClosed_finitePosSemidefMatrices⟩

/-- **Zero-threshold matrix-cone reporter.**  Every matrix outside the positive cone has a
continuous linear witness that is nonpositive on all positive matrices and positive at the failed
matrix. -/
theorem matrixPosSemidef_coneReporter {n : ℕ}
    {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : ¬ Q.PosSemidef) :
    ∃ reporter : StrongDual ℝ (Matrix (Fin n) (Fin n) ℂ),
      (∀ M : Matrix (Fin n) (Fin n) ℂ, M.PosSemidef → reporter M ≤ 0) ∧
        0 < reporter Q := by
  letI : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℂ))
  obtain ⟨f, hf, hq⟩ := (matrixPosSemidefProperCone n).hyperplane_separation_point hQ
  refine ⟨-f, ?_, ?_⟩
  · intro M hM
    simpa using neg_nonpos.mpr (hf M hM)
  · simpa using neg_pos.mpr hq

/-- Closed application: at every order, the corpus's globally indefinite context kernel is
detected by a continuous reporter that remains nonpositive on the entire matrix positive cone. -/
theorem balancedContext_coneReporter (r : ℕ) :
    ∃ reporter : StrongDual ℝ (Matrix (Fin (r + 3)) (Fin (r + 3)) ℂ),
      (∀ M, M.PosSemidef → reporter M ≤ 0) ∧
        0 < reporter (contextOrderKernel (balancedContextScale r)) :=
  matrixPosSemidef_coneReporter (balancedContext_global_not_posSemidef r)

/-- Every finite density matrix excluded from an occupied covariance body has a strict continuous
reporter certificate. -/
theorem finiteBuresOccupiedTargetBody_strictReporter {n : ℕ} {V : Set (Fin n → ℂ)}
    {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : Q ∉ finiteBuresOccupiedTargetBody V) :
    ∃ (reporter : StrongDual ℝ (Matrix (Fin n) (Fin n) ℂ)) (threshold : ℝ),
      (∀ M ∈ finiteBuresOccupiedTargetBody V, reporter M < threshold) ∧
        threshold < reporter Q := by
  letI : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℂ))
  exact geometric_hahn_banach_closed_point
    (finiteBuresOccupiedTargetBody_convex V)
    (finiteBuresOccupiedTargetBody_isClosed V) hQ

/-- A point outside the closed convex tail-law core has a strict continuous asymptotic reporter. -/
theorem asymptoticLawCore_strictReporter
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [LocallyConvexSpace ℝ E]
    {x : ℕ → E} {q : E} (hq : q ∉ asymptoticLawCore x) :
    ∃ (reporter : StrongDual ℝ E) (threshold : ℝ),
      (∀ state ∈ asymptoticLawCore x, reporter state < threshold) ∧
        threshold < reporter q :=
  geometric_hahn_banach_closed_point
    (asymptoticLawCore_convex x) (asymptoticLawCore_isClosed x) hq

/-- Every point excluded by a finite affine observer context has a strict continuous reporter. -/
theorem observerContext_strictReporter
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (Hol : ℕ → (F ≃ₗᵢ[ℝ] F)) (c : ℕ → F) (n : ℕ) {q : F}
    (hq : q ∉ observerContext Hol c n) :
    ∃ (reporter : StrongDual ℝ F) (threshold : ℝ),
      (∀ state ∈ observerContext Hol c n, reporter state < threshold) ∧
        threshold < reporter q :=
  geometric_hahn_banach_closed_point
    (observerContext_convex Hol c n) (observerContext_isClosed Hol c n) hq

/-- Every `ℓ²` point violating a finite harmonic constraint has a strict continuous reporter. -/
theorem harmonicConstraint_strictReporter (n : ℕ)
    {q : lp (fun _ : ℕ => ℝ) 2} (hq : q ∉ harmonicConstraint n) :
    ∃ (reporter : StrongDual ℝ (lp (fun _ : ℕ => ℝ) 2)) (threshold : ℝ),
      (∀ state ∈ harmonicConstraint n, reporter state < threshold) ∧
        threshold < reporter q :=
  geometric_hahn_banach_closed_point
    (harmonicConstraint_convex n) (harmonicConstraint_isClosed n) hq

/-- Closed application: the zero `ℓ²` sequence is strictly separated from the first nonzero
harmonic constraint. -/
theorem zero_strictReporter_from_harmonicConstraint_zero :
    ∃ (reporter : StrongDual ℝ (lp (fun _ : ℕ => ℝ) 2)) (threshold : ℝ),
      (∀ state ∈ harmonicConstraint 0, reporter state < threshold) ∧
        threshold < reporter 0 := by
  apply harmonicConstraint_strictReporter 0
  intro hzero
  have hcoordinate := hzero 0 le_rfl
  simp [harmonicProfile] at hcoordinate

/-- The unit-trace affine slice strictly separates every matrix outside it. -/
theorem finiteBuresTraceOne_strictReporter {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∉ {M : Matrix (Fin n) (Fin n) ℂ | M.trace.re = 1}) :
    ∃ (reporter : StrongDual ℝ (Matrix (Fin n) (Fin n) ℂ)) (threshold : ℝ),
      (∀ M : Matrix (Fin n) (Fin n) ℂ, M.trace.re = 1 → reporter M < threshold) ∧
        threshold < reporter Q := by
  letI : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℂ))
  exact geometric_hahn_banach_closed_point convex_finiteBuresTraceReal_eq_one
    isClosed_finiteBuresTraceReal_eq_one hQ

/-- A fixed matrix's closed convex left annihilator strictly separates every matrix outside it. -/
theorem finiteMatrixLeftAnnihilator_strictReporter {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℂ) {Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : C * Q ≠ 0) :
    ∃ (reporter : StrongDual ℝ (Matrix (Fin n) (Fin n) ℂ)) (threshold : ℝ),
      (∀ M : Matrix (Fin n) (Fin n) ℂ, C * M = 0 → reporter M < threshold) ∧
        threshold < reporter Q := by
  letI : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℂ))
  exact geometric_hahn_banach_closed_point (convex_finiteMatrix_leftAnnihilator C)
    (isClosed_finiteMatrix_leftAnnihilator C) hQ

/-- **Zero-threshold Lorentz-cone reporter.**  This is Feinberg--Lavine Corollary 2.1 on the
corpus's closed relativistic admissibility cone. -/
theorem closedLorentzAdmissibility_coneReporter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : ℝ × E}
    (hq : q ∉ closedLorentzAdmissibility) :
    ∃ reporter : StrongDual ℝ (ℝ × E),
      (∀ state ∈ closedLorentzAdmissibility, reporter state ≤ 0) ∧
        0 < reporter q := by
  obtain ⟨f, hf, hqf⟩ :=
    (closedLorentzProperCone (E := E)).hyperplane_separation_point hq
  refine ⟨-f, ?_, ?_⟩
  · intro state hstate
    simpa using neg_nonpos.mpr (hf state hstate)
  · simpa using neg_pos.mpr hqf

/-- Closed application of zero-threshold cone separation to negative energy and zero momentum. -/
theorem negativeEnergy_coneReporter :
    ∃ reporter : StrongDual ℝ (ℝ × ℝ),
      (∀ state ∈ closedLorentzAdmissibility (E := ℝ), reporter state ≤ 0) ∧
        0 < reporter (-1, 0) := by
  apply closedLorentzAdmissibility_coneReporter
  simp [closedLorentzAdmissibility]

/-- Closed application: negative energy with zero momentum is strictly separated from every state
in the one-dimensional closed Lorentz cone. -/
theorem negativeEnergy_strictReporter :
    ∃ (reporter : StrongDual ℝ (ℝ × ℝ)) (threshold : ℝ),
      (∀ state ∈ closedLorentzAdmissibility (E := ℝ), reporter state < threshold) ∧
        threshold < reporter (-1, 0) := by
  apply geometric_hahn_banach_closed_point
    (convex_closedLorentzAdmissibility (E := ℝ))
    (isClosed_closedLorentzAdmissibility (E := ℝ))
  simp [closedLorentzAdmissibility]

end GaloisForLFunctions.HTGeometry

namespace HTGeometry

open Set

/-- Every point outside a canonical confocal hull has a strict continuous reporter. -/
theorem confocalHullOfField_strictReporter (D : Set ℝ) (G : ℝ → ℝ) {q : ℝ × ℝ}
    (hq : q ∉ confocalHullOfField D G) :
    ∃ (reporter : StrongDual ℝ (ℝ × ℝ)) (threshold : ℝ),
      (∀ state ∈ confocalHullOfField D G, reporter state < threshold) ∧
        threshold < reporter q :=
  geometric_hahn_banach_closed_point
    (convex_confocalHullOfField D G) (isClosed_confocalHullOfField D G) hq

end HTGeometry
