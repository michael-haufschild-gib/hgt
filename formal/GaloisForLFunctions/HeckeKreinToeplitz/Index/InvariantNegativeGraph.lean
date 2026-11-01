import GaloisForLFunctions.HeckeKreinToeplitz.Index.ContractionGraphImages
import GaloisForLFunctions.HTGeometry.WeakContractionBall
import GaloisForLFunctions.HTGeometry.ConstitutiveInvariantPositivityKMSWall

/-!
# Invariant maximal nonpositive graphs

An isometry acts on the weakly compact convex ball of finite-column
contractions. Its graph relation is closed, hence the action is continuous
by the compact-codomain closed-graph theorem. A fixed point gives an
invariant nonpositive graph whose orthogonal complement is nonnegative.
-/

noncomputable section
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {m : ℕ}

/-- Positive coordinate of a transformed graph vector, in the weak topology. -/
def firstGraphValue (T : (H × EuclideanSpace ℂ (Fin m)) →L[ℂ]
    (H × EuclideanSpace ℂ (Fin m))) (x : EuclideanSpace ℂ (Fin m))
    (z : WeakSpace ℂ (WeakContraction.Columns H m)) : WeakSpace ℂ H :=
  toWeakSpace ℂ H (T (WeakContraction.columnEvaluation x
    ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), x)).1

/-- Negative coordinate of a transformed graph vector. -/
def lastGraphValue (T : (H × EuclideanSpace ℂ (Fin m)) →L[ℂ]
    (H × EuclideanSpace ℂ (Fin m))) (x : EuclideanSpace ℂ (Fin m))
    (z : WeakSpace ℂ (WeakContraction.Columns H m)) : EuclideanSpace ℂ (Fin m) :=
  (T (WeakContraction.columnEvaluation x
    ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), x)).2

theorem continuous_firstGraphValue (T : (H × EuclideanSpace ℂ (Fin m)) →L[ℂ]
    (H × EuclideanSpace ℂ (Fin m))) (x : EuclideanSpace ℂ (Fin m)) :
    Continuous (firstGraphValue T x) := by
  let L : WeakContraction.Columns H m →L[ℂ] H :=
    (ContinuousLinearMap.fst ℂ H (EuclideanSpace ℂ (Fin m))).comp
      (T.comp ((ContinuousLinearMap.inl ℂ H (EuclideanSpace ℂ (Fin m))).comp
        (WeakContraction.columnEvaluation x)))
  have he : firstGraphValue T x = fun z => WeakSpace.map L z +
      toWeakSpace ℂ H (T (0, x)).1 := by
    funext z
    change (T (WeakContraction.columnEvaluation x
      ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), x)).1 =
      (T (WeakContraction.columnEvaluation x
        ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), 0)).1 + (T (0, x)).1
    rw [show (WeakContraction.columnEvaluation x
        ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), x) =
        (WeakContraction.columnEvaluation x
          ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), 0) + (0, x) by simp,
      map_add]
    rfl
  rw [he]
  exact (WeakSpace.map L).continuous.add continuous_const

theorem continuous_lastGraphValue (T : (H × EuclideanSpace ℂ (Fin m)) →L[ℂ]
    (H × EuclideanSpace ℂ (Fin m))) (x : EuclideanSpace ℂ (Fin m)) :
    Continuous (lastGraphValue T x) := by
  let L (i : Fin m) : WeakContraction.Columns H m →L[ℂ] ℂ :=
    (PiLp.proj 2 (fun _ : Fin m => ℂ) i).comp
      ((ContinuousLinearMap.snd ℂ H (EuclideanSpace ℂ (Fin m))).comp
        (T.comp ((ContinuousLinearMap.inl ℂ H (EuclideanSpace ℂ (Fin m))).comp
          (WeakContraction.columnEvaluation x))))
  have he : lastGraphValue T x = fun z => WithLp.toLp 2
      (fun i => L i ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z) + (T (0, x)).2 i) := by
    funext z
    apply PiLp.ext
    intro i
    change (T (WeakContraction.columnEvaluation x
      ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), x)).2 i =
      (T (WeakContraction.columnEvaluation x
        ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), 0)).2 i + (T (0, x)).2 i
    rw [show (WeakContraction.columnEvaluation x
        ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), x) =
        (WeakContraction.columnEvaluation x
          ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z), 0) + (0, x) by simp,
      map_add]
    rfl
  rw [he]
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin m => ℂ)).symm.continuous.comp
    (continuous_pi fun i =>
      (WeakBilin.eval_continuous (topDualPairing ℂ (WeakContraction.Columns H m)).flip (L i)).add
        continuous_const)

/-- Operator represented by a point of the weak contraction ball. -/
def ballOperator (z : WeakContraction.ball (H := H) (m := m)) :
    EuclideanSpace ℂ (Fin m) →ₗ[ℂ] H :=
  WeakContraction.columnOperator ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z.val)

theorem ballOperator_norm_le (z : WeakContraction.ball (H := H) (m := m))
    (x : EuclideanSpace ℂ (Fin m)) : ‖ballOperator z x‖ ≤ ‖x‖ := by
  rw [ballOperator, WeakContraction.columnOperator_apply]
  exact z.property x

theorem ballOperator_injective : Function.Injective (ballOperator (H := H) (m := m)) := by
  intro z w h
  apply Subtype.ext
  apply (toWeakSpace ℂ (WeakContraction.Columns H m)).symm.injective
  have he := congrArg WeakContraction.toColumns h
  simpa only [ballOperator, WeakContraction.toColumns_columnOperator] using he

theorem firstGraphValue_ballOperator
    (T : (H × EuclideanSpace ℂ (Fin m)) →L[ℂ] (H × EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin m)) (z : WeakContraction.ball (H := H) (m := m)) :
    firstGraphValue T x z.val = toWeakSpace ℂ H (T (ballOperator z x, x)).1 := by
  rw [firstGraphValue, ballOperator, WeakContraction.columnOperator_apply]

theorem lastGraphValue_ballOperator
    (T : (H × EuclideanSpace ℂ (Fin m)) ≃L[ℂ] (H × EuclideanSpace ℂ (Fin m)))
    (x : EuclideanSpace ℂ (Fin m)) (z : WeakContraction.ball (H := H) (m := m)) :
    lastGraphValue T.toContinuousLinearMap x z.val = graphNegative T.toLinearEquiv (ballOperator z) x := by
  change (T (WeakContraction.columnEvaluation x
    ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z.val), x)).2 =
      (T (WeakContraction.columnOperator
        ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z.val) x, x)).2
  rw [WeakContraction.columnOperator_apply]

theorem weakEvaluation_ballOperator (x : EuclideanSpace ℂ (Fin m))
    (z : WeakContraction.ball (H := H) (m := m)) :
    WeakSpace.map (WeakContraction.columnEvaluation x) z.val = toWeakSpace ℂ H (ballOperator z x) := by
  change toWeakSpace ℂ H (WeakContraction.columnEvaluation x
    ((toWeakSpace ℂ (WeakContraction.Columns H m)).symm z.val)) = _
  rw [ballOperator, WeakContraction.columnOperator_apply]

variable (T : (H × EuclideanSpace ℂ (Fin m)) ≃L[ℂ]
    (H × EuclideanSpace ℂ (Fin m)))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)

/-- Action of a form-isometry on the contraction ball. -/
def contractionBallAction : WeakContraction.ball (H := H) (m := m) →
    WeakContraction.ball (H := H) (m := m) := fun z =>
  ⟨toWeakSpace ℂ (WeakContraction.Columns H m)
    (WeakContraction.toColumns
      (imageGraph T.toLinearEquiv hT (ballOperator z) (ballOperator_norm_le z))), by
    intro x
    change ‖WeakContraction.columnEvaluation x
      (WeakContraction.toColumns
        (imageGraph T.toLinearEquiv hT (ballOperator z) (ballOperator_norm_le z)))‖ ≤ ‖x‖
    rw [← WeakContraction.columnOperator_apply, WeakContraction.columnOperator_toColumns]
    exact imageGraph_norm_le T.toLinearEquiv hT (ballOperator z) (ballOperator_norm_le z) x⟩

theorem contractionBallAction_operator (z : WeakContraction.ball (H := H) (m := m)) :
    ballOperator (contractionBallAction T hT z) =
      imageGraph T.toLinearEquiv hT (ballOperator z) (ballOperator_norm_le z) :=
  WeakContraction.columnOperator_toColumns _

theorem contractionBallAction_relation (z : WeakContraction.ball (H := H) (m := m))
    (x : EuclideanSpace ℂ (Fin m)) :
    T (ballOperator z x, x) =
      (ballOperator (contractionBallAction T hT z) (graphNegative T.toLinearEquiv (ballOperator z) x),
        graphNegative T.toLinearEquiv (ballOperator z) x) := by
  rw [contractionBallAction_operator]
  exact imageGraph_relation T.toLinearEquiv hT (ballOperator z) (ballOperator_norm_le z) x

/-- Equality of transformed graphs determines the action on the contraction ball. -/
theorem eq_contractionBallAction_of_relation
    (z w : WeakContraction.ball (H := H) (m := m))
    (h : ∀ x, T (ballOperator z x, x) =
      (ballOperator w (graphNegative T.toLinearEquiv (ballOperator z) x),
        graphNegative T.toLinearEquiv (ballOperator z) x)) :
    w = contractionBallAction T hT z := by
  apply ballOperator_injective
  rw [contractionBallAction_operator]
  exact eq_imageGraph_of_relation T.toLinearEquiv hT (ballOperator z) (ballOperator_norm_le z)
    (ballOperator w) h

/-- The weak evaluation equations are exactly the transformed-graph relation. -/
theorem eq_contractionBallAction_of_weak_evaluations
    (z w : WeakContraction.ball (H := H) (m := m))
    (h : ∀ x, firstGraphValue T.toContinuousLinearMap x z.val =
      WeakSpace.map (WeakContraction.columnEvaluation
        (lastGraphValue T.toContinuousLinearMap x z.val)) w.val) :
    w = contractionBallAction T hT z := by
  apply eq_contractionBallAction_of_relation T hT z w
  intro x
  apply Prod.ext
  · change (T (ballOperator z x, x)).1 =
      ballOperator w (graphNegative T.toLinearEquiv (ballOperator z) x)
    have hx := h x
    rw [firstGraphValue_ballOperator, lastGraphValue_ballOperator, weakEvaluation_ballOperator] at hx
    exact (toWeakSpace ℂ H).injective hx
  · rfl

/-- Fixed weak evaluation equations characterize the graph action. -/
theorem eq_contractionBallAction_iff_weak_evaluations
    (z w : WeakContraction.ball (H := H) (m := m)) :
    w = contractionBallAction T hT z ↔
      ∀ x, firstGraphValue T.toContinuousLinearMap x z.val =
        WeakSpace.map (WeakContraction.columnEvaluation
          (lastGraphValue T.toContinuousLinearMap x z.val)) w.val := by
  constructor
  · intro hw x
    rw [hw, firstGraphValue_ballOperator, lastGraphValue_ballOperator,
      weakEvaluation_ballOperator]
    exact congrArg (toWeakSpace ℂ H) (congrArg Prod.fst (contractionBallAction_relation T hT z x))
  · exact eq_contractionBallAction_of_weak_evaluations T hT z w

private theorem continuous_weak_evaluation_comp {X : Type*} [TopologicalSpace X]
    (f : X → WeakSpace ℂ (WeakContraction.Columns H m))
    (g : X → EuclideanSpace ℂ (Fin m)) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => WeakSpace.map (WeakContraction.columnEvaluation (g x)) (f x)) := by
  exact (WeakContraction.continuous_evaluation (H := H) (m := m)).comp (hf.prodMk hg)

/-- A graph equation in the ambient product of weak column spaces. -/
def graphEquationSet (x : EuclideanSpace ℂ (Fin m)) :
    Set (WeakSpace ℂ (WeakContraction.Columns H m) × WeakSpace ℂ (WeakContraction.Columns H m)) :=
  {p | firstGraphValue T.toContinuousLinearMap x p.1 =
    WeakSpace.map (WeakContraction.columnEvaluation
      (lastGraphValue T.toContinuousLinearMap x p.1)) p.2}

theorem isClosed_graphEquationSet (x : EuclideanSpace ℂ (Fin m)) :
    IsClosed (graphEquationSet T x) := by
  apply isClosed_eq
  · exact (continuous_firstGraphValue T.toContinuousLinearMap x).comp continuous_fst
  · exact continuous_weak_evaluation_comp (H := H) (m := m)
      Prod.snd (fun p => lastGraphValue T.toContinuousLinearMap x p.1)
      continuous_snd ((continuous_lastGraphValue T.toContinuousLinearMap x).comp continuous_fst)

/-- The transformed-graph equation cuts out a closed graph in the product of contraction balls. -/
theorem isClosed_graph_contractionBallAction : IsClosed
    {p : WeakContraction.ball (H := H) (m := m) × WeakContraction.ball (H := H) (m := m) |
      p.2 = contractionBallAction T hT p.1} := by
  let inclusion : WeakContraction.ball (H := H) (m := m) × WeakContraction.ball (H := H) (m := m) →
      WeakSpace ℂ (WeakContraction.Columns H m) × WeakSpace ℂ (WeakContraction.Columns H m) :=
    fun p => (p.1.val, p.2.val)
  have hc : Continuous inclusion := continuous_subtype_val.prodMap continuous_subtype_val
  have he : {p : WeakContraction.ball (H := H) (m := m) ×
        WeakContraction.ball (H := H) (m := m) | p.2 = contractionBallAction T hT p.1} =
      ⋂ x : EuclideanSpace ℂ (Fin m), inclusion ⁻¹' graphEquationSet T x := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact eq_contractionBallAction_iff_weak_evaluations T hT p.1 p.2
  rw [he]
  exact isClosed_iInter fun x => (isClosed_graphEquationSet T x).preimage hc

variable [CompleteSpace H]

/-- Compactness turns the closed transformed-graph relation into continuity. -/
theorem continuous_contractionBallAction : Continuous (contractionBallAction T hT) := by
  letI : CompactSpace (WeakContraction.ball (H := H) (m := m)) :=
    isCompact_iff_compactSpace.mp (WeakContraction.isCompact_ball (H := H) (m := m))
  exact GaloisForLFunctions.HTGeometry.continuous_of_isClosed_graph
    (isClosed_graph_contractionBallAction T hT)

include hT in
/-- Every isometry with a finite negative factor has an invariant maximal nonpositive graph. -/
theorem exists_invariant_contraction_graph :
    ∃ A : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] H, (∀ x, ‖A x‖ ≤ ‖x‖) ∧
      ∃ D : EuclideanSpace ℂ (Fin m) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin m),
        ∀ x, T (A x, x) = (A (D x), D x) := by
  obtain ⟨z, hz⟩ := exists_fixedPoint_weakHilbert_convex
    (WeakContraction.isCompact_ball (H := H) (m := m)) WeakContraction.nonempty_ball
    WeakContraction.convex_ball (contractionBallAction T hT) (continuous_contractionBallAction T hT)
  refine ⟨ballOperator z, ballOperator_norm_le z,
    graphNegativeEquiv T.toLinearEquiv hT (ballOperator z) (ballOperator_norm_le z), ?_⟩
  intro x
  change T (ballOperator z x, x) =
    (ballOperator z (graphNegative T.toLinearEquiv (ballOperator z) x),
      graphNegative T.toLinearEquiv (ballOperator z) x)
  simpa only [hz] using contractionBallAction_relation T hT z x

#print axioms exists_invariant_contraction_graph

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
