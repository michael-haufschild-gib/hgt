import GaloisForLFunctions.HTGeometry.OuterJetSigmaChart
import GaloisForLFunctions.HTGeometry.ResidualShapeCoefficientRigidity
import GaloisForLFunctions.HTGeometry.JetPacketReindex
import GaloisForLFunctions.HTGeometry.DiscreteJetPacketContinuity

/-!
# The outer jet observation attached to a relation shape

A relation shape prescribes how many nodes to use, how deep to differentiate, and which expanded
monomials occur.  Its jet variables are indexed by (node, order) pairs with a constant order range,
which is the product form of the sigma-indexed packets the Cauchy machinery produces.

Transporting the outer jet observation through that identification gives, for each shape, an
observation of the mass parameter in exactly the coordinates the shape's evaluation matrix reads.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A packet with constant order range is a product packet. -/
def constOrderPacketHomeomorph (row : Type*) (d : ℕ) :
    ((Σ _ : row, Fin d) → ℂ) ≃ₜ ((row × Fin d) → ℂ) where
  toFun y := fun p => y ⟨p.1, p.2⟩
  invFun w := fun t => w (t.1, t.2)
  left_inv := by
    intro y
    funext t
    cases t
    rfl
  right_inv := by
    intro w
    funext p
    cases p
    rfl
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

/-- The outer jet observation attached to a shape: the Cayley outer jets of the discrete Cauchy
transform, at the shape's nodes and to the shape's depth. -/
def shapeOuterObservation (S : RelationShape)
    (nodes : Fin S.monomialCount × Fin (S.spectralDegree + 1) → ℂ) (x ε : ℕ → ℝ)
    (u : MassParameter) : ShapeJetIndex S → ℂ :=
  constOrderPacketHomeomorph _ S.jetDepth
    (outerJetSigma (fun _ => S.depthPred)
      (discreteJetPacket nodes (fun _ => S.depthPred + 1) x fun n => ε n * Real.exp (u n)))

/-- **The shape observation is locally surjective.** -/
theorem locallySurjective_shapeOuterObservation (S : RelationShape)
    {nodes : Fin S.monomialCount × Fin (S.spectralDegree + 1) → ℂ}
    (hnodesinj : Function.Injective nodes) (hupper : ∀ r, 0 < (nodes r).im)
    {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε) :
    LocallySurjectiveObservation (shapeOuterObservation S nodes x ε) :=
  (locallySurjective_outerJetObservation nodes hnodesinj hupper (fun _ => S.depthPred) x hx
    hεpos hε).congr_homeomorph (constOrderPacketHomeomorph _ S.jetDepth)

/-- **The shape observation is continuous.** -/
theorem continuous_shapeOuterObservation (S : RelationShape)
    {nodes : Fin S.monomialCount × Fin (S.spectralDegree + 1) → ℂ}
    (hupper : ∀ r, 0 < (nodes r).im) (x : ℕ → ℝ) {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Summable ε) :
    Continuous (shapeOuterObservation S nodes x ε) := by
  have hbase : Continuous fun u : MassParameter =>
      discreteJetPacket nodes (fun _ => S.depthPred + 1) x fun n => ε n * Real.exp (u n) :=
    continuous_discreteJetPacket_expParameter nodes hupper _ x hεpos hε
  have hmaps : ∀ u : MassParameter,
      (discreteJetPacket nodes (fun _ => S.depthPred + 1) x fun n => ε n * Real.exp (u n))
        ∈ {y : (Σ _ : Fin S.monomialCount × Fin (S.spectralDegree + 1), Fin (S.depthPred + 1)) → ℂ |
          ∀ i, y ⟨i, 0⟩ + Complex.I ≠ 0} := fun u =>
    discreteJetPacket_mem_chartDomain nodes hupper (fun _ => S.depthPred) x hεpos hε u
  have hcomp : Continuous fun u : MassParameter =>
      outerJetSigma (fun _ => S.depthPred)
        (discreteJetPacket nodes (fun _ => S.depthPred + 1) x fun n => ε n * Real.exp (u n)) :=
    (continuousOn_outerJetSigma _).comp_continuous hbase hmaps
  exact (constOrderPacketHomeomorph _ S.jetDepth).continuous.comp hcomp

/-! ## The residual set of rigid mass parameters -/

/-- Shapes whose expanded monomials are pairwise distinct. -/
abbrev ReducedShape : Type := {S : RelationShape // Function.Injective S.exponent}

/-- **Residual rigidity of the outer jets.**  For a positive summable weight family and an injective
atom family there is a choice of admissible node packets, all above the real axis, and a residual set
of bounded exponential mass parameters at which no relation of any reduced shape survives. -/
theorem residual_outerJet_shape_rigidity {x : ℕ → ℝ} (hx : Function.Injective x)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Summable ε) :
    ∃ nodeOf : ∀ S : ReducedShape,
        Fin S.1.monomialCount × Fin (S.1.spectralDegree + 1) → ℂ,
      (∀ S, Function.Injective (nodeOf S)) ∧ (∀ S r, 0 < (nodeOf S r).im) ∧
      {u : MassParameter | ∀ (S : ReducedShape)
          (c : Fin S.1.monomialCount × Fin (S.1.spectralDegree + 1) → ℂ),
          (expandedDifferentialEvaluationMatrix S.1.spectralDegree S.1.jetDepth (nodeOf S)
            S.1.exponent (shapeOuterObservation S.1 (nodeOf S) x ε u)).mulVec c = 0 → c = 0}
        ∈ residual MassParameter := by
  classical
  choose nodeOf hinj hupper hne using fun S : ReducedShape =>
    exists_upper_injective_nodes_shapeDeterminant_ne_zero S.1.spectralDegree S.1.jetDepth
      S.1.exponent S.2
  refine ⟨nodeOf, hinj, hupper, ?_⟩
  exact residual_forall_shape_coeff_eq_zero (Sh := ReducedShape) (sh := fun S => S.1)
    (nodeOf := nodeOf) (jetOf := fun S => shapeOuterObservation S.1 (nodeOf S) x ε)
    (fun S => continuous_shapeOuterObservation S.1 (hupper S) x hεpos hε)
    (fun S => locallySurjective_shapeOuterObservation S.1 (hinj S) (hupper S) hx hεpos hε) hne

/-! ## The fixed carrier is invisible -/

/-- **Residual rigidity survives a fixed additive perturbation.**  Adding a fixed jet vector -- the
jets of the fixed exponential carrier at the same nodes -- only translates the observed packet, so
neither continuity nor local surjectivity is affected and the same residual set works. -/
theorem residual_perturbedOuterJet_shape_rigidity {x : ℕ → ℝ} (hx : Function.Injective x)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Summable ε)
    (carrier : ∀ S : ReducedShape, ShapeJetIndex S.1 → ℂ) :
    ∃ nodeOf : ∀ S : ReducedShape,
        Fin S.1.monomialCount × Fin (S.1.spectralDegree + 1) → ℂ,
      (∀ S, Function.Injective (nodeOf S)) ∧ (∀ S r, 0 < (nodeOf S r).im) ∧
      {u : MassParameter | ∀ (S : ReducedShape)
          (c : Fin S.1.monomialCount × Fin (S.1.spectralDegree + 1) → ℂ),
          (expandedDifferentialEvaluationMatrix S.1.spectralDegree S.1.jetDepth (nodeOf S)
            S.1.exponent
            (shapeOuterObservation S.1 (nodeOf S) x ε u + carrier S)).mulVec c = 0 → c = 0}
        ∈ residual MassParameter := by
  classical
  choose nodeOf hinj hupper hne using fun S : ReducedShape =>
    exists_upper_injective_nodes_shapeDeterminant_ne_zero S.1.spectralDegree S.1.jetDepth
      S.1.exponent S.2
  refine ⟨nodeOf, hinj, hupper, ?_⟩
  exact residual_forall_shape_coeff_eq_zero (Sh := ReducedShape) (sh := fun S => S.1)
    (nodeOf := nodeOf)
    (jetOf := fun S => fun u => shapeOuterObservation S.1 (nodeOf S) x ε u + carrier S)
    (fun S => (continuous_shapeOuterObservation S.1 (hupper S) x hεpos hε).add continuous_const)
    (fun S => (locallySurjective_shapeOuterObservation S.1 (hinj S) (hupper S) hx hεpos
      hε).add_const (carrier S)) hne

end

end GaloisForLFunctions.HTGeometry
