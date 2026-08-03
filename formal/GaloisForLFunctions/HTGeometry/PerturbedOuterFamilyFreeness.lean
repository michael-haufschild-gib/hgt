import GaloisForLFunctions.HTGeometry.PerturbedOuterFamilyJets
import GaloisForLFunctions.HTGeometry.ComplexExponentialSeriesCarrier

/-!
# Full translation freeness of the perturbed outer background

For a residual set of bounded exponential mass parameters, the real translates of the outer
background corrected by a fixed multiple of a fixed smooth function satisfy no nonzero differential
relation at all on the upper half plane.

The proof is the transversality argument assembled from its three parts: a relation of a given jet
depth carries a shape, its coefficient vector is annihilated by the shape's evaluation matrix at any
packet of nodes, and at a residual set of mass parameters that matrix is invertible at a packet of
admissible nodes.  Nodes at pairwise distinct heights stay distinct under real translation, so the
same packet serves all the members of the family at once.  The jet depths are countable, so the
residual sets intersect to a residual set.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **No relation of a fixed jet depth survives at a residual set of mass parameters.** -/
theorem residual_relation_eq_zero_perturbedOuterFamily (m' n : ℕ) {t : Fin (m' + 1) → ℝ}
    (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ) {A : ℂ → ℂ}
    (hA : ∀ ζ : ℂ, 0 < ζ.im → ContDiffAt ℂ (⊤ : ℕ∞) A ζ) :
    {u : MassParameter | ∀ P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ,
        (∀ z ∈ {ζ : ℂ | 0 < ζ.im}, MvPolynomial.eval
          (familyJetVec (n := n) (perturbedOuterFamily x ε u c A t) z) P = 0) → P = 0}
      ∈ residual MassParameter := by
  classical
  choose nodeOf hupper hsep hD using fun S : FamilyShape m' n =>
    exists_distinctIm_nodes_shapeDeterminant_ne_zero S.1.1.spectralDegree S.1.1.jetDepth
      S.1.1.exponent S.1.2
  set carrier : ∀ S : FamilyShape m' n, ShapeJetIndex S.1.1 → ℂ := fun S =>
    outerCarrierJets (m' + 1) n (S.1.1.depthPred + 1) (familyShape_mul m' n S) (nodeOf S) t c A
    with hcarrier
  refine Filter.mem_of_superset
    (residual_familyOuterJet_rigidity t hx hεpos hε carrier nodeOf
      (fun S => injective_combinedNodes (hsep S) ht) hupper hD) ?_
  intro u hu P hrel
  set S : FamilyShape m' n := ⟨⟨relationShapeOf P, injective_relationShapeOf_exponent P⟩, rfl⟩
    with hSdef
  refine eq_zero_of_relation_of_rigid_jets (U := {ζ : ℂ | 0 < ζ.im}) P hrel (nodeOf S)
    (fun b => hupper S b)
    (familyOuterObservation (m' + 1) n ((relationShapeOf P).depthPred + 1)
      (familyShape_mul m' n S) (nodeOf S) t x ε u + carrier S) (fun p => ?_) (fun cv hcv => ?_)
  · exact familyOuterObservation_add_carrier_apply (m' + 1) n ((relationShapeOf P).depthPred + 1)
      (familyShape_mul m' n S) (nodeOf S) t (hupper S) x hεpos hε u c hA p.1 p.2
  · exact hu S cv hcv

/-- **The perturbed outer background is fully translation free at a residual set of mass
parameters.**  No nonzero differential relation of any order holds among finitely many distinct real
translates of it. -/
theorem residual_not_familyDifferentiallyAlgebraicOn_perturbedOuterFamily (m' : ℕ)
    {t : Fin (m' + 1) → ℝ} (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x)
    {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ) {A : ℂ → ℂ}
    (hA : ∀ ζ : ℂ, 0 < ζ.im → ContDiffAt ℂ (⊤ : ℕ∞) A ζ) :
    {u : MassParameter | ¬ FamilyDifferentiallyAlgebraicOn
        (perturbedOuterFamily x ε u c A t) {ζ : ℂ | 0 < ζ.im}} ∈ residual MassParameter := by
  refine Filter.mem_of_superset (residual_iInter fun n : ℕ =>
    residual_relation_eq_zero_perturbedOuterFamily m' n ht hx hεpos hε c hA) ?_
  intro u hu
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hu
  rintro ⟨n, P, hPne, hrel⟩
  exact hPne (hu n P hrel)

/-- **The fully free mass parameters are dense.** -/
theorem dense_not_familyDifferentiallyAlgebraicOn_perturbedOuterFamily (m' : ℕ)
    {t : Fin (m' + 1) → ℝ} (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x)
    {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ) {A : ℂ → ℂ}
    (hA : ∀ ζ : ℂ, 0 < ζ.im → ContDiffAt ℂ (⊤ : ℕ∞) A ζ) :
    Dense {u : MassParameter | ¬ FamilyDifferentiallyAlgebraicOn
        (perturbedOuterFamily x ε u c A t) {ζ : ℂ | 0 < ζ.im}} :=
  dense_of_mem_residual (residual_not_familyDifferentiallyAlgebraicOn_perturbedOuterFamily m' ht hx
    hεpos hε c hA)

/-! ## The exponential carrier as the fixed correction -/

/-- The entire carrier of an exponential series is smooth. -/
theorem contDiffAt_cexpSeriesCarrier {ι : Type*} {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) (z : ℂ) :
    ContDiffAt ℂ (⊤ : ℕ∞) (cexpSeriesCarrier a omega) z :=
  ((differentiable_cexpSeriesCarrier h).differentiableOn.analyticOnNhd isOpen_univ z
    (Set.mem_univ z)).contDiffAt

/-- **The outer background perturbed by an exponential carrier is fully translation free at a
residual set of mass parameters.**  The carrier is entire, hence smooth on the upper half plane, so
it is an admissible fixed correction. -/
theorem residual_not_familyDifferentiallyAlgebraicOn_perturbedOuterOrbit {ι : Type*} (m' : ℕ)
    {t : Fin (m' + 1) → ℝ} (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x)
    {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ) {a : ι → ℂ} {omega : ι → ℝ}
    (hcar : ExpSeriesNormallySummable a omega) :
    {u : MassParameter | ¬ FamilyDifferentiallyAlgebraicOn
        (perturbedOuterFamily x ε u c (cexpSeriesCarrier a omega) t) {ζ : ℂ | 0 < ζ.im}}
      ∈ residual MassParameter :=
  residual_not_familyDifferentiallyAlgebraicOn_perturbedOuterFamily m' ht hx hεpos hε c
    fun ζ _ => contDiffAt_cexpSeriesCarrier hcar ζ

/-- **The fully free mass parameters of the exponentially perturbed outer background are dense.** -/
theorem dense_not_familyDifferentiallyAlgebraicOn_perturbedOuterOrbit {ι : Type*} (m' : ℕ)
    {t : Fin (m' + 1) → ℝ} (ht : Function.Injective t) {x : ℕ → ℝ} (hx : Function.Injective x)
    {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ) {a : ι → ℂ} {omega : ι → ℝ}
    (hcar : ExpSeriesNormallySummable a omega) :
    Dense {u : MassParameter | ¬ FamilyDifferentiallyAlgebraicOn
        (perturbedOuterFamily x ε u c (cexpSeriesCarrier a omega) t) {ζ : ℂ | 0 < ζ.im}} :=
  dense_of_mem_residual
    (residual_not_familyDifferentiallyAlgebraicOn_perturbedOuterOrbit m' ht hx hεpos hε c hcar)

end

end GaloisForLFunctions.HTGeometry
