import GaloisForLFunctions.HTGeometry.ShiftUniformDescentData
import GaloisForLFunctions.HTGeometry.ComplexExponentialSeriesCarrier

/-!
# Shift-uniform freeness of the perturbed outer background

For each relation shape the transversality argument supplies a residual set of mass parameters at
which the shape's evaluation matrix has full column rank at every tuple of distinct real shifts.
The shapes are countable, so the residual sets intersect.

At a parameter of the intersection every differential relation among the translates of the perturbed
outer background is zero -- for every tuple of distinct shifts at once.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Enough evaluation rows for the codimension count: more rows than columns, and a surplus
exceeding the number of shift parameters. -/
def descentRowCount {m' n : ℕ} (S : FamilyShape m' n) : ℕ :=
  Fintype.card (Fin S.1.1.monomialCount × Fin (S.1.1.spectralDegree + 1))
    + S.1.1.spectralDegree + (m' + 1) + 1

theorem descentRowCount_rows {m' n : ℕ} (S : FamilyShape m' n) :
    Fintype.card (Fin S.1.1.monomialCount × Fin (S.1.1.spectralDegree + 1))
        + S.1.1.spectralDegree < Fintype.card (Fin (descentRowCount S)) := by
  rw [Fintype.card_fin, descentRowCount]
  omega

theorem descentRowCount_dim {m' n : ℕ} (S : FamilyShape m' n) :
    m' + 1 < 2 * (Fintype.card (Fin (descentRowCount S))
      - Fintype.card (Fin S.1.1.monomialCount × Fin (S.1.1.spectralDegree + 1))
      - S.1.1.spectralDegree + 1) := by
  rw [Fintype.card_fin, descentRowCount]
  omega

/-- The mass parameters at which the shape's evaluation matrix stays at full column rank for every
tuple of distinct real shifts. -/
def descentGood {m' : ℕ} (x ε : ℕ → ℝ) (c : ℂ) (A : ℂ → ℂ) {n : ℕ} (S : FamilyShape m' n) :
    Set MassParameter :=
  {u : MassParameter | ∀ τ : RealShiftConfiguration (m' + 1),
    massShiftObservation (gridNodes (descentRowCount S)) n x ε
        (sigmaCarrierJets (m' + 1) n (S.1.1.depthPred + 1) (familyShape_mul m' n S)
          (gridNodes (descentRowCount S)) c A) (u, τ.1)
      ∉ outerShiftBad (Fin (descentRowCount S)) (m' + 1) n (S.1.1.depthPred + 1)
          S.1.1.spectralDegree (familyShape_mul m' n S) (gridNodes (descentRowCount S))
          S.1.1.exponent}

theorem residual_descentGood {m' : ℕ} {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ) {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) {n : ℕ} (S : FamilyShape m' n) :
    descentGood x ε c A S ∈ residual MassParameter :=
  residual_globalAvoidance_massShift (gridNodes_injective _) (gridNodes_upper _)
    (gridNodes_sep _) (familyShape_mul m' n S) S.1.2 (descentRowCount_rows S)
    (descentRowCount_dim S) hx hεpos hε
    (contDiff_sigmaCarrierJets (m' + 1) n (S.1.1.depthPred + 1) (familyShape_mul m' n S)
      (gridNodes_upper _) c hA)

/-- **A relation dies at every good parameter, for every tuple of distinct shifts.** -/
theorem eq_zero_of_relation_of_descentGood {m' n : ℕ} {x : ℕ → ℝ} {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) {c : ℂ} {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) {u : MassParameter}
    {t : Fin (m' + 1) → ℝ} (ht : Function.Injective t)
    (P : MvPolynomial (FamilyJetIndex (m' + 1) n) ℂ)
    (hgood : u ∈ descentGood x ε c A
      (⟨⟨relationShapeOf P, injective_relationShapeOf_exponent P⟩, rfl⟩ : FamilyShape m' n))
    (hrel : ∀ z ∈ {ζ : ℂ | 0 < ζ.im}, MvPolynomial.eval
      (familyJetVec (n := n) (perturbedOuterFamily x ε u c A t) z) P = 0) :
    P = 0 := by
  classical
  set S : FamilyShape m' n :=
    ⟨⟨relationShapeOf P, injective_relationShapeOf_exponent P⟩, rfl⟩ with hSdef
  set N : ℕ := descentRowCount S with hN
  set z : Fin N → ℂ := gridNodes N with hz
  have hAt : ∀ ζ : ℂ, 0 < ζ.im → ContDiffAt ℂ (⊤ : ℕ∞) A ζ := fun ζ hζ => (hA ζ hζ).contDiffAt
  have havoid := hgood ⟨t, ht⟩
  have hinj := mulVec_injective_of_notMem_outerShiftBad z n ((relationShapeOf P).depthPred + 1)
    (relationShapeOf P).spectralDegree (familyShape_mul m' n S) (relationShapeOf P).exponent x ε
    (sigmaCarrierJets (m' + 1) n ((relationShapeOf P).depthPred + 1) (familyShape_mul m' n S)
      z c A) u t havoid
  refine eq_zero_of_relation_of_rigid_jets_row (row := Fin N) P hrel z
    (fun b => gridNodes_upper N b)
    (familyOuterObservation (m' + 1) n ((relationShapeOf P).depthPred + 1)
      (familyShape_mul m' n S) z t x ε u
      + outerCarrierJets (m' + 1) n ((relationShapeOf P).depthPred + 1)
        (familyShape_mul m' n S) z t c A) (fun p => ?_) (fun cv hcv => ?_)
  · exact familyOuterObservation_add_carrier_apply (m' + 1) n
      ((relationShapeOf P).depthPred + 1) (familyShape_mul m' n S) z t (gridNodes_upper N) x
      hεpos hε u c hAt p.1 p.2
  · refine hinj ?_
    have hfold : (fun p => sigmaCarrierJets (m' + 1) n ((relationShapeOf P).depthPred + 1)
        (familyShape_mul m' n S) z c A t
          ((sigmaJetIndexEquiv (m' + 1) n ((relationShapeOf P).depthPred + 1)
            (familyShape_mul m' n S)).symm p))
        = outerCarrierJets (m' + 1) n ((relationShapeOf P).depthPred + 1)
          (familyShape_mul m' n S) z t c A := by
      funext p
      exact sigmaCarrierJets_fold (m' + 1) n ((relationShapeOf P).depthPred + 1)
        (familyShape_mul m' n S) z c A t p
    rw [hfold, hcv, Matrix.mulVec_zero]

/-! ## One residual set for every family and every tuple of distinct shifts -/

/-- Relation shapes of every member count and every jet depth. -/
abbrev DescentIndex : Type := Σ m' : ℕ, Σ n : ℕ, FamilyShape m' n

/-- The mass parameters which are good for every shape at once. -/
def shiftUniformGood (x ε : ℕ → ℝ) (c : ℂ) (A : ℂ → ℂ) : Set MassParameter :=
  ⋂ i : DescentIndex, descentGood x ε c A i.2.2

theorem residual_shiftUniformGood {x : ℕ → ℝ} (hx : Function.Injective x) {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ) {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) :
    shiftUniformGood x ε c A ∈ residual MassParameter :=
  residual_iInter fun i => residual_descentGood hx hεpos hε c hA i.2.2

/-- **Shift-uniform full translation freeness.**  At a good mass parameter the translates of the
perturbed outer background satisfy no nonzero differential relation, for every finite tuple of
distinct real shifts at once. -/
theorem not_familyDifferentiallyAlgebraicOn_of_shiftUniformGood {x : ℕ → ℝ} {ε : ℕ → ℝ}
    (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) {c : ℂ} {A : ℂ → ℂ}
    (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) {u : MassParameter}
    (hu : u ∈ shiftUniformGood x ε c A) {m' : ℕ} {t : Fin (m' + 1) → ℝ}
    (ht : Function.Injective t) :
    ¬ FamilyDifferentiallyAlgebraicOn (perturbedOuterFamily x ε u c A t)
      {ζ : ℂ | 0 < ζ.im} := by
  rintro ⟨n, P, hPne, hrel⟩
  refine hPne (eq_zero_of_relation_of_descentGood hεpos hε hA ht P ?_ hrel)
  exact Set.mem_iInter.mp hu
    ⟨m', n, ⟨⟨relationShapeOf P, injective_relationShapeOf_exponent P⟩, rfl⟩⟩

/-- **The shift-uniform statement.**  One residual set of bounded exponential mass parameters makes
every finite family of distinct real translates of the perturbed outer background differentially
algebraically independent. -/
theorem residual_not_familyDifferentiallyAlgebraicOn_shiftUniform {x : ℕ → ℝ}
    (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) :
    {u : MassParameter | ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ), Function.Injective t →
        ¬ FamilyDifferentiallyAlgebraicOn (perturbedOuterFamily x ε u c A t) {ζ : ℂ | 0 < ζ.im}}
      ∈ residual MassParameter := by
  refine Filter.mem_of_superset (residual_shiftUniformGood hx hεpos hε c hA) ?_
  intro u hu m' t ht
  exact not_familyDifferentiallyAlgebraicOn_of_shiftUniformGood hεpos hε hA hu ht

/-- **The good parameters are dense.** -/
theorem dense_not_familyDifferentiallyAlgebraicOn_shiftUniform {x : ℕ → ℝ}
    (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A {ζ : ℂ | 0 < ζ.im}) :
    Dense {u : MassParameter | ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ), Function.Injective t →
        ¬ FamilyDifferentiallyAlgebraicOn (perturbedOuterFamily x ε u c A t)
          {ζ : ℂ | 0 < ζ.im}} :=
  dense_of_mem_residual
    (residual_not_familyDifferentiallyAlgebraicOn_shiftUniform hx hεpos hε c hA)

/-! ## The exponential carrier -/

theorem analyticOnNhd_cexpSeriesCarrier {ι : Type*} {a : ι → ℂ} {omega : ι → ℝ}
    (h : ExpSeriesNormallySummable a omega) :
    AnalyticOnNhd ℂ (cexpSeriesCarrier a omega) {ζ : ℂ | 0 < ζ.im} :=
  (differentiable_cexpSeriesCarrier h).differentiableOn.analyticOnNhd isOpen_upperHalfSet

/-- **Claim (9), shift-uniform.**  One residual set of bounded exponential mass parameters makes
every finite family of distinct real translates of the outer background perturbed by an exponential
carrier differentially algebraically independent. -/
theorem residual_shiftUniform_perturbedOuterOrbit {ι : Type*} {x : ℕ → ℝ}
    (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ)
    {a : ι → ℂ} {omega : ι → ℝ} (hcar : ExpSeriesNormallySummable a omega) :
    {u : MassParameter | ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ), Function.Injective t →
        ¬ FamilyDifferentiallyAlgebraicOn
          (perturbedOuterFamily x ε u c (cexpSeriesCarrier a omega) t) {ζ : ℂ | 0 < ζ.im}}
      ∈ residual MassParameter :=
  residual_not_familyDifferentiallyAlgebraicOn_shiftUniform hx hεpos hε c
    (analyticOnNhd_cexpSeriesCarrier hcar)

/-- **The good parameters of the exponentially perturbed orbit are dense.** -/
theorem dense_shiftUniform_perturbedOuterOrbit {ι : Type*} {x : ℕ → ℝ}
    (hx : Function.Injective x) {ε : ℕ → ℝ} (hεpos : ∀ k, 0 < ε k) (hε : Summable ε) (c : ℂ)
    {a : ι → ℂ} {omega : ι → ℝ} (hcar : ExpSeriesNormallySummable a omega) :
    Dense {u : MassParameter | ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ), Function.Injective t →
        ¬ FamilyDifferentiallyAlgebraicOn
          (perturbedOuterFamily x ε u c (cexpSeriesCarrier a omega) t) {ζ : ℂ | 0 < ζ.im}} :=
  dense_of_mem_residual (residual_shiftUniform_perturbedOuterOrbit hx hεpos hε c hcar)

end

end GaloisForLFunctions.HTGeometry
