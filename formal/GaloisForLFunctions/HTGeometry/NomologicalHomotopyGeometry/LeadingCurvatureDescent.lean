import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.FlatSuperconnection
import GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.HigherPeriodSpencer

/-!
# Leading curvature cohomology descent and period generation

A flat completed superconnection supplies the internal differential, the homology connection, and
its curvature nullhomotopy.  The first two surviving form-degree pieces of the universal Bianchi
identity make the first nonzero curvature a cycle and its covariant derivative a boundary.  This
file constructs the resulting cohomology class, proves flatness and covariant closure, proves
representative independence, and attaches the common higher-period/Spencer theorem at arbitrary
arity.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.LeadingCurvatureDescent

open FlatSuperconnection HigherPeriodSpencer

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A first surviving curvature layer at arbitrary finite form degree. -/
structure LeadingLayer where
  superconnection : ℕ → Module.End ℝ E
  flat : FlatSuperconnection.IsFlat superconnection
  order : ℕ
  order_ge_three : 3 ≤ order
  curvature : ℕ → E
  lower_vanishes : ∀ q, 2 ≤ q → q < order → curvature q = 0
  nextCurvature : E
  leading_bianchi : superconnection 0 (curvature order) = 0
  next_bianchi :
    superconnection 1 (curvature order) + superconnection 0 nextCurvature = 0

namespace LeadingLayer

variable (L : LeadingLayer (E := E))

/-- Internal differential extracted from form degree zero. -/
def differential : FlatSuperconnection.Differential (k := ℝ) (E := E) :=
  FlatSuperconnection.differentialOfFlat L.superconnection L.flat

/-- First surviving curvature as an internal cycle. -/
def leadingCycle : L.differential.cycles :=
  ⟨L.curvature L.order, L.leading_bianchi⟩

/-- Cohomology class of the first surviving curvature. -/
def leadingClass : L.differential.Cohomology :=
  L.differential.classOf L.leadingCycle

/-- Connection induced on internal homology. -/
theorem connection_anticommutes :
    L.differential.d.comp (L.superconnection 1) +
      (L.superconnection 1).comp L.differential.d = 0 :=
  FlatSuperconnection.differential_connection_anticommute L.flat

/-- Connection induced on internal homology. -/
def homologyConnection : Module.End ℝ L.differential.Cohomology :=
  L.differential.inducedConnection (L.superconnection 1)
    L.connection_anticommutes

/-- Fake flatness of the lower layer makes the internal-homology connection flat. -/
theorem homologyConnection_sq_eq_zero :
    L.homologyConnection.comp L.homologyConnection = 0 := by
  exact FlatSuperconnection.Differential.inducedConnection_sq_eq_zero
    L.differential (L.superconnection 1) (L.superconnection 2)
    L.connection_anticommutes
    (FlatSuperconnection.curvature_add_nullhomotopy_eq_zero L.flat)

/-- Form degree `r+1` in Bianchi says the leading cohomology class is covariantly closed. -/
theorem leadingClass_covariantly_closed :
    L.homologyConnection L.leadingClass = 0 := by
  change L.differential.classOf
    ⟨L.superconnection 1 (L.curvature L.order),
      L.differential.maps_cycles_of_anticommutes
        (L.superconnection 1) L.connection_anticommutes L.leadingCycle⟩ = 0
  apply (L.differential.classOf_eq_zero_iff _).mpr
  refine ⟨-L.nextCurvature, ?_⟩
  change L.superconnection 0 (-L.nextCurvature) =
    L.superconnection 1 (L.curvature L.order)
  have h := L.next_bianchi
  have hconnection :
      L.superconnection 1 (L.curvature L.order) =
        -L.superconnection 0 L.nextCurvature :=
    eq_neg_of_add_eq_zero_left h
  rw [map_neg, hconnection]

/-- Adding an internal boundary changes the leading cycle representative but not its class. -/
theorem leadingClass_add_boundary (b : E) :
    let shifted : L.differential.cycles :=
      ⟨L.curvature L.order + L.superconnection 0 b, by
        change L.superconnection 0
          (L.curvature L.order + L.superconnection 0 b) = 0
        rw [map_add, L.leading_bianchi]
        have hsq := FlatSuperconnection.differential_sq_zero L.flat
        have hb := LinearMap.congr_fun hsq b
        simpa using hb⟩
    L.differential.classOf shifted = L.leadingClass := by
  dsimp only [FlatSuperconnection.Differential.classOf, leadingClass]
  change Submodule.Quotient.mk
      (⟨L.curvature L.order + L.superconnection 0 b, _⟩ : L.differential.cycles) =
    Submodule.Quotient.mk L.leadingCycle
  rw [Submodule.Quotient.eq]
  change (L.curvature L.order + L.superconnection 0 b) - L.curvature L.order ∈
    L.differential.boundaries
  simpa using (show L.superconnection 0 b ∈ L.differential.boundaries from ⟨b, rfl⟩)

/-- Complete all-finite-length leading-curvature descent theorem. -/
theorem descent_capstone :
    L.homologyConnection.comp L.homologyConnection = 0 ∧
      L.homologyConnection L.leadingClass = 0 ∧
      ∀ b : E,
        let shifted : L.differential.cycles :=
          ⟨L.curvature L.order + L.superconnection 0 b, by
            change L.superconnection 0
              (L.curvature L.order + L.superconnection 0 b) = 0
            rw [map_add, L.leading_bianchi]
            have hsq := FlatSuperconnection.differential_sq_zero L.flat
            have hb := LinearMap.congr_fun hsq b
            simpa using hb⟩
        L.differential.classOf shifted = L.leadingClass :=
  ⟨L.homologyConnection_sq_eq_zero, L.leadingClass_covariantly_closed,
    L.leadingClass_add_boundary⟩

end LeadingLayer

section PeriodGeneration

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The first surviving cohomology curvature generates its lifted higher-period algebra at every
finite order `r ≥ 3`. -/
theorem leading_period_generation {ι σ : Type*}
    (P : PeriodGeometry (V := V) ι σ) :
    P.restrictedAlgebra = Submodule.span ℝ (Set.range P.curvatureValue) :=
  P.higher_ambroseSinger

/-- In the analytic case, covariant Spencer jets generate the same leading period algebra. -/
theorem leading_period_spencer_generation {ι σ κ : Type*}
    (A : AnalyticSpencerGeometry (V := V) ι σ κ) :
    A.toPeriodGeometry.restrictedAlgebra = A.jetSpan :=
  A.higher_ambroseSinger_spencer

end PeriodGeneration

end HTGeometry.NomologicalHomotopyGeometry.LeadingCurvatureDescent
