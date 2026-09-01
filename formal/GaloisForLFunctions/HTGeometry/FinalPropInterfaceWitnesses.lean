import GaloisForLFunctions.HTGeometry.BorsukUlam.CrossPolytope
import GaloisForLFunctions.HTGeometry.BorsukUlam.Tucker
import GaloisForLFunctions.HTGeometry.ABHN.RestrictedInvariantSupportHasse
import GaloisForLFunctions.HTGeometry.DerivativeShadowStaircase
import GaloisForLFunctions.HTGeometry.DifferentialGenericPointHorizon
import GaloisForLFunctions.HTGeometry.FormalAnalyticADE
import GaloisForLFunctions.HTGeometry.HelsonCriterionNecessary
import GaloisForLFunctions.HTGeometry.HelsonPrescribedDivisor
import GaloisForLFunctions.HTGeometry.MovingDivisorEvenFreeness
import GaloisForLFunctions.HTGeometry.MovingDivisorRankGenericity
import GaloisForLFunctions.HTGeometry.PlaceLimit
import GaloisForLFunctions.HTGeometry.PolynomialPlaceResidue
import GaloisForLFunctions.HTGeometry.ThermodynamicSelectedPathLifecycleLaw
import GaloisForLFunctions.HTGeometry.UniversalJetRelationRank
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Final proposition-interface witnesses

Concrete endpoint models for structural predicates used throughout `HTGeometry`.  The witnesses
cover a nontrivial rational-function place, the empty-coordinate differential boundary, both
moving-divisor rank interfaces, the one-dimensional cross-polytope Fan graph, the trivial Helson
phase, and an actual continuous-circuit excursion extracted from the thermodynamic lifecycle law.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

/-- The `X`-adic place of `F(X)` is trivial on the embedded coefficient field. -/
theorem placeTrivialOn_polyPlace_algebraMapRange
    (F : Type*) [Field F] :
    PlaceTrivialOn (polyPlace (Polynomial.irreducible_X (R := F)))
      (algebraMap F (RatFunc F)).fieldRange := by
  intro x hx hx0
  rcases hx with ⟨a, rfl⟩
  change (polyPlace (Polynomial.irreducible_X (R := F))).valuation (RatFunc F)
    (RatFunc.C a) = 1
  rw [← RatFunc.algebraMap_C,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
  change Polynomial.C a ∉ Ideal.span {Polynomial.X}
  intro h
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff] at h
  exact hx0 (by simpa using h)

/-- Prolonging the zero coordinate ideal produces the zero jet ideal. -/
theorem prolongedIdeal_bot
    {C κ : Type*} [Field C] :
    prolongedIdeal (C := C) (⊥ : Ideal (MvPolynomial κ C)) = ⊥ := by
  apply le_antisymm
  · rw [prolongedIdeal, Ideal.span_le]
    rintro Q ⟨P, hP, j, rfl⟩
    have hP0 : P = 0 := by simpa using hP
    subst P
    simp
  · exact bot_le

/-- The unique family on an empty coordinate type is differentially generic. -/
theorem isDifferentiallyGeneric_empty
    {C F : Type*} [Field C] [Field F] [Differential F] [Algebra C F] :
    IsDifferentiallyGeneric (C := C) (fun i : Empty => i.elim : Empty → F) := by
  rw [IsDifferentiallyGeneric]
  have hbase : RingHom.ker
      (MvPolynomial.aeval (fun i : Empty => i.elim) :
        MvPolynomial Empty C →ₐ[C] F).toRingHom = ⊥ := by
    apply le_antisymm
    · intro P hP
      have hP0 : P = 0 := by
        apply MvPolynomial.aeval_injective_iff_of_isEmpty.mpr
          (FaithfulSMul.algebraMap_injective C F)
        exact hP.trans (map_zero _).symm
      simpa [hP0]
    · exact bot_le
  have hjet : RingHom.ker
      (jetFamilyEval (C := C) (fun i : Empty => i.elim) :
        JetPoly C Empty →ₐ[C] F).toRingHom = ⊥ := by
    apply le_antisymm
    · intro P hP
      have hP0 : P = 0 := by
        apply MvPolynomial.aeval_injective_iff_of_isEmpty.mpr
          (FaithfulSMul.algebraMap_injective C F)
        exact hP.trans (map_zero _).symm
      simpa [hP0]
    · exact bot_le
  rw [hbase, hjet, prolongedIdeal_bot]

/-- Unique collision-free shift configuration on an empty index. -/
def emptyInjectiveShiftConfiguration : InjectiveShiftConfiguration Empty :=
  ⟨fun i => i.elim, fun i => i.elim⟩

/-- Unique collision-free projective row packet on an empty index. -/
def emptyInjectiveProjectiveRowPacket : InjectiveProjectiveRowPacket Empty :=
  ⟨fun i => i.elim, fun i => i.elim⟩

/-- Empty row and coefficient types realize the expanded full-rank boundary. -/
theorem MovingDivisor.expandedFullRankWitness_empty
    (Dv : MovingDivisor) (degree : ℕ) (θ : BoundedRealSequence) :
    Dv.expandedFullRankWitness
      (row := Empty) (κ := Empty) (ι := Empty)
      degree (fun i => i.elim) (fun i => i.elim) θ
      emptyInjectiveShiftConfiguration := by
  refine ⟨emptyInjectiveProjectiveRowPacket, ?_, ?_, ?_⟩
  · intro x
    exact x.1.elim
  · intro x
    exact x.1.elim
  · intro f g _
    exact Subsingleton.elim f g

/-- Empty row and coefficient types realize the even expanded full-rank boundary. -/
theorem MovingDivisor.evenExpandedFullRankWitness_empty
    (Dv : MovingDivisor) (degree : ℕ) (θ : BoundedRealSequence) :
    Dv.evenExpandedFullRankWitness
      (row := Empty) (κ := Empty) (ι := Empty)
      degree (fun i => i.elim) (fun i => i.elim) θ
      emptyInjectiveShiftConfiguration := by
  refine ⟨emptyInjectiveProjectiveRowPacket, ?_, ?_, ?_, ?_⟩
  · intro x
    exact x.1.elim
  · intro x
    exact x.1.elim
  · intro x
    exact x.1.elim
  · intro f g _
    exact Subsingleton.elim f g

/-- The trivial Helson phase carries continuation certificates at every level. -/
theorem continuationCriterion_trivialPhase : ContinuationCriterion trivialPhase := by
  intro N
  apply exists_levelData_of_mem_continuableStratum
  apply mem_continuableStratum_of_finiteModification
  simp [GaloisForLFunctions.finiteModification]

/-- At least one literal finite prefix satisfies the complete continuous-circuit excursion law. -/
theorem exists_continuousCircuitExcursionLaw :
    ∃ (n s : ℕ) (H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
      ContinuousCircuitExcursionLaw n s H := by
  obtain ⟨p, _, _, _, hevent⟩ :=
    exists_nestedCentered_staticPath_ramp_and_continuousCircuitLifecycle
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨k, hk⟩ := hevent
  exact ⟨k + 3, nearHilbertContinuousCircuitBudget (k + 3),
    pathHamiltonian (infinitePathPrefixShell k p), hk k le_rfl⟩

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.BorsukUlam

noncomputable section

/-- The Fan graph of the one-dimensional cross-polytope has an actual edge. -/
theorem exists_flagComplex_adj :
    ∃ (K : FlagComplex 1) (lab : K.V → ℤ) (σ τ : Finset K.V),
      FlagComplex.Adj K lab σ τ := by
  classical
  let K : FlagComplex 1 := CrossPolytope.cross 1
  let lab : K.V → ℤ := fun _ => 1
  have hdeg : K.deg lab ({K.base} : Finset K.V) = 1 :=
    K.deg_base (by omega) (by intro v; simp [lab])
  have hnonempty :
      ((K.nodes lab).filter (K.Adj lab {K.base})).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [FlagComplex.deg, hempty, Finset.card_empty] at hdeg
    omega
  obtain ⟨τ, hτ⟩ := hnonempty
  exact ⟨K, lab, {K.base}, τ, (Finset.mem_filter.mp hτ).2⟩

/-- The same explicit Fan-graph edge contains an actual covering pair. -/
theorem exists_flagComplex_cov :
    ∃ (K : FlagComplex 1) (lab : K.V → ℤ) (σ τ : Finset K.V),
      FlagComplex.Cov K lab σ τ := by
  obtain ⟨K, lab, σ, τ, hadj⟩ := exists_flagComplex_adj
  rcases hadj.2.2 with hcov | hcov
  · exact ⟨K, lab, σ, τ, hcov⟩
  · exact ⟨K, lab, τ, σ, hcov⟩

end

end GaloisForLFunctions.BorsukUlam
