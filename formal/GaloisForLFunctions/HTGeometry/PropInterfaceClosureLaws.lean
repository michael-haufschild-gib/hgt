import GaloisForLFunctions.HTGeometry.SpectralCharacterRealizabilityLaw
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.WaveTracePoleDivergence
import GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology
import GaloisForLFunctions.HTGeometry.PrimeRadialFusionRankSurfaceRealization
import GaloisForLFunctions.HTGeometry.PrimeClockPolynomialSaturation
import GaloisForLFunctions.HTGeometry.FacetRestrictionEmbedding
import GaloisForLFunctions.HTGeometry.ComponentReplicaCollisionLaw
import GaloisForLFunctions.HTGeometry.ReplicaActionCrowdingShortcutLaw
import GaloisForLFunctions.HTGeometry.ConstitutiveFailureKernelTransversal
import GaloisForLFunctions.HTGeometry.AdaptiveEigenframeTwoQuerySourceMemory
import GaloisForLFunctions.HTGeometry.FormationCloneRigidityCompletion
import GaloisForLFunctions.HTGeometry.CanonicalEventSlice
import GaloisForLFunctions.HTGeometry.GammaPoleMovingAffineProfileHorizon
import GaloisForLFunctions.HTGeometry.ConstitutiveEndpointInsufficiency
import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import GaloisForLFunctions.HTGeometry.ConstitutiveFutureReporterPromotion
import GaloisForLFunctions.HTGeometry.SingletonPropInterfaceWitnesses

/-!
# Closure laws for the residual proposition interfaces

These theorems expose canonical inhabitants that were hidden behind equivalences, aliases, or
existential packages.  The nondegenerate laws are exact: every nonzero projective character gets a
chosen jet with prescribed birth order, every positive member of an additive order spectrum is
realized by its monomial fusion algebra, unequal replica energies determine their own open action
radius, and equality is a strict reporter promotion exactly for commuting law pairs.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Spectral and differential-circuit leaves -/

/-- A chosen jet realizing a nonzero projective character at the prescribed birth order. -/
def spectralCharacterRealizingJet
    {I : Type*} (k : ProjectiveCharacter I) (r : ℕ) (hk : k ≠ 0) :
    ℕ → I → ℂ :=
  Classical.choose
    ((exists_spectralCharacterActive_birthOrder_eq_iff_ne_zero k r).2 hk)

/-- The chosen prescribed-birth jet is active. -/
theorem spectralCharacterRealizingJet_active
    {I : Type*} (k : ProjectiveCharacter I) (r : ℕ) (hk : k ≠ 0) :
    SpectralCharacterActive (spectralCharacterRealizingJet k r hk) k :=
  Classical.choose
    (Classical.choose_spec
      ((exists_spectralCharacterActive_birthOrder_eq_iff_ne_zero k r).2 hk))

/-- The chosen jet has exactly the requested first active order. -/
theorem spectralCharacterRealizingJet_birthOrder
    {I : Type*} (k : ProjectiveCharacter I) (r : ℕ) (hk : k ≠ 0) :
    spectralCharacterBirthOrder (spectralCharacterRealizingJet k r hk) k
      (spectralCharacterRealizingJet_active k r hk) = r := by
  exact Classical.choose_spec
    (Classical.choose_spec
      ((exists_spectralCharacterActive_birthOrder_eq_iff_ne_zero k r).2 hk))

/-- Every declared atom is a scalar-or-atom leaf. -/
theorem baseScalarOrAtom_of_atom
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {Atom : E → Prop} {x : E} (hx : Atom x) :
    BaseScalarOrAtom F E Atom x :=
  Or.inl hx

/-- Every base-field scalar is a scalar-or-atom leaf, independently of the atom predicate. -/
theorem baseScalarOrAtom_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (Atom : E → Prop) (c : F) :
    BaseScalarOrAtom F E Atom (algebraMap F E c) :=
  Or.inr ⟨c, rfl⟩

/-! ## Locally finite spectra and regular Koszul factors -/

namespace WaveSpectrum

/-- Every spectrum on a finite frequency type is locally finite. -/
theorem isLocallyFiniteSpectrum_of_finite
    {G : Type*} [Finite G] (S : WaveSpectrum G) :
    S.IsLocallyFiniteSpectrum := by
  intro R
  exact Set.toFinite _

end WaveSpectrum

/-- The unit is a regular Koszul factor in every commutative ring. -/
theorem isKoszulRegular_one {R : Type*} [CommRing R] :
    IsKoszulRegular (1 : R) := by
  intro r hr
  simpa using hr

/-! ## Exact radial, clock, compatibility, and recombination witnesses -/

/-- Every positive member of an additive order spectrum occurs in its canonical monomial algebra. -/
theorem primeRadialOrderOccurs_monoidProfileAlgebra
    (S : AddSubmonoid ℕ) {n : ℕ} (hnS : n ∈ S) (hn : 0 < n) :
    PrimeRadialOrderOccurs (primeRadialMonoidProfileAlgebra S) n :=
  (primeRadialMonoidProfileAlgebra_orderOccurs_iff S n).2 ⟨hnS, hn⟩

/-- The zero prime-power profile is finite-prime local. -/
theorem primePowerClockLocal_zero :
    PrimePowerClockLocal (0 : PrimePowerClockIndex → ℂ) :=
  rayLocal_zero primePowerClockRay

/-- Compatibility on an empty fracture family is automatic. -/
theorem familyPairwiseCompatibleOn_empty
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (J : ι → Submodule R M) (x : (i : ι) → M ⧸ J i) :
    familyPairwiseCompatibleOn J ∅ x := by
  intro i hi
  simp at hi

/-- Keeping the two inputs in their original order is a componentwise recombination. -/
theorem isComponentwiseRecombination_pair
    {C : Type*} {I : C → Type*} (x y : ∀ c, I c) :
    IsComponentwiseRecombination x y (x, y) := by
  intro c
  exact Or.inl ⟨rfl, rfl⟩

/-- Distinct replica energies canonically determine a radius on which they are near. -/
theorem replicaNearAction_at_gap_add_one
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (p q : ReplicaMultiplicityIndex I n)
    (hgap : replicaMultiplicityEnergy energy p.1 ≠
      replicaMultiplicityEnergy energy q.1) :
    replicaNearAction energy n
      (|replicaMultiplicityEnergy energy p.1 -
        replicaMultiplicityEnergy energy q.1| + 1) p q := by
  refine ⟨abs_pos.mpr (sub_ne_zero.mpr hgap), ?_⟩
  exact lt_add_of_pos_right _ zero_lt_one

/-! ## Failure systems and finite dictionaries -/

/-- A singleton removal hits the matching singleton failure kernel. -/
theorem hitsFailureKernel_singleton
    {α : Type*} [DecidableEq α] (a : α) :
    HitsFailureKernel ({a} : Finset α) {a} := by
  exact ⟨a, by simp, by simp⟩

/-- Consequence system deriving nothing from every finite base. -/
def emptyFiniteConsequence (α : Type*) [DecidableEq α] : FiniteConsequence α where
  derive := fun _ => ∅
  monotone := fun _ _ _ => Finset.Subset.rfl

/-- Every revision succeeds in the empty consequence system. -/
theorem successfulKernelRevision_emptyConsequence
    {α : Type*} [DecidableEq α] (T : Finset α) (a : α) (R : Finset α) :
    SuccessfulKernelRevision (emptyFiniteConsequence α) T a R := by
  simp [SuccessfulKernelRevision, emptyFiniteConsequence]

/-- Every actual fixed-body Majorana monomial belongs to its complete dictionary. -/
theorem majoranaQBodyDictionary_image
    (n q : ℕ) (S : MajoranaQBodyIndex n q) :
    MajoranaQBodyDictionary n q (majoranaQBodyPauliLabel n q S) :=
  ⟨S, rfl⟩

/-- The zero packet is singular against every finite packet. -/
theorem finiteFormationSingular_zero_left
    {X : Type*} (q : X → ℝ) :
    FiniteFormationSingular (fun _ => 0) q := by
  intro x
  exact Or.inl rfl

/-! ## Order, Gamma-profile, and observer closures -/

/-- Equality-or-incomparability is transitive in every linear order. -/
theorem augmentedIncomparableTransitive_of_linearOrder
    {α : Type*} [LinearOrder α] :
    AugmentedIncomparableTransitive (α := α) := by
  intro x y z hxy hyz
  have hxy' : x = y :=
    le_antisymm (not_lt.mp hxy.2) (not_lt.mp hxy.1)
  subst y
  exact hyz

/-- The zero symbolic Gamma profile has pole grade at most zero. -/
theorem gammaPoleSymbolicProfilePoleGradeAtMost_zero (n : ℕ) :
    GammaPoleSymbolicProfilePoleGradeAtMost n 0
      (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :=
  (gammaPoleSymbolicProfilePoleGradeAtMost_zero_iff_constant
    (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ))).2 ⟨0, by simp⟩

/-- The zero actual Gamma profile has pole grade at most zero. -/
theorem gammaPoleProfilePoleGradeAtMost_zero (n : ℕ) :
    GammaPoleProfilePoleGradeAtMost n 0
      (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) :=
  (gammaPoleProfilePoleGradeAtMost_zero_iff_constant
    (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ))).2 ⟨0, by simp⟩

/-- The zero symbolic Gamma profile has at most a simple pole. -/
theorem gammaPoleSymbolicProfileAtMostSimple_zero (n : ℕ) :
    GammaPoleSymbolicProfileAtMostSimple n
      (0 : MvPolynomial (Fin (n + 1)) (Polynomial ℂ)) := by
  intro q hq
  exact gammaPoleSymbolicProfilePoleGradeAtMost_zero n q (by omega)

/-- Constant functions are derived observers. -/
theorem derivedObserver_const
    {k : Type*} [Field k] {Y : Type*} (c : Y) :
    DerivedObserver (fun _ : kˣ => c) := by
  intro u v hker hrange
  rfl

/-- Constant functions are endpoint observers. -/
theorem endpointObserver_const {Y : Type*} (c : Y) :
    EndpointObserver (fun _ => c) := by
  intro w w' h
  rfl

/-- Constant functions are Euler observers. -/
theorem eulerObserver_const {Y : Type*} (c : Y) :
    EulerObserver (fun _ => c) := by
  intro n m h
  rfl

/-! ## Cofinite reconstruction and strict reporter promotion -/

/-- An empty coefficient family is tail independent on every source. -/
theorem tailCoefficientIndependent_empty_index
    {X : Type*} (u : Empty → X → ℂ) : TailCoefficientIndependent u := by
  intro c hfinite
  funext i
  exact i.elim

/-- The empty coefficient family has complete cofinite Hilbert reconstruction. -/
theorem cofiniteEvaluationHilbertReconstruction_empty_index
    {X : Type*} (u : Empty → X → ℂ) :
    CofiniteEvaluationHilbertReconstruction u :=
  (cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent u).2
    (tailCoefficientIndependent_empty_index u)

/-- Equality is a strict reporter promotion for every pair of commuting source laws. -/
theorem reporterStrictExchangePromotion_eq_of_commute
    {α β : Type*} (f g : α → α) (r : α → β)
    (hcomm : ∀ x, f (g x) = g (f x)) :
    ReporterStrictExchangePromotion f g r Eq := by
  refine ⟨eq_equivalence, ?_, ?_, hcomm, ?_⟩
  · intro x y hxy
    simpa using congrArg f hxy
  · intro x y hxy
    simpa using congrArg g hxy
  · intro x y hxy
    exact congrArg r hxy

/-- Equality is a strict reporter promotion exactly when the two laws commute pointwise. -/
theorem reporterStrictExchangePromotion_eq_iff_commute
    {α β : Type*} (f g : α → α) (r : α → β) :
    ReporterStrictExchangePromotion f g r Eq ↔
      ∀ x, f (g x) = g (f x) := by
  constructor
  · intro h
    exact h.2.2.2.1
  · exact reporterStrictExchangePromotion_eq_of_commute f g r

end

end GaloisForLFunctions.HTGeometry
