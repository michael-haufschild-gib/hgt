import GaloisForLFunctions.HTGeometry.OrientationTraceFactorizationLaw
import GaloisForLFunctions.HTGeometry.GreenObservationSplittingLaw
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittOrientedSource
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittRelativeBoundaryTransgression

/-!
# Orientation--transgression completeness of the Calderón--Witt source

The oriented algebraic source has no degree-zero or degree-one absolute
cohomology and exactly one degree-two orientation line.  Its Green
contractions also classify every class created by restricting incidence
primitives to an admitted sector.

Together these facts give a complete observation law:

* every boundary-blind linear consumer factors uniquely through the one
  source orientation trace;
* every consumer carrying information beyond that trace must detect an
  exact source boundary;
* every relative middle class is exactly the failure of the canonical
  Green primitive to remain in the admitted sector.

There is therefore no third regular source channel.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## Local completeness -/

/-- Orientation-carried part of an arbitrary local source consumer. -/
def deningerCalderonWittOrientationConsumerPrimary
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W) :
    (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W :=
  greenObservationPrimary
    (deningerCalderonWittOrientedTrace p)
    (deningerCalderonWittOrientationInclusion p) F

/-- Boundary-sensitive Green-transgression part of an arbitrary local
source consumer. -/
def deningerCalderonWittOrientationConsumerSecondary
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W) :
    (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W :=
  greenObservationSecondary
    (deningerCalderonWittOrientedBoundary p)
    (deningerCalderonWittOrientedTopGreenLift p) F

/--
**Unconditional local Green-observation splitting.** Every local source
consumer is its Haar-orientation compression plus its boundary-sensitive
Green transgression.
-/
theorem deningerCalderonWittOrientationConsumer_primary_add_secondary
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W) :
    deningerCalderonWittOrientationConsumerPrimary p F +
        deningerCalderonWittOrientationConsumerSecondary p F =
      F := by
  exact greenObservation_primary_add_secondary
    (deningerCalderonWittOrientedBoundary p)
    (deningerCalderonWittOrientedTrace p)
    (deningerCalderonWittOrientationInclusion p)
    (deningerCalderonWittOrientedTopGreenLift p)
    (deningerCalderonWittOrientedTopGreenDecomposition p) F

/-- The local secondary channel vanishes exactly for boundary-blind
consumers. -/
theorem deningerCalderonWittOrientationConsumerSecondary_eq_zero_iff
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W) :
    deningerCalderonWittOrientationConsumerSecondary p F = 0 ↔
      ∀ w, F (deningerCalderonWittOrientedBoundary p w) = 0 := by
  apply greenObservationSecondary_eq_zero_iff_boundaryBlind
    (deningerCalderonWittOrientedBoundary p)
    (deningerCalderonWittOrientedTrace p)
    (deningerCalderonWittOrientationInclusion p)
    (deningerCalderonWittOrientedTopGreenLift p)
    (deningerCalderonWittOrientedTopGreenDecomposition p)
  intro w
  exact
    (deningerCalderonWittOrientedBoundary_exact
      (deningerCalderonWittOrientedBoundary p w)).2
      ⟨w, rfl⟩

/--
The local observer descends uniquely through Haar orientation exactly when
its canonical secondary Green transgression vanishes.
-/
theorem
    deningerCalderonWittOrientationConsumerSecondary_eq_zero_iff_factorization
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W) :
    deningerCalderonWittOrientationConsumerSecondary p F = 0 ↔
      ∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp (deningerCalderonWittOrientedTrace p) := by
  apply greenObservation_traceFactorization_iff_secondary_eq_zero
    (deningerCalderonWittOrientedBoundary p)
    (deningerCalderonWittOrientedTrace p)
    (deningerCalderonWittOrientationInclusion p)
    (deningerCalderonWittOrientedTopGreenLift p)
    (deningerCalderonWittOrientedTopGreenDecomposition p)
  · intro w
    exact
      (deningerCalderonWittOrientedBoundary_exact
        (deningerCalderonWittOrientedBoundary p w)).2
        ⟨w, rfl⟩
  · intro c
    simp [deningerCalderonWittOrientedTrace,
      deningerCalderonWittOrientationInclusion]

/-- The local primary--secondary split is the unique decomposition whose
primary part is boundary-blind and whose secondary part kills the
orientation line. -/
theorem deningerCalderonWittOrientationConsumer_primary_secondary_unique
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F P S :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W)
    (hF : P + S = F)
    (hP : ∀ w, P (deningerCalderonWittOrientedBoundary p w) = 0)
    (hS : ∀ c, S (deningerCalderonWittOrientationInclusion p c) = 0) :
    P = deningerCalderonWittOrientationConsumerPrimary p F ∧
      S = deningerCalderonWittOrientationConsumerSecondary p F := by
  exact greenObservation_primary_secondary_unique
    (deningerCalderonWittOrientedBoundary p)
    (deningerCalderonWittOrientedTrace p)
    (deningerCalderonWittOrientationInclusion p)
    (deningerCalderonWittOrientedTopGreenLift p)
    (deningerCalderonWittOrientedTopGreenDecomposition p)
    F P S hF hP hS

/--
Every local boundary-blind source consumer factors uniquely through the
normalized Haar orientation trace.
-/
theorem deningerCalderonWittOrientationConsumer_factorization_unique_iff
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W) :
    (∀ w, F (deningerCalderonWittOrientedBoundary p w) = 0) ↔
      ∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp (deningerCalderonWittOrientedTrace p) := by
  rw [← deningerCalderonWittOrientationConsumerSecondary_eq_zero_iff p F]
  exact
    deningerCalderonWittOrientationConsumerSecondary_eq_zero_iff_factorization
      p F

/--
Local information beyond the Haar orientation trace is exactly sensitivity
to an exact oriented source boundary.
-/
theorem deningerCalderonWittOrientationConsumer_nonfactorization_iff
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W) :
    (¬ ∃ phi : ℂ →ₗ[ℂ] W,
      F = phi.comp (deningerCalderonWittOrientedTrace p)) ↔
      ∃ w, F (deningerCalderonWittOrientedBoundary p w) ≠ 0 := by
  apply orientationTrace_nonfactorization_iff_detects_boundary
    (boundary := deningerCalderonWittOrientedBoundary p)
    (trace := deningerCalderonWittOrientedTrace p)
    (inclusion := deningerCalderonWittOrientationInclusion p)
    (lift := deningerCalderonWittOrientedTopGreenLift p)
    (hdecomposition :=
      deningerCalderonWittOrientedTopGreenDecomposition p)
  · intro w
    exact
      (deningerCalderonWittOrientedBoundary_exact
        (deningerCalderonWittOrientedBoundary p w)).2
        ⟨w, rfl⟩
  · intro c
    simp [deningerCalderonWittOrientedTrace,
      deningerCalderonWittOrientationInclusion]

/--
**Unconditional local observation--transgression completeness.** Every
consumer has its canonical primary--secondary Green split.  Vanishing of
the secondary channel is exactly unique descent through Haar orientation,
while an exact incidence input has vanishing relative class exactly when
its Green primitive stays in the admitted sector.
-/
theorem deningerCalderonWittGreenObservationTransgressionCompleteness
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W)
    (S : Submodule ℂ (deningerCalderonWittMilnorIncidence p))
    (w : deningerCalderonWittMilnorIncidence p) :
    (deningerCalderonWittOrientationConsumerPrimary p F +
        deningerCalderonWittOrientationConsumerSecondary p F = F) ∧
      (deningerCalderonWittOrientationConsumerSecondary p F = 0 ↔
        ∃! phi : ℂ →ₗ[ℂ] W,
          F = phi.comp (deningerCalderonWittOrientedTrace p)) ∧
      (deningerCalderonWittRelativeBoundaryClass p S w.1 = 0 ↔
        deningerCalderonWittMilnorGreenRetraction p w.1 ∈ S) :=
  ⟨deningerCalderonWittOrientationConsumer_primary_add_secondary p F,
    deningerCalderonWittOrientationConsumerSecondary_eq_zero_iff_factorization
      p F,
    deningerCalderonWittRelativeBoundaryClass_incidence_eq_zero_iff
      p S w⟩

/--
**Local orientation--transgression completeness law.**  A regular consumer
has exactly one orientation factor, while a relative exterior cocycle
vanishes exactly when Green contraction preserves its admitted sector.
-/
theorem deningerCalderonWittOrientationTransgressionCompleteness
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (p : Nat.Primes)
    (F :
      (DeningerCalderonWittAlgebraicDegreeTwo p × ℂ) →ₗ[ℂ] W)
    (hregular :
      ∀ v, F (deningerCalderonWittOrientedBoundary p v) = 0)
    (S : Submodule ℂ (deningerCalderonWittMilnorIncidence p))
    (w : ⋀[ℂ]^(2 : ℕ) (DeningerCalderonWittAlgebraicDegreeOne p))
    (hcocycle : deningerCalderonWittAlgebraicExteriorCup p w = 0) :
    (∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp (deningerCalderonWittOrientedTrace p)) ∧
      (deningerCalderonWittRelativeBoundaryClass p S w = 0 ↔
        deningerCalderonWittMilnorGreenRetraction p w ∈ S) := by
  let wi : deningerCalderonWittMilnorIncidence p := ⟨w, hcocycle⟩
  have hcomplete :=
    deningerCalderonWittGreenObservationTransgressionCompleteness
      p F S wi
  refine ⟨?hfactor, ?hrelative⟩
  case hfactor =>
    exact hcomplete.2.1.mp
      ((deningerCalderonWittOrientationConsumerSecondary_eq_zero_iff
        p F).2 hregular)
  case hrelative =>
    simpa only [wi] using hcomplete.2.2

/-! ## All-prime completeness -/

/-- Orientation-carried part of an arbitrary all-prime source consumer. -/
def deningerCalderonWittGlobalOrientationConsumerPrimary
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W) :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W :=
  greenObservationPrimary
    deningerCalderonWittGlobalOrientedTrace
    deningerCalderonWittGlobalOrientationInclusion F

/-- Boundary-sensitive Green-transgression part of an arbitrary all-prime
source consumer. -/
def deningerCalderonWittGlobalOrientationConsumerSecondary
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W) :
    (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W :=
  greenObservationSecondary
    deningerCalderonWittGlobalOrientedBoundary
    deningerCalderonWittGlobalOrientedTopGreenLift F

/--
**Unconditional all-prime Green-observation splitting.** Every finite-support
global source consumer is its Haar-orientation compression plus its unique
boundary-sensitive Green transgression.
-/
theorem deningerCalderonWittGlobalOrientationConsumer_primary_add_secondary
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W) :
    deningerCalderonWittGlobalOrientationConsumerPrimary F +
        deningerCalderonWittGlobalOrientationConsumerSecondary F =
      F := by
  exact greenObservation_primary_add_secondary
    deningerCalderonWittGlobalOrientedBoundary
    deningerCalderonWittGlobalOrientedTrace
    deningerCalderonWittGlobalOrientationInclusion
    deningerCalderonWittGlobalOrientedTopGreenLift
    deningerCalderonWittGlobalOrientedTopGreenDecomposition F

/-- The all-prime secondary channel vanishes exactly for boundary-blind
consumers. -/
theorem deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W) :
    deningerCalderonWittGlobalOrientationConsumerSecondary F = 0 ↔
      ∀ w, F (deningerCalderonWittGlobalOrientedBoundary w) = 0 := by
  apply greenObservationSecondary_eq_zero_iff_boundaryBlind
    deningerCalderonWittGlobalOrientedBoundary
    deningerCalderonWittGlobalOrientedTrace
    deningerCalderonWittGlobalOrientationInclusion
    deningerCalderonWittGlobalOrientedTopGreenLift
    deningerCalderonWittGlobalOrientedTopGreenDecomposition
  intro w
  exact
    (deningerCalderonWittGlobalOrientedBoundary_exact
      (deningerCalderonWittGlobalOrientedBoundary w)).2
      ⟨w, rfl⟩

/--
The all-prime observer descends uniquely through Haar orientation exactly
when its canonical secondary Green transgression vanishes.
-/
theorem
    deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff_factorization
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W) :
    deningerCalderonWittGlobalOrientationConsumerSecondary F = 0 ↔
      ∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp deningerCalderonWittGlobalOrientedTrace := by
  apply greenObservation_traceFactorization_iff_secondary_eq_zero
    deningerCalderonWittGlobalOrientedBoundary
    deningerCalderonWittGlobalOrientedTrace
    deningerCalderonWittGlobalOrientationInclusion
    deningerCalderonWittGlobalOrientedTopGreenLift
    deningerCalderonWittGlobalOrientedTopGreenDecomposition
  · intro w
    exact
      (deningerCalderonWittGlobalOrientedBoundary_exact
        (deningerCalderonWittGlobalOrientedBoundary w)).2
        ⟨w, rfl⟩
  · intro c
    simp [deningerCalderonWittGlobalOrientedTrace,
      deningerCalderonWittGlobalOrientationInclusion]

/-- The all-prime primary--secondary split is uniquely characterized by its
boundary and orientation vanishing laws. -/
theorem deningerCalderonWittGlobalOrientationConsumer_primary_secondary_unique
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F P S :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W)
    (hF : P + S = F)
    (hP : ∀ w, P (deningerCalderonWittGlobalOrientedBoundary w) = 0)
    (hS : ∀ c, S (deningerCalderonWittGlobalOrientationInclusion c) = 0) :
    P = deningerCalderonWittGlobalOrientationConsumerPrimary F ∧
      S = deningerCalderonWittGlobalOrientationConsumerSecondary F := by
  exact greenObservation_primary_secondary_unique
    deningerCalderonWittGlobalOrientedBoundary
    deningerCalderonWittGlobalOrientedTrace
    deningerCalderonWittGlobalOrientationInclusion
    deningerCalderonWittGlobalOrientedTopGreenLift
    deningerCalderonWittGlobalOrientedTopGreenDecomposition
    F P S hF hP hS

/--
Every all-prime boundary-blind source consumer factors uniquely through the
single finite-support Haar orientation trace.
-/
theorem deningerCalderonWittGlobalOrientationConsumer_factorization_unique_iff
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W) :
    (∀ w, F (deningerCalderonWittGlobalOrientedBoundary w) = 0) ↔
      ∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp deningerCalderonWittGlobalOrientedTrace := by
  rw [← deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff F]
  exact
    deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff_factorization
      F

/--
All-prime information beyond the one orientation trace is exactly
sensitivity to an exact all-prime source boundary.
-/
theorem deningerCalderonWittGlobalOrientationConsumer_nonfactorization_iff
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W) :
    (¬ ∃ phi : ℂ →ₗ[ℂ] W,
      F = phi.comp deningerCalderonWittGlobalOrientedTrace) ↔
      ∃ w, F (deningerCalderonWittGlobalOrientedBoundary w) ≠ 0 := by
  apply orientationTrace_nonfactorization_iff_detects_boundary
    (boundary := deningerCalderonWittGlobalOrientedBoundary)
    (trace := deningerCalderonWittGlobalOrientedTrace)
    (inclusion := deningerCalderonWittGlobalOrientationInclusion)
    (lift := deningerCalderonWittGlobalOrientedTopGreenLift)
    (hdecomposition :=
      deningerCalderonWittGlobalOrientedTopGreenDecomposition)
  · intro w
    exact
      (deningerCalderonWittGlobalOrientedBoundary_exact
        (deningerCalderonWittGlobalOrientedBoundary w)).2
        ⟨w, rfl⟩
  · intro c
    simp [deningerCalderonWittGlobalOrientedTrace,
      deningerCalderonWittGlobalOrientationInclusion]

/--
**Unconditional all-prime observation--transgression completeness.** Every
finite-support global consumer splits canonically into Haar orientation and
boundary Green channels, and exact global incidence internalizes the
cocycle condition in the relative-sector criterion.
-/
theorem deningerCalderonWittGlobalGreenObservationTransgressionCompleteness
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W)
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : deningerCalderonWittGlobalMilnorIncidence) :
    (deningerCalderonWittGlobalOrientationConsumerPrimary F +
        deningerCalderonWittGlobalOrientationConsumerSecondary F = F) ∧
      (deningerCalderonWittGlobalOrientationConsumerSecondary F = 0 ↔
        ∃! phi : ℂ →ₗ[ℂ] W,
          F = phi.comp deningerCalderonWittGlobalOrientedTrace) ∧
      (deningerCalderonWittGlobalRelativeBoundaryClass S w.1 = 0 ↔
        deningerCalderonWittGlobalMilnorGreenRetraction w.1 ∈ S) :=
  ⟨deningerCalderonWittGlobalOrientationConsumer_primary_add_secondary F,
    deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff_factorization
      F,
    deningerCalderonWittGlobalRelativeBoundaryClass_incidence_eq_zero_iff
      S w⟩

/--
**All-prime orientation--transgression completeness law.**  Every regular
all-prime consumer is the unique image of the one orientation trace, and
every relative exterior class is exactly canonical Green-primitive escape
from its admitted incidence sector.
-/
theorem deningerCalderonWittGlobalOrientationTransgressionCompleteness
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (F :
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo × ℂ) →ₗ[ℂ] W)
    (hregular :
      ∀ v, F (deningerCalderonWittGlobalOrientedBoundary v) = 0)
    (S : Submodule ℂ deningerCalderonWittGlobalMilnorIncidence)
    (w : ⋀[ℂ]^(2 : ℕ) DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hcocycle :
      deningerCalderonWittAlgebraicGlobalExteriorCup w = 0) :
    (∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp deningerCalderonWittGlobalOrientedTrace) ∧
      (deningerCalderonWittGlobalRelativeBoundaryClass S w = 0 ↔
        deningerCalderonWittGlobalMilnorGreenRetraction w ∈ S) := by
  let wi : deningerCalderonWittGlobalMilnorIncidence := ⟨w, hcocycle⟩
  have hcomplete :=
    deningerCalderonWittGlobalGreenObservationTransgressionCompleteness
      F S wi
  refine ⟨?hfactor, ?hrelative⟩
  case hfactor =>
    exact hcomplete.2.1.mp
      ((deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff
        F).2 hregular)
  case hrelative =>
    simpa only [wi] using hcomplete.2.2

end

end RHTower
