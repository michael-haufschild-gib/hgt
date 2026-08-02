import GaloisForLFunctions.HTGeometry.OrientationTraceFactorizationLaw
import GaloisForLFunctions.RHTower.DeningerCalderonWittOrientedSource
import GaloisForLFunctions.RHTower.DeningerCalderonWittRelativeBoundaryTransgression

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
  apply orientationTrace_factorization_unique_iff
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
    (w : ⋀[ℂ]^2 (DeningerCalderonWittAlgebraicDegreeOne p))
    (hcocycle : deningerCalderonWittAlgebraicExteriorCup p w = 0) :
    (∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp (deningerCalderonWittOrientedTrace p)) ∧
      (deningerCalderonWittRelativeBoundaryClass p S w = 0 ↔
        deningerCalderonWittMilnorGreenRetraction p w ∈ S) := by
  exact
    ⟨(deningerCalderonWittOrientationConsumer_factorization_unique_iff
        p F).mp hregular,
      deningerCalderonWittRelativeBoundaryClass_eq_zero_iff
        p S w hcocycle⟩

/-! ## All-prime completeness -/

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
  apply orientationTrace_factorization_unique_iff
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
    (w : ⋀[ℂ]^2 DeningerCalderonWittAlgebraicGlobalDegreeOne)
    (hcocycle :
      deningerCalderonWittAlgebraicGlobalExteriorCup w = 0) :
    (∃! phi : ℂ →ₗ[ℂ] W,
        F = phi.comp deningerCalderonWittGlobalOrientedTrace) ∧
      (deningerCalderonWittGlobalRelativeBoundaryClass S w = 0 ↔
        deningerCalderonWittGlobalMilnorGreenRetraction w ∈ S) := by
  exact
    ⟨(deningerCalderonWittGlobalOrientationConsumer_factorization_unique_iff
        F).mp hregular,
      deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff
        S w hcocycle⟩

end

end RHTower
