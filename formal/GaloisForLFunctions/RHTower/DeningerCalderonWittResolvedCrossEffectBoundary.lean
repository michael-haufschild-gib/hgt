import GaloisForLFunctions.HTGeometry.ResolvedDefectConservationLaw
import GaloisForLFunctions.RHTower.DeningerCalderonWittAlgebraicSource

/-!
# Resolved Calderón--Witt cross-effect boundary

The ordinary Calderón--Witt cup alternates two ordered source cross-effects.  This module retains
those two terms before their codiagonal.  A source vector cups with itself to zero, but its resolved
self-cup is an antidiagonal pair.  At every arithmetic prime the canonical algebraic
rational-Witt unit makes that pair nonzero, and one-prime inclusion gives a nonzero resolved
boundary in the all-prime algebraic source.

This is the source-side counterpart of the resolved internal Deninger Green defect.  No completed
source-to-Green comparison or RH conclusion is asserted here.
-/

namespace RHTower

open scoped DirectSum
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Retain the two ordered terms of an alternating bilinear cross-effect before adding them. -/
def deningerResolvedAlternatingCrossEffect
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S) :
    (Q × P) →ₗ[R] (Q × P) →ₗ[R] (S × S) where
  toFun x :=
    { toFun := fun y => (B x.1 y.2, -B y.1 x.2)
      map_add' := by
        intro y z
        apply Prod.ext
        · simp
        · simp
          abel
      map_smul' := by
        intro c y
        apply Prod.ext <;> simp }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    apply Prod.ext
    · simp
    · simp
      abel
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    apply Prod.ext <;> simp

@[simp]
theorem deningerResolvedAlternatingCrossEffect_apply
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x y : Q × P) :
    deningerResolvedAlternatingCrossEffect B x y =
      (B x.1 y.2, -B y.1 x.2) :=
  rfl

/-- Adding the resolved coordinates recovers exactly the ordinary alternating cross-effect. -/
theorem deningerResolvedAlternatingCrossEffect_codiagonal
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x y : Q × P) :
    resolvedDefectCodiagonal (R := R)
        (deningerResolvedAlternatingCrossEffect B x y) =
      deningerAlternatingCrossEffect B x y := by
  simp [resolvedDefectCodiagonal, deningerAlternatingCrossEffect,
    sub_eq_add_neg]

/-- A self-cup is an antidiagonal resolved boundary before alternation kills it. -/
theorem deningerResolvedAlternatingCrossEffect_self_eq_antidiagonal
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x : Q × P) :
    deningerResolvedAlternatingCrossEffect B x x =
      resolvedDefectAntidiagonal (R := R) (B x.1 x.2) := by
  rfl

/-- Swapping source inputs exchanges the two resolved channels and reverses their signs. -/
theorem deningerResolvedAlternatingCrossEffect_swap
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x y : Q × P) :
    deningerResolvedAlternatingCrossEffect B y x =
      (-((deningerResolvedAlternatingCrossEffect B x y).2),
        -((deningerResolvedAlternatingCrossEffect B x y).1)) := by
  simp

/-- Left ordered cross-effects occupy the first resolved source axis. -/
def deningerResolvedCrossEffectLeftAxis
    (R S : Type*) [CommRing R] [AddCommGroup S] [Module R S] :
    Submodule R (S × S) :=
  Submodule.prod (⊤ : Submodule R S) (⊥ : Submodule R S)

/-- Right ordered cross-effects occupy the second resolved source axis. -/
def deningerResolvedCrossEffectRightAxis
    (R S : Type*) [CommRing R] [AddCommGroup S] [Module R S] :
    Submodule R (S × S) :=
  Submodule.prod (⊥ : Submodule R S) (⊤ : Submodule R S)

/-- The two ordered source axes are genuinely disjoint before codiagonalization. -/
theorem deningerResolvedCrossEffectAxes_disjoint
    (R S : Type*) [CommRing R] [AddCommGroup S] [Module R S] :
    Disjoint (deningerResolvedCrossEffectLeftAxis R S)
      (deningerResolvedCrossEffectRightAxis R S) := by
  rw [Submodule.disjoint_def]
  intro z hzLeft hzRight
  rcases z with ⟨zLeft, zRight⟩
  have hzLeftZero : zLeft = 0 := by
    simpa [deningerResolvedCrossEffectRightAxis] using hzRight
  have hzRightZero : zRight = 0 := by
    simpa [deningerResolvedCrossEffectLeftAxis] using hzLeft
  subst zLeft
  subst zRight
  rfl

/-- Every resolved value is the sum of its two source-forced ordered channels. -/
theorem deningerResolvedAlternatingCrossEffect_eq_left_add_right
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x y : Q × P) :
    deningerResolvedAlternatingCrossEffect B x y =
      (B x.1 y.2, 0) + (0, -B y.1 x.2) := by
  apply Prod.ext <;> simp

/-- First ordered term lands in the canonical left source grade. -/
theorem deningerResolvedAlternatingCrossEffect_left_mem
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x y : Q × P) :
    (B x.1 y.2, 0) ∈ deningerResolvedCrossEffectLeftAxis R S := by
  simp [deningerResolvedCrossEffectLeftAxis]

/-- Second ordered term lands in the canonical right source grade. -/
theorem deningerResolvedAlternatingCrossEffect_right_mem
    {R Q P S : Type*}
    [CommRing R]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup P] [Module R P]
    [AddCommGroup S] [Module R S]
    (B : Q →ₗ[R] P →ₗ[R] S)
    (x y : Q × P) :
    (0, -B y.1 x.2) ∈ deningerResolvedCrossEffectRightAxis R S := by
  simp [deningerResolvedCrossEffectRightAxis]

/-- Local resolved cup on the actual analytic Calderón--Witt source. -/
def deningerCalderonWittResolvedCup (p : Nat.Primes) :
    DeningerCalderonWittDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittDegreeOne p →ₗ[ℂ]
        (DeningerCalderonWittDegreeTwo p ×
          DeningerCalderonWittDegreeTwo p) :=
  deningerResolvedAlternatingCrossEffect
    (deningerMeyerCalderonGaugePacketCrossEffect p)

@[simp]
theorem deningerCalderonWittResolvedCup_codiagonal
    (p : Nat.Primes)
    (x y : DeningerCalderonWittDegreeOne p) :
    resolvedDefectCodiagonal (R := ℂ)
        (deningerCalderonWittResolvedCup p x y) =
      deningerCalderonWittCup p x y := by
  exact deningerResolvedAlternatingCrossEffect_codiagonal
    (deningerMeyerCalderonGaugePacketCrossEffect p) x y

/-- Local resolved cup restricted to the cofinal algebraic rational-Witt source. -/
def deningerCalderonWittAlgebraicResolvedCup (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
      DeningerCalderonWittAlgebraicDegreeOne p →ₗ[ℂ]
        (DeningerCalderonWittAlgebraicDegreeTwo p ×
          DeningerCalderonWittAlgebraicDegreeTwo p) :=
  deningerResolvedAlternatingCrossEffect
    (deningerMeyerCalderonWittAlgebraicCrossEffect p)

@[simp]
theorem deningerCalderonWittAlgebraicResolvedCup_codiagonal
    (p : Nat.Primes)
    (x y : DeningerCalderonWittAlgebraicDegreeOne p) :
    resolvedDefectCodiagonal (R := ℂ)
        (deningerCalderonWittAlgebraicResolvedCup p x y) =
      deningerCalderonWittAlgebraicCup p x y := by
  exact deningerResolvedAlternatingCrossEffect_codiagonal
    (deningerMeyerCalderonWittAlgebraicCrossEffect p) x y

/-- Canonical degree-one source point carrying both actual Calderón and algebraic Wrat legs. -/
def deningerCalderonWittAlgebraicResolvedUnit
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeOne p :=
  (deningerCalderonWittUnitDefect p,
    deningerCalderonWittAlgebraicUnitPacket p)

/-- Cross-effect amplitude of the canonical resolved source point. -/
def deningerCalderonWittAlgebraicResolvedUnitAmplitude
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicDegreeTwo p :=
  deningerMeyerCalderonWittAlgebraicCrossEffect p
    (deningerCalderonWittUnitDefect p)
    (deningerCalderonWittAlgebraicUnitPacket p)

/-- Source faithfulness: the canonical algebraic ordered cross-effect is nonzero at every prime. -/
theorem deningerCalderonWittAlgebraicResolvedUnitAmplitude_ne_zero
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicResolvedUnitAmplitude p ≠ 0 := by
  intro hzero
  have hval := congrArg Subtype.val hzero
  have hpacket :
      (deningerCalderonWittAlgebraicUnitPacket p :
        DeningerPrimeFinitePacketGaugeComplexHaarL2 p) = 0 := by
    apply
      (deningerMeyerCalderonGaugePacketCrossEffect_unit_injective p)
    simpa [deningerCalderonWittAlgebraicResolvedUnitAmplitude] using hval
  exact deningerCalderonWittUnitPacket_ne_zero p
    (by simpa using hpacket)

/-- The canonical resolved self-cup is the antidiagonal of its nonzero source amplitude. -/
theorem deningerCalderonWittAlgebraicResolvedUnit_self_eq_antidiagonal
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicResolvedCup p
        (deningerCalderonWittAlgebraicResolvedUnit p)
        (deningerCalderonWittAlgebraicResolvedUnit p) =
      resolvedDefectAntidiagonal (R := ℂ)
        (deningerCalderonWittAlgebraicResolvedUnitAmplitude p) := by
  rfl

/-- Ordinary source multiplication kills the canonical self-boundary by alternation. -/
@[simp]
theorem deningerCalderonWittAlgebraicResolvedUnit_cup_self
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicCup p
        (deningerCalderonWittAlgebraicResolvedUnit p)
        (deningerCalderonWittAlgebraicResolvedUnit p) = 0 := by
  change
    deningerCalderonWittAlgebraicResolvedUnitAmplitude p -
        deningerCalderonWittAlgebraicResolvedUnitAmplitude p = 0
  exact sub_self _

/-- The resolved source self-boundary is nonzero although its ordinary cup is zero. -/
theorem deningerCalderonWittAlgebraicResolvedUnit_self_ne_zero
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicResolvedCup p
        (deningerCalderonWittAlgebraicResolvedUnit p)
        (deningerCalderonWittAlgebraicResolvedUnit p) ≠ 0 := by
  rw [deningerCalderonWittAlgebraicResolvedUnit_self_eq_antidiagonal]
  intro hzero
  have hfirst := congrArg Prod.fst hzero
  exact deningerCalderonWittAlgebraicResolvedUnitAmplitude_ne_zero p hfirst

/-- One-prime embedding of the canonical amplitude in the all-prime algebraic source. -/
def deningerCalderonWittAlgebraicGlobalResolvedUnitAmplitude
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  DirectSum.lof ℂ Nat.Primes
    DeningerCalderonWittAlgebraicDegreeTwo p
    (deningerCalderonWittAlgebraicResolvedUnitAmplitude p)

/-- Canonical all-prime finite-support resolved boundary forced by one arithmetic prime. -/
def deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary
    (p : Nat.Primes) :
    DeningerCalderonWittAlgebraicGlobalDegreeTwo ×
      DeningerCalderonWittAlgebraicGlobalDegreeTwo :=
  resolvedDefectAntidiagonal (R := ℂ)
    (deningerCalderonWittAlgebraicGlobalResolvedUnitAmplitude p)

/-- Source-selected resolved sector generated by one canonical arithmetic-prime boundary. -/
def deningerCalderonWittAlgebraicGlobalResolvedUnitSector
    (p : Nat.Primes) :
    Submodule ℂ
      (DeningerCalderonWittAlgebraicGlobalDegreeTwo ×
        DeningerCalderonWittAlgebraicGlobalDegreeTwo) :=
  Submodule.span ℂ
    {deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary p}

/-- The all-prime resolved unit boundary is nonzero before the source augmentation. -/
theorem deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary_ne_zero
    (p : Nat.Primes) :
    deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary p ≠ 0 := by
  intro hzero
  have hfirst :
      deningerCalderonWittAlgebraicGlobalResolvedUnitAmplitude p = 0 := by
    simpa [deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary,
      resolvedDefectAntidiagonal] using congrArg Prod.fst hzero
  have hcomponent := congrArg
    (DirectSum.component ℂ Nat.Primes
      DeningerCalderonWittAlgebraicDegreeTwo p) hfirst
  simp [deningerCalderonWittAlgebraicGlobalResolvedUnitAmplitude] at hcomponent
  exact deningerCalderonWittAlgebraicResolvedUnitAmplitude_ne_zero p hcomponent

/-- Every post-cup observation loses the canonical nonzero all-prime resolved boundary. -/
@[simp]
theorem deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary_codiagonal
    (p : Nat.Primes) :
    resolvedDefectCodiagonal (R := ℂ)
        (deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary p) = 0 := by
  simp [deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary,
    resolvedDefectCodiagonal, resolvedDefectAntidiagonal]

/-- **Concrete source no-go.**  No linear observer applied after the ordinary source cup can be
conservative on the canonical nonzero resolved Calderón--Witt boundary sector. -/
theorem deningerCalderonWitt_no_codiagonalObserver_conservativeOn_resolvedUnitSector
    (p : Nat.Primes)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (observe : DeningerCalderonWittAlgebraicGlobalDegreeTwo →ₗ[ℂ] W) :
    ¬ IsConservativeOn
      (observe.comp
        (resolvedDefectCodiagonal
          (R := ℂ)
          (Z := DeningerCalderonWittAlgebraicGlobalDegreeTwo)))
      (deningerCalderonWittAlgebraicGlobalResolvedUnitSector p) := by
  intro hconservative
  let boundary :=
    deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary p
  have hsector :
      boundary ∈ deningerCalderonWittAlgebraicGlobalResolvedUnitSector p := by
    exact Submodule.subset_span (Set.mem_singleton boundary)
  have hkernel :
      boundary ∈ LinearMap.ker
        (observe.comp
          (resolvedDefectCodiagonal
            (R := ℂ)
            (Z := DeningerCalderonWittAlgebraicGlobalDegreeTwo))) := by
    change observe (resolvedDefectCodiagonal (R := ℂ) boundary) = 0
    rw [show boundary =
        deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary p from rfl,
      deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary_codiagonal,
      map_zero]
  have hzero :=
    (Submodule.disjoint_def.mp hconservative)
      boundary hsector hkernel
  exact deningerCalderonWittAlgebraicGlobalResolvedUnitBoundary_ne_zero p hzero

end

end RHTower
