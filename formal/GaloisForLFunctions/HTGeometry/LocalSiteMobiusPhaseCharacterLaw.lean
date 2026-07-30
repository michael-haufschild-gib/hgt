import GaloisForLFunctions.HTGeometry.LocalSpectralJetCausality
import GaloisForLFunctions.HTGeometry.SpectralCharacterDimensionBridgeLaw

/-!
# Local Möbius observers are projective phase characters

Every nonempty Boolean site contrast has total charge zero. It is therefore
one literal character of the projective spectral torus. Pairing that
character with any spectrum reproduces the original site contrast exactly.
The integer phase character and its rational temporal-dimension coordinate
are the same character under scalar extension.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational coefficient function of a Boolean site-Möbius contrast. -/
def siteMobiusRationalCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V) :
    (∀ v, A v) → ℚ :=
  fun config =>
    ∑ d ∈ sites.powerset,
      if dependentUpdateOnFinset x alternative (sites \ d) = config
      then (-1 : ℚ) ^ d.card else 0

/-- Every nonempty Boolean Möbius contrast has zero rational total charge. -/
theorem sum_siteMobiusRationalCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) {sites : Finset V}
    (hsites : sites.Nonempty) :
    ∑ config, siteMobiusRationalCoefficient x alternative sites config = 0 := by
  rw [show (∑ config, siteMobiusRationalCoefficient x alternative sites config) =
      ∑ d ∈ sites.powerset, (-1 : ℚ) ^ d.card by
    simp [siteMobiusRationalCoefficient, Finset.sum_comm]]
  calc
    (∑ d ∈ sites.powerset, (-1 : ℚ) ^ d.card) =
        ∏ _p ∈ sites, ((1 : ℚ) - 1) := by
      simpa using
        (Finset.prod_sub (fun _ : V => (1 : ℚ))
          (fun _ : V => (1 : ℚ)) sites).symm
    _ = 0 := by
      rcases hsites with ⟨p, hp⟩
      exact Finset.prod_eq_zero hp (by ring)

/-- A nonempty local site contrast as a rational projective character. -/
def siteMobiusProjectiveRationalCharacter
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty) :
    ProjectiveRationalCharacter (∀ v, A v) :=
  ⟨siteMobiusRationalCoefficient x alternative sites,
    sum_siteMobiusRationalCoefficient x alternative hsites⟩

/-- Pairing the rational projective character with a complex spectrum is
exactly its Boolean site contrast. -/
theorem siteMobiusProjectiveRationalCharacter_evaluate
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (energy : (∀ v, A v) → ℂ) :
    ∑ config,
        ((siteMobiusProjectiveRationalCharacter
          x alternative sites hsites).1 config : ℂ) * energy config =
      dependentHigherCoordinateContrast x alternative sites energy := by
  simp only [siteMobiusProjectiveRationalCharacter,
    siteMobiusRationalCoefficient,
    dependentHigherCoordinateContrast, finsetMobiusResponse]
  push_cast
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Fintype.sum_eq_single
    (dependentUpdateOnFinset x alternative (sites \ d))]
  · simp
  · intro config hconfig
    simp [hconfig.symm]

/-- Integer coefficient function of a Boolean site-Möbius contrast. -/
def siteMobiusIntegerCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V) :
    (∀ v, A v) → ℤ :=
  fun config =>
    ∑ d ∈ sites.powerset,
      if dependentUpdateOnFinset x alternative (sites \ d) = config
      then (-1 : ℤ) ^ d.card else 0

/-- Finite-support integer form of the local Möbius character. -/
def siteMobiusIntegerFinsupp
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V) :
    (∀ v, A v) →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm
    (siteMobiusIntegerCoefficient x alternative sites)

/-- Every nonempty Boolean Möbius contrast has zero integer total charge. -/
theorem integerCharacterCharge_siteMobiusIntegerFinsupp
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) {sites : Finset V}
    (hsites : sites.Nonempty) :
    integerCharacterCharge (∀ v, A v)
        (siteMobiusIntegerFinsupp x alternative sites) = 0 := by
  change
    (Finsupp.equivFunOnFinite.symm
      (siteMobiusIntegerCoefficient x alternative sites)).sum
        (fun _ m => m) = 0
  rw [Finsupp.equivFunOnFinite_symm_sum]
  rw [show
      (∑ config, siteMobiusIntegerCoefficient
        x alternative sites config) =
        ∑ d ∈ sites.powerset, (-1 : ℤ) ^ d.card by
    simp [siteMobiusIntegerCoefficient, Finset.sum_comm]]
  calc
    (∑ d ∈ sites.powerset, (-1 : ℤ) ^ d.card) =
        ∏ _p ∈ sites, ((1 : ℤ) - 1) := by
      simpa using
        (Finset.prod_sub (fun _ : V => (1 : ℤ))
          (fun _ : V => (1 : ℤ)) sites).symm
    _ = 0 := by
      rcases hsites with ⟨p, hp⟩
      exact Finset.prod_eq_zero hp (by ring)

/-- A nonempty local site contrast as an integral projective phase
character. -/
def siteMobiusProjectiveCharacter
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty) :
    ProjectiveCharacter (∀ v, A v) :=
  ⟨siteMobiusIntegerFinsupp x alternative sites,
    integerCharacterCharge_siteMobiusIntegerFinsupp
      x alternative hsites⟩

/-- Pairing the integral projective character with a complex spectrum is
exactly its Boolean site contrast. -/
theorem siteMobiusProjectiveCharacter_evaluate
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty)
    (energy : (∀ v, A v) → ℂ) :
    (siteMobiusProjectiveCharacter
      x alternative sites hsites).1.sum
        (fun config m => (m : ℂ) * energy config) =
      dependentHigherCoordinateContrast x alternative sites energy := by
  change
    (Finsupp.equivFunOnFinite.symm
      (siteMobiusIntegerCoefficient x alternative sites)).sum
        (fun config m => (m : ℂ) * energy config) =
      ∑ d ∈ sites.powerset, (-1 : ℂ) ^ d.card *
        energy (dependentUpdateOnFinset x alternative (sites \ d))
  rw [Finsupp.sum_fintype]
  · change
      (∑ config,
        (siteMobiusIntegerCoefficient x alternative sites config : ℂ) *
          energy config) =
        ∑ d ∈ sites.powerset, (-1 : ℂ) ^ d.card *
          energy (dependentUpdateOnFinset x alternative (sites \ d))
    simp only [siteMobiusIntegerCoefficient]
    push_cast
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Fintype.sum_eq_single
      (dependentUpdateOnFinset x alternative (sites \ d))]
    · simp
    · intro config hconfig
      simp [hconfig.symm]
  · intro config
    norm_num

/-- Integer and rational presentations of a local observer are the same
projective character under scalar extension. -/
theorem projectiveCharacterToRational_siteMobiusProjectiveCharacter
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)]
    [∀ v, DecidableEq (A v)]
    (x alternative : ∀ v, A v) (sites : Finset V)
    (hsites : sites.Nonempty) :
    projectiveCharacterToRational
        (siteMobiusProjectiveCharacter
          x alternative sites hsites) =
      siteMobiusProjectiveRationalCharacter
        x alternative sites hsites := by
  ext config
  change
    (siteMobiusIntegerCoefficient
      x alternative sites config : ℚ) =
      siteMobiusRationalCoefficient
        x alternative sites config
  simp only [siteMobiusIntegerCoefficient,
    siteMobiusRationalCoefficient]
  push_cast
  rfl

end

end GaloisForLFunctions.HTGeometry
