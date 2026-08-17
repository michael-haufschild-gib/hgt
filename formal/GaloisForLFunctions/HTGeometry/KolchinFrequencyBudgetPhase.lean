import GaloisForLFunctions.HTGeometry.ShortExactRankConservation
import GaloisForLFunctions.HTGeometry.CoveringDimensionShrinking
import GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier
import GaloisForLFunctions.HTGeometry.GaussPairedChannelSchattenDepth

/-!
# Singular and nonautonomous Kolchin-frequency budgets

This module assembles the checked short-exact rank, arithmetic-complement, covering-dimension, and
Gauss-residue cores.  Ritt--Kolchin finite-capacity, Bohr-hull/Pontryagin identification, and the
operator-analytic weak-Schatten endpoint are represented by explicit inputs rather than axioms.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Submodule

universe u

/-- Exact analytic input remaining after the finite-capacity and inverse-limit arguments for a
singular autonomous ADE. -/
structure SingularKolchinFrequencyInput where
  frequencyRank : ℕ
  hullCoverDimension : ℕ
  kolchinCapacity : ℕ
  rank_eq_coverDimension : frequencyRank = hullCoverDimension
  coverDimension_le : hullCoverDimension ≤ 2 * kolchinCapacity

/-- Singular implicit equations have frequency rank at most twice their Kolchin jet capacity. -/
theorem singularKolchin_frequencyRank_le
    (input : SingularKolchinFrequencyInput) :
    input.frequencyRank ≤ 2 * input.kolchinCapacity := by
  rw [input.rank_eq_coverDimension]
  exact input.coverDimension_le

/-- Every continuous equivariant compact observable inherits the same singular Kolchin budget. -/
theorem singularKolchin_observableFrequencyRank_le
    (input : SingularKolchinFrequencyInput)
    (observableRank : ℕ) (hfactor : observableRank ≤ input.frequencyRank) :
    observableRank ≤ 2 * input.kolchinCapacity :=
  hfactor.trans (singularKolchin_frequencyRank_le input)

/-- Retaining `π(N)` independent prime frequencies forces the exact half-rank Kolchin floor. -/
theorem singularKolchin_primeCapacity_floor
    (input : SingularKolchinFrequencyInput) (N : ℕ)
    (hprime : Nat.primeCounting N ≤ input.frequencyRank) :
    (Nat.primeCounting N + 1) / 2 ≤ input.kolchinCapacity := by
  have h := hprime.trans (singularKolchin_frequencyRank_le input)
  omega

/-- The exact coefficient/state rational-rank split obtained from the Pontryagin-dual short exact
sequence after tensoring with `ℚ`. -/
theorem nonautonomous_frequencyRank_exactSplit
    {Coefficient Joint State : Type u}
    [AddCommGroup Coefficient] [Module ℚ Coefficient]
    [AddCommGroup Joint] [Module ℚ Joint]
    [AddCommGroup State] [Module ℚ State]
    [FiniteDimensional ℚ Joint]
    (includeCoefficient : Coefficient →ₗ[ℚ] Joint)
    (projectState : Joint →ₗ[ℚ] State)
    (hinjective : Function.Injective includeCoefficient)
    (hsurjective : Function.Surjective projectState)
    (hexact : LinearMap.range includeCoefficient = LinearMap.ker projectState) :
    finrank ℚ Coefficient + finrank ℚ State = finrank ℚ Joint :=
  HTGeometry.finrank_add_of_shortExact includeCoefficient projectState
    hinjective hsurjective hexact

/-- A finite relative Kolchin state capacity turns exact frequency conservation into the
nonautonomous coefficient/state budget. -/
theorem nonautonomous_frequencyRank_le_coefficient_add_twiceCapacity
    {Coefficient Joint State : Type u}
    [AddCommGroup Coefficient] [Module ℚ Coefficient]
    [AddCommGroup Joint] [Module ℚ Joint]
    [AddCommGroup State] [Module ℚ State]
    [FiniteDimensional ℚ Joint]
    (includeCoefficient : Coefficient →ₗ[ℚ] Joint)
    (projectState : Joint →ₗ[ℚ] State)
    (hinjective : Function.Injective includeCoefficient)
    (hsurjective : Function.Surjective projectState)
    (hexact : LinearMap.range includeCoefficient = LinearMap.ker projectState)
    (kappa : ℕ) (hstate : finrank ℚ State ≤ 2 * kappa) :
    finrank ℚ Joint ≤ finrank ℚ Coefficient + 2 * kappa := by
  have hsplit := nonautonomous_frequencyRank_exactSplit
    includeCoefficient projectState hinjective hsurjective hexact
  omega

/-- Exact arithmetic-complement budget for a prime module inside a nonautonomous carrier. -/
theorem nonautonomous_primeComplement_budget
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (N kappa : ℕ) (V coefficientModule : Submodule ℚ E)
    (hprime : finrank ℚ ↥V = Nat.primeCounting N)
    (hstate : finrank ℚ
      (↥V ⧸ Submodule.comap V.subtype coefficientModule) ≤ 2 * kappa) :
    Nat.primeCounting N ≤
      finrank ℚ ↥(V ⊓ coefficientModule) + 2 * kappa :=
  GaloisForLFunctions.RHTower.primeCounting_le_coefficientRank_add_twice_stateCapacity
    N kappa V coefficientModule hprime hstate

/-- A coefficient hull of rank at most `r∞` leaves the remaining prime directions to the relative
Kolchin state carrier. -/
theorem nonautonomous_gammaCoefficient_capacity_floor
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (N kappa rInfinity : ℕ) (V coefficientModule : Submodule ℚ E)
    (hprime : finrank ℚ ↥V = Nat.primeCounting N)
    (hstate : finrank ℚ
      (↥V ⧸ Submodule.comap V.subtype coefficientModule) ≤ 2 * kappa)
    (hcoeff : finrank ℚ ↥(V ⊓ coefficientModule) ≤ rInfinity) :
    (Nat.primeCounting N - rInfinity + 1) / 2 ≤ kappa := by
  have hbudget := nonautonomous_primeComplement_budget
    N kappa V coefficientModule hprime hstate
  omega

/-- The canonical aperture module removes the abstract prime-rank premise from the nonautonomous
budget: its rational rank is exactly `π(N)`.  The displayed quotient is the arithmetic complement
for `V = ⊤` inside the aperture module. -/
theorem primeAperture_nonautonomous_primeComplement_budget
    (N kappa : ℕ)
    (coefficientModule :
      Submodule ℚ (GaloisForLFunctions.primeApertureCharacterModule N))
    (hstate :
      let V : Submodule ℚ
          (GaloisForLFunctions.primeApertureCharacterModule N) := ⊤
      finrank ℚ (↥V ⧸ Submodule.comap V.subtype coefficientModule) ≤ 2 * kappa) :
    Nat.primeCounting N ≤ finrank ℚ ↥coefficientModule + 2 * kappa := by
  letI : Module.Finite ℚ
      (GaloisForLFunctions.primeApertureCharacterModule N) := by
    unfold GaloisForLFunctions.primeApertureCharacterModule
      GaloisForLFunctions.primeLogSpan
    exact Module.Finite.span_of_finite ℚ (Set.finite_range _)
  dsimp only at hstate
  have hbudget := nonautonomous_primeComplement_budget
    N kappa
    (⊤ : Submodule ℚ (GaloisForLFunctions.primeApertureCharacterModule N))
    coefficientModule
    (by simp [GaloisForLFunctions.primeApertureCharacterModule_finrank])
    hstate
  rw [inf_eq_right.mpr le_top] at hbudget
  exact hbudget

/-- For the canonical prime-aperture source, a coefficient hull of rank at most `rInfinity`
forces the exact residual half-rank Kolchin-capacity floor without a supplied prime-rank equality. -/
theorem primeAperture_nonautonomous_gammaCoefficient_capacity_floor
    (N kappa rInfinity : ℕ)
    (coefficientModule :
      Submodule ℚ (GaloisForLFunctions.primeApertureCharacterModule N))
    (hstate :
      let V : Submodule ℚ
          (GaloisForLFunctions.primeApertureCharacterModule N) := ⊤
      finrank ℚ (↥V ⧸ Submodule.comap V.subtype coefficientModule) ≤ 2 * kappa)
    (hcoeff : finrank ℚ ↥coefficientModule ≤ rInfinity) :
    (Nat.primeCounting N - rInfinity + 1) / 2 ≤ kappa := by
  have hbudget := primeAperture_nonautonomous_primeComplement_budget
    N kappa coefficientModule hstate
  omega

/-- Explicit operator-analytic endpoint input for the direct-sum Gauss channel.  The arithmetic
residue and cofinal depth are proved internally; only membership in weak/strong Schatten ideals is
supplied by the named Connes--Consani/Dixmier-trace parent theorem. -/
structure GaussChannelSchattenEndpointInput
    (J : Type*) [Fintype J] (m : ℕ) (prime : J → Nat.Primes) where
  weakEndpoint : Prop
  strongEndpoint : Prop
  schattenMembership : ℕ → Prop
  endpointResidue : ℝ
  weakEndpoint_holds : weakEndpoint
  strongEndpoint_fails : ¬ strongEndpoint
  aboveCritical : ∀ q, 2 * m < q → schattenMembership q
  atOrBelowCritical : ∀ q, q ≤ 2 * m → ¬ schattenMembership q
  residue_exact : endpointResidue =
    GaloisForLFunctions.RHTower.gaussPairedChannelResidue m prime

/-- Complete direct-sum endpoint law: positive arithmetic residue, weak but not strong membership
at `2m`, and ordinary Schatten membership exactly above `2m`. -/
theorem gaussChannelSchatten_exactEndpoint
    {J : Type*} [Fintype J] [Nonempty J]
    {m : ℕ} (hm : 1 ≤ m) (prime : J → Nat.Primes)
    (input : GaussChannelSchattenEndpointInput J m prime) :
    0 < input.endpointResidue ∧
      input.weakEndpoint ∧ ¬ input.strongEndpoint ∧
      (∀ q, input.schattenMembership q ↔ 2 * m < q) := by
  refine ⟨?_, input.weakEndpoint_holds, input.strongEndpoint_fails, ?_⟩
  · rw [input.residue_exact]
    exact GaloisForLFunctions.RHTower.gaussPairedChannelResidue_pos hm prime
  · intro q
    constructor
    · intro hq
      by_contra hnot
      exact input.atOrBelowCritical q (by omega) hq
    · exact input.aboveCritical q

/-- The exact Gauss critical depth is cofinal, so neither one fixed Schatten exponent nor one fixed
integer regularization order can contain every prime cutoff. -/
theorem gaussChannelSchatten_cofinalDepth :
    Filter.Tendsto
        GaloisForLFunctions.RHTower.gaussPairedCriticalDepth
        Filter.atTop Filter.atTop ∧
      (∀ q : ℝ, ∃ N, q <
        GaloisForLFunctions.RHTower.gaussPairedCriticalDepth N) ∧
      (∀ r : ℕ, ∃ N, r ≤
        GaloisForLFunctions.RHTower.gaussPairedCriticalDepth N) :=
  ⟨GaloisForLFunctions.RHTower.tendsto_gaussPairedCriticalDepth,
    GaloisForLFunctions.RHTower.exists_gaussPairedCriticalDepth_gt,
    GaloisForLFunctions.RHTower.exists_gaussPairedCriticalDepth_ge⟩

end GaloisForLFunctions.HTGeometry
