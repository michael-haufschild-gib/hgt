import GaloisForLFunctions.RHTower.Suzuki.SuzukiCofinalPositiveFinitePartNoGo
import GaloisForLFunctions.RHTower.VonMangoldtGammaBoundaryDisplacementThreshold

/-!
# No positive finite domain contains a completed Suzuki Mellin profile

The preceding cofinal obstruction used the order unit.  This file removes that premise.  For any
nonnegative profile `f`, positivity of a finite-valued linear functional containing `f` and all
finite truncations forces the weighted profile mass to be summable: positivity of
`f - f|_F` bounds every finite weighted sum by the single finite value at `f`.

For the critical Suzuki sharp source, transport from critical exponent `1/2` to an actual Mellin
abscissa `sigma` multiplies the sharp mass by

`exp (-(sigma - 1/2) log p)`.

The resulting mass is exactly the first-prime Euler coefficient

`Lambda(p) exp (-sigma log p)`.

The corpus displacement-threshold theorem therefore gives the sharp ordinary-summability law

`Summable <-> 1 < sigma`.

Consequently no positive finite part on any linear domain can contain even one critical-strip
Mellin profile while preserving its finite Suzuki cutoff values.  No order unit, continuity,
normality, topology, or regulator hypothesis is used.  Every exact linear extension on such a
domain is moreover unbounded below on the domain's full nonnegative cone.

This kills positive-semifinite realizations of the RH-bearing completed profile itself.  A survivor
must be signed and may assert a floor only on a non-conic, source-normalized test family.
-/

namespace RHTower

noncomputable section

/-! ## Universal positive-profile obstruction -/

section Universal

variable {ι : Type*} [DecidableEq ι]

/-- Restriction of a coordinate profile to a finite set. -/
def finiteCoordinateTruncation (f : ι → ℝ) (s : Finset ι) : ι → ℝ :=
  fun i => if i ∈ s then f i else 0

theorem finiteCoordinateTruncation_le
    {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) (s : Finset ι) (i : ι) :
    finiteCoordinateTruncation f s i ≤ f i := by
  by_cases hi : i ∈ s <;> simp [finiteCoordinateTruncation, hi, hf i]

/-- **Universal profile obstruction.**  A positive finite-valued linear functional cannot
contain a nonnegative profile of nonsummable weighted mass while preserving every finite profile
cutoff.  Unlike the order-unit obstruction, the domain need not contain the constant function. -/
theorem not_exists_positive_extension_containing_nonsummable_profile
    {w f : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i)
    (hnotsum : ¬ Summable (fun i => w i * f i))
    (D : Submodule ℝ (ι → ℝ)) (hfD : f ∈ D)
    (htrunc : ∀ s : Finset ι, finiteCoordinateTruncation f s ∈ D) :
    ¬ ∃ Φ : D →ₗ[ℝ] ℝ,
      (∀ s : Finset ι,
        Φ ⟨finiteCoordinateTruncation f s, htrunc s⟩ =
          ∑ i ∈ s, w i * f i) ∧
      (∀ g : D, (∀ i, 0 ≤ g.1 i) → 0 ≤ Φ g) := by
  rintro ⟨Φ, hext, hpos⟩
  apply hnotsum
  apply summable_of_sum_le (fun i => mul_nonneg (hw i) (hf i))
  intro s
  let fD : D := ⟨f, hfD⟩
  let truncD : D := ⟨finiteCoordinateTruncation f s, htrunc s⟩
  have hnonneg : ∀ i, 0 ≤ (fD - truncD).1 i := by
    intro i
    change 0 ≤ f i - finiteCoordinateTruncation f s i
    exact sub_nonneg.mpr (finiteCoordinateTruncation_le hf s i)
  have h := hpos (fD - truncD) hnonneg
  rw [map_sub, hext s] at h
  exact sub_nonneg.mp h

/-- A finite lower floor on the entire nonnegative cone would force positivity by scaling.
Therefore every exact extension containing a nonsummable positive profile is unbounded below on
that cone, without an order-unit premise. -/
theorem profile_extension_unboundedBelow_on_coordinate_domain
    {w f : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i)
    (hnotsum : ¬ Summable (fun i => w i * f i))
    (D : Submodule ℝ (ι → ℝ)) (hfD : f ∈ D)
    (htrunc : ∀ s : Finset ι, finiteCoordinateTruncation f s ∈ D)
    (Φ : D →ₗ[ℝ] ℝ)
    (hext : ∀ s : Finset ι,
      Φ ⟨finiteCoordinateTruncation f s, htrunc s⟩ =
        ∑ i ∈ s, w i * f i)
    (L : ℝ) :
    ∃ g : D, (∀ i, 0 ≤ g.1 i) ∧ Φ g < L := by
  by_contra h
  push Not at h
  have hpos := positiveOnCoordinateSubmoduleCone_of_lowerBounded D Φ ⟨L, h⟩
  exact not_exists_positive_extension_containing_nonsummable_profile
    hw hf hnotsum D hfD htrunc ⟨Φ, hext, hpos⟩

end Universal

/-! ## Exact critical-Suzuki Mellin threshold -/

/-- Positive radial profile transporting the critical Suzuki exponent `1/2` to the actual Mellin
abscissa `sigma`. -/
def suzukiCriticalMellinProfile (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-(sigma - 1 / 2) * Real.log (p : ℝ))

/-- Critical Suzuki sharp mass after transport to Mellin abscissa `sigma`. -/
def suzukiCriticalMellinWeightedPrimeMass
    (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  suzukiCriticalSharpPrimeMass p * suzukiCriticalMellinProfile sigma p

/-- Critical-profile transport is exactly the existing Gamma--Bianchi displacement
`x = sigma - 1`. -/
theorem suzukiCriticalMellinWeightedPrimeMass_eq_rootedBianchi
    (sigma : ℝ) (p : Nat.Primes) :
    suzukiCriticalMellinWeightedPrimeMass sigma p =
      suzukiRootedBianchiPrimeMassAt (sigma - 1) p := by
  rw [suzukiCriticalMellinWeightedPrimeMass, suzukiCriticalSharpPrimeMass,
    suzukiCriticalEntryWallBareAmplitude_zero_eq_rootedBianchiAmplitude,
    suzukiCriticalRootedBianchiPrimeAmplitude_sq,
    ← suzukiRootedBianchiPrimeMassAt_neg_half]
  unfold suzukiCriticalMellinProfile suzukiRootedBianchiPrimeMassAt
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The transported sharp mass is literally the first-prime von-Mangoldt Mellin coefficient. -/
theorem suzukiCriticalMellinWeightedPrimeMass_eq_vonMangoldt
    (sigma : ℝ) (p : Nat.Primes) :
    suzukiCriticalMellinWeightedPrimeMass sigma p =
      ArithmeticFunction.vonMangoldt p *
        Real.exp (-sigma * Real.log (p : ℝ)) := by
  rw [suzukiCriticalMellinWeightedPrimeMass_eq_rootedBianchi,
    suzukiRootedBianchiPrimeMassAt, div_eq_mul_inv]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hinv : (p : ℝ)⁻¹ = Real.exp (-Real.log (p : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hp]
  rw [hinv, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Public square connector between the uniquely renormalized Gamma boundary coordinate and its
raw rooted-Bianchi mass. -/
theorem vonMangoldtGammaRenormalizedBoundaryCoordinate_sq_eq_rootedBianchiPrimeMassAt
    (x : ℝ) (p : Nat.Primes) :
    vonMangoldtGammaRenormalizedBoundaryCoordinate x p ^ (2 : ℕ) =
      suzukiRootedBianchiPrimeMassAt x p := by
  have hp2 : 2 ≤ (p : ℕ) := p.prop.two_le
  have hnonneg : 0 ≤ suzukiRootedBianchiPrimeMassAt x p := by
    rw [suzukiRootedBianchiPrimeMassAt]
    exact mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
      (Real.exp_pos _).le
  rw [vonMangoldtGammaRenormalizedBoundaryCoordinate_eq hp2,
    Real.sq_sqrt]
  · rfl
  · simpa only [suzukiRootedBianchiPrimeMassAt] using hnonneg

/-- **Sharp Suzuki--Euler abscissa law.**  The transported critical sharp mass has an ordinary
cofinal sum exactly on the Euler half-plane `Re s > 1`. -/
theorem summable_suzukiCriticalMellinWeightedPrimeMass_iff (sigma : ℝ) :
    Summable (suzukiCriticalMellinWeightedPrimeMass sigma) ↔ 1 < sigma := by
  rw [show Summable (suzukiCriticalMellinWeightedPrimeMass sigma) ↔
      Summable (fun p : Nat.Primes =>
        vonMangoldtGammaRenormalizedBoundaryCoordinate (sigma - 1) p ^ (2 : ℕ)) by
    apply summable_congr
    intro p
    rw [suzukiCriticalMellinWeightedPrimeMass_eq_rootedBianchi,
      vonMangoldtGammaRenormalizedBoundaryCoordinate_sq_eq_rootedBianchiPrimeMassAt]]
  rw [summable_sq_vonMangoldtGammaRenormalizedBoundaryCoordinate_prime_iff]
  constructor <;> intro h <;> linarith

theorem suzukiCriticalMellinProfile_nonneg (sigma : ℝ) (p : Nat.Primes) :
    0 ≤ suzukiCriticalMellinProfile sigma p :=
  (Real.exp_pos _).le

theorem not_summable_suzukiCriticalMellinWeightedPrimeMass_of_le_one
    {sigma : ℝ} (hsigma : sigma ≤ 1) :
    ¬ Summable (suzukiCriticalMellinWeightedPrimeMass sigma) := by
  intro hsum
  have hgt := (summable_suzukiCriticalMellinWeightedPrimeMass_iff sigma).1 hsum
  linarith

/-! ## No positive or globally semibounded completed profile domain -/

/-- **Domain-independent positive Suzuki no-go.**  At or left of the Euler abscissa, no positive
finite-valued extension on any linear domain containing the Mellin profile and all of its finite
truncations can preserve the exact finite Suzuki values.  The domain need not be unital. -/
theorem not_exists_positive_suzukiCriticalMellinProfile_extension_of_le_one
    {sigma : ℝ} (hsigma : sigma ≤ 1)
    (D : Submodule ℝ (Nat.Primes → ℝ))
    (hprofile : suzukiCriticalMellinProfile sigma ∈ D)
    (htrunc : ∀ s : Finset Nat.Primes,
      finiteCoordinateTruncation (suzukiCriticalMellinProfile sigma) s ∈ D) :
    ¬ ∃ Φ : D →ₗ[ℝ] ℝ,
      (∀ s : Finset Nat.Primes,
        Φ ⟨finiteCoordinateTruncation (suzukiCriticalMellinProfile sigma) s,
          htrunc s⟩ =
          ∑ p ∈ s, suzukiCriticalMellinWeightedPrimeMass sigma p) ∧
      (∀ g : D, (∀ p, 0 ≤ g.1 p) → 0 ≤ Φ g) := by
  apply not_exists_positive_extension_containing_nonsummable_profile
    suzukiCriticalSharpPrimeMass_nonneg
    (suzukiCriticalMellinProfile_nonneg sigma)
    (not_summable_suzukiCriticalMellinWeightedPrimeMass_of_le_one hsigma)
    D hprofile htrunc

/-- Every exact extension containing the profile is unbounded below on its full nonnegative cone.
This excludes a global finite floor as well as positivity, still without a unit premise. -/
theorem suzukiCriticalMellinProfile_extension_unboundedBelow_of_le_one
    {sigma : ℝ} (hsigma : sigma ≤ 1)
    (D : Submodule ℝ (Nat.Primes → ℝ))
    (hprofile : suzukiCriticalMellinProfile sigma ∈ D)
    (htrunc : ∀ s : Finset Nat.Primes,
      finiteCoordinateTruncation (suzukiCriticalMellinProfile sigma) s ∈ D)
    (Φ : D →ₗ[ℝ] ℝ)
    (hext : ∀ s : Finset Nat.Primes,
      Φ ⟨finiteCoordinateTruncation (suzukiCriticalMellinProfile sigma) s,
        htrunc s⟩ =
        ∑ p ∈ s, suzukiCriticalMellinWeightedPrimeMass sigma p)
    (L : ℝ) :
    ∃ g : D, (∀ p, 0 ≤ g.1 p) ∧ Φ g < L :=
  profile_extension_unboundedBelow_on_coordinate_domain
    suzukiCriticalSharpPrimeMass_nonneg
    (suzukiCriticalMellinProfile_nonneg sigma)
    (not_summable_suzukiCriticalMellinWeightedPrimeMass_of_le_one hsigma)
    D hprofile htrunc Φ hext L

/-- Every Gaussian-rational point used by the completed left-half RH gate lies outside the
ordinary positive Suzuki profile domain. -/
theorem not_summable_suzukiCriticalMellinWeightedPrimeMass_gaussianRat_leftHalf
    (q : ℚ × ℚ) (hq : (gaussianRatPoint q).re < 1 / 2) :
    ¬ Summable
      (suzukiCriticalMellinWeightedPrimeMass (gaussianRatPoint q).re) :=
  not_summable_suzukiCriticalMellinWeightedPrimeMass_of_le_one (by linarith)

/-- Positive finite-part exclusion specialized to the exact Gaussian-rational left-half test
family consumed by the formal RH endpoint. -/
theorem not_exists_positive_suzukiCriticalGaussianRatLeftHalfProfile_extension
    (q : ℚ × ℚ) (hq : (gaussianRatPoint q).re < 1 / 2)
    (D : Submodule ℝ (Nat.Primes → ℝ))
    (hprofile : suzukiCriticalMellinProfile (gaussianRatPoint q).re ∈ D)
    (htrunc : ∀ s : Finset Nat.Primes,
      finiteCoordinateTruncation
        (suzukiCriticalMellinProfile (gaussianRatPoint q).re) s ∈ D) :
    ¬ ∃ Φ : D →ₗ[ℝ] ℝ,
      (∀ s : Finset Nat.Primes,
        Φ ⟨finiteCoordinateTruncation
          (suzukiCriticalMellinProfile (gaussianRatPoint q).re) s,
          htrunc s⟩ =
          ∑ p ∈ s,
            suzukiCriticalMellinWeightedPrimeMass (gaussianRatPoint q).re p) ∧
      (∀ g : D, (∀ p, 0 ≤ g.1 p) → 0 ≤ Φ g) := by
  exact not_exists_positive_suzukiCriticalMellinProfile_extension_of_le_one
    (by linarith) D hprofile htrunc

/-- Any exact finite-valued Gaussian-rational left-half extension is unbounded below on the
domain's nonnegative cone. -/
theorem suzukiCriticalGaussianRatLeftHalfProfile_extension_unboundedBelow
    (q : ℚ × ℚ) (hq : (gaussianRatPoint q).re < 1 / 2)
    (D : Submodule ℝ (Nat.Primes → ℝ))
    (hprofile : suzukiCriticalMellinProfile (gaussianRatPoint q).re ∈ D)
    (htrunc : ∀ s : Finset Nat.Primes,
      finiteCoordinateTruncation
        (suzukiCriticalMellinProfile (gaussianRatPoint q).re) s ∈ D)
    (Φ : D →ₗ[ℝ] ℝ)
    (hext : ∀ s : Finset Nat.Primes,
      Φ ⟨finiteCoordinateTruncation
        (suzukiCriticalMellinProfile (gaussianRatPoint q).re) s,
        htrunc s⟩ =
        ∑ p ∈ s,
          suzukiCriticalMellinWeightedPrimeMass (gaussianRatPoint q).re p)
    (L : ℝ) :
    ∃ g : D, (∀ p, 0 ≤ g.1 p) ∧ Φ g < L := by
  exact suzukiCriticalMellinProfile_extension_unboundedBelow_of_le_one
    (by linarith) D hprofile htrunc Φ hext L

end


end RHTower
