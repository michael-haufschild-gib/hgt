import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoherentSharpSourceDomainNoGo

/-!
# No positive cofinal finite part for the critical Suzuki source

Finite Suzuki prime cutoffs carry positive Gram mass.  This file proves that this positivity
cannot survive as a finite-valued linear functional on the full prime observable space.  The
obstruction is not continuity or a choice of regulator: exact finite source values already force
the functional to be unbounded below on the pointwise nonnegative cone.

The abstract law applies to every nonnegative nonsummable weight.  Its Suzuki specialization uses
the exact depth-zero sharp-wall mass, whose nonsummability was connected to the rooted-Bianchi
source in `SuzukiCoherentSharpSourceDomainNoGo`.

Consequently any cofinal Suzuki completion must be genuinely semifinite or signed and must lose
the finite-cutoff positive-trace order.  A cutoff-uniform completed lower floor cannot follow by
linear positive extension of the finite Gram traces.
-/

namespace RHTower

noncomputable section

/-! ## Universal positive-extension obstruction -/

section Universal

variable {ι : Type*} [DecidableEq ι]

/-- Indicator of a finite coordinate set. -/
def finiteCoordinateIndicator (s : Finset ι) : ι → ℝ :=
  fun i => if i ∈ s then 1 else 0

/-- A linear functional extends a weight from finite coordinate cutoffs when its value on every
finite indicator is the corresponding finite weight sum. -/
def ExtendsFiniteCoordinateWeight (w : ι → ℝ)
    (Φ : (ι → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ s : Finset ι, Φ (finiteCoordinateIndicator s) = ∑ i ∈ s, w i

/-- Positivity on the pointwise nonnegative coordinate cone. -/
def PositiveOnCoordinateCone (Φ : (ι → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → 0 ≤ Φ f

/-- Existence of one finite lower floor on the full pointwise nonnegative cone. -/
def LowerBoundedOnCoordinateCone (Φ : (ι → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∃ L : ℝ, ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → L ≤ Φ f

theorem finiteCoordinateIndicator_nonneg (s : Finset ι) (i : ι) :
    0 ≤ finiteCoordinateIndicator s i := by
  by_cases hi : i ∈ s <;> simp [finiteCoordinateIndicator, hi]

theorem finiteCoordinateIndicator_le_one (s : Finset ι) (i : ι) :
    finiteCoordinateIndicator s i ≤ 1 := by
  by_cases hi : i ∈ s <;> simp [finiteCoordinateIndicator, hi]

/-- **Universal positive-extension obstruction.**  A nonnegative nonsummable coordinate weight
has no finite-valued positive linear extension to the full product space.  No continuity or norm
bound is assumed. -/
theorem not_exists_positive_linear_extension_of_not_summable
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hnotsum : ¬ Summable w) :
    ¬ ∃ Φ : (ι → ℝ) →ₗ[ℝ] ℝ,
      ExtendsFiniteCoordinateWeight w Φ ∧ PositiveOnCoordinateCone Φ := by
  rintro ⟨Φ, hext, hpos⟩
  apply hnotsum
  apply summable_of_sum_le hw
  intro s
  have hnonneg : ∀ i : ι, 0 ≤ (1 - finiteCoordinateIndicator s) i := by
    intro i
    simp only [Pi.one_apply, Pi.sub_apply]
    linarith [finiteCoordinateIndicator_le_one s i]
  have h := hpos (1 - finiteCoordinateIndicator s) hnonneg
  rw [map_sub, hext s] at h
  exact sub_nonneg.mp h

omit [DecidableEq ι] in
/-- A globally lower-bounded linear functional on a cone is automatically positive there:
scaling any negative value would cross the proposed floor. -/
theorem positiveOnCoordinateCone_of_lowerBounded
    (Φ : (ι → ℝ) →ₗ[ℝ] ℝ) (hΦ : LowerBoundedOnCoordinateCone Φ) :
    PositiveOnCoordinateCone Φ := by
  obtain ⟨L, hL⟩ := hΦ
  intro f hf
  by_contra hneg
  have hΦf : Φ f < 0 := lt_of_not_ge hneg
  let c : ℝ := (|L| + 1) / (-Φ f)
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (by positivity) (neg_pos.mpr hΦf)
  have hcf : ∀ i, 0 ≤ (c • f) i := by
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hc.le (hf i)
  have hbound := hL (c • f) hcf
  rw [map_smul] at hbound
  have hvalue : c * Φ f = -(|L| + 1) := by
    dsimp [c]
    field_simp [hΦf.ne]
  rw [smul_eq_mul, hvalue] at hbound
  have hstrict : -(|L| + 1) < L := by
    linarith [neg_abs_le L]
  exact (not_lt_of_ge hbound) hstrict

/-- **Universal cofinal lower-floor obstruction.**  Every finite-valued linear extension of a
nonnegative nonsummable finite-cutoff weight is unbounded below on the nonnegative cone. -/
theorem finite_weight_extension_unboundedBelow_of_not_summable
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hnotsum : ¬ Summable w)
    (Φ : (ι → ℝ) →ₗ[ℝ] ℝ) (hext : ExtendsFiniteCoordinateWeight w Φ) (L : ℝ) :
    ∃ f : ι → ℝ, (∀ i, 0 ≤ f i) ∧ Φ f < L := by
  by_contra h
  push Not at h
  have hlower : LowerBoundedOnCoordinateCone Φ := ⟨L, h⟩
  have hpos := positiveOnCoordinateCone_of_lowerBounded Φ hlower
  exact not_exists_positive_linear_extension_of_not_summable hw hnotsum
    ⟨Φ, hext, hpos⟩

/-- **Unital-domain form.**  Passing to a proper linear domain does not restore positivity if
that domain still contains its order unit and every finite coordinate cutoff. -/
theorem not_exists_positive_extension_on_unital_coordinate_domain
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hnotsum : ¬ Summable w)
    (D : Submodule ℝ (ι → ℝ)) (hone : (1 : ι → ℝ) ∈ D)
    (hind : ∀ s : Finset ι, finiteCoordinateIndicator s ∈ D) :
    ¬ ∃ Φ : D →ₗ[ℝ] ℝ,
      (∀ s : Finset ι,
        Φ ⟨finiteCoordinateIndicator s, hind s⟩ = ∑ i ∈ s, w i) ∧
      (∀ f : D, (∀ i, 0 ≤ f.1 i) → 0 ≤ Φ f) := by
  rintro ⟨Φ, hext, hpos⟩
  apply hnotsum
  apply summable_of_sum_le hw
  intro s
  let oneD : D := ⟨1, hone⟩
  let indicatorD : D := ⟨finiteCoordinateIndicator s, hind s⟩
  have hnonneg : ∀ i : ι, 0 ≤ (oneD - indicatorD).1 i := by
    intro i
    change 0 ≤ 1 - finiteCoordinateIndicator s i
    linarith [finiteCoordinateIndicator_le_one s i]
  have h := hpos (oneD - indicatorD) hnonneg
  rw [map_sub, hext s] at h
  exact sub_nonneg.mp h

omit [DecidableEq ι] in
/-- A finite lower floor on the positive cone of a linear subdomain again forces positivity. -/
theorem positiveOnCoordinateSubmoduleCone_of_lowerBounded
    (D : Submodule ℝ (ι → ℝ)) (Φ : D →ₗ[ℝ] ℝ)
    (hΦ : ∃ L : ℝ, ∀ f : D, (∀ i, 0 ≤ f.1 i) → L ≤ Φ f) :
    ∀ f : D, (∀ i, 0 ≤ f.1 i) → 0 ≤ Φ f := by
  obtain ⟨L, hL⟩ := hΦ
  intro f hf
  by_contra hneg
  have hΦf : Φ f < 0 := lt_of_not_ge hneg
  let c : ℝ := (|L| + 1) / (-Φ f)
  have hc : 0 < c := div_pos (by positivity) (neg_pos.mpr hΦf)
  have hcf : ∀ i, 0 ≤ (c • f).1 i := by
    intro i
    change 0 ≤ c * f.1 i
    exact mul_nonneg hc.le (hf i)
  have hbound := hL (c • f) hcf
  rw [map_smul] at hbound
  have hvalue : c * Φ f = -(|L| + 1) := by
    dsimp [c]
    field_simp [hΦf.ne]
  rw [smul_eq_mul, hvalue] at hbound
  linarith [neg_abs_le L]

/-- **Unital-domain cofinal no-go.**  Any exact finite-weight extension on a linear domain
containing the order unit and all finite cutoffs is unbounded below on that domain's nonnegative
cone.  Avoiding the obstruction requires excluding the cofinal unit, losing linearity, or losing
the lower floor. -/
theorem finite_weight_extension_unboundedBelow_on_unital_coordinate_domain
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hnotsum : ¬ Summable w)
    (D : Submodule ℝ (ι → ℝ)) (hone : (1 : ι → ℝ) ∈ D)
    (hind : ∀ s : Finset ι, finiteCoordinateIndicator s ∈ D)
    (Φ : D →ₗ[ℝ] ℝ)
    (hext : ∀ s : Finset ι,
      Φ ⟨finiteCoordinateIndicator s, hind s⟩ = ∑ i ∈ s, w i)
    (L : ℝ) :
    ∃ f : D, (∀ i, 0 ≤ f.1 i) ∧ Φ f < L := by
  by_contra h
  push Not at h
  have hpos := positiveOnCoordinateSubmoduleCone_of_lowerBounded D Φ ⟨L, h⟩
  exact not_exists_positive_extension_on_unital_coordinate_domain
    hw hnotsum D hone hind ⟨Φ, hext, hpos⟩

end Universal

/-! ## Exact Suzuki specialization -/

/-- Critical depth-zero Suzuki sharp-wall mass on one prime coordinate. -/
def suzukiCriticalSharpPrimeMass (p : Nat.Primes) : ℝ :=
  suzukiCriticalEntryWallBareAmplitude p 0 ^ (2 : ℕ)

theorem suzukiCriticalSharpPrimeMass_nonneg (p : Nat.Primes) :
    0 ≤ suzukiCriticalSharpPrimeMass p := by
  exact sq_nonneg _

theorem not_summable_suzukiCriticalSharpPrimeMass :
    ¬ Summable suzukiCriticalSharpPrimeMass := by
  exact not_summable_sq_suzukiCriticalEntryWallBareAmplitude_zero

/-- Exact finite-cutoff source-value requirement for a proposed Suzuki cofinal finite part. -/
def ExtendsSuzukiCriticalSharpPrimeSource
    (Φ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ExtendsFiniteCoordinateWeight suzukiCriticalSharpPrimeMass Φ

/-- **No positive Suzuki cofinal finite part.**  No finite-valued positive linear functional on
all prime observables can preserve every exact finite critical Suzuki source value. -/
theorem not_exists_positive_suzukiCriticalSharpPrimeSource_extension :
    ¬ ∃ Φ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ,
      ExtendsSuzukiCriticalSharpPrimeSource Φ ∧ PositiveOnCoordinateCone Φ :=
  not_exists_positive_linear_extension_of_not_summable
    suzukiCriticalSharpPrimeMass_nonneg
    not_summable_suzukiCriticalSharpPrimeMass

/-- **Suzuki cofinal finite-part no-go.**  Every finite-valued linear functional preserving all
finite critical sharp-source traces takes arbitrarily negative values on pointwise nonnegative
prime observables.  Hence finite-cutoff Gram positivity cannot descend to a global linear finite
part with any finite lower floor. -/
theorem suzukiCriticalSharpPrimeSource_extension_unboundedBelow
    (Φ : (Nat.Primes → ℝ) →ₗ[ℝ] ℝ)
    (hext : ExtendsSuzukiCriticalSharpPrimeSource Φ) (L : ℝ) :
    ∃ f : Nat.Primes → ℝ, (∀ p, 0 ≤ f p) ∧ Φ f < L :=
  finite_weight_extension_unboundedBelow_of_not_summable
    suzukiCriticalSharpPrimeMass_nonneg
    not_summable_suzukiCriticalSharpPrimeMass Φ hext L

/-- **Domain-complete Suzuki obstruction.**  Restricting a candidate finite part to a linear
domain does not help when the domain contains the cofinal unit and all finite prime cutoffs: every
exact extension remains unbounded below on its nonnegative cone. -/
theorem suzukiCriticalSharpPrimeSource_unboundedBelow_on_unital_domain
    (D : Submodule ℝ (Nat.Primes → ℝ))
    (hone : (1 : Nat.Primes → ℝ) ∈ D)
    (hind : ∀ s : Finset Nat.Primes, finiteCoordinateIndicator s ∈ D)
    (Φ : D →ₗ[ℝ] ℝ)
    (hext : ∀ s : Finset Nat.Primes,
      Φ ⟨finiteCoordinateIndicator s, hind s⟩ =
        ∑ p ∈ s, suzukiCriticalSharpPrimeMass p)
    (L : ℝ) :
    ∃ f : D, (∀ p, 0 ≤ f.1 p) ∧ Φ f < L :=
  finite_weight_extension_unboundedBelow_on_unital_coordinate_domain
    suzukiCriticalSharpPrimeMass_nonneg
    not_summable_suzukiCriticalSharpPrimeMass D hone hind Φ hext L

end

end RHTower
