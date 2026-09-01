import GaloisForLFunctions.RHTower.SourceHorizontalFiniteDimensionalQuadraticCarrierNoGo

/-!
# Finite-negative-capacity quadratic carriers cannot receive all reflected source packets

The finite-dimensional obstruction only uses target dimension to bound dimensions of
negative-definite images.  This file removes finite ambient dimension: an arbitrary real quadratic
carrier is allowed, but its finite negative subspaces are assumed to have one uniform dimension
bound.  Exact quadratic pullback injects every negative source subspace into a negative target
subspace, so the source-horizontal packets force genuinely unbounded negative index.

This kills all Hilbert, Pontryagin, and arbitrary-dimensional finite-negative-index linear
quadratic carriers before the common HB/FZZ-P/PW-B/RBH Ward receiver.  A survivor must have
finite negative subspaces of every dimension, or use nonlinear/singular/domain-changing landing.
-/

namespace RHTower

noncomputable section

/-- Operational finite negative capacity for an arbitrary-dimensional real quadratic carrier.
Every injectively landed finite-dimensional negative-definite source has dimension at most `k`. -/
def QuadraticFiniteNegativeCapacityAtMost
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (k : ℕ) : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
      (g : V →ₗ[ℝ] M),
    Function.Injective g →
      (∀ x : V, x ≠ 0 → Q (g x) < 0) →
        Module.finrank ℝ V ≤ k

/-- Exact quadratic pullback cannot have more negative directions than the arbitrary target's
finite negative capacity. -/
theorem sigNeg_le_of_quadraticPullback_finiteNegativeCapacity
    {V : Type} {M : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup M] [Module ℝ M]
    (S : QuadraticForm ℝ V) (Q : QuadraticForm ℝ M) (k : ℕ)
    (hcapacity : QuadraticFiniteNegativeCapacityAtMost Q k)
    (f : V →ₗ[ℝ] M) (hpull : ∀ x, S x = Q (f x)) :
    sigNeg S ≤ k := by
  obtain ⟨W, hWrank, hWneg⟩ := exists_finrank_eq_sigNeg_and_negDef S
  have hinj : Function.Injective (f.domRestrict W) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    by_contra hy0
    have hSneg : S (y : V) < 0 := by
      have hp := hWneg y hy0
      rwa [QuadraticMap.restrict_apply, QuadraticMap.neg_apply, neg_pos] at hp
    have hSzero : S (y : V) = 0 := by
      rw [hpull, LinearMap.domRestrict_apply] at *
      rw [hy]
      simp
    linarith
  have hnegative : ∀ y : W, y ≠ 0 → Q ((f.domRestrict W) y) < 0 := by
    intro y hy
    rw [LinearMap.domRestrict_apply, ← hpull]
    have hp := hWneg y hy
    rwa [QuadraticMap.restrict_apply, QuadraticMap.neg_apply, neg_pos] at hp
  have hle := hcapacity (f.domRestrict W) hinj hnegative
  rwa [hWrank] at hle

/-- Any arbitrary-dimensional quadratic target receiving a right-half packet of size `m` has
finite negative capacity at least `m - 1`. -/
theorem sourceZeroHorizontalSharedReservoir_target_negativeCapacity_ge_of_right
    {m : ℕ} (hm : 2 ≤ m)
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re)
    (p : Fin m → Nat.Primes)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (k : ℕ)
    (hcapacity : QuadraticFiniteNegativeCapacityAtMost Q k)
    (f : (Fin m → ℝ) →ₗ[ℝ] M)
    (hpull : ∀ x,
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x = Q (f x)) :
    m - 1 ≤ k := by
  have hle := sigNeg_le_of_quadraticPullback_finiteNegativeCapacity
    (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' Q k hcapacity f hpull
  have hsig :=
    (sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right q hright p hm).2.1
  rwa [hsig] at hle

/-- If two arbitrary-dimensional targets have finite negative capacities below `m - 1`, they
cannot receive both reflected orientations of an off-wall packet. -/
theorem sourceZeroHorizontalSharedReservoir_twoOrientation_finiteNegativeCapacity_obstruction
    {m : ℕ} (hm : 2 ≤ m)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes)
    {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module ℝ M₁]
    [AddCommGroup M₂] [Module ℝ M₂]
    (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
    (k₁ k₂ : ℕ)
    (hcapacity₁ : QuadraticFiniteNegativeCapacityAtMost Q₁ k₁)
    (hcapacity₂ : QuadraticFiniteNegativeCapacityAtMost Q₂ k₂)
    (hbound₁ : k₁ < m - 1) (hbound₂ : k₂ < m - 1)
    (f₁ : (Fin m → ℝ) →ₗ[ℝ] M₁)
    (f₂ : (Fin m → ℝ) →ₗ[ℝ] M₂) :
    ¬ ((∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          Q₁ (f₁ x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x = Q₂ (f₂ x))) := by
  rintro ⟨hforward, hreflected⟩
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · have hge := sourceZeroHorizontalSharedReservoir_target_negativeCapacity_ge_of_right
      hm (xiZeroCopyLineConjEquiv q)
      (sourceZeroHorizontal_reflection_right_of_left q hleft) p Q₂ k₂ hcapacity₂ f₂ hreflected
    omega
  · have hge := sourceZeroHorizontalSharedReservoir_target_negativeCapacity_ge_of_right
      hm q hright p Q₁ k₁ hcapacity₁ f₁ hforward
    omega

/-- Strong positive survivor: any arbitrary-dimensional quadratic carrier receiving every
right-half source packet has finite negative subspaces of unbounded dimension. -/
theorem sourceZeroHorizontalSharedReservoir_allPacketsLanding_forces_unboundedNegativeCapacity
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M)
    (hlanding : ∀ (m : ℕ), 2 ≤ m → ∀ p : Fin m → Nat.Primes,
      Function.Injective p →
        ∃ f : (Fin m → ℝ) →ₗ[ℝ] M,
          ∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x = Q (f x)) :
    ∀ k : ℕ, ¬ QuadraticFiniteNegativeCapacityAtMost Q k := by
  intro k hcapacity
  have hmpos : 0 < k + 2 := by omega
  have hoff : (q.1 : ℂ).re ≠ 1 / 2 := ne_of_gt hright
  obtain ⟨p, hpInjective, -, -⟩ :=
    exists_sourceZeroHorizontalSharedReservoirPacket
      q hoff (k + 2) hmpos (ε := 1) zero_lt_one
  obtain ⟨f, hpull⟩ := hlanding (k + 2) (by omega) p hpInjective
  have hge := sourceZeroHorizontalSharedReservoir_target_negativeCapacity_ge_of_right
    (m := k + 2) (by omega) q hright p Q k hcapacity f hpull
  omega

/-- Closed route certificate: every pair of arbitrary-dimensional real quadratic carriers with
finite negative capacity is defeated on each off-wall Xi fibre by one reflected prime packet. -/
def SourceHorizontalFiniteNegativeCapacityQuadraticCarrierRouteKilled : Prop :=
  ∀ (q : XiZeroCopy), (q.1 : ℂ).re ≠ 1 / 2 →
    ∀ (M₁ M₂ : Type)
      [AddCommGroup M₁] [Module ℝ M₁]
      [AddCommGroup M₂] [Module ℝ M₂]
      (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
      (k₁ k₂ : ℕ),
      QuadraticFiniteNegativeCapacityAtMost Q₁ k₁ →
      QuadraticFiniteNegativeCapacityAtMost Q₂ k₂ →
      ∃ p : Fin (max k₁ k₂ + 2) → Nat.Primes,
        Function.Injective p ∧
        ∀ (f₁ : (Fin (max k₁ k₂ + 2) → ℝ) →ₗ[ℝ] M₁)
          (f₂ : (Fin (max k₁ k₂ + 2) → ℝ) →ₗ[ℝ] M₂),
          ¬ ((∀ x,
              (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
                Q₁ (f₁ x)) ∧
            (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
              (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x = Q₂ (f₂ x)))

/-- **[SHARED-WARD ROUTE-CLASS KILL].** Arbitrary ambient dimension does not rescue a linear
quadratic HB/FZZ-P/PW-B/RBH source carrier: every finite-negative-index carrier fails. -/
theorem sourceHorizontalFiniteNegativeCapacityQuadraticCarrierRouteKilled :
    SourceHorizontalFiniteNegativeCapacityQuadraticCarrierRouteKilled := by
  intro q hoff M₁ M₂ _ _ _ _ Q₁ Q₂ k₁ k₂ hcapacity₁ hcapacity₂
  have hmpos : 0 < max k₁ k₂ + 2 := by omega
  obtain ⟨p, hpInjective, -, -⟩ :=
    exists_sourceZeroHorizontalSharedReservoirPacket
      q hoff _ hmpos (ε := 1) zero_lt_one
  refine ⟨p, hpInjective, ?_⟩
  intro f₁ f₂
  apply sourceZeroHorizontalSharedReservoir_twoOrientation_finiteNegativeCapacity_obstruction
    (m := max k₁ k₂ + 2) (by omega) q hoff p Q₁ Q₂ k₁ k₂
      hcapacity₁ hcapacity₂ <;> omega

end

end RHTower
