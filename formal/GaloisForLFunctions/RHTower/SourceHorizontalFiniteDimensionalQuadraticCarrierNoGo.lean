import GaloisForLFunctions.RHTower.SourceHorizontalFinitePortStokesCapacity

/-!
# Finite-dimensional quadratic carriers cannot receive all reflected source packets

The finite-port Stokes obstruction assumes a sum of one-port forms.  Here no decomposition,
positivity, or Stokes structure is assumed: an arbitrary quadratic form on an arbitrary
finite-dimensional real target is allowed, together with an arbitrary linear landing map.

A negative-definite subspace of a quadratic pullback injects into its target, so pullback negative
index is at most target dimension.  A right-half source-horizontal packet of size `m` has exact
negative index `m - 1`.  Off the critical wall, one of a packet and its line-conjugate reflection
is right-half.  Choosing more prime-labelled source slots than either fixed target can carry kills
simultaneous reflected landing through every fixed finite-dimensional quadratic carrier.

This closes the finite-dimensional carrier branch before the common HB/FZZ-P/PW-B/RBH Ward
receiver.  A surviving source producer must have unbounded-dimensional negative capacity, or
abandon linear quadratic landing through nonlinear or singular dynamics.
-/

namespace RHTower

noncomputable section

/-- Negative index cannot increase beyond the dimension of an arbitrary linear quadratic target.
No positivity, nondegeneracy, or normal form for the target quadratic form is required. -/
theorem sigNeg_le_finrank_of_quadraticPullback
    {V M : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (S : QuadraticForm ℝ V) (Q : QuadraticForm ℝ M)
    (f : V →ₗ[ℝ] M) (hpull : ∀ x, S x = Q (f x)) :
    sigNeg S ≤ Module.finrank ℝ M := by
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
  have hle : Module.finrank ℝ W ≤ Module.finrank ℝ M :=
    LinearMap.finrank_le_finrank_of_injective hinj
  rwa [hWrank] at hle

/-- **Exact target-capacity survivor.**  Any arbitrary quadratic target receiving a right-half
source-horizontal packet of size `m` has real dimension at least `m - 1`. -/
theorem sourceZeroHorizontalSharedReservoir_target_finrank_ge_of_right
    {m : ℕ} (hm : 2 ≤ m)
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re)
    (p : Fin m → Nat.Primes)
    {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    (Q : QuadraticForm ℝ M)
    (f : (Fin m → ℝ) →ₗ[ℝ] M)
    (hpull : ∀ x,
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x = Q (f x)) :
    m - 1 ≤ Module.finrank ℝ M := by
  have hle := sigNeg_le_finrank_of_quadraticPullback
    (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' Q f hpull
  have hsig :=
    (sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right q hright p hm).2.1
  rwa [hsig] at hle

/-- **Arbitrary finite-dimensional reflected-carrier obstruction.**  If both target dimensions
are below `m - 1`, no pair of arbitrary quadratic targets and arbitrary linear maps receives both
orientations of an off-wall packet. -/
theorem sourceZeroHorizontalSharedReservoir_twoOrientation_finiteDimensional_obstruction
    {m : ℕ} (hm : 2 ≤ m)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes)
    {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module ℝ M₁] [FiniteDimensional ℝ M₁]
    [AddCommGroup M₂] [Module ℝ M₂] [FiniteDimensional ℝ M₂]
    (hcapacity₁ : Module.finrank ℝ M₁ < m - 1)
    (hcapacity₂ : Module.finrank ℝ M₂ < m - 1)
    (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
    (f₁ : (Fin m → ℝ) →ₗ[ℝ] M₁)
    (f₂ : (Fin m → ℝ) →ₗ[ℝ] M₂) :
    ¬ ((∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          Q₁ (f₁ x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x = Q₂ (f₂ x))) := by
  rintro ⟨hforward, hreflected⟩
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · have hge := sourceZeroHorizontalSharedReservoir_target_finrank_ge_of_right
      hm (xiZeroCopyLineConjEquiv q)
      (sourceZeroHorizontal_reflection_right_of_left q hleft) p Q₂ f₂ hreflected
    omega
  · have hge := sourceZeroHorizontalSharedReservoir_target_finrank_ge_of_right
      hm q hright p Q₁ f₁ hforward
    omega

/-- Closed route certificate: every pair of fixed finite-dimensional real quadratic carriers is
defeated on each off-wall Xi fibre by one injectively prime-labelled reflected source packet. -/
def SourceHorizontalFiniteDimensionalQuadraticCarrierRouteKilled : Prop :=
  ∀ (q : XiZeroCopy), (q.1 : ℂ).re ≠ 1 / 2 →
    ∀ (M₁ M₂ : Type)
      [AddCommGroup M₁] [Module ℝ M₁] [FiniteDimensional ℝ M₁]
      [AddCommGroup M₂] [Module ℝ M₂] [FiniteDimensional ℝ M₂],
      ∃ p : Fin (max (Module.finrank ℝ M₁) (Module.finrank ℝ M₂) + 2) → Nat.Primes,
        Function.Injective p ∧
        ∀ (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂)
          (f₁ : (Fin (max (Module.finrank ℝ M₁) (Module.finrank ℝ M₂) + 2) → ℝ) →ₗ[ℝ] M₁)
          (f₂ : (Fin (max (Module.finrank ℝ M₁) (Module.finrank ℝ M₂) + 2) → ℝ) →ₗ[ℝ] M₂),
          ¬ ((∀ x,
              (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
                Q₁ (f₁ x)) ∧
            (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
              (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x = Q₂ (f₂ x)))

/-- **[SHARED-WARD ROUTE-CLASS KILL].**  Fixed finite-dimensional quadratic source carriers cannot
manufacture the reflected source orientation needed by the common HB/FZZ-P/PW-B/RBH endpoint. -/
theorem sourceHorizontalFiniteDimensionalQuadraticCarrierRouteKilled :
    SourceHorizontalFiniteDimensionalQuadraticCarrierRouteKilled := by
  intro q hoff M₁ M₂ _ _ _ _ _ _
  have hmpos :
      0 < max (Module.finrank ℝ M₁) (Module.finrank ℝ M₂) + 2 := by omega
  obtain ⟨p, hpInjective, -, -⟩ :=
    exists_sourceZeroHorizontalSharedReservoirPacket
      q hoff _ hmpos (ε := 1) zero_lt_one
  refine ⟨p, hpInjective, ?_⟩
  intro Q₁ Q₂ f₁ f₂
  apply sourceZeroHorizontalSharedReservoir_twoOrientation_finiteDimensional_obstruction
    (m := max (Module.finrank ℝ M₁) (Module.finrank ℝ M₂) + 2)
      (by omega) q hoff p <;> omega

end

end RHTower
