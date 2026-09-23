import GaloisForLFunctions.RHTower.SourceHorizontalSharedReservoirStokesObstruction

/-!
# Unbounded Stokes negative-port capacity of reflected source packets

Every coefficient-generated global Stokes Witt carrier is nonnegative after one rank-square
correction.  A sum of `k` such carriers therefore has at most `k` negative directions after any
linear pullback.  In contrast, one orientation of an off-line source-horizontal shared-reservoir
packet of size `m` has exact negative index `m - 1`.

Consequently no fixed finite number of coefficient-generated Stokes carriers can receive all
reflected source packets on an off-line Xi fibre.  For every port budget `k`, an injectively
prime-labelled packet of size `k + 2` defeats it.  This is stronger than the earlier one-port
obstruction: increasing finite Stokes data, finite direct sums, or finite Pontryagin index never
closes the SC landing problem.  A surviving all-prime carrier must have unbounded/infinite
negative-index capacity, or abandon finite sums of one-port quadratic landings.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- A sum of `k` one-port forms has negative index at most `k` after arbitrary linear pullback. -/
theorem sigNeg_le_of_finiteOnePortSumPullback
    {V M : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup M] [Module ℝ M]
    (S : QuadraticForm ℝ V) {k : ℕ}
    (Q : Fin k → QuadraticForm ℝ M)
    (f : Fin k → V →ₗ[ℝ] M)
    (ell : Fin k → M →ₗ[ℝ] ℝ)
    (hQ : ∀ i y, 0 ≤ Q i y + (ell i y) ^ (2 : ℕ))
    (hpull : ∀ x, S x = ∑ i, Q i (f i x)) :
    sigNeg S ≤ k := by
  apply GaloisForLFunctions.sigNeg_le_of_add_sum_sq_nonneg S
    (fun i => (ell i).comp (f i))
  intro x
  rw [hpull]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_nonneg fun i _ => hQ i (f i x)

/-- A right-half source packet of size `m` cannot factor through fewer than `m - 1` one-port
carriers. -/
theorem not_finiteOnePortSumPullback_of_sourceZeroHorizontal_right
    {m k : ℕ} (hm : 2 ≤ m) (hcapacity : k < m - 1)
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re)
    (p : Fin m → Nat.Primes)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : Fin k → QuadraticForm ℝ M)
    (f : Fin k → (Fin m → ℝ) →ₗ[ℝ] M)
    (ell : Fin k → M →ₗ[ℝ] ℝ)
    (hQ : ∀ i y, 0 ≤ Q i y + (ell i y) ^ (2 : ℕ)) :
    ¬ ∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
      ∑ i, Q i (f i x) := by
  intro hpull
  have hle := sigNeg_le_of_finiteOnePortSumPullback
    (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'
    Q f ell hQ hpull
  have hsig :=
    (sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right q hright p hm).2.1
  rw [hsig] at hle
  omega

/-- **Finite-port reflection obstruction.**  If `k < m - 1`, an off-line source packet and its
line-conjugate reflection cannot both factor through sums of `k` one-port forms. -/
theorem sourceZeroHorizontalSharedReservoir_twoOrientation_finitePort_obstruction
    {m k : ℕ} (hm : 2 ≤ m) (hcapacity : k < m - 1)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes)
    {M₁ M₂ : Type*}
    [AddCommGroup M₁] [Module ℝ M₁]
    [AddCommGroup M₂] [Module ℝ M₂]
    (Q₁ : Fin k → QuadraticForm ℝ M₁)
    (Q₂ : Fin k → QuadraticForm ℝ M₂)
    (f₁ : Fin k → (Fin m → ℝ) →ₗ[ℝ] M₁)
    (f₂ : Fin k → (Fin m → ℝ) →ₗ[ℝ] M₂)
    (ell₁ : Fin k → M₁ →ₗ[ℝ] ℝ)
    (ell₂ : Fin k → M₂ →ₗ[ℝ] ℝ)
    (hQ₁ : ∀ i y, 0 ≤ Q₁ i y + (ell₁ i y) ^ (2 : ℕ))
    (hQ₂ : ∀ i y, 0 ≤ Q₂ i y + (ell₂ i y) ^ (2 : ℕ)) :
    ¬ ((∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          ∑ i, Q₁ i (f₁ i x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
            ∑ i, Q₂ i (f₂ i x))) := by
  rintro ⟨hforward, hreflected⟩
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · exact not_finiteOnePortSumPullback_of_sourceZeroHorizontal_right
      hm hcapacity (xiZeroCopyLineConjEquiv q)
      (sourceZeroHorizontal_reflection_right_of_left q hleft) p
      Q₂ f₂ ell₂ hQ₂ hreflected
  · exact not_finiteOnePortSumPullback_of_sourceZeroHorizontal_right
      hm hcapacity q hright p Q₁ f₁ ell₁ hQ₁ hforward

namespace GlobalPuiseuxWittFinitePort

open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

/-- No `k`-fold sum of one coefficient-generated global Stokes Witt carrier can receive both
orientations of an off-line packet when the packet has more than `k + 1` prime slots. -/
theorem not_both_sourceZeroHorizontal_orientations_land_in_finiteGlobalWitt
    {m k : ℕ} (hm : 2 ≤ m) (hcapacity : k < m - 1)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes)
    {j : ℕ} {n r K N : Fin (j + 1) → ℕ}
    (genus : ℕ) (d : LocalData j n r K N)
    (forward reflected :
      Fin k → (Fin m → ℝ) →ₗ[ℝ] compatibleCharges d) :
    ¬ ((∀ x, (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
          ∑ a, globalWittForm genus d (forward a x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
            ∑ a, globalWittForm genus d (reflected a x))) := by
  exact sourceZeroHorizontalSharedReservoir_twoOrientation_finitePort_obstruction
    hm hcapacity q hoff p
      (fun _ => globalWittForm genus d)
      (fun _ => globalWittForm genus d)
      forward reflected
      (fun _ => GlobalPuiseuxWittLanding.rankCorrection genus d)
      (fun _ => GlobalPuiseuxWittLanding.rankCorrection genus d)
      (fun _ =>
        GlobalPuiseuxWittLanding.globalWittForm_add_rankCorrection_nonneg genus d)
      (fun _ =>
        GlobalPuiseuxWittLanding.globalWittForm_add_rankCorrection_nonneg genus d)

/-- **Unbounded negative-port law for SC.**  On every off-line Xi fibre, each finite Stokes port
budget `k` is defeated by an injectively prime-labelled packet of size `k + 2`.  All Stokes data,
genus, and landing maps are quantified after the source fibre and port budget are fixed. -/
theorem xiOffLineFiniteGlobalWittPortExhaustion :
    ∀ (q : XiZeroCopy), (q.1 : ℂ).re ≠ 1 / 2 →
      ∀ (k j : ℕ) (n r K N : Fin (j + 1) → ℕ)
        (genus : ℕ) (d : LocalData j n r K N),
      ∃ p : Fin (k + 2) → Nat.Primes,
        Function.Injective p ∧
        ∀ (forward reflected :
          Fin k → (Fin (k + 2) → ℝ) →ₗ[ℝ] compatibleCharges d),
          ¬ ((∀ x,
              (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
                ∑ a, globalWittForm genus d (forward a x)) ∧
            (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
              (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
                ∑ a, globalWittForm genus d (reflected a x))) := by
  intro q hoff k j n r K N genus d
  have hmpos : 0 < k + 2 := by omega
  obtain ⟨p, hpInjective, -, -⟩ :=
    exists_sourceZeroHorizontalSharedReservoirPacket
      q hoff (k + 2) hmpos (ε := 1) zero_lt_one
  refine ⟨p, hpInjective, ?_⟩
  intro forward reflected
  exact not_both_sourceZeroHorizontal_orientations_land_in_finiteGlobalWitt
    (m := k + 2) (k := k) (by omega) (by omega)
      q hoff p genus d forward reflected

end GlobalPuiseuxWittFinitePort

end

end RHTower
