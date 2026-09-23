import GaloisForLFunctions.RHTower.SourceHorizontalFiniteNegativeCapacityQuadraticCarrierNoGo

/-!
# Finite-rank scalar reflection perturbations cannot receive all shared Ward packets

The finite-negative-capacity obstruction leaves open targets with genuinely infinite positive and
negative index.  This module removes a different regular escape: the reflection operator cannot be
a finite-rank perturbation of any real scalar multiple of identity, even on an arbitrary-dimensional
infinite-index target.

If `T - c I` has rank at most `k` and `T` reverses a quadratic form on an exact landed packet, then
`T - c I` is injective on every positive- or negative-definite source subspace.  Indeed, a vector in
its kernel satisfies `T x = c x`; anti-isometry then gives

`c^(2 : ℕ) Q(x) = -Q(x)`,

which is impossible when `Q(x)` is strictly positive or negative.  Both source inertia indices are
therefore at most `k`.  An off-wall source-horizontal packet of size `k+2` has one index equal to
`k+1`, so exact reflected landing is impossible.

This kills scalar-essential finite-rank reflection dynamics before the common
HB/FZZ-P/PW-B/RBH Ward receiver.  The sharp survivor is infinite-rank and non-scalar: an all-packet
reflection must make `T - c I` have unbounded operational rank for every real `c`, or leave linear
quadratic landing through nonlinear, singular, or domain-changing data.

`[NEW] [SHARED-WARD NO-GO] [FINITE-RANK REFLECTION] [INFINITE-INDEX TARGET]`
-/

namespace RHTower

noncomputable section

/-- Operational rank bound for an endomorphism of an arbitrary-dimensional real vector space.
Every finite-dimensional probe has image dimension at most `k`. -/
def LinearMapFiniteRankAtMost
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (A : M →ₗ[ℝ] M) (k : ℕ) : Prop :=
  ∀ {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
      (g : V →ₗ[ℝ] M),
    Module.finrank ℝ (LinearMap.range (A.comp g)) ≤ k

/-- A finite-rank scalar perturbation that reverses an exact quadratic landing bounds its negative
index, without any dimension or index assumption on the target. -/
theorem sigNeg_le_of_finiteRankPerturbation_antiIsometry
    {V : Type} {M : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup M] [Module ℝ M]
    (S : QuadraticForm ℝ V) (Q : QuadraticForm ℝ M)
    (T : M →ₗ[ℝ] M) (c : ℝ) (k : ℕ)
    (hfinite : LinearMapFiniteRankAtMost (T - c • LinearMap.id) k)
    (f : V →ₗ[ℝ] M)
    (hpull : ∀ x, S x = Q (f x))
    (hanti : ∀ x, Q (T (f x)) = -Q (f x)) :
    sigNeg S ≤ k := by
  obtain ⟨W, hWrank, hWneg⟩ := exists_finrank_eq_sigNeg_and_negDef S
  let g : W →ₗ[ℝ] M := f.domRestrict W
  have hinj : Function.Injective ((T - c • LinearMap.id).comp g) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hfix : T (g x) = c • g x := by
      simpa [g, sub_eq_zero] using hx
    by_contra hx0
    have hneg : Q (g x) < 0 := by
      change Q (f (x : V)) < 0
      rw [← hpull]
      have hw := hWneg x hx0
      rwa [QuadraticMap.restrict_apply, QuadraticMap.neg_apply, neg_pos] at hw
    have ha := hanti (x : V)
    change Q (T (g x)) = -Q (g x) at ha
    rw [hfix, QuadraticMap.map_smul] at ha
    change (c * c) * Q (g x) = -Q (g x) at ha
    nlinarith [sq_nonneg c]
  have hrank := hfinite g
  rw [LinearMap.finrank_range_of_inj hinj, hWrank] at hrank
  exact hrank

/-- The same finite-rank anti-isometry mechanism bounds the positive index. -/
theorem sigPos_le_of_finiteRankPerturbation_antiIsometry
    {V : Type} {M : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup M] [Module ℝ M]
    (S : QuadraticForm ℝ V) (Q : QuadraticForm ℝ M)
    (T : M →ₗ[ℝ] M) (c : ℝ) (k : ℕ)
    (hfinite : LinearMapFiniteRankAtMost (T - c • LinearMap.id) k)
    (f : V →ₗ[ℝ] M)
    (hpull : ∀ x, S x = Q (f x))
    (hanti : ∀ x, Q (T (f x)) = -Q (f x)) :
    sigPos S ≤ k := by
  have hneg := sigNeg_le_of_finiteRankPerturbation_antiIsometry
    (-S) (-Q) T c k hfinite f (by
      intro x
      simp only [QuadraticMap.neg_apply]
      rw [hpull x]) (by
      intro x
      simp only [QuadraticMap.neg_apply]
      rw [hanti x])
  rwa [sigNeg_neg] at hneg

/-- A reflected right-half source packet forces the scalar perturbation rank to be at least its
large negative index. -/
theorem sourceZeroHorizontalSharedReservoir_finiteRankReflection_ge_of_right
    {m : ℕ} (hm : 2 ≤ m)
    (q : XiZeroCopy) (hright : 1 / 2 < (q.1 : ℂ).re)
    (p : Fin m → Nat.Primes)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (T : M →ₗ[ℝ] M) (c : ℝ) (k : ℕ)
    (hfinite : LinearMapFiniteRankAtMost (T - c • LinearMap.id) k)
    (f : (Fin m → ℝ) →ₗ[ℝ] M)
    (hpull : ∀ x,
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x = Q (f x))
    (hreflected : ∀ x,
      (sourceZeroHorizontalSharedReservoirMatrix
        (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x = Q (T (f x))) :
    m - 1 ≤ k := by
  have hanti : ∀ x, Q (T (f x)) = -Q (f x) := by
    intro x
    rw [← hreflected x, ← hpull x,
      sourceZeroHorizontalSharedReservoirMatrix_reflection]
    simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂']
  have hle := sigNeg_le_of_finiteRankPerturbation_antiIsometry
    (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'
      Q T c k hfinite f hpull hanti
  have hsig :=
    (sourceZeroHorizontalSharedReservoirMatrix_inertia_of_right q hright p hm).2.1
  rwa [hsig] at hle

/-- Either source orientation has an index `m-1`, so exact reflection-covariant landing forces
scalar-perturbation rank at least `m-1` on every off-wall fibre. -/
theorem sourceZeroHorizontalSharedReservoir_finiteRankReflection_ge_of_offLine
    {m : ℕ} (hm : 2 ≤ m)
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    (p : Fin m → Nat.Primes)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (T : M →ₗ[ℝ] M) (c : ℝ) (k : ℕ)
    (hfinite : LinearMapFiniteRankAtMost (T - c • LinearMap.id) k)
    (f : (Fin m → ℝ) →ₗ[ℝ] M)
    (hpull : ∀ x,
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x = Q (f x))
    (hreflected : ∀ x,
      (sourceZeroHorizontalSharedReservoirMatrix
        (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x = Q (T (f x))) :
    m - 1 ≤ k := by
  have hanti : ∀ x, Q (T (f x)) = -Q (f x) := by
    intro x
    rw [← hreflected x, ← hpull x,
      sourceZeroHorizontalSharedReservoirMatrix_reflection]
    simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂']
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · have hle := sigPos_le_of_finiteRankPerturbation_antiIsometry
      (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm'
        Q T c k hfinite f hpull hanti
    have hsig :=
      (sourceZeroHorizontalSharedReservoirMatrix_inertia_of_left q hleft p hm).1
    rwa [hsig] at hle
  · exact sourceZeroHorizontalSharedReservoir_finiteRankReflection_ge_of_right
      hm q hright p Q T c k hfinite f hpull hreflected

/-- Closed route class: a finite-rank perturbation of any real scalar operator cannot carry one
large reflected source-horizontal packet on an off-wall Xi fibre. -/
def SourceHorizontalFiniteRankReflectionQuadraticCarrierRouteKilled : Prop :=
  ∀ (q : XiZeroCopy), (q.1 : ℂ).re ≠ 1 / 2 →
    ∀ (M : Type) [AddCommGroup M] [Module ℝ M]
      (Q : QuadraticForm ℝ M) (T : M →ₗ[ℝ] M) (c : ℝ) (k : ℕ),
      LinearMapFiniteRankAtMost (T - c • LinearMap.id) k →
      ∃ p : Fin (k + 2) → Nat.Primes,
        Function.Injective p ∧
        ∀ f : (Fin (k + 2) → ℝ) →ₗ[ℝ] M,
          ¬ ((∀ x,
              (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
                Q (f x)) ∧
            (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
              (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
                Q (T (f x))))

/-- **[SHARED-WARD ROUTE-CLASS KILL].** Infinite target index does not rescue an essentially
scalar finite-rank reflection: no such linear quadratic carrier can produce the common
HB/FZZ-P/PW-B/RBH Ward orientation. -/
theorem sourceHorizontalFiniteRankReflectionQuadraticCarrierRouteKilled :
    SourceHorizontalFiniteRankReflectionQuadraticCarrierRouteKilled := by
  intro q hoff M _ _ Q T c k hfinite
  have hmpos : 0 < k + 2 := by omega
  obtain ⟨p, hpInjective, -, -⟩ :=
    exists_sourceZeroHorizontalSharedReservoirPacket
      q hoff (k + 2) hmpos (ε := 1) zero_lt_one
  refine ⟨p, hpInjective, ?_⟩
  intro f hlandings
  have hge :=
    sourceZeroHorizontalSharedReservoir_finiteRankReflection_ge_of_offLine
      (m := k + 2) (by omega) q hoff p Q T c k hfinite f
        hlandings.1 hlandings.2
  omega

/-- Sharp positive survivor: if one linear quadratic reflection carries every finite packet, its
difference from every real scalar operator has unbounded operational rank. -/
theorem sourceZeroHorizontalSharedReservoir_allReflectionLandings_forces_infiniteRankPerturbation
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (Q : QuadraticForm ℝ M) (T : M →ₗ[ℝ] M) (c : ℝ)
    (hlanding : ∀ (m : ℕ), 2 ≤ m → ∀ p : Fin m → Nat.Primes,
      Function.Injective p →
        ∃ f : (Fin m → ℝ) →ₗ[ℝ] M,
          (∀ x,
            (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
              Q (f x)) ∧
          (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
            (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
              Q (T (f x)))) :
    ∀ k : ℕ, ¬ LinearMapFiniteRankAtMost (T - c • LinearMap.id) k := by
  intro k hfinite
  have hmpos : 0 < k + 2 := by omega
  obtain ⟨p, hpInjective, -, -⟩ :=
    exists_sourceZeroHorizontalSharedReservoirPacket
      q hoff (k + 2) hmpos (ε := 1) zero_lt_one
  obtain ⟨f, hpull, hreflected⟩ := hlanding (k + 2) (by omega) p hpInjective
  have hge :=
    sourceZeroHorizontalSharedReservoir_finiteRankReflection_ge_of_offLine
      (m := k + 2) (by omega) q hoff p Q T c k hfinite f hpull hreflected
  omega

end

end RHTower
