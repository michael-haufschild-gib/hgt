import GaloisForLFunctions.RHTower.SourceHorizontalFiniteRankReflectionQuadraticCarrierNoGo
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Scalar-Calkin involutive reflections cannot receive all shared Ward packets

Finite-rank-near-scalar reflection is already impossible for the common HB/FZZ-P/PW-B/RBH
source. Compact perturbations might still have infinite algebraic rank, so that theorem alone does
not control a scalar Calkin class. Involutivity closes the gap.

For `K = T - cI` and `T² = I`, either `c² ≠ 1`, when

`K (T + cI) = (1 - c²) I`

makes a nonzero scalar identity compact and forces the carrier finite dimensional, or `c² = 1`,
when `(-c/2)K` is a compact idempotent and therefore has finite-dimensional range. Thus `K` has
finite operational rank in both cases, contradicting the source theorem requiring unbounded rank
for every scalar perturbation.

Consequently every bounded involutive exact all-packet reflection has non-scalar Calkin class. Its
two spectral projections are both noncompact. This kills every essentially one-orientation compact
repair before the common four-route Ward receiver; surviving dynamics must retain two infinite
essential sectors or become nonlinear, unbounded/singular, or domain-changing.

`[NEW] [SHARED-WARD NO-GO] [CALKIN REFLECTION] [ESSENTIAL BIPOLARITY]`
-/

namespace RHTower

noncomputable section

private theorem isCompactOperator_congr_fun_real
    {M : Type*} [TopologicalSpace M] [AddCommMonoid M]
    {f g : M → M} (hf : IsCompactOperator f) (h : ∀ x, f x = g x) :
    IsCompactOperator g := by
  rw [← funext h]
  exact hf

/-- A compact nonzero scalar identity forces finite dimension over the reals. -/
theorem finiteDimensional_of_compact_nonzero_smul_id_real
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (a : ℝ) (ha : a ≠ 0)
    (hcompact : IsCompactOperator (a • ContinuousLinearMap.id ℝ M)) :
    FiniteDimensional ℝ M := by
  apply FiniteDimensional.of_isCompactOperator_id
  have h := hcompact.comp_clm (a⁻¹ • ContinuousLinearMap.id ℝ M)
  apply isCompactOperator_congr_fun_real h
  intro x
  simp [ha]

/-- A compact idempotent bounded real operator has finite-dimensional range. -/
theorem finiteDimensional_range_of_compact_idempotent_real
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    {P : M →L[ℝ] M} (hcompact : IsCompactOperator P) (hP : IsIdempotentElem P) :
    FiniteDimensional ℝ (LinearMap.range (P : M →ₗ[ℝ] M)) := by
  let W : Submodule ℝ M := LinearMap.range (P : M →ₗ[ℝ] M)
  have hWclosed : IsClosed (W : Set M) :=
    ContinuousLinearMap.IsIdempotentElem.isClosed_range hP
  letI : CompleteSpace W := hWclosed.completeSpace_coe
  have hmaps : ∀ x ∈ W, (P : M →ₗ[ℝ] M) x ∈ W := by
    intro x hx
    exact ⟨x, rfl⟩
  have hrestrictCompact : IsCompactOperator ((P : M →ₗ[ℝ] M).restrict hmaps) :=
    hcompact.restrict hmaps hWclosed
  have hrestrict : (P : M →ₗ[ℝ] M).restrict hmaps = LinearMap.id := by
    ext x
    obtain ⟨y, hy⟩ := x.2
    have hmul : P (P y) = P y := by
      have := congrArg (fun A : M →L[ℝ] M => A y) hP
      simpa only [mul_apply_eq_comp] using this
    change P (x : M) = x
    rw [← hy]
    exact hmul
  apply FiniteDimensional.of_isCompactOperator_id
  simpa [hrestrict] using hrestrictCompact

/-- A compact scalar perturbation of a bounded involution has finite operational rank. -/
theorem linearMapFiniteRankAtMost_of_compactScalarPerturbation_involution
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    (T : M →L[ℝ] M) (c : ℝ)
    (hcompact : IsCompactOperator (T - c • ContinuousLinearMap.id ℝ M))
    (hinvol : T * T = 1) :
    ∃ k : ℕ, LinearMapFiniteRankAtMost
      ((T - c • ContinuousLinearMap.id ℝ M : M →L[ℝ] M) : M →ₗ[ℝ] M) k := by
  let K : M →L[ℝ] M := T - c • ContinuousLinearMap.id ℝ M
  have hKcompact : IsCompactOperator K := by exact hcompact
  by_cases hc : c ^ 2 = 1
  · let P : M →L[ℝ] M := (-c / 2) • K
    have hPcompact : IsCompactOperator P := by
      exact hKcompact.smul (-c / 2)
    have hKsq : K * K = (-2 * c) • K := by
      ext x
      have hx : T (T x) = x := by
        have := congrArg (fun A : M →L[ℝ] M => A x) hinvol
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using this
      have hc' : c * c = 1 := by simpa [pow_two] using hc
      have hcoef : (-2 * c) * c = -2 := by nlinarith [hc']
      change T (T x - c • x) - c • (T x - c • x) =
        (-2 * c) • (T x - c • x)
      rw [map_sub, map_smul, hx, smul_sub, smul_smul, hc']
      rw [smul_sub, smul_smul, hcoef]
      module
    have hP : IsIdempotentElem P := by
      dsimp only [IsIdempotentElem]
      dsimp [P]
      rw [smul_mul_smul, hKsq]
      rw [smul_smul]
      congr 1
      calc
        (-c / 2) * (-c / 2) * (-2 * c) = (-c / 2) * (c ^ 2) := by ring
        _ = -c / 2 := by rw [hc, mul_one]
    letI : FiniteDimensional ℝ (LinearMap.range (P : M →ₗ[ℝ] M)) :=
      finiteDimensional_range_of_compact_idempotent_real hPcompact hP
    refine ⟨Module.finrank ℝ (LinearMap.range (P : M →ₗ[ℝ] M)), ?_⟩
    intro V _ _ _ g
    apply Submodule.finrank_mono
    intro y hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨(-2 * c) • g x, ?_⟩
    change P ((-2 * c) • g x) = K (g x)
    simp only [P, smul_apply, map_smul, smul_smul]
    rw [show (-2 * c) * (-c / 2) = 1 by
      calc
        (-2 * c) * (-c / 2) = c ^ 2 := by ring
        _ = 1 := hc, one_smul]
  · have hfactor : K * (T + c • ContinuousLinearMap.id ℝ M) =
        (1 - c ^ 2) • ContinuousLinearMap.id ℝ M := by
      ext x
      have hx : T (T x) = x := by
        have := congrArg (fun A : M →L[ℝ] M => A x) hinvol
        simpa only [mul_apply_eq_comp, one_apply_eq_self] using this
      simp only [K, mul_apply_eq_comp, add_apply, sub_apply, smul_apply,
        ContinuousLinearMap.id_apply, map_add, map_smul, hx, pow_two]
      module
    have hscalarCompact :
        IsCompactOperator (((1 - c ^ 2) • ContinuousLinearMap.id ℝ M) :
          M →L[ℝ] M) := by
      have hprod : IsCompactOperator
          (K * (T + c • ContinuousLinearMap.id ℝ M)) := by
        apply isCompactOperator_congr_fun_real
          (hKcompact.comp_clm (T + c • ContinuousLinearMap.id ℝ M))
        intro x
        rfl
      rw [hfactor] at hprod
      exact hprod
    have ha : 1 - c ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    letI : FiniteDimensional ℝ M :=
      finiteDimensional_of_compact_nonzero_smul_id_real (1 - c ^ 2) ha hscalarCompact
    refine ⟨Module.finrank ℝ M, ?_⟩
    intro V _ _ _ g
    exact Submodule.finrank_le _

/-- One bounded carrier receives every injectively labelled source packet and its reflection. -/
def SourceHorizontalAllPacketBoundedReflectionLanding
    (q : XiZeroCopy)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (Q : QuadraticForm ℝ M) (T : M →L[ℝ] M) : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ p : Fin m → Nat.Primes,
    Function.Injective p →
      ∃ f : (Fin m → ℝ) →ₗ[ℝ] M,
        (∀ x,
          (sourceZeroHorizontalSharedReservoirMatrix q p).toQuadraticForm' x =
            Q (f x)) ∧
        (∀ x, (sourceZeroHorizontalSharedReservoirMatrix
          (xiZeroCopyLineConjEquiv q) p).toQuadraticForm' x =
            Q (T (f x)))

/-- Positive survivor: every bounded involutive all-packet reflection has non-scalar Calkin class. -/
theorem sourceZeroHorizontalSharedReservoir_allBoundedInvolutiveReflectionLandings_forces_noncompactPerturbation
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    (Q : QuadraticForm ℝ M) (T : M →L[ℝ] M)
    (hinvol : T * T = 1)
    (hlanding : SourceHorizontalAllPacketBoundedReflectionLanding q Q T) :
    ∀ c : ℝ, ¬ IsCompactOperator (T - c • ContinuousLinearMap.id ℝ M) := by
  intro c hcompact
  obtain ⟨k, hfinite⟩ :=
    linearMapFiniteRankAtMost_of_compactScalarPerturbation_involution T c hcompact hinvol
  have hfinite' : LinearMapFiniteRankAtMost
      ((T : M →ₗ[ℝ] M) - c • LinearMap.id) k := by
    intro V _ _ _ g
    exact hfinite g
  have hinfinite :=
    sourceZeroHorizontalSharedReservoir_allReflectionLandings_forces_infiniteRankPerturbation
      q hoff Q (T : M →ₗ[ℝ] M) c (by
        intro m hm p hp
        obtain ⟨f, hpull, hreflected⟩ := hlanding m hm p hp
        exact ⟨f, hpull, by
          intro x
          exact hreflected x⟩)
  exact hinfinite k hfinite'

/-- Both spectral projections of a surviving involution are noncompact. -/
theorem sourceZeroHorizontalSharedReservoir_allBoundedInvolutiveReflectionLandings_forces_bothEssentialSectors
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
    (Q : QuadraticForm ℝ M) (T : M →L[ℝ] M)
    (hinvol : T * T = 1)
    (hlanding : SourceHorizontalAllPacketBoundedReflectionLanding q Q T) :
    (¬ IsCompactOperator ((1 / 2 : ℝ) •
      (ContinuousLinearMap.id ℝ M + T))) ∧
    (¬ IsCompactOperator ((1 / 2 : ℝ) •
      (ContinuousLinearMap.id ℝ M - T))) := by
  have hnoncompact :=
    sourceZeroHorizontalSharedReservoir_allBoundedInvolutiveReflectionLandings_forces_noncompactPerturbation
      q hoff Q T hinvol hlanding
  constructor
  · intro hplus
    apply hnoncompact (-1)
    have hscaled := hplus.smul (2 : ℝ)
    apply isCompactOperator_congr_fun_real hscaled
    intro x
    simp
    module
  · intro hminus
    apply hnoncompact 1
    have hscaled := hminus.smul (-2 : ℝ)
    apply isCompactOperator_congr_fun_real hscaled
    intro x
    simp

/-- Closed route class: scalar-Calkin bounded involutions cannot be the common reflected producer. -/
def SourceHorizontalScalarCalkinInvolutiveReflectionRouteKilled : Prop :=
  ∀ (q : XiZeroCopy), (q.1 : ℂ).re ≠ 1 / 2 →
    ∀ (M : Type) [NormedAddCommGroup M] [NormedSpace ℝ M] [CompleteSpace M]
      (Q : QuadraticForm ℝ M) (T : M →L[ℝ] M),
      T * T = 1 →
      ∀ c : ℝ, IsCompactOperator (T - c • ContinuousLinearMap.id ℝ M) →
        ¬ SourceHorizontalAllPacketBoundedReflectionLanding q Q T

/-- **[SHARED-WARD ROUTE-CLASS KILL].** No bounded involutive exact all-packet reflection is
scalar modulo compact operators, including on arbitrary infinite-index Banach carriers. -/
theorem sourceHorizontalScalarCalkinInvolutiveReflectionRouteKilled :
    SourceHorizontalScalarCalkinInvolutiveReflectionRouteKilled := by
  intro q hoff M _ _ _ Q T hinvol c hcompact hlanding
  exact
    sourceZeroHorizontalSharedReservoir_allBoundedInvolutiveReflectionLandings_forces_noncompactPerturbation
      q hoff Q T hinvol hlanding c hcompact

end

end RHTower
