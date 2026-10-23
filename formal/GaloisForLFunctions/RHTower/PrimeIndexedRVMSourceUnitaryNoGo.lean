import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMRelocation
import GaloisForLFunctions.RHTower.PrimeIndexedRVMSignedSkeleton
import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm
import GaloisForLFunctions.HTGeometry.SourceLinearClosedRelationSplitting
import GaloisForLFunctions.RHTower.XiPrimeMarkedCofinalTriangleNuclearCarrier
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuadraticIncidence
import GaloisForLFunctions.RHTower.XiPrimeMarkedPhysicalEndpointRVMQuarticIncidence
import GaloisForLFunctions.RHTower.SoninApertureAreaRigidity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace
import GaloisForLFunctions.RHTower.TraceNormLimit
import GaloisForLFunctions.HTGeometry.NonnegativeSumCriterionNoGo
import GaloisForLFunctions.HTGeometry.DeterminantCompletionNaturality
import GaloisForLFunctions.HTGeometry.OperatorDeterminantScaling
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.HTGeometry.HilbertSchmidtSpace
import GaloisForLFunctions.HTGeometry.RegularizedResolventTraceOperator
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtCompactOpen
import GaloisForLFunctions.HTGeometry.HermitianDilationSecondJetObstruction
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantTraceRecovery
import GaloisForLFunctions.HTGeometry.CompactSelfAdjointEigenvalue
import GaloisForLFunctions.RHTower.GammaPrimeHybridEulerWeierstrassFredholmUniversalityLaw

/-!
# Prime-source RVM unitary-recovery obstruction

The literal completed-endpoint correction is a nonzero Hilbert--Schmidt operator orthogonal to
the smooth prime Riemann--von Mangoldt skeleton.  Any unitary recovery of the skeleton from a
Hilbert--Schmidt-corrected source must instead have the exact negative cross energy
`Re <K,C> = -‖C‖² / 2`.  Hence the literal orthogonal correction cannot supply an eigenbasis or
isospectral recovery.  The surviving source requirement is an indefinite, non-orthogonal
correction satisfying this cancellation law.
-/

namespace RHTower

noncomputable section

open scoped Matrix

/-- Ordinary trace is invariant under a Route K unitary transport of every Schatten-one
operator.  This is the global invariant needed when a unitary is allowed to mix a finite
source triangle with its infinite-dimensional complement. -/
theorem opTrace_unitaryPush_routeK_of_memSchattenClass_one
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hT : MemSchattenClass 1 T)
    (u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert) :
    ContinuousLinearMap.opTrace (unitaryPush u T) =
      ContinuousLinearMap.opTrace T := by
  rw [unitaryPush]
  let U : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
    u.toLinearIsometry.toContinuousLinearMap
  let V : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
    u.symm.toLinearIsometry.toContinuousLinearMap
  change ContinuousLinearMap.opTrace (U ∘L (T ∘L V)) =
    ContinuousLinearMap.opTrace T
  calc
    ContinuousLinearMap.opTrace (U ∘L (T ∘L V)) =
        ContinuousLinearMap.opTrace ((T ∘L V) ∘L U) := by
      exact (memSchattenClass_one_comp_right hT V).one_opTrace_comp_comm U
    _ = ContinuousLinearMap.opTrace T := by
      congr 1
      apply ContinuousLinearMap.ext
      intro x
      simp [U, V]

/-- A Route K Schatten-one carrier with nonzero ordinary trace cannot be globally unitarily
conjugate to its negative. -/
theorem not_exists_unitaryPush_eq_neg_routeK_of_memSchattenClass_one_opTrace_ne_zero
    (T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hT : MemSchattenClass 1 T)
    (htrace : ContinuousLinearMap.opTrace T ≠ 0) :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u T = -T := by
  rintro ⟨u, hu⟩
  have hinvariant := opTrace_unitaryPush_routeK_of_memSchattenClass_one T hT u
  rw [hu, opTrace_neg] at hinvariant
  apply htrace
  have hdouble : (2 : ℂ) * ContinuousLinearMap.opTrace T = 0 := by
    calc
      (2 : ℂ) * ContinuousLinearMap.opTrace T =
          ContinuousLinearMap.opTrace T + ContinuousLinearMap.opTrace T := by ring
      _ = ContinuousLinearMap.opTrace T + (-ContinuousLinearMap.opTrace T) := by
        rw [hinvariant]
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hdouble).resolve_left (by norm_num)

/-- Exact action of a selected source triangle at its first marked prime. -/
theorem routeKCofinalTriangleSymmetricBlock_apply_zero (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKPrimeBasis (routeKCofinalTrianglePrime n 0)) =
      lp.single 2 (routeKCofinalTrianglePrime n 1)
        (routeKCofinalTriangleAmplitude n 0 : ℂ) +
      lp.single 2 (routeKCofinalTrianglePrime n 2)
        (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
  apply lp.ext
  funext q
  have hmatrix := routeKCofinalTriangleSymmetricBlock_matrix n q
    (routeKCofinalTrianglePrime n 0)
  have hinner :
      inner ℂ (routeKPrimeBasis q)
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))) =
        inner ℂ (routeKPrimeBasis q)
          (lp.single 2 (routeKCofinalTrianglePrime n 1)
              (routeKCofinalTriangleAmplitude n 0 : ℂ) +
            lp.single 2 (routeKCofinalTrianglePrime n 2)
              (routeKCofinalTriangleAmplitude n 2 : ℂ)) := by
    rw [hmatrix]
    simp [routeKPrimeBasis, lp.inner_single_left, Pi.single_apply, eq_comm,
      Fin.sum_univ_three, (routeKCofinalTrianglePrime_injective n).eq_iff]
  simpa [routeKPrimeBasis, lp.inner_single_left] using hinner

/-- Exact action of a selected source triangle at its second marked prime. -/
theorem routeKCofinalTriangleSymmetricBlock_apply_one (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKPrimeBasis (routeKCofinalTrianglePrime n 1)) =
      lp.single 2 (routeKCofinalTrianglePrime n 0)
        (routeKCofinalTriangleAmplitude n 0 : ℂ) +
      lp.single 2 (routeKCofinalTrianglePrime n 2)
        (routeKCofinalTriangleAmplitude n 1 : ℂ) := by
  apply lp.ext
  funext q
  have hmatrix := routeKCofinalTriangleSymmetricBlock_matrix n q
    (routeKCofinalTrianglePrime n 1)
  have hinner :
      inner ℂ (routeKPrimeBasis q)
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))) =
        inner ℂ (routeKPrimeBasis q)
          (lp.single 2 (routeKCofinalTrianglePrime n 0)
              (routeKCofinalTriangleAmplitude n 0 : ℂ) +
            lp.single 2 (routeKCofinalTrianglePrime n 2)
              (routeKCofinalTriangleAmplitude n 1 : ℂ)) := by
    rw [hmatrix]
    simp [routeKPrimeBasis, lp.inner_single_left, Pi.single_apply, eq_comm,
      Fin.sum_univ_three, (routeKCofinalTrianglePrime_injective n).eq_iff]
  simpa [routeKPrimeBasis, lp.inner_single_left] using hinner

/-- Exact action of a selected source triangle at its third marked prime. -/
theorem routeKCofinalTriangleSymmetricBlock_apply_two (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKPrimeBasis (routeKCofinalTrianglePrime n 2)) =
      lp.single 2 (routeKCofinalTrianglePrime n 1)
        (routeKCofinalTriangleAmplitude n 1 : ℂ) +
      lp.single 2 (routeKCofinalTrianglePrime n 0)
        (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
  apply lp.ext
  funext q
  have hmatrix := routeKCofinalTriangleSymmetricBlock_matrix n q
    (routeKCofinalTrianglePrime n 2)
  have hinner :
      inner ℂ (routeKPrimeBasis q)
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))) =
        inner ℂ (routeKPrimeBasis q)
          (lp.single 2 (routeKCofinalTrianglePrime n 1)
              (routeKCofinalTriangleAmplitude n 1 : ℂ) +
            lp.single 2 (routeKCofinalTrianglePrime n 0)
              (routeKCofinalTriangleAmplitude n 2 : ℂ)) := by
    rw [hmatrix]
    simp [routeKPrimeBasis, lp.inner_single_left, Pi.single_apply, eq_comm,
      Fin.sum_univ_three, (routeKCofinalTrianglePrime_injective n).eq_iff]
  simpa [routeKPrimeBasis, lp.inner_single_left] using hinner

/-- A selected triangle has no action outside its three literal prime vertices. -/
theorem routeKCofinalTriangleSymmetricBlock_apply_eq_zero_of_not_mem
    (n : ℕ) (p : Nat.Primes)
    (hp : ∀ i : Fin 3, p ≠ routeKCofinalTrianglePrime n i) :
    routeKCofinalTriangleSymmetricBlock n (routeKPrimeBasis p) = 0 := by
  apply lp.ext
  funext q
  have hinner : inner ℂ (routeKPrimeBasis q)
      (routeKCofinalTriangleSymmetricBlock n (routeKPrimeBasis p)) = 0 := by
    rw [routeKCofinalTriangleSymmetricBlock_matrix]
    apply Finset.sum_eq_zero
    intro i _
    have hnext : routeKCofinalTrianglePrimeNext n i ≠ p := by
      fin_cases i
      · exact Ne.symm (hp 1)
      · exact Ne.symm (hp 2)
      · exact Ne.symm (hp 0)
    have hprime : routeKCofinalTrianglePrime n i ≠ p := Ne.symm (hp i)
    simp [hprime, hnext]
  simpa [routeKPrimeBasis, lp.inner_single_left] using hinner

/-- The cubic return is likewise supported on the same three literal vertices. -/
theorem routeKCofinalTriangleSymmetricBlock_cube_apply_eq_zero_of_not_mem
    (n : ℕ) (p : Nat.Primes)
    (hp : ∀ i : Fin 3, p ≠ routeKCofinalTrianglePrime n i) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n (routeKPrimeBasis p))) = 0 := by
  rw [routeKCofinalTriangleSymmetricBlock_apply_eq_zero_of_not_mem n p hp]
  simp

private theorem routeKCofinalTriangleSymmetricBlock_apply_zero_scaled (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKPrimeBasis (routeKCofinalTrianglePrime n 0)) =
      (routeKCofinalTriangleAmplitude n 0 : ℂ) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 1) +
      (routeKCofinalTriangleAmplitude n 2 : ℂ) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 2) := by
  simpa only [routeKPrimeBasis, ← lp.single_smul, smul_eq_mul, mul_one] using
    routeKCofinalTriangleSymmetricBlock_apply_zero n

private theorem routeKCofinalTriangleSymmetricBlock_apply_one_scaled (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKPrimeBasis (routeKCofinalTrianglePrime n 1)) =
      (routeKCofinalTriangleAmplitude n 0 : ℂ) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 0) +
      (routeKCofinalTriangleAmplitude n 1 : ℂ) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 2) := by
  simpa only [routeKPrimeBasis, ← lp.single_smul, smul_eq_mul, mul_one] using
    routeKCofinalTriangleSymmetricBlock_apply_one n

private theorem routeKCofinalTriangleSymmetricBlock_apply_two_scaled (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKPrimeBasis (routeKCofinalTrianglePrime n 2)) =
      (routeKCofinalTriangleAmplitude n 1 : ℂ) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 1) +
      (routeKCofinalTriangleAmplitude n 2 : ℂ) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 0) := by
  simpa only [routeKPrimeBasis, ← lp.single_smul, smul_eq_mul, mul_one] using
    routeKCofinalTriangleSymmetricBlock_apply_two n

/-- The second iterate on the first selected prime has its exact three-vertex expansion. -/
theorem routeKCofinalTriangleSymmetricBlock_sq_apply_zero (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))) =
      ((routeKCofinalTriangleAmplitude n 0 : ℂ) ^ 2 +
          (routeKCofinalTriangleAmplitude n 2 : ℂ) ^ 2) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 0) +
      ((routeKCofinalTriangleAmplitude n 1 : ℂ) *
          (routeKCofinalTriangleAmplitude n 2 : ℂ)) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 1) +
      ((routeKCofinalTriangleAmplitude n 0 : ℂ) *
          (routeKCofinalTriangleAmplitude n 1 : ℂ)) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 2) := by
  rw [routeKCofinalTriangleSymmetricBlock_apply_zero_scaled,
    map_add, map_smul, map_smul,
    routeKCofinalTriangleSymmetricBlock_apply_one_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_two_scaled]
  module

/-- The second iterate on the second selected prime has its exact three-vertex expansion. -/
theorem routeKCofinalTriangleSymmetricBlock_sq_apply_one (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))) =
      ((routeKCofinalTriangleAmplitude n 1 : ℂ) *
          (routeKCofinalTriangleAmplitude n 2 : ℂ)) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 0) +
      ((routeKCofinalTriangleAmplitude n 0 : ℂ) ^ 2 +
          (routeKCofinalTriangleAmplitude n 1 : ℂ) ^ 2) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 1) +
      ((routeKCofinalTriangleAmplitude n 0 : ℂ) *
          (routeKCofinalTriangleAmplitude n 2 : ℂ)) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 2) := by
  rw [routeKCofinalTriangleSymmetricBlock_apply_one_scaled,
    map_add, map_smul, map_smul,
    routeKCofinalTriangleSymmetricBlock_apply_zero_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_two_scaled]
  module

/-- The second iterate on the third selected prime has its exact three-vertex expansion. -/
theorem routeKCofinalTriangleSymmetricBlock_sq_apply_two (n : ℕ) :
    routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))) =
      ((routeKCofinalTriangleAmplitude n 0 : ℂ) *
          (routeKCofinalTriangleAmplitude n 1 : ℂ)) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 0) +
      ((routeKCofinalTriangleAmplitude n 0 : ℂ) *
          (routeKCofinalTriangleAmplitude n 2 : ℂ)) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 1) +
      ((routeKCofinalTriangleAmplitude n 1 : ℂ) ^ 2 +
          (routeKCofinalTriangleAmplitude n 2 : ℂ) ^ 2) •
        routeKPrimeBasis (routeKCofinalTrianglePrime n 2) := by
  rw [routeKCofinalTriangleSymmetricBlock_apply_two_scaled,
    map_add, map_smul, map_smul,
    routeKCofinalTriangleSymmetricBlock_apply_one_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_zero_scaled]
  module

/-- The literal odd triangle has a nonzero third-order return at every selected block. -/
theorem inner_routeKCofinalTriangleSymmetricBlock_cube_apply_zero (n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))
      (routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))))) =
      2 * (routeKCofinalTriangleAmplitude n 0 : ℂ) *
        (routeKCofinalTriangleAmplitude n 1 : ℂ) *
        (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
  rw [routeKCofinalTriangleSymmetricBlock_sq_apply_zero,
    map_add, map_smul, map_add, map_smul, map_smul,
    routeKCofinalTriangleSymmetricBlock_apply_zero_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_one_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_two_scaled]
  have hnorm : ‖routeKPrimeBasis (routeKCofinalTrianglePrime n 0)‖ = 1 := by
    rw [routeKPrimeBasis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    norm_num
  simp [hnorm, inner_routeKPrimeBasis_routeKPrimeBasis,
    (routeKCofinalTrianglePrime_injective n).eq_iff]
  ring

/-- The same odd return occurs at the second selected prime. -/
theorem inner_routeKCofinalTriangleSymmetricBlock_cube_apply_one (n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))
      (routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKPrimeBasis (routeKCofinalTrianglePrime n 1))))) =
      2 * (routeKCofinalTriangleAmplitude n 0 : ℂ) *
        (routeKCofinalTriangleAmplitude n 1 : ℂ) *
        (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
  rw [routeKCofinalTriangleSymmetricBlock_sq_apply_one,
    map_add, map_smul, map_add, map_smul, map_smul,
    routeKCofinalTriangleSymmetricBlock_apply_zero_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_one_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_two_scaled]
  have hnorm : ‖routeKPrimeBasis (routeKCofinalTrianglePrime n 1)‖ = 1 := by
    rw [routeKPrimeBasis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    norm_num
  simp [hnorm, inner_routeKPrimeBasis_routeKPrimeBasis,
    (routeKCofinalTrianglePrime_injective n).eq_iff]
  ring

/-- The same odd return occurs at the third selected prime. -/
theorem inner_routeKCofinalTriangleSymmetricBlock_cube_apply_two (n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))
      (routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKPrimeBasis (routeKCofinalTrianglePrime n 2))))) =
      2 * (routeKCofinalTriangleAmplitude n 0 : ℂ) *
        (routeKCofinalTriangleAmplitude n 1 : ℂ) *
        (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
  rw [routeKCofinalTriangleSymmetricBlock_sq_apply_two,
    map_add, map_smul, map_add, map_smul, map_smul,
    routeKCofinalTriangleSymmetricBlock_apply_zero_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_one_scaled,
    routeKCofinalTriangleSymmetricBlock_apply_two_scaled]
  have hnorm : ‖routeKPrimeBasis (routeKCofinalTrianglePrime n 2)‖ = 1 := by
    rw [routeKPrimeBasis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    norm_num
  simp [hnorm, inner_routeKPrimeBasis_routeKPrimeBasis,
    (routeKCofinalTrianglePrime_injective n).eq_iff]
  ring

/-- Thus every selected source triangle has a genuinely nonzero odd return. -/
theorem inner_routeKCofinalTriangleSymmetricBlock_cube_apply_zero_ne_zero (n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))
      (routeKCofinalTriangleSymmetricBlock n
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKPrimeBasis (routeKCofinalTrianglePrime n 0))))) ≠ 0 := by
  rw [inner_routeKCofinalTriangleSymmetricBlock_cube_apply_zero]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr (routeKCofinalTriangleAmplitude_pos n 0).ne'))
      (Complex.ofReal_ne_zero.mpr (routeKCofinalTriangleAmplitude_pos n 1).ne'))
    (Complex.ofReal_ne_zero.mpr (routeKCofinalTriangleAmplitude_pos n 2).ne')

/-- A Schatten-one operator has ordinary trace given by the diagonal sum in any Hilbert basis. -/
private theorem opTrace_eq_tsum_basis_of_memSchattenClass_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : MemSchattenClass 1 T)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    ContinuousLinearMap.opTrace T = ∑' i, inner ℂ (b i) (T (b i)) := by
  obtain ⟨A, B, hA, hB, hfac⟩ := hT.one_isTraceClass
  rw [hfac]
  exact ContinuousLinearMap.opTrace_comp_eq_tsum_basis hA hB b

/-- Each literal cofinal prime triangle is a finite-rank Schatten-one operator on the full
prime Hilbert space. -/
theorem routeKCofinalTriangleSymmetricBlock_memSchattenClass_one
    (n : ℕ) :
    MemSchattenClass 1 (routeKCofinalTriangleSymmetricBlock n) := by
  rw [← routeKCofinalTriangleRankOneTerm_sum_fiber n]
  simpa only [tsum_fintype] using
    (memSchattenClass_one_tsum_rankOneTerms_of_summable_norm
      (fun io : Fin 3 × Fin 2 => routeKCofinalTriangleRankOneTerm (n, io))
      (fun io => routeKCofinalTriangleRankOneTerm_hasRankLE (n, io))
      Summable.of_finite)

/-- The cubic return of a cofinal triangle remains Schatten-one on the full prime Hilbert space. -/
theorem routeKCofinalTriangleSymmetricBlock_cube_memSchattenClass_one
    (n : ℕ) :
    MemSchattenClass 1
      (routeKCofinalTriangleSymmetricBlock n ∘L
        (routeKCofinalTriangleSymmetricBlock n ∘L
          routeKCofinalTriangleSymmetricBlock n)) := by
  exact memSchattenClass_one_comp_left
    (memSchattenClass_one_comp_left
      (routeKCofinalTriangleSymmetricBlock_memSchattenClass_one n)
      (routeKCofinalTriangleSymmetricBlock n))
    (routeKCofinalTriangleSymmetricBlock n)

/-- The full-space cubic trace of a literal cofinal prime triangle is its two oriented cyclic
returns.  In particular, complement-mixing cannot erase this odd source invariant. -/
theorem opTrace_routeKCofinalTriangleSymmetricBlock_cube
    (n : ℕ) :
    ContinuousLinearMap.opTrace
      (routeKCofinalTriangleSymmetricBlock n ∘L
        (routeKCofinalTriangleSymmetricBlock n ∘L
          routeKCofinalTriangleSymmetricBlock n)) =
      6 * (routeKCofinalTriangleAmplitude n 0 : ℂ) *
        (routeKCofinalTriangleAmplitude n 1 : ℂ) *
        (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one
    (routeKCofinalTriangleSymmetricBlock_cube_memSchattenClass_one n)
    (HilbertSchmidt.lpBasis Nat.Primes)]
  let s : Finset Nat.Primes := {routeKCofinalTrianglePrime n 0,
    routeKCofinalTrianglePrime n 1, routeKCofinalTrianglePrime n 2}
  have hdiag0 :
      inner ℂ (HilbertSchmidt.lpBasis Nat.Primes (routeKCofinalTrianglePrime n 0))
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKCofinalTriangleSymmetricBlock n
              (HilbertSchmidt.lpBasis Nat.Primes (routeKCofinalTrianglePrime n 0)))) ) =
        2 * (routeKCofinalTriangleAmplitude n 0 : ℂ) *
          (routeKCofinalTriangleAmplitude n 1 : ℂ) *
          (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
    simpa [HilbertSchmidt.lpBasis_apply, routeKPrimeBasis] using
      inner_routeKCofinalTriangleSymmetricBlock_cube_apply_zero n
  have hdiag1 :
      inner ℂ (HilbertSchmidt.lpBasis Nat.Primes (routeKCofinalTrianglePrime n 1))
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKCofinalTriangleSymmetricBlock n
              (HilbertSchmidt.lpBasis Nat.Primes (routeKCofinalTrianglePrime n 1)))) ) =
        2 * (routeKCofinalTriangleAmplitude n 0 : ℂ) *
          (routeKCofinalTriangleAmplitude n 1 : ℂ) *
          (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
    simpa [HilbertSchmidt.lpBasis_apply, routeKPrimeBasis] using
      inner_routeKCofinalTriangleSymmetricBlock_cube_apply_one n
  have hdiag2 :
      inner ℂ (HilbertSchmidt.lpBasis Nat.Primes (routeKCofinalTrianglePrime n 2))
        (routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKCofinalTriangleSymmetricBlock n
              (HilbertSchmidt.lpBasis Nat.Primes (routeKCofinalTrianglePrime n 2)))) ) =
        2 * (routeKCofinalTriangleAmplitude n 0 : ℂ) *
          (routeKCofinalTriangleAmplitude n 1 : ℂ) *
          (routeKCofinalTriangleAmplitude n 2 : ℂ) := by
    simpa [HilbertSchmidt.lpBasis_apply, routeKPrimeBasis] using
      inner_routeKCofinalTriangleSymmetricBlock_cube_apply_two n
  rw [tsum_eq_sum (s := s)]
  · simp [s, (routeKCofinalTrianglePrime_injective n).eq_iff]
    rw [hdiag0, hdiag1, hdiag2]
    ring
  · intro p hp
    have hp' : p ≠ routeKCofinalTrianglePrime n 0 ∧
        p ≠ routeKCofinalTrianglePrime n 1 ∧
        p ≠ routeKCofinalTrianglePrime n 2 := by
      simpa [s] using hp
    have hzero := routeKCofinalTriangleSymmetricBlock_cube_apply_eq_zero_of_not_mem n p
      (fun i => by
        fin_cases i
        · exact hp'.1
        · exact hp'.2.1
        · exact hp'.2.2)
    have hzero' :
        routeKCofinalTriangleSymmetricBlock n
          (routeKCofinalTriangleSymmetricBlock n
            (routeKCofinalTriangleSymmetricBlock n
              (lp.single 2 p (1 : ℂ)))) = 0 := by
      simpa [routeKPrimeBasis] using hzero
    rw [HilbertSchmidt.lpBasis_apply]
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun v => inner ℂ (lp.single 2 p (1 : ℂ)) v) hzero'

/-- No global unitary may send a literal cofinal source triangle to its negative: the cubic
ordinary trace rules out even a unitary that mixes the triangle with its complement. -/
theorem not_exists_unitaryPush_neg_routeKCofinalTriangleSymmetricBlock
    (n : ℕ) :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u (routeKCofinalTriangleSymmetricBlock n) =
        -routeKCofinalTriangleSymmetricBlock n := by
  rintro ⟨u, hu⟩
  have hcube : unitaryPush u
      (routeKCofinalTriangleSymmetricBlock n ∘L
        (routeKCofinalTriangleSymmetricBlock n ∘L
          routeKCofinalTriangleSymmetricBlock n)) =
      -(routeKCofinalTriangleSymmetricBlock n ∘L
        (routeKCofinalTriangleSymmetricBlock n ∘L
          routeKCofinalTriangleSymmetricBlock n)) := by
    change unitaryPush u (routeKCofinalTriangleSymmetricBlock n *
      (routeKCofinalTriangleSymmetricBlock n *
        routeKCofinalTriangleSymmetricBlock n)) =
      -(routeKCofinalTriangleSymmetricBlock n *
        (routeKCofinalTriangleSymmetricBlock n *
          routeKCofinalTriangleSymmetricBlock n))
    rw [unitaryPush_mul, unitaryPush_mul, hu]
    noncomm_ring
  apply not_exists_unitaryPush_eq_neg_routeK_of_memSchattenClass_one_opTrace_ne_zero
    (routeKCofinalTriangleSymmetricBlock n ∘L
      (routeKCofinalTriangleSymmetricBlock n ∘L
        routeKCofinalTriangleSymmetricBlock n))
    (routeKCofinalTriangleSymmetricBlock_cube_memSchattenClass_one n)
  · rw [opTrace_routeKCofinalTriangleSymmetricBlock_cube]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr (routeKCofinalTriangleAmplitude_pos n 0).ne'))
        (Complex.ofReal_ne_zero.mpr (routeKCofinalTriangleAmplitude_pos n 1).ne'))
      (Complex.ofReal_ne_zero.mpr (routeKCofinalTriangleAmplitude_pos n 2).ne')
  · exact ⟨u, hcube⟩

/-- Arbitrarily far out in the literal prime source, a triangle resists every global
unitary sign reversal. -/
theorem exists_cofinal_routeKCofinalTriangleSymmetricBlock_no_unitaryPush_neg
    (N : ℕ) :
    ∃ n : ℕ, N ≤ routeKCofinalTriangleStart n ∧
      ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
        unitaryPush u (routeKCofinalTriangleSymmetricBlock n) =
          -routeKCofinalTriangleSymmetricBlock n := by
  exact ⟨N, routeKCofinalTriangleStart_self_le N,
    not_exists_unitaryPush_neg_routeKCofinalTriangleSymmetricBlock N⟩

/-- A triangle block kills every basis vector belonging to a distinct selected triangle. -/
theorem routeKCofinalTriangleSymmetricBlock_apply_eq_zero_of_disjoint
    {m n : ℕ} (hmn : m ≠ n) (i : Fin 3) :
    routeKCofinalTriangleSymmetricBlock m
        (routeKPrimeBasis (routeKCofinalTrianglePrime n i)) = 0 := by
  apply lp.ext
  funext q
  have hprime : ∀ j : Fin 3,
      routeKCofinalTrianglePrime m j ≠ routeKCofinalTrianglePrime n i := by
    rcases lt_or_gt_of_ne hmn with hlt | hlt
    · intro j
      exact routeKCofinalTrianglePrime_disjoint hlt j i
    · intro j
      exact (routeKCofinalTrianglePrime_disjoint hlt i j).symm
  have hnext : ∀ j : Fin 3,
      routeKCofinalTrianglePrimeNext m j ≠ routeKCofinalTrianglePrime n i := by
    intro j
    fin_cases j
    · simpa using hprime 1
    · simpa using hprime 2
    · simpa using hprime 0
  have hinner :
      inner ℂ (routeKPrimeBasis q)
        (routeKCofinalTriangleSymmetricBlock m
          (routeKPrimeBasis (routeKCofinalTrianglePrime n i))) = 0 := by
    rw [routeKCofinalTriangleSymmetricBlock_matrix]
    apply Finset.sum_eq_zero
    intro j _
    simp [hprime j, hnext j]
  simpa [routeKPrimeBasis, lp.inner_single_left] using hinner

/-- The cofinal nuclear carrier acts exactly as its selected finite block on every vertex of
that block.  Later blocks cannot alter a retained triangle. -/
theorem routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock
    (K n : ℕ) (i : Fin 3) :
    routeKCofinalTriangleNuclearCarrierFrom K
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) i)) =
      routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) i)) := by
  let A : (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ]
      RouteKPrimeHilbert :=
    ContinuousLinearMap.apply ℂ RouteKPrimeHilbert
      (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) i))
  rw [routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks]
  have hmap := A.map_tsum
    (summable_routeKCofinalTriangleSymmetricBlock_add K)
  rw [show
      (∑' m, routeKCofinalTriangleSymmetricBlock (m + K))
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) i)) =
        ∑' m, routeKCofinalTriangleSymmetricBlock (m + K)
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) i)) by
    simpa [A] using hmap]
  rw [tsum_eq_single n]
  intro m hmn
  apply routeKCofinalTriangleSymmetricBlock_apply_eq_zero_of_disjoint
  exact fun h => hmn (Nat.add_right_cancel h)

/-- On the first vertex of a retained block, one carrier step after a block step is still the
same block step; this carries the local odd-cycle invariant into the full tail. -/
private theorem routeKCofinalTriangleNuclearCarrierFrom_apply_block_apply_zero
    (K n : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K
      (routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))) =
      routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))) := by
  rw [routeKCofinalTriangleSymmetricBlock_apply_zero]
  have hsingle (p : Nat.Primes) (a : ℝ) :
      lp.single 2 p (a : ℂ) = (a : ℂ) • routeKPrimeBasis p := by
    rw [routeKPrimeBasis, ← lp.single_smul]
    simp
  rw [hsingle, hsingle]
  simp only [map_add, map_smul]
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock,
    routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]

/-- Two carrier steps after the local block input equal the finite block's third return. -/
private theorem routeKCofinalTriangleNuclearCarrierFrom_sq_apply_block_apply_zero
    (K n : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0)))) =
      routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKCofinalTriangleSymmetricBlock (n + K)
            (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0)))) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_block_apply_zero]
  rw [routeKCofinalTriangleSymmetricBlock_sq_apply_zero]
  simp only [map_add, map_smul]
  repeat' rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]

/-- Each retained cofinal tail has an explicit strictly nonzero cubic diagonal return at the first
vertex of every selected block.  This is the local ingredient for a whole-tail odd-trace law. -/
theorem inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_zero
    (K n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))))) =
      2 * (routeKCofinalTriangleAmplitude (n + K) 0 : ℂ) *
        (routeKCofinalTriangleAmplitude (n + K) 1 : ℂ) *
        (routeKCofinalTriangleAmplitude (n + K) 2 : ℂ) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]
  rw [routeKCofinalTriangleNuclearCarrierFrom_sq_apply_block_apply_zero]
  exact inner_routeKCofinalTriangleSymmetricBlock_cube_apply_zero (n + K)

private theorem routeKCofinalTriangleNuclearCarrierFrom_apply_block_apply_one
    (K n : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K
      (routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))) =
      routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))) := by
  rw [routeKCofinalTriangleSymmetricBlock_apply_one]
  have hsingle (p : Nat.Primes) (a : ℝ) :
      lp.single 2 p (a : ℂ) = (a : ℂ) • routeKPrimeBasis p := by
    rw [routeKPrimeBasis, ← lp.single_smul]
    simp
  rw [hsingle, hsingle]
  simp only [map_add, map_smul]
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock,
    routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]

private theorem routeKCofinalTriangleNuclearCarrierFrom_apply_block_apply_two
    (K n : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K
      (routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))) =
      routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))) := by
  rw [routeKCofinalTriangleSymmetricBlock_apply_two]
  have hsingle (p : Nat.Primes) (a : ℝ) :
      lp.single 2 p (a : ℂ) = (a : ℂ) • routeKPrimeBasis p := by
    rw [routeKPrimeBasis, ← lp.single_smul]
    simp
  rw [hsingle, hsingle]
  simp only [map_add, map_smul]
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock,
    routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]

private theorem routeKCofinalTriangleNuclearCarrierFrom_sq_apply_block_apply_one
    (K n : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1)))) =
      routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKCofinalTriangleSymmetricBlock (n + K)
            (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1)))) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_block_apply_one]
  rw [routeKCofinalTriangleSymmetricBlock_sq_apply_one]
  simp only [map_add, map_smul]
  repeat' rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]

private theorem routeKCofinalTriangleNuclearCarrierFrom_sq_apply_block_apply_two
    (K n : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2)))) =
      routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKCofinalTriangleSymmetricBlock (n + K)
            (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2)))) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_block_apply_two]
  rw [routeKCofinalTriangleSymmetricBlock_sq_apply_two]
  simp only [map_add, map_smul]
  repeat' rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]

/-- The same full-tail cubic return occurs at the second vertex of every selected block. -/
theorem inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_one
    (K n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))))) =
      2 * (routeKCofinalTriangleAmplitude (n + K) 0 : ℂ) *
        (routeKCofinalTriangleAmplitude (n + K) 1 : ℂ) *
        (routeKCofinalTriangleAmplitude (n + K) 2 : ℂ) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]
  rw [routeKCofinalTriangleNuclearCarrierFrom_sq_apply_block_apply_one]
  exact inner_routeKCofinalTriangleSymmetricBlock_cube_apply_one (n + K)

/-- The same full-tail cubic return occurs at the third vertex of every selected block. -/
theorem inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_two
    (K n : ℕ) :
    inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))))) =
      2 * (routeKCofinalTriangleAmplitude (n + K) 0 : ℂ) *
        (routeKCofinalTriangleAmplitude (n + K) 1 : ℂ) *
        (routeKCofinalTriangleAmplitude (n + K) 2 : ℂ) := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_selectedBlock]
  rw [routeKCofinalTriangleNuclearCarrierFrom_sq_apply_block_apply_two]
  exact inner_routeKCofinalTriangleSymmetricBlock_cube_apply_two (n + K)

/-- The cubic power of the complete cofinal source tail remains Schatten-one. -/
private theorem routeKCofinalTriangleNuclearCarrierFrom_cube_memSchattenClass_one
    (K : ℕ) :
    MemSchattenClass 1
      (routeKCofinalTriangleNuclearCarrierFrom K ∘L
        (routeKCofinalTriangleNuclearCarrierFrom K ∘L
          routeKCofinalTriangleNuclearCarrierFrom K)) := by
  exact memSchattenClass_one_comp_left
    (memSchattenClass_one_comp_left
      (routeKCofinalTriangleNuclearCarrierFrom_memSchattenClass_one K)
      (routeKCofinalTriangleNuclearCarrierFrom K))
    (routeKCofinalTriangleNuclearCarrierFrom K)

/-- A cofinal source tail annihilates a basis vector outside all of its retained triangles. -/
private theorem routeKCofinalTriangleNuclearCarrierFrom_apply_eq_zero_of_not_mem
    (K : ℕ) (p : Nat.Primes)
    (hp : ∀ n : ℕ, ∀ i : Fin 3,
      p ≠ routeKCofinalTrianglePrime (n + K) i) :
    routeKCofinalTriangleNuclearCarrierFrom K (routeKPrimeBasis p) = 0 := by
  let A : (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) →L[ℂ]
      RouteKPrimeHilbert :=
    ContinuousLinearMap.apply ℂ RouteKPrimeHilbert (routeKPrimeBasis p)
  rw [routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks]
  have hmap := A.map_tsum
    (summable_routeKCofinalTriangleSymmetricBlock_add K)
  rw [show
      (∑' n, routeKCofinalTriangleSymmetricBlock (n + K))
          (routeKPrimeBasis p) =
        ∑' n, routeKCofinalTriangleSymmetricBlock (n + K)
          (routeKPrimeBasis p) by
    simpa [A] using hmap]
  have hzero :
      (fun n : ℕ => routeKCofinalTriangleSymmetricBlock (n + K)
        (routeKPrimeBasis p)) = 0 := by
    funext n
    apply routeKCofinalTriangleSymmetricBlock_apply_eq_zero_of_not_mem
    exact hp n
  rw [hzero]
  exact tsum_zero

/-- Outside the retained triangles, the cofinal source tail has zero cubic diagonal. -/
private theorem inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_eq_zero_of_not_mem
    (K : ℕ) (p : Nat.Primes)
    (hp : ∀ n : ℕ, ∀ i : Fin 3,
      p ≠ routeKCofinalTrianglePrime (n + K) i) :
    inner ℂ (routeKPrimeBasis p)
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis p)))) = 0 := by
  rw [routeKCofinalTriangleNuclearCarrierFrom_apply_eq_zero_of_not_mem K p hp]
  simp

/-- Every full-tail cubic diagonal is nonnegative: it is either zero off the retained blocks or
one positive triangle return on a retained block. -/
private theorem re_inner_routeKCofinalTriangleNuclearCarrierFrom_cube_nonneg
    (K : ℕ) (p : Nat.Primes) :
    0 ≤ (inner ℂ (routeKPrimeBasis p)
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis p))))).re := by
  classical
  by_cases hp : ∃ n : ℕ, ∃ i : Fin 3,
      p = routeKCofinalTrianglePrime (n + K) i
  · rcases hp with ⟨n, i, rfl⟩
    fin_cases i
    · change 0 ≤ (inner ℂ
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0))
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKCofinalTriangleNuclearCarrierFrom K
              (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 0)))))).re
      rw [inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_zero]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (routeKCofinalTriangleAmplitude_pos (n + K) 0).le)
          (routeKCofinalTriangleAmplitude_pos (n + K) 1).le)
        (routeKCofinalTriangleAmplitude_pos (n + K) 2).le
    · change 0 ≤ (inner ℂ
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1))
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKCofinalTriangleNuclearCarrierFrom K
              (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 1)))))).re
      rw [inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_one]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (routeKCofinalTriangleAmplitude_pos (n + K) 0).le)
          (routeKCofinalTriangleAmplitude_pos (n + K) 1).le)
        (routeKCofinalTriangleAmplitude_pos (n + K) 2).le
    · change 0 ≤ (inner ℂ
        (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2))
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKCofinalTriangleNuclearCarrierFrom K
              (routeKPrimeBasis (routeKCofinalTrianglePrime (n + K) 2)))))).re
      rw [inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_two]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            (routeKCofinalTriangleAmplitude_pos (n + K) 0).le)
          (routeKCofinalTriangleAmplitude_pos (n + K) 1).le)
        (routeKCofinalTriangleAmplitude_pos (n + K) 2).le
  · rw [inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_eq_zero_of_not_mem K p]
    · norm_num
    · intro n i hpi
      exact hp ⟨n, i, hpi⟩

/-- The cubic trace of every complete cofinal triangle tail has strictly positive real part. -/
theorem re_opTrace_routeKCofinalTriangleNuclearCarrierFrom_cube_pos (K : ℕ) :
    0 < (ContinuousLinearMap.opTrace
      (routeKCofinalTriangleNuclearCarrierFrom K ∘L
        (routeKCofinalTriangleNuclearCarrierFrom K ∘L
          routeKCofinalTriangleNuclearCarrierFrom K))).re := by
  let T := routeKCofinalTriangleNuclearCarrierFrom K
  let f : Nat.Primes → ℂ := fun p =>
    inner ℂ (routeKPrimeBasis p) (T (T (T (routeKPrimeBasis p))))
  have hT : MemSchattenClass 1 (T ∘L (T ∘L T)) := by
    exact routeKCofinalTriangleNuclearCarrierFrom_cube_memSchattenClass_one K
  have hsum : Summable f := by
    have h := hT.one_summable_inner_diag_basis
      (HilbertSchmidt.lpBasis Nat.Primes)
    simpa [f, T, routeKPrimeBasis, HilbertSchmidt.lpBasis_apply,
      ContinuousLinearMap.comp_apply] using h
  have hsumRe : Summable (fun p : Nat.Primes => (f p).re) := by
    simpa [Function.comp_def] using
      hsum.map Complex.reCLM Complex.continuous_re
  have hnonneg : ∀ p : Nat.Primes, 0 ≤ (f p).re := by
    intro p
    exact re_inner_routeKCofinalTriangleNuclearCarrierFrom_cube_nonneg K p
  let p0 : Nat.Primes := routeKCofinalTrianglePrime K 0
  have hpos : 0 < (f p0).re := by
    change 0 < (inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime K 0))
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis (routeKCofinalTrianglePrime K 0)))))).re
    have h := inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_zero K 0
    rw [show 0 + K = K by omega] at h
    rw [h]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num)
          (routeKCofinalTriangleAmplitude_pos K 0))
        (routeKCofinalTriangleAmplitude_pos K 1))
      (routeKCofinalTriangleAmplitude_pos K 2)
  have hsumPos : 0 < ∑' p : Nat.Primes, (f p).re := by
    exact lt_of_lt_of_le hpos
      (GaloisForLFunctions.term_le_tsum_of_nonneg hsumRe hnonneg p0)
  have htrace : ContinuousLinearMap.opTrace (T ∘L (T ∘L T)) = ∑' p, f p := by
    rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hT
      (HilbertSchmidt.lpBasis Nat.Primes)]
    simp [f, T, routeKPrimeBasis, HilbertSchmidt.lpBasis_apply,
      ContinuousLinearMap.comp_apply]
  rw [htrace, Complex.re_tsum hsum]
  exact hsumPos

/-- The cubic ordinary trace of every complete cofinal triangle tail is nonzero.  Absolute
summability and nonnegative diagonals prevent cancellation of its first positive block return. -/
theorem opTrace_routeKCofinalTriangleNuclearCarrierFrom_cube_ne_zero (K : ℕ) :
    ContinuousLinearMap.opTrace
      (routeKCofinalTriangleNuclearCarrierFrom K ∘L
        (routeKCofinalTriangleNuclearCarrierFrom K ∘L
          routeKCofinalTriangleNuclearCarrierFrom K)) ≠ 0 := by
  let T := routeKCofinalTriangleNuclearCarrierFrom K
  let f : Nat.Primes → ℂ := fun p =>
    inner ℂ (routeKPrimeBasis p) (T (T (T (routeKPrimeBasis p))))
  have hT : MemSchattenClass 1 (T ∘L (T ∘L T)) := by
    exact routeKCofinalTriangleNuclearCarrierFrom_cube_memSchattenClass_one K
  have hsum : Summable f := by
    have h := hT.one_summable_inner_diag_basis
      (HilbertSchmidt.lpBasis Nat.Primes)
    simpa [f, T, routeKPrimeBasis, HilbertSchmidt.lpBasis_apply,
      ContinuousLinearMap.comp_apply] using h
  have hsumRe : Summable (fun p : Nat.Primes => (f p).re) := by
    simpa [Function.comp_def] using
      hsum.map Complex.reCLM Complex.continuous_re
  have hnonneg : ∀ p : Nat.Primes, 0 ≤ (f p).re := by
    intro p
    exact re_inner_routeKCofinalTriangleNuclearCarrierFrom_cube_nonneg K p
  let p0 : Nat.Primes := routeKCofinalTrianglePrime K 0
  have hpos : 0 < (f p0).re := by
    change 0 < (inner ℂ (routeKPrimeBasis (routeKCofinalTrianglePrime K 0))
      (routeKCofinalTriangleNuclearCarrierFrom K
        (routeKCofinalTriangleNuclearCarrierFrom K
          (routeKCofinalTriangleNuclearCarrierFrom K
            (routeKPrimeBasis (routeKCofinalTrianglePrime K 0)))))).re
    have h := inner_routeKCofinalTriangleNuclearCarrierFrom_cube_apply_zero K 0
    rw [show 0 + K = K by omega] at h
    rw [h]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num)
          (routeKCofinalTriangleAmplitude_pos K 0))
        (routeKCofinalTriangleAmplitude_pos K 1))
      (routeKCofinalTriangleAmplitude_pos K 2)
  have hsumPos : 0 < ∑' p : Nat.Primes, (f p).re := by
    exact lt_of_lt_of_le hpos
      (GaloisForLFunctions.term_le_tsum_of_nonneg hsumRe hnonneg p0)
  intro hzero
  have htrace : ContinuousLinearMap.opTrace (T ∘L (T ∘L T)) = ∑' p, f p := by
    rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hT
      (HilbertSchmidt.lpBasis Nat.Primes)]
    simp [f, T, routeKPrimeBasis, HilbertSchmidt.lpBasis_apply,
      ContinuousLinearMap.comp_apply]
  have hrealzero : (∑' p, f p).re = 0 := by
    rw [← htrace, hzero]
    rfl
  rw [Complex.re_tsum hsum] at hrealzero
  linarith

/-- No global unitary can reverse any complete cofinal source tail.  The trace obstruction applies
to the entire infinite carrier, so mixing its triangles with the complement cannot evade it. -/
theorem not_exists_unitaryPush_neg_routeKCofinalTriangleNuclearCarrierFrom
    (K : ℕ) :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u (routeKCofinalTriangleNuclearCarrierFrom K) =
        -routeKCofinalTriangleNuclearCarrierFrom K := by
  rintro ⟨u, hu⟩
  have hcube : unitaryPush u
      (routeKCofinalTriangleNuclearCarrierFrom K ∘L
        (routeKCofinalTriangleNuclearCarrierFrom K ∘L
          routeKCofinalTriangleNuclearCarrierFrom K)) =
      -(routeKCofinalTriangleNuclearCarrierFrom K ∘L
        (routeKCofinalTriangleNuclearCarrierFrom K ∘L
          routeKCofinalTriangleNuclearCarrierFrom K)) := by
    change unitaryPush u (routeKCofinalTriangleNuclearCarrierFrom K *
      (routeKCofinalTriangleNuclearCarrierFrom K *
        routeKCofinalTriangleNuclearCarrierFrom K)) =
      -(routeKCofinalTriangleNuclearCarrierFrom K *
        (routeKCofinalTriangleNuclearCarrierFrom K *
          routeKCofinalTriangleNuclearCarrierFrom K))
    rw [unitaryPush_mul, unitaryPush_mul, hu]
    noncomm_ring
  apply not_exists_unitaryPush_eq_neg_routeK_of_memSchattenClass_one_opTrace_ne_zero
    (routeKCofinalTriangleNuclearCarrierFrom K ∘L
      (routeKCofinalTriangleNuclearCarrierFrom K ∘L
        routeKCofinalTriangleNuclearCarrierFrom K))
    (routeKCofinalTriangleNuclearCarrierFrom_cube_memSchattenClass_one K)
  · exact opTrace_routeKCofinalTriangleNuclearCarrierFrom_cube_ne_zero K
  · exact ⟨u, hcube⟩

/-- At every cofinal cut, the full literal source tail resists global unitary sign reversal. -/
theorem exists_cofinal_routeKCofinalTriangleNuclearCarrierFrom_no_unitaryPush_neg
    (N : ℕ) :
    ∃ K : ℕ, N ≤ K ∧
      ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
        unitaryPush u (routeKCofinalTriangleNuclearCarrierFrom K) =
          -routeKCofinalTriangleNuclearCarrierFrom K := by
  exact ⟨N, le_rfl,
    not_exists_unitaryPush_neg_routeKCofinalTriangleNuclearCarrierFrom N⟩

/-- A Hilbert--Schmidt correction that is unitarily isospectral to the prime RVM skeleton must
cancel exactly half of its squared energy through a negative source/skeleton cross term. -/
theorem routeKRVM_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    (C : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hC : C.IsHilbertSchmidt)
    (u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert)
    (htransport : unitaryPush u routeKRVMSkeletonOperator =
      routeKRVMSkeletonOperator + C) :
    Complex.re (ContinuousLinearMap.hsInner routeKRVMSkeletonOperator C) =
      -ContinuousLinearMap.hsNormSq C / 2 := by
  have henergy := hsNormSq_unitaryPush routeKRVMSkeletonOperator_isHilbertSchmidt u
  rw [htransport, GaloisForLFunctions.HTGeometry.hsNormSq_add
    routeKRVMSkeletonOperator_isHilbertSchmidt hC] at henergy
  linarith

/-- A unitary recovery of any Hilbert--Schmidt prime carrier from itself plus a correction
requires exact negative cross energy. -/
theorem routeK_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    (D C : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hD : D.IsHilbertSchmidt) (hC : C.IsHilbertSchmidt)
    (u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert)
    (htransport : unitaryPush u D = D + C) :
    Complex.re (ContinuousLinearMap.hsInner D C) =
      -ContinuousLinearMap.hsNormSq C / 2 := by
  have henergy := hsNormSq_unitaryPush hD u
  rw [htransport, GaloisForLFunctions.HTGeometry.hsNormSq_add hD hC] at henergy
  linarith

/-- A diagonal prime carrier is Hilbert--Schmidt orthogonal to every Hilbert--Schmidt carrier
whose diagonal vanishes in the marked-prime basis. -/
theorem hsInner_routeKDiagonal_zeroDiagonal_eq_zero
    (D C : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert)
    (hD : D.IsHilbertSchmidt) (hC : C.IsHilbertSchmidt)
    (d : Nat.Primes → ℂ)
    (hDbasis : ∀ p, D (routeKPrimeBasis p) = d p • routeKPrimeBasis p)
    (hCdiag : ∀ p, inner ℂ (routeKPrimeBasis p) (C (routeKPrimeBasis p)) = 0) :
    ContinuousLinearMap.hsInner D C = 0 := by
  rw [ContinuousLinearMap.hsInner_eq_tsum_basis hD hC
    (HilbertSchmidt.lpBasis Nat.Primes)]
  have hterm :
      (fun p : Nat.Primes => inner ℂ
        (D (HilbertSchmidt.lpBasis Nat.Primes p))
        (C (HilbertSchmidt.lpBasis Nat.Primes p))) = 0 := by
    funext p
    have hDbasis' : D (lp.single 2 p (1 : ℂ)) =
        d p • lp.single 2 p (1 : ℂ) := by
      simpa only [routeKPrimeBasis] using hDbasis p
    have hCdiag' : inner ℂ (lp.single 2 p (1 : ℂ))
        (C (lp.single 2 p (1 : ℂ))) = 0 := by
      simpa only [routeKPrimeBasis] using hCdiag p
    rw [HilbertSchmidt.lpBasis_apply, hDbasis', inner_smul_left, hCdiag']
    simp
  rw [hterm]
  exact tsum_zero

/-- The finite, source-normalized non-diagonal block in the exact quadratic Route K carrier. -/
def routeKQuadraticSourceBlock : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
  (routeKQuadraticAdmissionScale : ℂ) •
    (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
      routeKPhysicalEndpointRVMRelocation)

theorem routeKQuadraticSourceBlock_isHilbertSchmidt :
    routeKQuadraticSourceBlock.IsHilbertSchmidt :=
  ((routeKRVMHeadOperator_isHilbertSchmidt _).add
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt).smul _

theorem hsInner_routeKQuadraticSourceBlock_tail_eq_zero :
    ContinuousLinearMap.hsInner routeKQuadraticSourceBlock
      (routeKRVMTailOperator routeKQuadraticAdmissionFinset) = 0 :=
  hsInner_smul_head_add_relocation_tail_eq_zero

/-- A source-preserving diagonal sign gauge cannot reverse every edge of a nonzero
three-prime cycle.  Such a reversal would be the elementary way to obtain the exact
negative-cross-energy correction `C = -2D`, but its three edge equations multiply to `1 = -1`. -/
theorem not_exists_routeKDiagonalSignGauge_eq_neg_threePrimeCycle
    (edge : Fin 3 → ℝ) (hedge : ∀ i, edge i ≠ 0) :
    ¬ ∃ ε : Fin 3 → ℝ,
      (∀ i, ε i * ε i = 1) ∧
      routeKDiagonalSignGauge ε
          (routeKThreePrimeRelocationMatrix (fun _ => 0) edge) =
        -routeKThreePrimeRelocationMatrix (fun _ => 0) edge := by
  rintro ⟨ε, hsq, hneg⟩
  have h01 := congrFun (congrFun hneg 0) 1
  have h12 := congrFun (congrFun hneg 1) 2
  have h20 := congrFun (congrFun hneg 2) 0
  norm_num [routeKDiagonalSignGauge, routeKThreePrimeRelocationMatrix] at h01 h12 h20
  change ε 1 * edge 1 * ε 2 = -edge 1 at h12
  change ε 2 * edge 2 * ε 0 = -edge 2 at h20
  have hphase01 : ε 0 * ε 1 = -1 := by
    have hfac : (ε 0 * ε 1 + 1) * edge 0 = 0 := by
      calc
        (ε 0 * ε 1 + 1) * edge 0 = ε 0 * edge 0 * ε 1 + edge 0 := by ring
        _ = -edge 0 + edge 0 := by rw [h01]
        _ = 0 := by ring
    rcases mul_eq_zero.mp hfac with hphase | hzero
    · linarith
    · exact False.elim (hedge 0 hzero)
  have hphase12 : ε 1 * ε 2 = -1 := by
    have hfac : (ε 1 * ε 2 + 1) * edge 1 = 0 := by
      calc
        (ε 1 * ε 2 + 1) * edge 1 = ε 1 * edge 1 * ε 2 + edge 1 := by ring
        _ = -edge 1 + edge 1 := by rw [h12]
        _ = 0 := by ring
    rcases mul_eq_zero.mp hfac with hphase | hzero
    · linarith
    · exact False.elim (hedge 1 hzero)
  have hphase20 : ε 2 * ε 0 = -1 := by
    have hfac : (ε 2 * ε 0 + 1) * edge 2 = 0 := by
      calc
        (ε 2 * ε 0 + 1) * edge 2 = ε 2 * edge 2 * ε 0 + edge 2 := by ring
        _ = -edge 2 + edge 2 := by rw [h20]
        _ = 0 := by ring
    rcases mul_eq_zero.mp hfac with hphase | hzero
    · linarith
    · exact False.elim (hedge 2 hzero)
  have hcontr : (1 : ℝ) = -1 := by
    calc
      (1 : ℝ) = (ε 0 * ε 0) * (ε 1 * ε 1) * (ε 2 * ε 2) := by
        rw [hsq 0, hsq 1, hsq 2]
        norm_num
      _ = (ε 0 * ε 1) * (ε 1 * ε 2) * (ε 2 * ε 0) := by ring
      _ = -1 := by rw [hphase01, hphase12, hphase20]; norm_num
  norm_num at hcontr

/-- The literal complexification of a zero-diagonal three-prime relocation triangle. -/
def routeKThreePrimeZeroDiagonalMatrixComplex (edge : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (edge 0 : ℂ), (edge 2 : ℂ);
     (edge 0 : ℂ), 0, (edge 1 : ℂ);
     (edge 2 : ℂ), (edge 1 : ℂ), 0]

/-- This is the coefficientwise complexification of the actual real relocation packet. -/
theorem routeKThreePrimeZeroDiagonalMatrixComplex_eq_map
    (edge : Fin 3 → ℝ) :
    routeKThreePrimeZeroDiagonalMatrixComplex edge =
      (routeKThreePrimeRelocationMatrix (fun _ => 0) edge).map Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [routeKThreePrimeZeroDiagonalMatrixComplex, routeKThreePrimeRelocationMatrix]

/-- The odd three-cycle determinant is exactly twice the closed-cycle product. -/
theorem det_routeKThreePrimeZeroDiagonalMatrixComplex
    (edge : Fin 3 → ℝ) :
    (routeKThreePrimeZeroDiagonalMatrixComplex edge).det =
      2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ) := by
  simp [routeKThreePrimeZeroDiagonalMatrixComplex, Matrix.det_fin_three]
  ring

/-- A nonzero three-prime cycle cannot be similar, even through arbitrary complex invertible
matrices, to its negative.  Similarity preserves its nonzero odd determinant, whereas negation
reverses that determinant in dimension three. -/
theorem not_exists_complexSimilarity_neg_routeKThreePrimeCycle
    (edge : Fin 3 → ℝ) (hedge : ∀ i, edge i ≠ 0) :
    ¬ ∃ U V : Matrix (Fin 3) (Fin 3) ℂ,
      U * V = 1 ∧ V * U = 1 ∧
        U * routeKThreePrimeZeroDiagonalMatrixComplex edge * V =
          -routeKThreePrimeZeroDiagonalMatrixComplex edge := by
  rintro ⟨U, V, hUV, hVU, hneg⟩
  let A := routeKThreePrimeZeroDiagonalMatrixComplex edge
  have hdetUV : U.det * V.det = 1 := by
    rw [← Matrix.det_mul, hUV, Matrix.det_one]
  have hdet := congrArg Matrix.det hneg
  change (U * A * V).det = (-A).det at hdet
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hAdet : A.det = 2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ) := by
    exact det_routeKThreePrimeZeroDiagonalMatrixComplex edge
  rw [Matrix.det_neg, hAdet] at hdet
  norm_num at hdet
  have hprod : 2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (hedge 0)))
        (Complex.ofReal_ne_zero.mpr (hedge 1)))
      (Complex.ofReal_ne_zero.mpr (hedge 2))
  have hleft : U.det * (2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ)) * V.det =
      2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ) := by
    calc
      U.det * (2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ)) * V.det =
          (U.det * V.det) * (2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ)) := by ring
      _ = 2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ) := by rw [hdetUV, one_mul]
  rw [hleft] at hdet
  let c : ℂ := 2 * (edge 0 : ℂ) * (edge 1 : ℂ) * (edge 2 : ℂ)
  have hc : c = -c := by simpa [c] using hdet
  have hdouble : (2 : ℂ) * c = 0 := by
    calc
      (2 : ℂ) * c = c + c := by ring
      _ = c + (-c) := congrArg (fun z : ℂ => c + z) hc
      _ = 0 := by ring
  have hczero : c = 0 :=
    (mul_eq_zero.mp hdouble).resolve_left (by norm_num)
  exact hprod (by simpa [c] using hczero)

/-- The exact quadratically admitted source carrier retains arbitrarily late nonzero triangles,
so no source-preserving diagonal sign gauge can provide its global sign-reversal correction. -/
theorem exists_cofinal_routeKQuadraticallyAdmitted_no_diagonalSignGauge_neg
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      ¬ ∃ ε : Fin 3 → ℝ,
        (∀ i, ε i * ε i = 1) ∧
        routeKDiagonalSignGauge ε
            (routeKThreePrimeRelocationMatrix (fun _ => 0)
              (routeKQuadraticallyAdmittedTriangleEdge
                (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
                  (nthPrimeSubtype (n + 2)))) =
          -routeKThreePrimeRelocationMatrix (fun _ => 0)
              (routeKQuadraticallyAdmittedTriangleEdge
                (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
                  (nthPrimeSubtype (n + 2))) := by
  obtain ⟨n, hn, hpq, hqr, hrp⟩ :=
    exists_cofinal_positive_physicalEndpoint_pair_triangle N
  refine ⟨n, hn, ?_⟩
  apply not_exists_routeKDiagonalSignGauge_eq_neg_threePrimeCycle
  apply routeKQuadraticallyAdmittedTriangleEdge_ne_zero
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact hpq.ne'
  · exact hqr.ne'
  · exact hrp.ne'

/-- Every cofinal tail contains a literal quadratically admitted triangle whose complex finite
block cannot be conjugated to its negative.  This excludes all finite-block unitary recoveries;
an infinite recovery must fail to preserve these triangle subspaces. -/
theorem exists_cofinal_routeKQuadraticallyAdmitted_no_complexSimilarity_neg
    (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧
      ¬ ∃ U V : Matrix (Fin 3) (Fin 3) ℂ,
        U * V = 1 ∧ V * U = 1 ∧
          U * routeKThreePrimeZeroDiagonalMatrixComplex
              (routeKQuadraticallyAdmittedTriangleEdge
                (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
                  (nthPrimeSubtype (n + 2))) * V =
            -routeKThreePrimeZeroDiagonalMatrixComplex
              (routeKQuadraticallyAdmittedTriangleEdge
                (nthPrimeSubtype n) (nthPrimeSubtype (n + 1))
                  (nthPrimeSubtype (n + 2))) := by
  obtain ⟨n, hn, hpq, hqr, hrp⟩ :=
    exists_cofinal_positive_physicalEndpoint_pair_triangle N
  refine ⟨n, hn, ?_⟩
  apply not_exists_complexSimilarity_neg_routeKThreePrimeCycle
  apply routeKQuadraticallyAdmittedTriangleEdge_ne_zero
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact nthPrimeSubtype_injective.ne (by omega)
  · exact hpq.ne'
  · exact hqr.ne'
  · exact hrp.ne'

/-- Removing any finite prime head leaves a nonzero reciprocal RVM tail. -/
theorem routeKRVMTailOperator_ne_zero (s : Finset Nat.Primes) :
    routeKRVMTailOperator s ≠ 0 := by
  classical
  intro hzero
  obtain ⟨q, hq, hqprime⟩ :=
    Nat.exists_infinite_primes (s.sup (fun p : Nat.Primes => (p : ℕ)) + 1)
  let p : Nat.Primes := ⟨q, hqprime⟩
  have hpnot : p ∉ s := by
    intro hp
    have hle : (p : ℕ) ≤ s.sup (fun p : Nat.Primes => (p : ℕ)) :=
      Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) hp
    change s.sup (fun p : Nat.Primes => (p : ℕ)) + 1 ≤ q at hq
    change q ≤ s.sup (fun p : Nat.Primes => (p : ℕ)) at hle
    omega
  have hvzero : routeKRVMTailOperator s (routeKPrimeBasis p) = 0 := by
    rw [hzero]
    simp
  rw [routeKRVMTailOperator_basis, routeKRVMTailWeight, if_neg hpnot] at hvzero
  have hpbasis : routeKPrimeBasis p ≠ 0 := by
    intro h
    have hpoint := congrArg (fun x : RouteKPrimeHilbert => x p) h
    simp [routeKPrimeBasis] at hpoint
  rcases smul_eq_zero.mp hvzero with hscalar | hbasis
  · exact (Complex.ofReal_ne_zero.mpr (routeKPrimeRVMReciprocal_pos p).ne') hscalar
  · exact hpbasis hbasis

theorem routeKQuadraticSourceBlock_ne_zero :
    routeKQuadraticSourceBlock ≠ 0 := by
  apply smul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr routeKQuadraticAdmissionScale_pos.ne'
  · intro hzero
    have hnormzero :
        ContinuousLinearMap.hsNormSq
          (routeKRVMHeadOperator routeKQuadraticAdmissionFinset +
            routeKPhysicalEndpointRVMRelocation) = 0 :=
      (ContinuousLinearMap.hsNormSq_eq_zero_iff
        ((routeKRVMHeadOperator_isHilbertSchmidt _).add
          routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt)).mpr hzero
    exact (ne_of_gt (hsNormSq_routeKRVMHead_add_physicalEndpointRVMRelocation_pos _)) hnormzero

/-- The exact degree-two prime-source carrier cannot arise by a unitary transport of its
non-diagonal source block: the cofinite reciprocal correction has zero, rather than negative,
cross energy. -/
theorem not_exists_unitaryPush_routeKQuadraticSourceBlock_eq_admitted :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u routeKQuadraticSourceBlock = routeKQuadraticallyAdmittedOperator := by
  rintro ⟨u, hu⟩
  have htransport : unitaryPush u routeKQuadraticSourceBlock =
      routeKQuadraticSourceBlock +
        routeKRVMTailOperator routeKQuadraticAdmissionFinset := by
    simpa [routeKQuadraticSourceBlock, routeKQuadraticallyAdmittedOperator] using hu
  have hcross := routeK_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    routeKQuadraticSourceBlock (routeKRVMTailOperator routeKQuadraticAdmissionFinset)
    routeKQuadraticSourceBlock_isHilbertSchmidt
    (routeKRVMTailOperator_isHilbertSchmidt _) u htransport
  rw [hsInner_routeKQuadraticSourceBlock_tail_eq_zero, Complex.zero_re] at hcross
  have hnormzero :
      ContinuousLinearMap.hsNormSq
        (routeKRVMTailOperator routeKQuadraticAdmissionFinset) = 0 := by
    linarith
  exact routeKRVMTailOperator_ne_zero _
    ((ContinuousLinearMap.hsNormSq_eq_zero_iff
      (routeKRVMTailOperator_isHilbertSchmidt _)).mp hnormzero)

/-- Nor can the source-normalized quadratic carrier be unitarily transported back to its
cofinite reciprocal tail: the non-diagonal source block is nonzero and orthogonal to that tail. -/
theorem not_exists_unitaryPush_routeKRVMQuadraticTail_eq_admitted :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u (routeKRVMTailOperator routeKQuadraticAdmissionFinset) =
        routeKQuadraticallyAdmittedOperator := by
  rintro ⟨u, hu⟩
  have htransport : unitaryPush u (routeKRVMTailOperator routeKQuadraticAdmissionFinset) =
      routeKRVMTailOperator routeKQuadraticAdmissionFinset + routeKQuadraticSourceBlock := by
    simpa [routeKQuadraticSourceBlock, routeKQuadraticallyAdmittedOperator, add_comm] using hu
  have hcross := routeK_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    (routeKRVMTailOperator routeKQuadraticAdmissionFinset) routeKQuadraticSourceBlock
    (routeKRVMTailOperator_isHilbertSchmidt _)
    routeKQuadraticSourceBlock_isHilbertSchmidt u htransport
  have horth : ContinuousLinearMap.hsInner
      (routeKRVMTailOperator routeKQuadraticAdmissionFinset) routeKQuadraticSourceBlock = 0 := by
    rw [ContinuousLinearMap.hsInner_conj_symm,
      hsInner_routeKQuadraticSourceBlock_tail_eq_zero]
    simp
  rw [horth, Complex.zero_re] at hcross
  have hnormzero : ContinuousLinearMap.hsNormSq routeKQuadraticSourceBlock = 0 := by
    linarith
  exact routeKQuadraticSourceBlock_ne_zero
    ((ContinuousLinearMap.hsNormSq_eq_zero_iff
      routeKQuadraticSourceBlock_isHilbertSchmidt).mp hnormzero)

/-- Each retained cofinal source-triangle carrier remains nonzero. -/
theorem routeKCofinalTriangleNuclearCarrierFrom_ne_zero (K : ℕ) :
    routeKCofinalTriangleNuclearCarrierFrom K ≠ 0 := by
  intro hzero
  have hhol := routeKCofinalTriangleNuclearCarrierFrom_selectedHolonomy_ne_zero K 0
  simp [hzero] at hhol

/-- Every cofinite diagonal RVM tail is excluded from unitary recovery after adding a retained
source triangle carrier: its necessary negative cross energy is identically zero. -/
theorem not_exists_unitaryPush_routeKRVMTail_eq_add_cofinalTriangle
    (s : Finset Nat.Primes) (K : ℕ) :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u (routeKRVMTailOperator s) =
        routeKRVMTailOperator s + routeKCofinalTriangleNuclearCarrierFrom K := by
  rintro ⟨u, hu⟩
  have hcross := routeK_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    (routeKRVMTailOperator s) (routeKCofinalTriangleNuclearCarrierFrom K)
    (routeKRVMTailOperator_isHilbertSchmidt s)
    (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K) u hu
  have horth := hsInner_routeKDiagonal_zeroDiagonal_eq_zero
    (routeKRVMTailOperator s) (routeKCofinalTriangleNuclearCarrierFrom K)
    (routeKRVMTailOperator_isHilbertSchmidt s)
    (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K)
    (fun p => (routeKRVMTailWeight s p : ℂ))
    (routeKRVMTailOperator_basis s)
    (routeKCofinalTriangleNuclearCarrierFrom_diagonal_zero K)
  rw [horth, Complex.zero_re] at hcross
  have hnormzero : ContinuousLinearMap.hsNormSq (routeKCofinalTriangleNuclearCarrierFrom K) = 0 := by
    linarith
  exact routeKCofinalTriangleNuclearCarrierFrom_ne_zero K
    ((ContinuousLinearMap.hsNormSq_eq_zero_iff
      (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K)).mp hnormzero)

/-- The literal quartic reserve cannot be a unitary recovery of its cofinite RVM diagonal.
The retained source cycle is Hilbert--Schmidt orthogonal to that diagonal, while unitary
recovery would require their real cross energy to be negative.  Thus an exact K-RVM
resolvent bridge must be genuinely nonunitary. -/
theorem not_exists_unitaryPush_routeKQuarticRVMReserve_eq_quarticReserve :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u routeKQuarticRVMReserve = routeKQuarticReserve := by
  rintro ⟨u, hu⟩
  have htransport : unitaryPush u routeKQuarticRVMReserve =
      routeKQuarticRVMReserve + routeKQuarticCycleReserve := by
    simpa [routeKQuarticReserve] using hu
  have hcross := routeK_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    routeKQuarticRVMReserve routeKQuarticCycleReserve
    routeKQuarticRVMReserve_isHilbertSchmidt
    routeKQuarticCycleReserve_isHilbertSchmidt u htransport
  have horth := hsInner_routeKDiagonal_zeroDiagonal_eq_zero
    routeKQuarticRVMReserve routeKQuarticCycleReserve
    routeKQuarticRVMReserve_isHilbertSchmidt
    routeKQuarticCycleReserve_isHilbertSchmidt
    (fun p => (routeKRVMTailWeight
      (routeKInitialPrimeFinset routeKQuarticReserveParameters.N) p : ℂ))
    (by
      intro p
      exact routeKRVMTailOperator_basis
        (routeKInitialPrimeFinset routeKQuarticReserveParameters.N) p)
    (by
      intro p
      rw [routeKQuarticCycleReserve, smul_apply, inner_smul_right,
        routeKCofinalTriangleNuclearCarrierFrom_diagonal_zero, mul_zero])
  rw [horth, Complex.zero_re] at hcross
  have hnormzero : ContinuousLinearMap.hsNormSq routeKQuarticCycleReserve = 0 := by
    linarith
  have hcycle : routeKQuarticCycleReserve ≠ 0 := by
    unfold routeKQuarticCycleReserve
    exact smul_ne_zero
      (Complex.ofReal_ne_zero.mpr routeKQuarticReserveParameters.hdelta.ne')
      (routeKCofinalTriangleNuclearCarrierFrom_ne_zero _)
  exact hcycle
    ((ContinuousLinearMap.hsNormSq_eq_zero_iff
      routeKQuarticCycleReserve_isHilbertSchmidt).mp hnormzero)

/-- The full quartically admitted carrier cannot be a unitary image of the diagonal carrier with
the same finite moment head and cofinite RVM tail.  The retained cycle therefore cannot be
absorbed by an isospectral change of prime coordinates. -/
theorem not_exists_unitaryPush_routeKQuarticDiagonal_eq_admitted :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u (routeKQuarticHead + routeKQuarticRVMReserve) =
        routeKQuarticallyAdmittedOperator := by
  rintro ⟨u, hu⟩
  have htransport : unitaryPush u (routeKQuarticHead + routeKQuarticRVMReserve) =
      (routeKQuarticHead + routeKQuarticRVMReserve) + routeKQuarticCycleReserve := by
    simpa [routeKQuarticallyAdmittedOperator, routeKQuarticReserve, add_assoc] using hu
  have hD : (routeKQuarticHead + routeKQuarticRVMReserve).IsHilbertSchmidt :=
    routeKQuarticHead_isHilbertSchmidt.add routeKQuarticRVMReserve_isHilbertSchmidt
  have hcross := routeK_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    (routeKQuarticHead + routeKQuarticRVMReserve) routeKQuarticCycleReserve
    hD routeKQuarticCycleReserve_isHilbertSchmidt u htransport
  have horth := hsInner_routeKDiagonal_zeroDiagonal_eq_zero
    (routeKQuarticHead + routeKQuarticRVMReserve) routeKQuarticCycleReserve
    hD routeKQuarticCycleReserve_isHilbertSchmidt
    (fun p =>
      (twoLevelPrimeWeight routeKQuarticResidualMass routeKQuarticResidualEnergy
        routeKQuarticReserveParameters.N p : ℂ) +
      (routeKRVMTailWeight
        (routeKInitialPrimeFinset routeKQuarticReserveParameters.N) p : ℂ))
    (by
      intro p
      rw [add_apply, routeKQuarticHead_basis, routeKQuarticRVMReserve,
        routeKRVMTailOperator_basis, ← add_smul])
    (by
      intro p
      rw [routeKQuarticCycleReserve, smul_apply, inner_smul_right,
        routeKCofinalTriangleNuclearCarrierFrom_diagonal_zero, mul_zero])
  rw [horth, Complex.zero_re] at hcross
  have hnormzero : ContinuousLinearMap.hsNormSq routeKQuarticCycleReserve = 0 := by
    linarith
  have hcycle : routeKQuarticCycleReserve ≠ 0 := by
    unfold routeKQuarticCycleReserve
    exact smul_ne_zero
      (Complex.ofReal_ne_zero.mpr routeKQuarticReserveParameters.hdelta.ne')
      (routeKCofinalTriangleNuclearCarrierFrom_ne_zero _)
  exact hcycle
    ((ContinuousLinearMap.hsNormSq_eq_zero_iff
      routeKQuarticCycleReserve_isHilbertSchmidt).mp hnormzero)

/-- The literal completed-endpoint double commutator is nonzero and Hilbert--Schmidt orthogonal
to the RVM skeleton, so no unitary source transport can recover the corrected operator from the
skeleton. -/
theorem not_exists_unitaryPush_routeKRVMSkeleton_eq_physicalEndpointCorrection :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u routeKRVMSkeletonOperator =
        routeKRVMSkeletonOperator + routeKPhysicalEndpointRVMRelocation := by
  rintro ⟨u, hu⟩
  have hcross := routeKRVM_re_hsInner_eq_neg_half_hsNormSq_of_unitaryPush_add_eq
    routeKPhysicalEndpointRVMRelocation
    routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt u hu
  rw [hsInner_routeKRVMSkeletonOperator_physicalEndpointRVMRelocation_eq_zero,
    Complex.zero_re] at hcross
  have hzero : ContinuousLinearMap.hsNormSq routeKPhysicalEndpointRVMRelocation = 0 := by
    linarith
  exact routeKPhysicalEndpointRVMRelocation_ne_zero
    ((ContinuousLinearMap.hsNormSq_eq_zero_iff
      routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt).mp hzero)

/-- Nor can a unitary transport erase the literal correction and return to the smooth RVM
skeleton: the correction raises the squared Hilbert--Schmidt energy strictly. -/
theorem not_exists_unitaryPush_physicalEndpointCorrection_eq_routeKRVMSkeleton :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKPrimeHilbert,
      unitaryPush u
        (routeKRVMSkeletonOperator + routeKPhysicalEndpointRVMRelocation) =
          routeKRVMSkeletonOperator := by
  rintro ⟨u, hu⟩
  have hsum : (routeKRVMSkeletonOperator + routeKPhysicalEndpointRVMRelocation).IsHilbertSchmidt :=
    routeKRVMSkeletonOperator_isHilbertSchmidt.add
      routeKPhysicalEndpointRVMRelocation_isHilbertSchmidt
  have henergy := hsNormSq_unitaryPush hsum u
  rw [hu] at henergy
  exact (ne_of_gt hsNormSq_routeKRVMSkeleton_lt_add_physicalEndpointRVMRelocation) henergy.symm


/-- Unitary transport composes exactly: a source operator pushed first by `u` and then by `v`
is the direct push through their composite. -/
theorem unitaryPush_trans
    {H K L : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (u : H ≃ₗᵢ[ℂ] K) (v : K ≃ₗᵢ[ℂ] L)
    (T : H →L[ℂ] H) :
    unitaryPush (u.trans v) T = unitaryPush v (unitaryPush u T) := by
  ext x
  simp [unitaryPush]

/-- Chiral sign symmetry of a unitary image pulls back to sign symmetry of its source. -/
theorem unitaryPush_pull_chiral
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (u : H ≃ₗᵢ[ℂ] K) (r : K ≃ₗᵢ[ℂ] K)
    (T : H →L[ℂ] H)
    (h : unitaryPush r (unitaryPush u T) = -unitaryPush u T) :
    unitaryPush ((u.trans r).trans u.symm) T = -T := by
  rw [unitaryPush_trans, unitaryPush_trans, h,
    show -unitaryPush u T = (-1 : ℂ) • unitaryPush u T by module,
    unitaryPush_smul, unitaryPush_symm_unitaryPush]
  module

/-- No unitary image of a literal cofinal source tail admits a chiral sign symmetry.  Thus an
exact even-determinant K-RVM carrier cannot obtain its required opposite sector by a unitary
relabeling of the literal tail; that sector must be constructed from additional source data. -/
theorem not_exists_unitaryPush_chiral_routeKCofinalTriangleNuclearCarrierFrom
    (N : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] H) :
    ¬ ∃ r : H ≃ₗᵢ[ℂ] H,
      unitaryPush r (unitaryPush u (routeKCofinalTriangleNuclearCarrierFrom N)) =
        -unitaryPush u (routeKCofinalTriangleNuclearCarrierFrom N) := by
  rintro ⟨r, hr⟩
  apply not_exists_unitaryPush_neg_routeKCofinalTriangleNuclearCarrierFrom N
  refine ⟨(u.trans r).trans u.symm, ?_⟩
  exact unitaryPush_pull_chiral u r
    (routeKCofinalTriangleNuclearCarrierFrom N) hr


/-- The concrete signed smooth RVM model has the chiral swap symmetry exchanging its positive
and negative prime copies. -/
noncomputable def routeKSignedPrimeSwap :
    RouteKSignedPrimeHilbert ≃ₗᵢ[ℂ] RouteKSignedPrimeHilbert :=
  GaloisForLFunctions.HTGeometry.lpReindexEquiv (Equiv.sumComm Nat.Primes Nat.Primes)

theorem unitaryPush_routeKSignedPrimeSwap_routeKSignedPrimeRVMOperator :
    unitaryPush routeKSignedPrimeSwap routeKSignedPrimeRVMOperator =
      -routeKSignedPrimeRVMOperator := by
  ext x i
  rw [unitaryPush_apply]
  simp only [routeKSignedPrimeSwap, GaloisForLFunctions.HTGeometry.lpReindexEquiv_apply,
    GaloisForLFunctions.HTGeometry.lpReindexEquiv_symm_apply, routeKSignedPrimeRVMOperator,
    HTGeometry.ellTwoDiagonal_apply]
  cases i <;> simp [routeKSignedPrimeRVMMultiplier]

/-- The signed smooth RVM model cannot be an exact unitary transport of a literal cofinal source
tail.  Its required positive/negative copy swap would pull back to the forbidden sign reversal of
the literal tail. -/
theorem not_exists_unitaryPush_routeKCofinalTriangleNuclearCarrierFrom_eq_signedRVM
    (N : ℕ) :
    ¬ ∃ u : RouteKPrimeHilbert ≃ₗᵢ[ℂ] RouteKSignedPrimeHilbert,
      unitaryPush u (routeKCofinalTriangleNuclearCarrierFrom N) =
        routeKSignedPrimeRVMOperator := by
  rintro ⟨u, hu⟩
  apply not_exists_unitaryPush_chiral_routeKCofinalTriangleNuclearCarrierFrom N u
  refine ⟨routeKSignedPrimeSwap, ?_⟩
  rw [hu, unitaryPush_routeKSignedPrimeSwap_routeKSignedPrimeRVMOperator, ← hu]

/-- The orthogonal two-sector completion of a literal cofinal prime tail.  It retains the exact
source tail on the first sector and adds a formal opposite copy on a second sector. -/
abbrev RouteKDoubledPrimeHilbert :=
  GaloisForLFunctions.HTGeometry.HilbertSum RouteKPrimeHilbert RouteKPrimeHilbert

/-- Source-faithful doubled carrier with the literal tail and its formal negative. -/
def routeKDoubledTail (K : ℕ) :
    RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert :=
  GaloisForLFunctions.HTGeometry.hilbertBlockDiagonal
    (routeKCofinalTriangleNuclearCarrierFrom K)
    (-routeKCofinalTriangleNuclearCarrierFrom K)

/-- Swap of the two literal prime-tail sectors. -/
def routeKDoubledSwap :
    RouteKDoubledPrimeHilbert ≃ₗᵢ[ℂ] RouteKDoubledPrimeHilbert :=
  LinearIsometryEquiv.withLpProdComm 2 ℂ RouteKPrimeHilbert RouteKPrimeHilbert

/-- The doubled source carrier has exact chiral symmetry.  This is a positive survivor of the
single-tail obstruction, but its second sector and Xi determinant still require source derivation. -/
theorem unitaryPush_routeKDoubledSwap_routeKDoubledTail (K : ℕ) :
    unitaryPush routeKDoubledSwap (routeKDoubledTail K) = -routeKDoubledTail K := by
  ext z
  apply GaloisForLFunctions.HTGeometry.hilbertSum_ext
  · simp only [unitaryPush_apply, routeKDoubledSwap, routeKDoubledTail,
      LinearIsometryEquiv.withLpProdComm_apply]
    change (-routeKCofinalTriangleNuclearCarrierFrom K) z.ofLp.1 =
      -(routeKCofinalTriangleNuclearCarrierFrom K z.ofLp.1)
    rfl
  · simp only [unitaryPush_apply, routeKDoubledSwap, routeKDoubledTail,
      LinearIsometryEquiv.withLpProdComm_apply]
    change routeKCofinalTriangleNuclearCarrierFrom K z.ofLp.2 =
      -((-routeKCofinalTriangleNuclearCarrierFrom K) z.ofLp.2)
    rw [neg_apply]
    exact (neg_neg _).symm

/-- The first sector is exactly the literal cofinal prime tail. -/
theorem routeKDoubledTail_inl (K : ℕ) (x : RouteKPrimeHilbert) :
    routeKDoubledTail K (GaloisForLFunctions.HTGeometry.hilbertSumInl x) =
      GaloisForLFunctions.HTGeometry.hilbertSumInl
        (routeKCofinalTriangleNuclearCarrierFrom K x) := by
  simp [routeKDoubledTail]

/-- The second sector is precisely the formal opposite of the literal cofinal prime tail. -/
theorem routeKDoubledTail_inr (K : ℕ) (x : RouteKPrimeHilbert) :
    routeKDoubledTail K (GaloisForLFunctions.HTGeometry.hilbertSumInr x) =
      GaloisForLFunctions.HTGeometry.hilbertSumInr
        (-routeKCofinalTriangleNuclearCarrierFrom K x) := by
  simp [routeKDoubledTail]

/-- The two-sector completion remains Schatten-one.  Each sector is factored by lifting and
projecting the original literal-tail Hilbert--Schmidt factorization; no spectral target data is
introduced. -/
theorem routeKDoubledTail_memSchattenClass_one (K : ℕ) :
    MemSchattenClass 1 (routeKDoubledTail K) := by
  let T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
    routeKCofinalTriangleNuclearCarrierFrom K
  let i₁ : RouteKPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert :=
    GaloisForLFunctions.HTGeometry.hilbertSumInl
      (H₁ := RouteKPrimeHilbert) (H₂ := RouteKPrimeHilbert)
  let p₁ : RouteKDoubledPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
    GaloisForLFunctions.HTGeometry.hilbertSumFst
      (H₁ := RouteKPrimeHilbert) (H₂ := RouteKPrimeHilbert)
  let i₂ : RouteKPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert :=
    GaloisForLFunctions.HTGeometry.hilbertSumInr
      (H₁ := RouteKPrimeHilbert) (H₂ := RouteKPrimeHilbert)
  let p₂ : RouteKDoubledPrimeHilbert →L[ℂ] RouteKPrimeHilbert :=
    GaloisForLFunctions.HTGeometry.hilbertSumSnd
      (H₁ := RouteKPrimeHilbert) (H₂ := RouteKPrimeHilbert)
  let A : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert := i₁ ∘L T ∘L p₁
  let B : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert := i₂ ∘L (-T) ∘L p₂
  have hp₁i₁ (x : RouteKPrimeHilbert) : p₁ (i₁ x) = x := by
    change GaloisForLFunctions.HTGeometry.hilbertSumFst
      (GaloisForLFunctions.HTGeometry.hilbertSumInl x) = x
    exact GaloisForLFunctions.HTGeometry.hilbertSumFst_inl x
  have hp₂i₂ (x : RouteKPrimeHilbert) : p₂ (i₂ x) = x := by
    change GaloisForLFunctions.HTGeometry.hilbertSumSnd
      (GaloisForLFunctions.HTGeometry.hilbertSumInr x) = x
    exact GaloisForLFunctions.HTGeometry.hilbertSumSnd_inr x
  have hdecomp : routeKDoubledTail K = A + B := by
    ext z
    apply GaloisForLFunctions.HTGeometry.hilbertSum_ext
    · change T z.ofLp.1 = T z.ofLp.1 + 0
      simp
    · change (-T) z.ofLp.2 = 0 + (-T) z.ofLp.2
      simp
  have hA : MemSchattenClass 1 A := by
    obtain ⟨S, V, hS, hV, hfac⟩ :=
      (routeKCofinalTriangleNuclearCarrierFrom_memSchattenClass_one K).one_isTraceClass
    let S' : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert := i₁ ∘L S ∘L p₁
    let V' : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert := i₁ ∘L V ∘L p₁
    have hfactor : A = S' ∘L V' := by
      ext z
      apply GaloisForLFunctions.HTGeometry.hilbertSum_ext
      · simp [A, S', V', T, hfac, hp₁i₁]
      · simp [A, S', V', T, hfac, hp₁i₁]
    rw [hfactor]
    apply IsTraceClass.memSchattenClass_one
    exact ⟨S', V', (hS.comp_left i₁).comp_right p₁,
      (hV.comp_left i₁).comp_right p₁, rfl⟩
  have hB : MemSchattenClass 1 B := by
    obtain ⟨S, V, hS, hV, hfac⟩ :=
      (routeKCofinalTriangleNuclearCarrierFrom_memSchattenClass_one K).one_isTraceClass
    let S' : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert := i₂ ∘L S ∘L p₂
    let V' : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert := i₂ ∘L (-V) ∘L p₂
    have hfactor : B = S' ∘L V' := by
      ext z
      apply GaloisForLFunctions.HTGeometry.hilbertSum_ext
      · simp [B, S', V', T, hfac, hp₂i₂]
      · simp [B, S', V', T, hfac, hp₂i₂]
    rw [hfactor]
    apply IsTraceClass.memSchattenClass_one
    exact ⟨S', V', (hS.comp_left i₂).comp_right p₂,
      ((hV.neg).comp_left i₂).comp_right p₂, rfl⟩
  rw [hdecomp]
  exact hA.one_add hB

/-- Chiral symmetry makes the order-one determinant of the source-faithful doubled tail even.
This is a closed determinant consequence of the literal tail, but does not identify its divisor
with the completed zeta function. -/
theorem opSchattenDet_routeKDoubledTail_even (K : ℕ) (z : ℂ) :
    GaloisForLFunctions.HTGeometry.opSchattenDet 1 (routeKDoubledTail K) (-z) =
      GaloisForLFunctions.HTGeometry.opSchattenDet 1 (routeKDoubledTail K) z := by
  let T : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert := routeKDoubledTail K
  let U : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert :=
    routeKDoubledSwap.toLinearIsometry.toContinuousLinearMap
  let V : RouteKDoubledPrimeHilbert →L[ℂ] RouteKDoubledPrimeHilbert :=
    routeKDoubledSwap.symm.toLinearIsometry.toContinuousLinearMap
  have hVU : V * U = 1 := by
    ext x
    simp [U, V]
  have hUV : U * V = 1 := by
    ext x
    simp [U, V]
  have hconj :
      GaloisForLFunctions.HTGeometry.opSchattenDet 1 (-T) z =
        GaloisForLFunctions.HTGeometry.opSchattenDet 1 T z := by
    rw [← unitaryPush_routeKDoubledSwap_routeKDoubledTail]
    change GaloisForLFunctions.HTGeometry.opSchattenDet 1 (U * T * V) z =
      GaloisForLFunctions.HTGeometry.opSchattenDet 1 T z
    exact GaloisForLFunctions.HTGeometry.opSchattenDet_conj
      (p := 1) (A := T) (V := U) (W := V) (by norm_num)
      (by simpa only [Nat.cast_one, T] using routeKDoubledTail_memSchattenClass_one K) hVU hUV z
  calc
    GaloisForLFunctions.HTGeometry.opSchattenDet 1 T (-z) =
        GaloisForLFunctions.HTGeometry.opSchattenDet 1 (-T) z := by
      simpa using
        (GaloisForLFunctions.HTGeometry.opSchattenDet_smul 1 (-1 : ℂ) T z).symm
    _ = GaloisForLFunctions.HTGeometry.opSchattenDet 1 T z := hconj

/-- Matrix kernel of the literal cofinal source tail in the canonical prime basis. -/
abbrev routeKSourceTailKernel (K : ℕ) : Nat.Primes × Nat.Primes → ℂ :=
  HilbertSchmidt.matrixOf (routeKCofinalTriangleNuclearCarrierFrom K)

/-- The literal source-tail matrix is Hilbert--Schmidt, obtained from the already closed operator
Hilbert--Schmidt bound without selecting any target zero. -/
theorem routeKSourceTailKernel_isHS (K : ℕ) :
    HilbertSchmidt.IsHS (routeKSourceTailKernel K) := by
  apply HilbertSchmidt.isHS_matrixOf
  exact routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K

/-- The global Hilbert--Carleman determinant of the literal cofinal source tail. -/
noncomputable def routeKSourceTailEntireDet (K : ℕ) : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.entireDet2 (routeKSourceTailKernel K)

theorem differentiable_routeKSourceTailEntireDet (K : ℕ) :
    Differentiable ℂ (routeKSourceTailEntireDet K) := by
  exact GaloisForLFunctions.HTGeometry.differentiable_entireDet2
    (routeKSourceTailKernel_isHS K)

/-- The entire determinant of the source tail together with its formal opposite sector.  Its
definition is source-only and its evenness is a necessary symmetry, not an Xi divisor identity. -/
noncomputable def routeKSymmetrizedSourceEntireDet (K : ℕ) (z : ℂ) : ℂ :=
  routeKSourceTailEntireDet K z * routeKSourceTailEntireDet K (-z)

theorem differentiable_routeKSymmetrizedSourceEntireDet (K : ℕ) :
    Differentiable ℂ (routeKSymmetrizedSourceEntireDet K) := by
  exact (differentiable_routeKSourceTailEntireDet K).mul
    ((differentiable_routeKSourceTailEntireDet K).comp differentiable_neg)

/-- The source symmetrization has the functional-equation parity required of a centered Xi
determinant. -/
theorem routeKSymmetrizedSourceEntireDet_even (K : ℕ) (z : ℂ) :
    routeKSymmetrizedSourceEntireDet K (-z) = routeKSymmetrizedSourceEntireDet K z := by
  simp only [routeKSymmetrizedSourceEntireDet, neg_neg]
  ring

/-- Nonzero zeros of the source entire determinant are exactly reciprocal eigenvalues of the
literal cofinal prime tail. -/
theorem routeKSourceTailEntireDet_zero_iff_eigen (K : ℕ) {z : ℂ} (hz : z ≠ 0) :
    routeKSourceTailEntireDet K z = 0 ↔
      ∃ w : RouteKPrimeHilbert, w ≠ 0 ∧
        routeKCofinalTriangleNuclearCarrierFrom K w = z⁻¹ • w := by
  rw [routeKSourceTailEntireDet,
    GaloisForLFunctions.HTGeometry.entireDet2_eq_zero_iff_exists_eigenvector
      (routeKSourceTailKernel_isHS K) hz]
  simpa only [routeKSourceTailKernel] using
    (show (∃ w : RouteKPrimeHilbert, w ≠ 0 ∧
      HilbertSchmidt.toOperator
        (HilbertSchmidt.isHS_matrixOf
          (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K)) w = z⁻¹ • w) ↔
      ∃ w : RouteKPrimeHilbert, w ≠ 0 ∧
        routeKCofinalTriangleNuclearCarrierFrom K w = z⁻¹ • w from by
      rw [HilbertSchmidt.toOperator_matrixOf
        (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K)])

/-- Nonzero zeros of the even source determinant are exactly the two reciprocal source-spectrum
sectors.  Identifying this explicit divisor with Xi remains the K-RVM open theorem. -/
theorem routeKSymmetrizedSourceEntireDet_zero_iff_eigen (K : ℕ) {z : ℂ} (hz : z ≠ 0) :
    routeKSymmetrizedSourceEntireDet K z = 0 ↔
      (∃ w : RouteKPrimeHilbert, w ≠ 0 ∧
        routeKCofinalTriangleNuclearCarrierFrom K w = z⁻¹ • w) ∨
      (∃ w : RouteKPrimeHilbert, w ≠ 0 ∧
        routeKCofinalTriangleNuclearCarrierFrom K w = (-z)⁻¹ • w) := by
  simp only [routeKSymmetrizedSourceEntireDet, mul_eq_zero,
    routeKSourceTailEntireDet_zero_iff_eigen K hz,
    routeKSourceTailEntireDet_zero_iff_eigen K (neg_ne_zero.mpr hz)]

/-- Every zero of the literal source-tail entire determinant is real.  This uses only the
self-adjoint prime carrier, so any future Xi-divisor identification must be global rather than a
local determinant-germ match. -/
theorem routeKSourceTailEntireDet_zero_im (K : ℕ) {z : ℂ}
    (hz : routeKSourceTailEntireDet K z = 0) :
    z.im = 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    have hone :=
      (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
        (routeKSourceTailKernel_isHS K)).eq_one_at_zero
    exact one_ne_zero (hone.symm.trans hz)
  obtain ⟨w, hw0, hw⟩ :=
    (routeKSourceTailEntireDet_zero_iff_eigen K hz0).mp hz
  have heig : Module.End.HasEigenvalue
      (routeKCofinalTriangleNuclearCarrierFrom K : Module.End ℂ RouteKPrimeHilbert) z⁻¹ := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := w) ⟨?_, hw0⟩
    rw [Module.End.mem_eigenspace_iff]
    exact hw
  have hsymm : (routeKCofinalTriangleNuclearCarrierFrom K).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (routeKCofinalTriangleNuclearCarrierFrom_isSelfAdjoint K)
  have hrealInv : star z⁻¹ = z⁻¹ := hsymm.conj_eigenvalue_eq_self heig
  have himInv : z⁻¹.im = 0 := Complex.conj_eq_iff_im.mp hrealInv
  rw [Complex.inv_im] at himInv
  have hnorm : Complex.normSq z ≠ 0 := (Complex.normSq_pos.mpr hz0).ne'
  exact neg_eq_zero.mp (div_eq_zero_iff.mp himInv |>.resolve_right hnorm)

/-- The literal source-tail entire determinant is nonzero away from the real axis. -/
theorem routeKSourceTailEntireDet_ne_zero_of_im_ne (K : ℕ) {z : ℂ} (hz : z.im ≠ 0) :
    routeKSourceTailEntireDet K z ≠ 0 := by
  intro hzero
  exact hz (routeKSourceTailEntireDet_zero_im K hzero)

/-- Cofinal Euler deletion is a vanishing tail in the operator topology: the literal carriers
are tails of one fixed summable block series. -/
theorem tendsto_routeKCofinalTriangleNuclearCarrierFrom_atTop_zero :
    Filter.Tendsto (fun K : ℕ => routeKCofinalTriangleNuclearCarrierFrom K)
      Filter.atTop (nhds 0) := by
  simpa only [routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks] using
    (tendsto_sum_nat_add routeKCofinalTriangleSymmetricBlock)

/-- A zero of the source-tail determinant at `z` requires source operator norm at least the
reciprocal spectral scale `‖z⁻¹‖`. -/
theorem routeKSourceTailEntireDet_ne_zero_of_opNorm_lt (K : ℕ) {z : ℂ}
    (hbound : ‖routeKCofinalTriangleNuclearCarrierFrom K‖ < ‖z⁻¹‖) :
    routeKSourceTailEntireDet K z ≠ 0 := by
  intro hz
  obtain ⟨w, hw0, hw⟩ :=
    (routeKSourceTailEntireDet_zero_iff_eigen K (by
      intro hzero
      subst z
      have hone :=
        (GaloisForLFunctions.HTGeometry.isRegularizedDet_entireDet2
          (routeKSourceTailKernel_isHS K)).eq_one_at_zero
      exact one_ne_zero (hone.symm.trans hz))).mp hz
  have hle := (routeKCofinalTriangleNuclearCarrierFrom K).le_opNorm w
  rw [hw, norm_smul] at hle
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  nlinarith

/-- Every fixed nonzero spectral coordinate is eventually zero-free under literal cofinal
Euler deletion.  Thus these determinants cannot converge divisor-wise to a fixed nontrivial
Xi divisor without a non-tail renormalization or reconstruction. -/
theorem eventually_routeKSourceTailEntireDet_ne_zero (z : ℂ) (hz : z ≠ 0) :
    ∀ᶠ K : ℕ in Filter.atTop, routeKSourceTailEntireDet K z ≠ 0 := by
  have htail : Filter.Tendsto (fun K : ℕ => routeKCofinalTriangleNuclearCarrierFrom K)
      Filter.atTop (nhds 0) :=
    tendsto_routeKCofinalTriangleNuclearCarrierFrom_atTop_zero
  have hnorm : Filter.Tendsto
      (fun K : ℕ => ‖routeKCofinalTriangleNuclearCarrierFrom K‖)
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      ((fun T : RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert => ‖T‖) ∘
        fun K : ℕ => routeKCofinalTriangleNuclearCarrierFrom K)
      Filter.atTop (nhds 0)
    exact tendsto_norm_zero.comp htail
  have hinvpos : 0 < ‖z⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hz)
  filter_upwards [(tendsto_order.1 hnorm).2 _ hinvpos] with K hK
  exact routeKSourceTailEntireDet_ne_zero_of_opNorm_lt K hK

/-- The literal rank-one source terms, viewed in the Hilbert space of Hilbert--Schmidt
operators. -/
noncomputable def routeKPrimeHSTerm (idx : ℕ × Fin 3 × Fin 2) :
    GaloisForLFunctions.HTGeometry.HSpace ℂ RouteKPrimeHilbert :=
  GaloisForLFunctions.HTGeometry.HSpace.mk
    (routeKCofinalTriangleRankOneTerm idx) (by
      rw [routeKCofinalTriangleRankOneTerm]
      split_ifs <;>
        exact (GaloisForLFunctions.HTGeometry.isHilbertSchmidt_rankOne _ _).smul _)

lemma routeKPrimeHSTerm_op (idx : ℕ × Fin 3 × Fin 2) :
    (routeKPrimeHSTerm idx).op = routeKCofinalTriangleRankOneTerm idx := rfl

lemma hsNorm_routeKPrimeBasis_rankOne (p q : Nat.Primes) :
    ContinuousLinearMap.hsNorm (InnerProductSpace.rankOne ℂ
      (routeKPrimeBasis p) (routeKPrimeBasis q)) = 1 := by
  rw [ContinuousLinearMap.hsNorm,
    GaloisForLFunctions.HTGeometry.hsNormSq_rankOne]
  simp [routeKPrimeBasis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

lemma norm_routeKPrimeHSTerm (idx : ℕ × Fin 3 × Fin 2) :
    ‖routeKPrimeHSTerm idx‖ = ‖routeKCofinalTriangleRankOneTerm idx‖ := by
  change ContinuousLinearMap.hsNorm (routeKCofinalTriangleRankOneTerm idx) = _
  rw [routeKCofinalTriangleRankOneTerm]
  split_ifs <;>
    rw [ContinuousLinearMap.hsNorm_smul,
      hsNorm_routeKPrimeBasis_rankOne,
      norm_smul, InnerProductSpace.norm_rankOne] <;>
    simp [routeKPrimeBasis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

lemma summable_routeKPrimeHSTerm : Summable routeKPrimeHSTerm := by
  apply Summable.of_norm
  exact summable_norm_routeKCofinalTriangleRankOneTerm.congr
    (fun idx => (norm_routeKPrimeHSTerm idx).symm)

noncomputable def routeKPrimeHSBlock (n : ℕ) :
    GaloisForLFunctions.HTGeometry.HSpace ℂ RouteKPrimeHilbert :=
  ∑ io : Fin 3 × Fin 2, routeKPrimeHSTerm (n, io)

lemma routeKPrimeHSBlock_op (n : ℕ) :
    (routeKPrimeHSBlock n).op = routeKCofinalTriangleSymmetricBlock n := by
  change (∑ io : Fin 3 × Fin 2,
    routeKCofinalTriangleRankOneTerm (n, io)) = _
  exact routeKCofinalTriangleRankOneTerm_sum_fiber n

lemma summable_routeKPrimeHSBlock : Summable routeKPrimeHSBlock := by
  refine summable_routeKPrimeHSTerm.prod.congr ?_
  intro n
  simp [routeKPrimeHSBlock]

noncomputable def routeKPrimeHSpaceOp :
    GaloisForLFunctions.HTGeometry.HSpace ℂ RouteKPrimeHilbert →L[ℂ]
      (RouteKPrimeHilbert →L[ℂ] RouteKPrimeHilbert) :=
  LinearMap.mkContinuous
    { toFun := GaloisForLFunctions.HTGeometry.HSpace.op
      map_add' := fun S T => GaloisForLFunctions.HTGeometry.HSpace.op_add S T
      map_smul' := fun c S => GaloisForLFunctions.HTGeometry.HSpace.op_smul c S }
    1
    (fun S => by
      rw [GaloisForLFunctions.HTGeometry.HSpace.norm_def]
      simpa using ContinuousLinearMap.norm_le_hsNorm S.isHS)

lemma routeKPrimeHSpaceOp_apply
    (S : GaloisForLFunctions.HTGeometry.HSpace ℂ RouteKPrimeHilbert) :
    routeKPrimeHSpaceOp S = S.op := rfl

noncomputable def routeKPrimeHSTail (K : ℕ) :
    GaloisForLFunctions.HTGeometry.HSpace ℂ RouteKPrimeHilbert :=
  ∑' n : ℕ, routeKPrimeHSBlock (n + K)

lemma summable_routeKPrimeHSBlock_add (K : ℕ) :
    Summable (fun n : ℕ => routeKPrimeHSBlock (n + K)) :=
  summable_routeKPrimeHSBlock.comp_injective
    (fun _ _ h => Nat.add_right_cancel h)

lemma routeKPrimeHSTail_op (K : ℕ) :
    (routeKPrimeHSTail K).op = routeKCofinalTriangleNuclearCarrierFrom K := by
  change routeKPrimeHSpaceOp (∑' n : ℕ, routeKPrimeHSBlock (n + K)) = _
  rw [routeKPrimeHSpaceOp.map_tsum (summable_routeKPrimeHSBlock_add K)]
  simp only [routeKPrimeHSpaceOp_apply]
  rw [tsum_congr (fun n => routeKPrimeHSBlock_op (n + K))]
  exact (routeKCofinalTriangleNuclearCarrierFrom_eq_tsum_blocks K).symm

/-- Absolute rank-one summability makes literal cofinal deletion vanish in Hilbert--Schmidt
norm, not merely in operator norm. -/
lemma tendsto_routeKPrimeHSTail_atTop_zero :
    Filter.Tendsto routeKPrimeHSTail Filter.atTop (nhds 0) := by
  change Filter.Tendsto (fun K : ℕ => ∑' n : ℕ, routeKPrimeHSBlock (n + K))
    Filter.atTop (nhds 0)
  exact tendsto_sum_nat_add routeKPrimeHSBlock

theorem tendsto_hsNorm_routeKCofinalTriangleNuclearCarrierFrom_atTop_zero :
    Filter.Tendsto (fun K : ℕ =>
      ContinuousLinearMap.hsNorm (routeKCofinalTriangleNuclearCarrierFrom K))
      Filter.atTop (nhds 0) := by
  have h := tendsto_routeKPrimeHSTail_atTop_zero.norm
  simpa only [GaloisForLFunctions.HTGeometry.HSpace.norm_def,
    routeKPrimeHSTail_op, norm_zero] using h

lemma hsNorm_routeKSourceTailKernel (K : ℕ) :
    HilbertSchmidt.hsNorm (routeKSourceTailKernel K) =
      ContinuousLinearMap.hsNorm (routeKCofinalTriangleNuclearCarrierFrom K) := by
  rw [← HilbertSchmidt.hsNorm_toOperator
    (HilbertSchmidt.isHS_matrixOf
      (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K))]
  rw [HilbertSchmidt.toOperator_matrixOf
    (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K)]

theorem tendsto_hsNorm_routeKSourceTailKernel_sub_zero :
    Filter.Tendsto (fun K : ℕ => HilbertSchmidt.hsNorm (routeKSourceTailKernel K - 0))
      Filter.atTop (nhds 0) := by
  simpa only [sub_zero, hsNorm_routeKSourceTailKernel] using
    tendsto_hsNorm_routeKCofinalTriangleNuclearCarrierFrom_atTop_zero

theorem tendsto_routeKSourceTailEntireDet_at (z : ℂ) :
    Filter.Tendsto (fun K : ℕ => routeKSourceTailEntireDet K z)
      Filter.atTop (nhds 1) := by
  have hdet :=
    GaloisForLFunctions.HTGeometry.tendsto_entireDet2_of_hsNorm_sub_tendsto_zero
      (fun K : ℕ => routeKSourceTailKernel K) (0 : Nat.Primes × Nat.Primes → ℂ)
      routeKSourceTailKernel_isHS HilbertSchmidt.isHS_zero
      tendsto_hsNorm_routeKSourceTailKernel_sub_zero z
  simpa [routeKSourceTailEntireDet,
    GaloisForLFunctions.HTGeometry.entireDet2_zero_kernel] using hdet

/-- The entire determinants of literal cofinal deletion converge locally uniformly to one.
Consequently, the tail cannot be a nonconstant Xi-divisor limit; a viable K-RVM bridge must
retain or reconstruct a nonvanishing cumulative source contribution. -/
theorem tendstoLocallyUniformly_routeKSourceTailEntireDet_to_one :
    TendstoLocallyUniformly (fun K : ℕ => routeKSourceTailEntireDet K)
      (fun _ : ℂ => 1) Filter.atTop := by
  have hdet :=
    GaloisForLFunctions.HTGeometry.tendstoLocallyUniformly_entireDet2_of_hsNorm_sub_tendsto_zero
      (fun K : ℕ => routeKSourceTailKernel K) (0 : Nat.Primes × Nat.Primes → ℂ)
      routeKSourceTailKernel_isHS HilbertSchmidt.isHS_zero
      tendsto_hsNorm_routeKSourceTailKernel_sub_zero
  simpa [routeKSourceTailEntireDet,
    GaloisForLFunctions.HTGeometry.entireDet2_zero_kernel] using hdet

/-- A scalar trace completion of the vanishing literal cofinal tail can converge only to an
exponential.  Thus scalar renormalization cannot retain any zero divisor. -/
theorem routeKScalarCompletionLimit_eq_exp
    (c : ℕ → ℂ) (F : ℂ → ℂ)
    (hF : TendstoLocallyUniformlyOn
      (fun K : ℕ => GaloisForLFunctions.HTGeometry.completedDet2
        (routeKSourceTailKernel K) (c K)) F Filter.atTop Set.univ) :
    ∃ a : ℂ, Filter.Tendsto c Filter.atTop (nhds a) ∧
      F = fun z : ℂ => Complex.exp (-(z * a)) := by
  obtain ⟨hc, hF_eq⟩ :=
    GaloisForLFunctions.HTGeometry.tendsto_completionCoefficient
      (fun K : ℕ => routeKSourceTailKernel K)
      (0 : Nat.Primes × Nat.Primes → ℂ)
      routeKSourceTailKernel_isHS HilbertSchmidt.isHS_zero
      tendsto_hsNorm_routeKSourceTailKernel_sub_zero c F hF
  refine ⟨-deriv F 0, hc, ?_⟩
  calc
    F = GaloisForLFunctions.HTGeometry.completedDet2
        (0 : Nat.Primes × Nat.Primes → ℂ) (-deriv F 0) := hF_eq
    _ = fun z : ℂ => Complex.exp (-(z * (-deriv F 0))) := by
      funext z
      simp [GaloisForLFunctions.HTGeometry.completedDet2,
        GaloisForLFunctions.HTGeometry.entireDet2_zero_kernel]

/-- Every locally uniform scalar completion limit of literal cofinal deletion is zero-free. -/
theorem routeKScalarCompletionLimit_ne_zero
    (c : ℕ → ℂ) (F : ℂ → ℂ)
    (hF : TendstoLocallyUniformlyOn
      (fun K : ℕ => GaloisForLFunctions.HTGeometry.completedDet2
        (routeKSourceTailKernel K) (c K)) F Filter.atTop Set.univ)
    (z : ℂ) : F z ≠ 0 := by
  obtain ⟨a, -, hF_eq⟩ := routeKScalarCompletionLimit_eq_exp c F hF
  rw [hF_eq]
  exact Complex.exp_ne_zero _

/-- Literal cofinal deletion has no scalar-completed locally uniform limit with a zero. -/
theorem not_exists_routeKScalarCompletionLimit_with_zero :
    ¬ ∃ (c : ℕ → ℂ) (F : ℂ → ℂ),
      TendstoLocallyUniformlyOn
        (fun K : ℕ => GaloisForLFunctions.HTGeometry.completedDet2
          (routeKSourceTailKernel K) (c K)) F Filter.atTop Set.univ ∧
      ∃ z : ℂ, F z = 0 := by
  rintro ⟨c, F, hF, z, hz⟩
  exact routeKScalarCompletionLimit_ne_zero c F hF z hz

/-- Every fixed literal prime carrier has a nonzero determinant zero. -/
theorem exists_routeKSourceTailEntireDet_zero (K : ℕ) :
    ∃ z : ℂ, z ≠ 0 ∧ routeKSourceTailEntireDet K z = 0 := by
  have hcpt : IsCompactOperator (routeKCofinalTriangleNuclearCarrierFrom K) :=
    (routeKCofinalTriangleNuclearCarrierFrom_isHilbertSchmidt K).isCompactOperator
  have hsymm : (routeKCofinalTriangleNuclearCarrierFrom K).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (routeKCofinalTriangleNuclearCarrierFrom_isSelfAdjoint K)
  obtain ⟨mu, x, hmu, hxnorm, hxeig⟩ :=
    ContinuousLinearMap.exists_unit_eigenvector_norm hcpt hsymm
      (routeKCofinalTriangleNuclearCarrierFrom_ne_zero K)
  have hTpos : 0 < ‖routeKCofinalTriangleNuclearCarrierFrom K‖ :=
    norm_pos_iff.mpr (routeKCofinalTriangleNuclearCarrierFrom_ne_zero K)
  have hmu0 : mu ≠ 0 := by
    intro hzero
    apply hTpos.ne'
    simpa [hzero] using hmu.symm
  have hmuC : (mu : ℂ) ≠ 0 := by
    exact_mod_cast hmu0
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hxnorm
    norm_num at hxnorm
  refine ⟨(mu : ℂ)⁻¹, inv_ne_zero hmuC, ?_⟩
  apply (routeKSourceTailEntireDet_zero_iff_eigen K (inv_ne_zero hmuC)).mpr
  refine ⟨x, hx0, ?_⟩
  simpa using hxeig

/-- The fixed cumulative carrier has a nonzero real determinant zero.  It is therefore a genuine
carrier divisor, unlike any scalar-completed cofinal tail; identifying it with Xi remains the
K-RVM bridge problem. -/
theorem exists_routeKCumulativeSourceEntireDet_real_zero :
    ∃ z : ℂ, z ≠ 0 ∧ z.im = 0 ∧ routeKSourceTailEntireDet 0 z = 0 := by
  obtain ⟨z, hz0, hz⟩ := exists_routeKSourceTailEntireDet_zero 0
  exact ⟨z, hz0, routeKSourceTailEntireDet_zero_im 0 hz, hz⟩

/-- The Euler--Weierstrass Gamma--prime Fredholm identity has no radius at `z = 1`: its first
Gamma mode already forces the Hilbert--Schmidt norm above one.  Thus its conditional formula
cannot furnish the K-RVM divisor at that spectral point. -/
theorem not_exists_gammaPrimeHybrid_fredholm_radius
    (sigma : ℝ) (hsigma : 1 < sigma) :
    ¬ ∃ r : ℝ,
      r * HilbertSchmidt.hsNorm (gammaPrimeHybridKernel sigma) < 1 ∧
      (1 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
  let v : lp (fun _ : ℕ ⊕ Nat.Primes => ℂ) 2 :=
    lp.single 2 (Sum.inl 0 : ℕ ⊕ Nat.Primes) 1
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    norm_num
  have hmode := (gammaPrimeHybridOperator sigma hsigma).le_opNorm v
  rw [show v = lp.single 2 (Sum.inl 0 : ℕ ⊕ Nat.Primes) 1 by rfl,
    gammaPrimeHybridOperator_single_inl sigma hsigma 0,
    norm_smul, hvnorm] at hmode
  have hmode' : sigma ≤ ‖gammaPrimeHybridOperator sigma hsigma‖ := by
    simpa [abs_of_pos (lt_trans zero_lt_one hsigma)] using hmode
  have hHSop : (gammaPrimeHybridOperator sigma hsigma).IsHilbertSchmidt :=
    HilbertSchmidt.isHilbertSchmidt_toOperator (gammaPrimeHybridKernel_isHS hsigma)
  have hOpHS : ‖gammaPrimeHybridOperator sigma hsigma‖ ≤
      HilbertSchmidt.hsNorm (gammaPrimeHybridKernel sigma) := by
    rw [← HilbertSchmidt.hsNorm_toOperator (gammaPrimeHybridKernel_isHS hsigma)]
    exact ContinuousLinearMap.norm_le_hsNorm hHSop
  have hHS : sigma ≤ HilbertSchmidt.hsNorm (gammaPrimeHybridKernel sigma) := hmode'.trans hOpHS
  rintro ⟨r, hr, hball⟩
  have hrone : 1 < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  have hHSone : 1 < HilbertSchmidt.hsNorm (gammaPrimeHybridKernel sigma) :=
    lt_of_lt_of_le hsigma hHS
  have hprod : 0 < (r - 1) * (HilbertSchmidt.hsNorm (gammaPrimeHybridKernel sigma) - 1) :=
    mul_pos (sub_pos.mpr hrone) (sub_pos.mpr hHSone)
  nlinarith


open GaloisForLFunctions HilbertSchmidt
open scoped BigOperators

lemma finiteDet2_neg_block_diagMul_one_eq_prod
    {ι : Type*} [DecidableEq ι] (g : ι → ℂ) (s : Finset ι) :
    GaloisForLFunctions.HTGeometry.finiteDet2
        (-(blockMatrix (diagMul g) s)) 1 =
      ∏ i : s, (1 - g i) * Complex.exp (g i) := by
  classical
  letI : LinearOrder s := LinearOrder.lift' (Fintype.equivFin s) (Equiv.injective _)
  let M : Matrix s s ℂ := -(blockMatrix (diagMul g) s)
  have htri : M.BlockTriangular id := by
    intro i j hij
    have hij' : (i : ι) ≠ j := by
      intro h
      exact (ne_of_lt hij) (Subtype.ext h.symm)
    simp [M, blockMatrix, diagMul, hij']
  have hdet := GaloisForLFunctions.HTGeometry.finiteDet2_eq_prod
    (M := M) (U := (1 : Matrix s s ℂ)) (T := M)
    (by simp) (by simp) htri (by simp) (1 : ℂ)
  rw [hdet]
  apply Finset.prod_congr rfl
  intro i hi
  simp [M, blockMatrix, diagMul]
  ring

lemma entireDet2_diagMul_one_eq_tprod
    {ι : Type*} [DecidableEq ι] (g : ι → ℂ)
    (hs2 : Summable (fun i => ‖g i‖ ^ 2))
    (hprod : Multipliable (fun i => (1 - g i) * Complex.exp (g i))) :
    GaloisForLFunctions.HTGeometry.entireDet2 (diagMul g) 1 =
      ∏' i, (1 - g i) * Complex.exp (g i) := by
  have hHS : IsHS (diagMul g) := isHS_diagMul_infinite g hs2
  have hdet := GaloisForLFunctions.HTGeometry.tendsto_finiteDet2_entireDet2 hHS (1 : ℂ)
  have hfin :
      (fun s : Finset ι =>
        GaloisForLFunctions.HTGeometry.finiteDet2
          (-(blockMatrix (diagMul g) s)) 1) =
      fun s : Finset ι => ∏ i ∈ s, (1 - g i) * Complex.exp (g i) := by
    funext s
    rw [Finset.prod_subtype s (by intro x; exact Iff.rfl)]
    exact finiteDet2_neg_block_diagMul_one_eq_prod g s
  rw [hfin] at hdet
  exact tendsto_nhds_unique hdet hprod.hasProd
theorem entireDet2_gammaPrimeHybridKernel_one_eq_gamma_mul_zeta_mul_primeTrace
    (sigma : ℝ) (hsigma : 1 < sigma) :
    GaloisForLFunctions.HTGeometry.entireDet2 (gammaPrimeHybridKernel sigma) 1 =
      ((sigma : ℂ) *
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
          Complex.Gamma (sigma : ℂ))⁻¹ *
        (riemannZeta (sigma : ℂ))⁻¹ *
        Complex.exp (gammaPrimeHybridPrimeTrace sigma) := by
  let primeEigenvalue : Nat.Primes → ℂ := fun p =>
    ((p : ℕ) : ℂ) ^ (-(sigma : ℂ))
  let factor : ℕ ⊕ Nat.Primes → ℂ := fun i =>
    (1 - gammaPrimeHybridEigenvalue sigma i) *
      Complex.exp (gammaPrimeHybridEigenvalue sigma i)
  have hregular : ∀ m : ℕ, (sigma : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    have hspos : 0 < sigma := lt_trans zero_lt_one hsigma
    simp at hre
    linarith
  have hgammaMult :
      Multipliable (fun n : ℕ => factor (Sum.inl n)) := by
    apply (multipliable_weierstrassFactor (sigma : ℂ)).congr
    intro n
    simp only [factor, gammaPrimeHybridEigenvalue]
    congr 1 <;> ring_nf
  have hprimeSummable : Summable primeEigenvalue := by
    apply Summable.of_norm
    simpa only [primeEigenvalue] using
      summable_norm_gammaPrimeHybrid_prime hsigma
  have hprimeSq :
      Summable (fun p : Nat.Primes => ‖primeEigenvalue p‖ ^ 2) := by
    simpa only [primeEigenvalue] using
      summable_normSq_gammaPrimeHybrid_prime hsigma
  have hprimeBare : HasProd (fun p : Nat.Primes => 1 - primeEigenvalue p)
      (∏' p : Nat.Primes, (1 - primeEigenvalue p)) := by
    simpa only [sub_eq_add_neg] using
      (Complex.multipliable_one_add_of_summable hprimeSummable.neg).hasProd
  have hprimeExp :
      HasProd (fun p : Nat.Primes => Complex.exp (primeEigenvalue p))
        (Complex.exp (∑' p : Nat.Primes, primeEigenvalue p)) := by
    simpa only [Function.comp_apply] using! hprimeSummable.hasSum.cexp
  have hprimeHas :
      HasProd (fun p : Nat.Primes => factor (Sum.inr p))
        ((∏' p : Nat.Primes, (1 - primeEigenvalue p)) *
          Complex.exp (∑' p : Nat.Primes, primeEigenvalue p)) := by
    simpa only [factor, gammaPrimeHybridEigenvalue, primeEigenvalue] using
      hprimeBare.mul hprimeExp
  have hprod : Multipliable factor := by
    exact Multipliable.sum factor hgammaMult hprimeHas.multipliable
  rw [gammaPrimeHybridKernel,
    entireDet2_diagMul_one_eq_tprod (gammaPrimeHybridEigenvalue sigma)
      (summable_normSq_gammaPrimeHybridEigenvalue hsigma) (by simpa only [factor] using hprod)]
  rw [(Multipliable.tprod_sum (f := factor) hgammaMult) hprimeHas.multipliable]
  have hgammaProduct :
      (∏' n : ℕ, factor (Sum.inl n)) =
        ((sigma : ℂ) *
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
          Complex.Gamma (sigma : ℂ))⁻¹ := by
    let W : ℂ :=
      ∏' n : ℕ,
        (1 + (sigma : ℂ) / ((n : ℂ) + 1)) *
          Complex.exp (-((sigma : ℂ) / ((n : ℂ) + 1)))
    have hW :
        W = ((sigma : ℂ) *
          Complex.exp ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
          Complex.Gamma (sigma : ℂ))⁻¹ := by
      have hweierstrass :=
        Gamma_inv_weierstrass (sigma : ℂ) hregular
      have hGamma : Complex.Gamma (sigma : ℂ) ≠ 0 :=
        Complex.Gamma_ne_zero hregular
      refine eq_inv_of_mul_eq_one_right ?_
      calc
        ((sigma : ℂ) *
              Complex.exp
                ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) *
              Complex.Gamma (sigma : ℂ)) * W =
            Complex.Gamma (sigma : ℂ) *
              ((sigma : ℂ) *
                Complex.exp
                  ((Real.eulerMascheroniConstant : ℂ) * (sigma : ℂ)) * W) := by
                  ring
        _ = Complex.Gamma (sigma : ℂ) *
              (Complex.Gamma (sigma : ℂ))⁻¹ := by
              rw [← hweierstrass]
        _ = 1 := mul_inv_cancel₀ hGamma
    calc
      (∏' n : ℕ, factor (Sum.inl n)) = W := by
        apply tprod_congr
        intro n
        simp only [factor, gammaPrimeHybridEigenvalue]
        congr 1 <;> ring_nf
      _ = _ := hW
  have hprimeDet :
      (∏' p : Nat.Primes, (1 - primeEigenvalue p)) =
        (riemannZeta (sigma : ℂ))⁻¹ := by
    have hnorm : ∀ p : Nat.Primes, ‖primeEigenvalue p‖ < 1 := by
      intro p
      simp only [primeEigenvalue]
      rw [show ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast p.2.pos)]
      exact Real.rpow_lt_one_of_one_lt_of_neg
        (by exact_mod_cast p.2.one_lt) (by simp; linarith)
    have hne : ∀ p : Nat.Primes, (1 : ℂ) - primeEigenvalue p ≠ 0 := fun p => by
      intro h
      have hlt := hnorm p
      rw [show primeEigenvalue p = 1 from by linear_combination -h, norm_one] at hlt
      exact lt_irrefl 1 hlt
    have hHP2 := riemannZeta_eulerProduct_hasProd (show 1 < (sigma : ℂ).re by simpa using hsigma)
    have hdz : (∏' p : Nat.Primes, (1 - primeEigenvalue p)) * riemannZeta (sigma : ℂ) = 1 :=
      calc (∏' p : Nat.Primes, (1 - primeEigenvalue p)) * riemannZeta (sigma : ℂ)
          = (∏' p : Nat.Primes, (1 - primeEigenvalue p)) *
              ∏' p : Nat.Primes, ((1 - primeEigenvalue p)⁻¹) := by
            rw [← hprimeBare.tprod_eq, ← hHP2.tprod_eq]
        _ = ∏' p : Nat.Primes,
              ((1 - primeEigenvalue p) * (1 - primeEigenvalue p)⁻¹) :=
            (Multipliable.tprod_mul hprimeBare.multipliable
              hHP2.multipliable).symm
        _ = ∏' _p : Nat.Primes, (1 : ℂ) := by
            apply tprod_congr
            intro p
            exact mul_inv_cancel₀ (hne p)
        _ = 1 := tprod_one
    rw [inv_eq_one_div, eq_div_iff (riemannZeta_ne_zero_of_one_lt_re
      (show 1 < (sigma : ℂ).re by simpa using hsigma))]
    exact hdz
  have hprimeProduct :
      (∏' p : Nat.Primes, factor (Sum.inr p)) =
        (riemannZeta (sigma : ℂ))⁻¹ *
          Complex.exp (gammaPrimeHybridPrimeTrace sigma) := by
    rw [hprimeHas.tprod_eq, hprimeDet]
    rfl
  rw [hgammaProduct, hprimeProduct]
  ring

end

end RHTower
