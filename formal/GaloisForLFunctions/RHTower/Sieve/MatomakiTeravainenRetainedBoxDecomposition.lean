import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenCompleteBoxFamilies

/-!
# Exact retained-box decomposition

The complete post-iteration Harman main is restricted to `(Y / 2, 4Y]`.  Each of its four
literal box families is split into boxes whose lower product scale lies in that interval and one
product-scale boundary error.  No estimate or asymptotic parameter choice enters this identity.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

local instance instDecidableEqMTTripleSeparatedBoxIndexRetained (u t : ℕ) :
    DecidableEq (MTTripleSeparatedBoxIndex u t) := Classical.decEq _

theorem mtRealIntervalAF_add (f g : ℕ → ℂ) (L U : ℝ) :
    mtRealIntervalAF (fun n => f n + g n) L U =
      mtRealIntervalAF f L U + mtRealIntervalAF g L U := by
  ext n
  change (if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then
      f n + g n else 0) =
    (if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then f n else 0) +
    (if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then g n else 0)
  split_ifs <;> simp_all

theorem mtRealIntervalAF_sub (f g : ℕ → ℂ) (L U : ℝ) :
    mtRealIntervalAF (fun n => f n - g n) L U =
      mtRealIntervalAF f L U - mtRealIntervalAF g L U := by
  ext n
  change (if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then
      f n - g n else 0) =
    (if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then f n else 0) -
    (if n = 0 then 0 else if L < (n : ℝ) ∧ (n : ℝ) ≤ U then g n else 0)
  split_ifs <;> simp_all

def mtHarmanRetainedBoxMainAF {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    ArithmeticFunction ℂ :=
  (∑ idx ∈ mtProductScaleIndices
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y,
    mtOuterSeparatedBoxAF mtBaseOuterAlpha data data.z₀ data.D delta idx) -
  (∑ idx ∈ mtProductScaleIndices
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin outerQ))
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y,
    mtOuterSeparatedBoxAF (mtOnePrimeOuterAlpha endpointQ (primesIco z Q))
      data data.z₀ data.D delta idx) +
  (∑ idx ∈ mtProductScaleIndices
      (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedPairBoxScale endpointD delta recStart) Y,
    mtSeparatedPairBoxAF endpointD (primesIco z D) data data.z₀ data.D delta idx) -
  (∑ idx ∈ mtProductScaleIndices
      (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedTripleBoxScale endpointD delta recStart) Y,
    mtSeparatedTripleBoxAF endpointD (primesIco z D) data data.z₀ data.D delta idx)

def mtHarmanProductBoundaryErrorAF {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    ArithmeticFunction ℂ :=
  mtProductScaleBoundaryErrorAF
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin 1))
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxAF mtBaseOuterAlpha data data.z₀ data.D delta)
      (mtOuterSeparatedBoxScale (mtBaseOuterScale delta) delta recStart) Y -
  mtProductScaleBoundaryErrorAF
      (mtOuterSeparatedBoxIndexSet (Finset.univ : Finset (Fin outerQ))
        data maxDepth j (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtOuterSeparatedBoxAF (mtOnePrimeOuterAlpha endpointQ (primesIco z Q))
        data data.z₀ data.D delta)
      (mtOuterSeparatedBoxScale (mtOnePrimeOuterScale endpointQ) delta recStart) Y +
  mtProductScaleBoundaryErrorAF
      (mtSeparatedPairBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedPairBoxAF endpointD (primesIco z D) data data.z₀ data.D delta)
      (mtSeparatedPairBoxScale endpointD delta recStart) Y -
  mtProductScaleBoundaryErrorAF
      (mtSeparatedTripleBoxIndexSet (u := outerD) endpointD E data maxDepth j
        (mtUpperAdicIndex delta data.D) (mtUpperAdicIndex delta N))
      (mtSeparatedTripleBoxAF endpointD (primesIco z D) data data.z₀ data.D delta)
      (mtSeparatedTripleBoxScale endpointD delta recStart) Y

/-- Exact restriction of all complete box families into retained pieces and boundary error. -/
theorem mtHarmanBoxFamilies_interval_eq_retained_add_boundary
    {outerQ outerD recDepth : ℕ}
    (endpointQ endpointD : ℕ → ℕ) (z Q D : ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData recDepth) (maxDepth : ℕ)
    (j : Fin (recDepth + 1)) (delta : ℝ) (N recStart : ℕ) (Y : ℝ) :
    mtRealIntervalAF (fun n =>
      mtHarmanBaseBoxFamilyAF data maxDepth j delta N n -
        mtHarmanOnePrimeBoxFamilyAF (outerDepth := outerQ)
          endpointQ (primesIco z Q) data maxDepth j delta N n +
        mtHarmanPairBoxFamilyAF (outerDepth := outerD)
          endpointD (primesIco z D) E data maxDepth j delta N n -
        mtHarmanTripleBoxFamilyAF (outerDepth := outerD)
          endpointD (primesIco z D) E data maxDepth j delta N n)
      (Y / 2) (4 * Y) =
    mtHarmanRetainedBoxMainAF (outerQ := outerQ) (outerD := outerD)
        endpointQ endpointD z Q D E
        data maxDepth j delta N recStart Y +
      mtHarmanProductBoundaryErrorAF (outerQ := outerQ) (outerD := outerD)
        endpointQ endpointD z Q D E
        data maxDepth j delta N recStart Y := by
  rw [mtRealIntervalAF_sub, mtRealIntervalAF_add, mtRealIntervalAF_sub]
  rw [mtHarmanBaseBoxFamilyAF_eq_sum_outerSeparatedBoxes,
    mtHarmanOnePrimeBoxFamilyAF_eq_sum_outerSeparatedBoxes,
    mtHarmanPairBoxFamilyAF_eq_sum_separatedBoxes,
    mtHarmanTripleBoxFamilyAF_eq_sum_separatedBoxes]
  rw [mtRealIntervalAF_sum_eq_sum_productScaleIndices_add_error,
    mtRealIntervalAF_sum_eq_sum_productScaleIndices_add_error,
    mtRealIntervalAF_sum_eq_sum_productScaleIndices_add_error,
    mtRealIntervalAF_sum_eq_sum_productScaleIndices_add_error]
  unfold mtHarmanRetainedBoxMainAF mtHarmanProductBoundaryErrorAF
  abel

end

end RHTower.Sieve
