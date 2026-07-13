import GaloisForLFunctions.RHTower.CriticalDiscSchwarzCompleteness

namespace RHTower

noncomputable section

open Complex Metric Set

/-- The first functional-equation-odd coordinate on the critical disc. -/
def criticalDiscFETransverse (r : ℝ) : C(CriticalClosedDisc r, ℂ) :=
  criticalDiscCoordinate r - (1 - criticalDiscCoordinate r)

/-- Deleting any finite set of primes does not remove the FE-transverse coordinate from the
closed span of the remaining paired Euler-unit tangents. -/
theorem criticalDiscFETransverse_mem_closedSpan_compl_finset
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (S : Finset Nat.Primes) :
    criticalDiscFETransverse r ∈
      (Submodule.span ℂ
        (Set.range fun p : {p : Nat.Primes // p ∉ S} =>
          compactPrimeEulerUnitFETangent
            (criticalDiscCoordinate r) (criticalDiscReflection r)
            (p : Nat.Primes))).topologicalClosure := by
  simpa [criticalDiscFETransverse] using
    (criticalDisc_fe_odd_monomial_mem_closedSpan_compl_finset hr0 hr S 1)

/-- Every continuous scalar detector which kills the cofinite paired Euler family also kills the
FE-transverse coordinate.  Thus no Hausdorff continuous quotient by the Euler range can retain
this direction. -/
theorem continuous_detector_kills_criticalDiscFETransverse
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (S : Finset Nat.Primes)
    (L : C(CriticalClosedDisc r, ℂ) →L[ℂ] ℂ)
    (hL : ∀ p : {p : Nat.Primes // p ∉ S},
      L (compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r)
        (p : Nat.Primes)) = 0) :
    L (criticalDiscFETransverse r) = 0 := by
  let V : Set C(CriticalClosedDisc r, ℂ) :=
    Set.range fun p : {p : Nat.Primes // p ∉ S} =>
      compactPrimeEulerUnitFETangent
        (criticalDiscCoordinate r) (criticalDiscReflection r)
        (p : Nat.Primes)
  have hspan : Submodule.span ℂ V ≤ L.ker := by
    rw [Submodule.span_le]
    rintro f ⟨p, rfl⟩
    exact hL p
  have hclosure : (Submodule.span ℂ V).topologicalClosure ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hspan (ContinuousLinearMap.isClosed_ker L)
  exact hclosure
    (criticalDiscFETransverse_mem_closedSpan_compl_finset hr0 hr S)

def criticalDiscRightBoundaryPoint (r : ℝ) (hr0 : 0 ≤ r) : CriticalClosedDisc r :=
  ⟨((1 / 2 + r : ℝ) : ℂ), by
    rw [mem_closedBall, dist_eq]
    norm_num
    simp [abs_of_nonneg hr0]⟩

theorem criticalDiscFETransverse_apply_rightBoundary
    (r : ℝ) (hr0 : 0 ≤ r) :
    criticalDiscFETransverse r (criticalDiscRightBoundaryPoint r hr0) = 2 * r := by
  dsimp [criticalDiscFETransverse, criticalDiscRightBoundaryPoint,
    criticalDiscCoordinate]
  push_cast
  ring

/-- The reduced-quotient blindness is nonvacuous: on every positive-radius critical disc the
transverse coordinate itself is nonzero. -/
theorem criticalDiscFETransverse_ne_zero
    {r : ℝ} (hr : 0 < r) : criticalDiscFETransverse r ≠ 0 := by
  intro hzero
  have hpoint := congrArg
    (fun f : C(CriticalClosedDisc r, ℂ) =>
      f (criticalDiscRightBoundaryPoint r hr.le)) hzero
  change criticalDiscFETransverse r (criticalDiscRightBoundaryPoint r hr.le) = 0 at hpoint
  rw [criticalDiscFETransverse_apply_rightBoundary] at hpoint
  have : (2 * r : ℝ) = 0 := by exact_mod_cast hpoint
  nlinarith

end
end RHTower
