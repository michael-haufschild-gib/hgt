import GaloisForLFunctions.HTGeometry.ClockDescentAnomalyCocycle
import GaloisForLFunctions.HTGeometry.TateClockUnilateralShiftDefect

/-!
# Tate-clock boundary descent-anomaly universality

The oriented boundary interval of the unilateral Ind clock is not merely analogous to a descent
anomaly.  It is exactly the clock-descent anomaly comparing `m`-step tail reconstruction with the
identity shadow.  Its kernel is simultaneously the `m`th tail submodule and the range of `m`-fold
forward shift.  Its interval-addition law is therefore the explicit Tate-clock realization of the
general anomaly cocycle.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `m`-fold forward unilateral shift as a linear endomorphism. -/
def tateClockIndForwardNEnd {K : Type*} [Field K] (m : ℕ) :
    Module.End K (ℕ →₀ K) where
  toFun := tateClockIndForwardN m
  map_add' a b := by
    ext n
    simp only [tateClockIndForwardN_apply, Finsupp.add_apply]
    by_cases h : m ≤ n <;> simp [h]
  map_smul' c a := by
    ext n
    simp only [tateClockIndForwardN_apply, Finsupp.smul_apply, RingHom.id_apply]
    by_cases h : m ≤ n <;> simp [h]

/-- `m`-fold backward observation as a linear endomorphism. -/
def tateClockIndBackwardNEnd {K : Type*} [Field K] (m : ℕ) :
    Module.End K (ℕ →₀ K) where
  toFun := tateClockIndBackwardN m
  map_add' a b := by
    ext n
    simp
  map_smul' c a := by
    ext n
    simp

/-- Oriented boundary interval as a finite-rank linear observation. -/
def tateClockIndBoundaryIntervalEnd {K : Type*} [Field K] (m : ℕ) :
    Module.End K (ℕ →₀ K) where
  toFun := tateClockIndBoundaryInterval m
  map_add' a b := by
    ext n
    simp only [tateClockIndBoundaryInterval_apply, Finsupp.add_apply]
    by_cases h : n < m <;> simp [h]
  map_smul' c a := by
    ext n
    simp only [tateClockIndBoundaryInterval_apply, Finsupp.smul_apply, RingHom.id_apply]
    by_cases h : n < m <;> simp [h]

/-- The oriented boundary interval is exactly the descent anomaly of tail reconstruction against
the identity clock shadow. -/
theorem tateClockIndBoundaryIntervalEnd_eq_clockDescentAnomaly
    {K : Type*} [Field K] (m : ℕ) :
    tateClockIndBoundaryIntervalEnd (K := K) m =
      clockDescentAnomaly
        ((tateClockIndForwardNEnd m).comp (tateClockIndBackwardNEnd m))
        LinearMap.id LinearMap.id := by
  apply LinearMap.ext
  intro a
  rw [clockDescentAnomaly_apply]
  change tateClockIndBoundaryInterval m a =
    a - tateClockIndForwardN m (tateClockIndBackwardN m a)
  have hdecomp := tateClockInd_boundaryInterval_add_forwardN_backwardN m a
  calc
    tateClockIndBoundaryInterval m a =
        (tateClockIndBoundaryInterval m a +
          tateClockIndForwardN m (tateClockIndBackwardN m a)) -
            tateClockIndForwardN m (tateClockIndBackwardN m a) := by abel
    _ = a - tateClockIndForwardN m (tateClockIndBackwardN m a) := by rw [hdecomp]

/-- The anomaly-free states are exactly the one-sided tail. -/
theorem ker_tateClockIndBoundaryIntervalEnd
    {K : Type*} [Field K] (m : ℕ) :
    LinearMap.ker (tateClockIndBoundaryIntervalEnd (K := K) m) =
      tateClockIndTailSubmodule K m := by
  ext a
  rw [LinearMap.mem_ker]
  exact tateClockIndBoundaryInterval_eq_zero_iff_mem_tailSubmodule m a

/-- The anomaly-free tail is also exactly the range of forward reconstruction. -/
theorem range_tateClockIndForwardNEnd
    {K : Type*} [Field K] (m : ℕ) :
    LinearMap.range (tateClockIndForwardNEnd (K := K) m) =
      tateClockIndTailSubmodule K m := by
  ext a
  rw [LinearMap.mem_range]
  exact (mem_tateClockIndTailSubmodule_iff_exists_forwardN m a).symm

/-- The explicit interval-addition formula is the additive cocycle law of the boundary anomaly. -/
theorem tateClockIndBoundaryIntervalEnd_add_cocycle
    {K : Type*} [Field K] (m n : ℕ) :
    tateClockIndBoundaryIntervalEnd (K := K) (m + n) =
      tateClockIndBoundaryIntervalEnd m +
        (tateClockIndForwardNEnd m).comp
          ((tateClockIndBoundaryIntervalEnd n).comp
            (tateClockIndBackwardNEnd m)) := by
  apply LinearMap.ext
  intro a
  exact tateClockIndBoundaryInterval_add m n a

/-- **Tate-clock boundary descent-anomaly universality law.**  For every pair of clock depths,
the oriented finite boundary is the exact descent anomaly, its zero phase is both the tail and the
forward-reconstruction range, and depth addition is its anomaly cocycle. -/
theorem tateClock_boundaryDescentAnomalyUniversality
    {K : Type*} [Field K] (m n : ℕ) :
    tateClockIndBoundaryIntervalEnd (K := K) m =
        clockDescentAnomaly
          ((tateClockIndForwardNEnd m).comp (tateClockIndBackwardNEnd m))
          LinearMap.id LinearMap.id ∧
      LinearMap.ker (tateClockIndBoundaryIntervalEnd (K := K) m) =
        tateClockIndTailSubmodule K m ∧
      LinearMap.ker (tateClockIndBoundaryIntervalEnd (K := K) m) =
        LinearMap.range (tateClockIndForwardNEnd m) ∧
      tateClockIndBoundaryIntervalEnd (K := K) (m + n) =
        tateClockIndBoundaryIntervalEnd m +
          (tateClockIndForwardNEnd m).comp
            ((tateClockIndBoundaryIntervalEnd n).comp
              (tateClockIndBackwardNEnd m)) := by
  exact ⟨tateClockIndBoundaryIntervalEnd_eq_clockDescentAnomaly m,
    ker_tateClockIndBoundaryIntervalEnd m,
    (ker_tateClockIndBoundaryIntervalEnd m).trans
      (range_tateClockIndForwardNEnd m).symm,
    tateClockIndBoundaryIntervalEnd_add_cocycle m n⟩

end

end GaloisForLFunctions.HTGeometry
