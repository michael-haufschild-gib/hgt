import GaloisForLFunctions.HTGeometry.OccupiedBuresTargetBodyLaw
import GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw

/-!
# Projected Bures complete-incidence law

This module composes the exact one-copy projection threshold transfer with
the occupied-body Bures minimax law.  It gives the fixed-carrier `K-BIM`
bound: after one target-independent projection defect, the complete target
union is controlled by one Bures capacity of the projected replica source.
-/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical relabelling of an `r`-fold `d`-level tensor coordinate by one
finite coordinate type. -/
def finiteReplicaReindex {d r : ℕ}
    (v : (Fin r → Fin d) → ℂ) : Fin (d ^ r) → ℂ :=
  fun j => v (finFunctionFinEquiv.symm j)

theorem finiteComplexInner_finiteReplicaReindex
    {d r : ℕ} (u v : (Fin r → Fin d) → ℂ) :
    finiteComplexInner (finiteReplicaReindex u) (finiteReplicaReindex v) =
      finiteComplexInner u v := by
  unfold finiteComplexInner finiteReplicaReindex
  rw [← finFunctionFinEquiv.symm.sum_comp]

/-- Reindexed coordinate replica tensor. -/
def finiteReplicaReindexedPower {d : ℕ} (r : ℕ) (ψ : Fin d → ℂ) :
    Fin (d ^ r) → ℂ :=
  finiteReplicaReindex (finitePureTensorPower r ψ)

theorem finiteComplexInner_finiteReplicaReindexedPower
    {d : ℕ} (r : ℕ) (ψ φ : Fin d → ℂ) :
    finiteComplexInner (finiteReplicaReindexedPower r ψ)
        (finiteReplicaReindexedPower r φ) =
      finiteComplexInner ψ φ ^ r := by
  rw [finiteReplicaReindexedPower, finiteReplicaReindexedPower,
    finiteComplexInner_finiteReplicaReindex,
    finiteComplexInner_pureTensorPower]

/-- A complete one-copy capture survives projection and replica lifting at
the exact shifted threshold. -/
theorem completeTargetCapture_subset_projectedReplicaBuresCapture
    {X C : Type*} {d : ℕ}
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (target : C → Fin d → ℂ) (state : X → Fin d → ℂ)
    (htarget : ∀ c, ‖WithLp.toLp 2 (target c)‖ ≤ 1)
    {a eta : ℝ} (hdelta : 0 ≤ Real.sqrt a - eta)
    (hdef : ∀ x, ‖WithLp.toLp 2 (state x) -
      S.starProjection (WithLp.toLp 2 (state x))‖ ≤ eta)
    (r : ℕ) :
    {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} ⊆
      finitePositiveReporterCaptureEvent
        (fun c => finiteReplicaReindexedPower r (projectedReplicaTarget S target c))
        (fun x => finiteReplicaReindexedPower r
          (fun i => S.starProjection (WithLp.toLp 2 (state x)) i))
        ((Real.sqrt a - eta) ^ (2 * r)) := by
  intro x hx
  obtain ⟨c, hc⟩ :=
    completeTargetCapture_subset_projectedCapture
      S target state htarget hdelta hdef hx
  refine ⟨c, ?_⟩
  have hpow := pow_le_pow_left₀ (sq_nonneg (Real.sqrt a - eta)) hc r
  rw [finitePureStateFidelity] at hpow
  rw [finiteComplexInner_finiteReplicaReindexedPower, norm_pow]
  calc
    (Real.sqrt a - eta) ^ (2 * r) =
        ((Real.sqrt a - eta) ^ (2 : ℕ)) ^ r := by rw [pow_mul]
    _ ≤ (‖finiteComplexInner
          (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)
          (projectedReplicaTarget S target c)‖ ^ (2 : ℕ)) ^ r := hpow
    _ = (‖finiteComplexInner
          (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)
          (projectedReplicaTarget S target c)‖ ^ r) ^ (2 : ℕ) := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- **Fixed-carrier projected Bures incidence (`K-BIM`).**  Source sheets
remain in the original measure space, return mass is charged once, and the
complete projected target image enters through one compact Bures body. -/
theorem projectedBures_capture_le_return_add_capacity
    {X C : Type*} [MeasurableSpace X] [Fintype C] [Nonempty C]
    {d : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin d)))
    (target : C → Fin d → ℂ) (state : X → Fin d → ℂ)
    (htarget : ∀ c, ‖WithLp.toLp 2 (target c)‖ ≤ 1)
    {a eta : ℝ} (hdelta : eta < Real.sqrt a)
    (hdef : ∀ x, ‖WithLp.toLp 2 (state x) -
      S.starProjection (WithLp.toLp 2 (state x))‖ ≤ eta)
    {r : ℕ} (_hr : 0 < r)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hprod : ∀ i j, Integrable
      (fun x =>
        finiteReplicaReindexedPower r
            (fun q => S.starProjection (WithLp.toLp 2 (state x)) q) i *
          star (finiteReplicaReindexedPower r
            (fun q => S.starProjection (WithLp.toLp 2 (state x)) q) j))
      (mu.restrict returnSetᶜ)) :
    mu.real {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} ≤
      mu.real returnSet +
        compactBuresDualCapacity
          (finitePositiveReporterSourceCovariance
            (mu.restrict returnSetᶜ)
            (fun x => finiteReplicaReindexedPower r
              (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)))
          (finiteBuresOccupiedTargetBody
            (Set.range fun c => finiteReplicaReindexedPower r
              (projectedReplicaTarget S target c))) ^ (2 : ℕ) /
          (Real.sqrt a - eta) ^ (2 * r) := by
  let delta : ℝ := Real.sqrt a - eta
  let targetR : C → Fin (d ^ r) → ℂ := fun c =>
    finiteReplicaReindexedPower r (projectedReplicaTarget S target c)
  let stateR : X → Fin (d ^ r) → ℂ := fun x =>
    finiteReplicaReindexedPower r
      (fun i => S.starProjection (WithLp.toLp 2 (state x)) i)
  have hdeltaPos : 0 < delta := sub_pos.mpr hdelta
  have hthreshold : 0 < delta ^ (2 * r) :=
    pow_pos hdeltaPos (2 * r)
  have hsubset :
      {x | ∃ c, a ≤ finitePureStateFidelity (state x) (target c)} ⊆
        finitePositiveReporterCaptureEvent targetR stateR
          (delta ^ (2 * r)) := by
    simpa [delta, targetR, stateR] using
      completeTargetCapture_subset_projectedReplicaBuresCapture
        S target state htarget hdeltaPos.le hdef r
  have hcompact : IsCompact (Set.range targetR) :=
    Set.Finite.isCompact (Set.finite_range targetR)
  have hbures := occupiedTargetBures_returnExcisedIncidence_minimax_bound
    mu targetR stateR (delta ^ (2 * r)) hthreshold
      returnSet hreturn hcompact (by simpa [stateR] using hprod)
  exact (measureReal_mono hsubset).trans (by
    simpa [delta, targetR, stateR] using hbures)

/-- Hamiltonian specialization of `K-BIM` with the sharp factorial Krylov
boundary.  This is the exact fixed-carrier law in the paper. -/
theorem boundedHamiltonian_capture_le_return_add_projectedBuresCapacity
    {X C : Type*} [MeasurableSpace X] [Fintype C] [Nonempty C]
    {d : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    {r : ℕ} (hr : 0 < r)
    (H : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (hH : IsSelfAdjoint H)
    {psi : EuclideanSpace ℂ (Fin d)} (hpsi : ‖psi‖ ≤ 1)
    (target : C → Fin d → ℂ)
    (htarget : ∀ c, ‖WithLp.toLp 2 (target c)‖ ≤ 1)
    (time : X → ℝ) (K : ℕ) {B T a : ℝ}
    (hB : 0 ≤ B) (hHnorm : ‖H‖ ≤ B)
    (htime : ∀ x, |time x| ≤ T)
    (hboundary : krylovFactorialBoundary B T K < Real.sqrt a)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hprod : ∀ i j, Integrable
      (fun x =>
        finiteReplicaReindexedPower r
            (fun q => boundedHamiltonianKrylovProjection H psi K (time x) q) i *
          star (finiteReplicaReindexedPower r
            (fun q => boundedHamiltonianKrylovProjection H psi K (time x) q) j))
      (mu.restrict returnSetᶜ)) :
    mu.real {x | ∃ c, a ≤ finitePureStateFidelity
        (fun i => boundedHamiltonianOrbit H psi (time x) i) (target c)} ≤
      mu.real returnSet +
        compactBuresDualCapacity
          (finitePositiveReporterSourceCovariance
            (mu.restrict returnSetᶜ)
            (fun x => finiteReplicaReindexedPower r
              (fun i => boundedHamiltonianKrylovProjection H psi K (time x) i)))
          (finiteBuresOccupiedTargetBody
            (Set.range fun c => finiteReplicaReindexedPower r
              (projectedReplicaTarget
                (boundedHamiltonianKrylovSubspace H psi K) target c))) ^ (2 : ℕ) /
          (Real.sqrt a - krylovFactorialBoundary B T K) ^ (2 * r) := by
  let state : X → Fin d → ℂ := fun x i =>
    boundedHamiltonianOrbit H psi (time x) i
  let S := boundedHamiltonianKrylovSubspace H psi K
  have hdef : ∀ x,
      ‖WithLp.toLp 2 (state x) -
        S.starProjection (WithLp.toLp 2 (state x))‖ ≤
          krylovFactorialBoundary B T K := by
    intro x
    have hcoord : WithLp.toLp 2 (state x) =
        boundedHamiltonianOrbit H psi (time x) := by
      ext i
      rfl
    simpa [state, S, hcoord, boundedHamiltonianKrylovProjection] using
      norm_boundedHamiltonianOrbit_sub_krylovProjection_le_boundary
        H hH hpsi K hB hHnorm (htime x)
  simpa [state, S, boundedHamiltonianKrylovProjection] using
    projectedBures_capture_le_return_add_capacity
      mu S target state htarget hboundary hdef hr returnSet hreturn (by
        simpa [state, S, boundedHamiltonianKrylovProjection] using hprod)

end

end GaloisForLFunctions.HTGeometry
