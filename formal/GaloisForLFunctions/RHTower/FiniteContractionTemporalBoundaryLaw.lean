import GaloisForLFunctions.RHTower.FiniteContractionOperationalMemoryLaw

/-!
# The asymptotic temporal boundary of a finite contraction

Every orbit of every finite-dimensional Hilbert-space contraction approaches
the orbit of its canonical peripheral projection.  Motion on that peripheral
orbit preserves norm exactly.  For a pair of initial vectors, asymptotic
forgetting occurs exactly when their difference has zero peripheral
projection.

This joins transient decay, recurrent norm preservation and operational
memory into one unconditional boundary law.
-/

open Filter
open scoped Topology

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Every finite-contraction orbit approaches the orbit of its canonical
peripheral projection. -/
theorem tendsto_finiteContraction_orbit_sub_peripheralOrbit_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    Tendsto
      (fun n : ℕ =>
        (T ^ n) x -
          (T ^ n)
            ((finiteContractionPeripheralSubspace T).starProjection x))
      atTop (𝓝 0) := by
  have htransient :=
    tendsto_finiteContraction_pow_apply_transient_zero T hT
      (finiteContractionTransientComponent T x)
  refine htransient.congr' ?_
  filter_upwards with n
  change
    (T ^ n)
        (x -
          (finiteContractionPeripheralSubspace T).starProjection x) =
      (T ^ n) x -
        (T ^ n)
          ((finiteContractionPeripheralSubspace T).starProjection x)
  rw [map_sub]

/-- The distance from every finite-contraction orbit to its canonical
peripheral orbit tends to zero. -/
theorem tendsto_norm_finiteContraction_orbit_sub_peripheralOrbit_zero
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    Tendsto
      (fun n : ℕ =>
        ‖(T ^ n) x -
          (T ^ n)
            ((finiteContractionPeripheralSubspace T).starProjection x)‖)
      atTop (𝓝 0) := by
  simpa only [norm_zero] using
    (tendsto_finiteContraction_orbit_sub_peripheralOrbit_zero T hT x).norm

/-- **Finite-contraction temporal-boundary law.** Every orbit approaches a
norm-preserving peripheral orbit, and asymptotic loss of pairwise
distinguishability occurs exactly in the kernel of the peripheral
projection. -/
theorem finiteContraction_temporalBoundary_core
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) :
    (∀ x : H,
      Tendsto
        (fun n : ℕ =>
          ‖(T ^ n) x -
            (T ^ n)
              ((finiteContractionPeripheralSubspace T).starProjection x)‖)
        atTop (𝓝 0)) ∧
    (∀ (x : H) (n : ℕ),
      ‖(T ^ n)
          ((finiteContractionPeripheralSubspace T).starProjection x)‖ =
        ‖(finiteContractionPeripheralSubspace T).starProjection x‖) ∧
    (∀ x y : H,
      Tendsto
          (fun n : ℕ => ‖(T ^ n) x - (T ^ n) y‖)
          atTop (𝓝 0) ↔
        (finiteContractionPeripheralSubspace T).starProjection (x - y) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact tendsto_norm_finiteContraction_orbit_sub_peripheralOrbit_zero T hT x
  · intro x n
    exact norm_finiteContraction_pow_apply_peripheralProjection T hT x n
  · intro x y
    exact finiteContraction_pair_forgetting_iff T hT x y

end RHTower
