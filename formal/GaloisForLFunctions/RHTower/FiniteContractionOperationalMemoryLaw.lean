import GaloisForLFunctions.RHTower.DissipativeQuantumReturnInformationTransition
import GaloisForLFunctions.RHTower.UniversalOperationalMemoryFloor

/-!
# Exact operational memory of finite contractions

For a finite-dimensional Hilbert contraction, the norm of every orbit
converges to the norm of its canonical peripheral projection.  Applied to a
difference of two initial states, this identifies the exact asymptotic
distinguishability: information survives precisely when the initial
difference has a nonzero peripheral component.

Unlike the autocorrelation ceiling, this is a direct orbit-distance law.
-/

open Filter
open scoped BigOperators Topology

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Evolution on the peripheral sector preserves norm at every time. -/
theorem norm_finiteContraction_pow_apply_peripheralProjection
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) (n : ℕ) :
    ‖(T ^ n) ((finiteContractionPeripheralSubspace T).starProjection x)‖ =
      ‖(finiteContractionPeripheralSubspace T).starProjection x‖ := by
  have horth := finiteContractionPeripheralEigenspaces_orthogonal T hT
  have hbefore := horth.norm_sum
    (fun μ : FiniteContractionPeripheralEigenvalue T =>
      (finiteContractionPeripheralEigenspace T μ).orthogonalProjectionOnto x)
    Finset.univ
  have hafter := horth.norm_sum
    (fun μ : FiniteContractionPeripheralEigenvalue T =>
      ((μ : ℂ) ^ n) •
        (finiteContractionPeripheralEigenspace T μ).orthogonalProjectionOnto x)
    Finset.univ
  have hbeforeSum :
      (∑ μ : FiniteContractionPeripheralEigenvalue T,
        (finiteContractionPeripheralEigenspace T μ).subtypeₗᵢ
          ((finiteContractionPeripheralEigenspace T μ).orthogonalProjectionOnto x)) =
        (finiteContractionPeripheralSubspace T).starProjection x := by
    change
      (∑ μ : FiniteContractionPeripheralEigenvalue T,
        finiteContractionPeripheralComponent T x μ) =
          (finiteContractionPeripheralSubspace T).starProjection x
    exact sum_finiteContractionPeripheralComponent T hT x
  have hafterSum :
      (∑ μ : FiniteContractionPeripheralEigenvalue T,
        (finiteContractionPeripheralEigenspace T μ).subtypeₗᵢ
          (((μ : ℂ) ^ n) •
            (finiteContractionPeripheralEigenspace T μ).orthogonalProjectionOnto x)) =
        (T ^ n) ((finiteContractionPeripheralSubspace T).starProjection x) := by
    rw [← hbeforeSum, map_sum]
    apply Finset.sum_congr rfl
    intro μ _hμ
    change ((μ : ℂ) ^ n) • finiteContractionPeripheralComponent T x μ =
      (T ^ n) (finiteContractionPeripheralComponent T x μ)
    exact (finiteContraction_pow_apply_peripheralComponent T x μ n).symm
  rw [hbeforeSum] at hbefore
  rw [hafterSum] at hafter
  have hsquares :
      ‖(T ^ n) ((finiteContractionPeripheralSubspace T).starProjection x)‖ ^ 2 =
        ‖(finiteContractionPeripheralSubspace T).starProjection x‖ ^ 2 := by
    rw [hafter]
    rw [hbefore]
    apply Finset.sum_congr rfl
    intro μ _hμ
    rw [norm_smul, norm_pow, μ.property, one_pow, one_mul]
  nlinarith [norm_nonneg
    ((T ^ n) ((finiteContractionPeripheralSubspace T).starProjection x)),
    norm_nonneg ((finiteContractionPeripheralSubspace T).starProjection x)]

/-- Exact norm-memory law for every vector under every finite-dimensional
Hilbert contraction. -/
theorem tendsto_norm_finiteContraction_pow_apply_peripheralProjection
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x : H) :
    Tendsto (fun n : ℕ => ‖(T ^ n) x‖) atTop
      (𝓝 ‖(finiteContractionPeripheralSubspace T).starProjection x‖) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htrans :=
    (tendsto_finiteContraction_pow_apply_transient_zero T hT
      (finiteContractionTransientComponent T x)).norm
  have htrans0 :
      Tendsto
        (fun n : ℕ =>
          ‖(T ^ n) (finiteContractionTransientComponent T x : H)‖)
        atTop (𝓝 0) := by
    simpa only [norm_zero] using htrans
  have heventually :
      ∀ᶠ n : ℕ in atTop,
        ‖(T ^ n) (finiteContractionTransientComponent T x : H)‖ < ε :=
    htrans0.eventually_lt_const hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
  refine ⟨N, fun n hnN => ?_⟩
  have hn := hN n hnN
  rw [Real.dist_eq]
  calc
    |‖(T ^ n) x‖ -
        ‖(finiteContractionPeripheralSubspace T).starProjection x‖| =
        |‖(T ^ n) x‖ -
          ‖(T ^ n)
            ((finiteContractionPeripheralSubspace T).starProjection x)‖| := by
      rw [norm_finiteContraction_pow_apply_peripheralProjection T hT x n]
    _ ≤ ‖(T ^ n) x -
        (T ^ n) ((finiteContractionPeripheralSubspace T).starProjection x)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖(T ^ n) (finiteContractionTransientComponent T x : H)‖ := by
      congr 1
      rw [← map_sub]
      rfl
    _ < ε := hn

/-- Exact pairwise distinguishability law: the distance between two
trajectories converges to the norm of the peripheral projection of their
initial difference. -/
theorem tendsto_norm_finiteContraction_pow_apply_sub
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x y : H) :
    Tendsto (fun n : ℕ => ‖(T ^ n) x - (T ^ n) y‖) atTop
      (𝓝 ‖(finiteContractionPeripheralSubspace T).starProjection (x - y)‖) := by
  have hlimit :=
    tendsto_norm_finiteContraction_pow_apply_peripheralProjection
      T hT (x - y)
  simpa only [map_sub] using hlimit

/-- A finite contraction forgets a pair completely exactly when their
initial difference has no peripheral component. -/
theorem finiteContraction_pair_forgetting_iff
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1) (x y : H) :
    Tendsto (fun n : ℕ => ‖(T ^ n) x - (T ^ n) y‖) atTop (𝓝 0) ↔
      (finiteContractionPeripheralSubspace T).starProjection (x - y) = 0 := by
  constructor
  · intro hzero
    have heq :
        ‖(finiteContractionPeripheralSubspace T).starProjection (x - y)‖ =
          0 := tendsto_nhds_unique
      (tendsto_norm_finiteContraction_pow_apply_sub T hT x y) hzero
    exact norm_eq_zero.mp heq
  · intro hzero
    simpa [hzero] using
      tendsto_norm_finiteContraction_pow_apply_sub T hT x y

omit [CompleteSpace H] in
/-- The exact surviving pairwise memory is positive precisely when the
initial difference has a nonzero peripheral component. -/
theorem finiteContraction_pair_persistent_memory_iff
    (T : H →L[ℂ] H) (x y : H) :
    0 <
        ‖(finiteContractionPeripheralSubspace T).starProjection (x - y)‖ ↔
      (finiteContractionPeripheralSubspace T).starProjection (x - y) ≠ 0 := by
  exact norm_pos_iff

end RHTower
