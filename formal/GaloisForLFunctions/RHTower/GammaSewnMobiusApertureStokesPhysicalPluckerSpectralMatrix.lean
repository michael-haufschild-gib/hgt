import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPhysicalPluckerCovariance
import Mathlib.Analysis.Matrix.Order

/-!
# Physical Pluecker covariance spectral matrix

P-G91 exposes the full source covariance discarded by every scalar Schur reduction.  This module
places that covariance on the literal four reciprocal-gap nodes.  Congruence by the positive
square-root node diagonal produces a canonical Hermitian positive-semidefinite spectral matrix.

The resulting operator is not a residue reweighting: every physical packet has a nonzero
off-diagonal entry, rank exactly three, and a one-dimensional transformed common-mode kernel.
In particular it has a zero spectral mode although all four bare reciprocal-gap nodes are
strictly positive.  Thus the source itself forces pole movement off the bare diagonal grid.
-/

open Real Set Filter Topology Matrix
open scoped BigOperators

noncomputable section

namespace RHTower.HedenmalmThetaSource

def gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix
    (e : ℕ) (p q : Nat.Primes) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q
    (fourRateCoordinateDelta i) (fourRateCoordinateDelta j)

private theorem fourRatePluckerCovariance_symmetric
    (weight : Fin 6 → ℝ) (x y : Fin 4 → ℝ) :
    fourRatePluckerCovariance weight x y =
      fourRatePluckerCovariance weight y x := by
  unfold fourRatePluckerCovariance
  have hsum : (∑ s, weight s * RHTower.fourRateSelectedSum x s *
      RHTower.fourRateSelectedSum y s) =
      ∑ s, weight s * RHTower.fourRateSelectedSum y s *
        RHTower.fourRateSelectedSum x s := by
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hsum]
  ring

private theorem fourRatePluckerCovariance_smul_right
    (weight : Fin 6 → ℝ) (x y : Fin 4 → ℝ) (c : ℝ) :
    fourRatePluckerCovariance weight x (c • y) =
      c * fourRatePluckerCovariance weight x y := by
  have hselected : ∀ s : Fin 6,
      RHTower.fourRateSelectedSum (c • y) s =
        c * RHTower.fourRateSelectedSum y s := by
    intro s
    simp [RHTower.fourRateSelectedSum]
    ring
  unfold fourRatePluckerCovariance
  simp_rw [hselected]
  rw [show (∑ s, weight s * RHTower.fourRateSelectedSum x s *
        (c * RHTower.fourRateSelectedSum y s)) =
      c * ∑ s, weight s * RHTower.fourRateSelectedSum x s *
        RHTower.fourRateSelectedSum y s by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring]
  rw [show (∑ s, weight s *
        (c * RHTower.fourRateSelectedSum y s)) =
      c * ∑ s, weight s * RHTower.fourRateSelectedSum y s by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring]
  ring

private theorem fourRateCoordinateDelta_expansion (x : Fin 4 → ℝ) :
    (∑ i : Fin 4, x i • fourRateCoordinateDelta i) = x := by
  funext j
  fin_cases j <;> simp [fourRateCoordinateDelta]

theorem gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_isHermitian
    (e : ℕ) (p q : Nat.Primes) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  exact fourRatePluckerCovariance_symmetric _ _ _

private theorem gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_quadratic
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (x : Fin 4 → ℝ) :
    star x ⬝ᵥ
      (gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q).mulVec x =
        gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q x x := by
  let weight : Fin 6 → ℝ :=
    gammaSewnOrderedPrimeDepthPlucker_probability
      gammaSewnCriticalFinitePacket_aperture e p q
  have hsum : ∑ s, weight s = 1 :=
    sum_gammaSewnCriticalPrimeDepthPacket_probability hpq
  have hmulVec : ∀ i,
      (gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q).mulVec x i =
        fourRatePluckerCovariance weight (fourRateCoordinateDelta i) x := by
    intro i
    simp only [Matrix.mulVec, dotProduct,
      gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix,
      gammaSewnCriticalPrimeDepthPacket_PluckerCovariance, weight]
    calc
      (∑ j, fourRatePluckerCovariance weight (fourRateCoordinateDelta i)
          (fourRateCoordinateDelta j) * x j) =
          ∑ j, fourRatePluckerCovariance weight (fourRateCoordinateDelta i)
            (x j • fourRateCoordinateDelta j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [fourRatePluckerCovariance_smul_right]
        ring
      _ = fourRatePluckerCovariance weight (fourRateCoordinateDelta i)
          (∑ j : Fin 4, x j • fourRateCoordinateDelta j) := by
        symm
        simpa using fourRatePluckerCovariance_finset_sum_right weight hsum
          (fourRateCoordinateDelta i) Finset.univ
          (fun j => x j • fourRateCoordinateDelta j)
      _ = fourRatePluckerCovariance weight (fourRateCoordinateDelta i) x := by
        rw [fourRateCoordinateDelta_expansion]
  simp only [dotProduct, star_trivial]
  simp_rw [hmulVec]
  calc
    (∑ i, x i * fourRatePluckerCovariance weight
        (fourRateCoordinateDelta i) x) =
        ∑ i, fourRatePluckerCovariance weight x
          (x i • fourRateCoordinateDelta i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fourRatePluckerCovariance_smul_right,
        fourRatePluckerCovariance_symmetric]
    _ = fourRatePluckerCovariance weight x
        (∑ i : Fin 4, x i • fourRateCoordinateDelta i) := by
      symm
      simpa using fourRatePluckerCovariance_finset_sum_right weight hsum x
        Finset.univ (fun i => x i • fourRateCoordinateDelta i)
    _ = fourRatePluckerCovariance weight x x := by
      rw [fourRateCoordinateDelta_expansion]
    _ = gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q x x := rfl

theorem gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_posSemidef
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_isHermitian e p q)
  intro x
  rw [gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_quadratic hpq]
  exact gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_nonneg hpq x

def gammaSewnCriticalPrimeDepthPacket_node
    (e : ℕ) (p q : Nat.Primes) (i : Fin 4) : ℝ :=
  RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode (1 / 2)
    (gammaSewnOrderedPrimeDepthPlucker_cell e p q i)

theorem gammaSewnCriticalPrimeDepthPacket_node_pos
    (e : ℕ) (p q : Nat.Primes) (i : Fin 4) :
    0 < gammaSewnCriticalPrimeDepthPacket_node e p q i := by
  exact RHTower.gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_pos
    (by norm_num) _

def gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal
    (e : ℕ) (p q : Nat.Primes) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun i => Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i)

/-- Source-native non-diagonal spectral candidate: reciprocal-gap node congruence of the
full physical Pluecker covariance. -/
def gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix
    (e : ℕ) (p q : Nat.Primes) : Matrix (Fin 4) (Fin 4) ℝ :=
  let D := gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q
  Dᴴ * gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q * D

theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_posSemidef
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).PosSemidef := by
  unfold gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix
  exact
    (gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_posSemidef hpq).conjTranspose_mul_mul_same _

private theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_quadratic
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (x : Fin 4 → ℝ) :
    star x ⬝ᵥ
        (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVec x =
      gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q
        ((gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x)
        ((gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x) := by
  unfold gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
    gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix_quadratic hpq
      ((gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x)

theorem gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal_mulVec_apply
    (e : ℕ) (p q : Nat.Primes) (x : Fin 4 → ℝ) (i : Fin 4) :
    (gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x i =
      Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i) * x i := by
  exact Matrix.mulVec_diagonal _ _ _

/-- Exact one-dimensional nullspace after reciprocal-gap congruence. -/
theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (x : Fin 4 → ℝ) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVec x = 0 ↔
      ∃ c : ℝ,
        (gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x =
          fun _ => c := by
  let A := gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q
  have hA : A.PosSemidef :=
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_posSemidef hpq
  calc
    A.mulVec x = 0 ↔ star x ⬝ᵥ A.mulVec x = 0 :=
      (hA.dotProduct_mulVec_zero_iff x).symm
    _ ↔ gammaSewnCriticalPrimeDepthPacket_PluckerCovariance e p q
        ((gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x)
        ((gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x) = 0 := by
      rw [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_quadratic hpq]
    _ ↔ ∃ c : ℝ,
        (gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal e p q).mulVec x =
          fun _ => c :=
      gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_self_eq_zero_iff_constant
        hpq _

def gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector
    (e : ℕ) (p q : Nat.Primes) : Fin 4 → ℝ :=
  fun i => (Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i))⁻¹

theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector_ne_zero
    (e : ℕ) (p q : Nat.Primes) :
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q ≠ 0 := by
  intro hzero
  have h0 := congrFun hzero (0 : Fin 4)
  have hsqrt : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q 0) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos e p q 0)
  simp [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector,
    hsqrt.ne'] at h0

theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector_mulVec_eq_zero
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVec
        (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q) = 0 := by
  rw [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff hpq]
  refine ⟨1, funext fun i => ?_⟩
  rw [gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal_mulVec_apply]
  have hsqrt : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i) :=
    Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos e p q i)
  simp [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector,
    hsqrt.ne']

/-- Nullspace classification in scalar-span form. -/
theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff_smul_kernel
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ))
    (x : Fin 4 → ℝ) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVec x = 0 ↔
      ∃ c : ℝ,
        x = c • gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q := by
  rw [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff hpq]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun i => ?_⟩
    have hi := congrFun hc i
    rw [gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal_mulVec_apply] at hi
    have hsqrt : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i) :=
      Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos e p q i)
    change x i = c * (Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i))⁻¹
    rw [← div_eq_mul_inv, eq_div_iff hsqrt.ne']
    simpa [mul_comm] using hi
  · rintro ⟨c, rfl⟩
    refine ⟨c, funext fun i => ?_⟩
    rw [gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal_mulVec_apply]
    have hsqrt : 0 < Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i) :=
      Real.sqrt_pos.2 (gammaSewnCriticalPrimeDepthPacket_node_pos e p q i)
    simp only [Pi.smul_apply, smul_eq_mul,
      gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector]
    field_simp

theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_ker_eq_span
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    LinearMap.ker
        (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVecLin =
      ℝ ∙ gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q := by
  ext x
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_mulVec_eq_zero_iff_smul_kernel
      hpq]
  constructor
  · rintro ⟨c, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    exact ⟨c, rfl⟩

/-- Exact rank-three quotient: source common mode is the only null direction. -/
theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_rank_eq_three
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).rank = 3 := by
  let A := gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q
  have hker : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 1 := by
    rw [show LinearMap.ker A.mulVecLin =
        ℝ ∙ gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q by
      exact gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_ker_eq_span hpq]
    exact finrank_span_singleton
      (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector_ne_zero e p q)
  have hsum := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) =
    Module.finrank ℝ (Fin 4 → ℝ) at hsum
  rw [hker, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsum
  have hrank : A.rank = 3 := by omega
  simpa [A] using hrank

theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_apply
    (e : ℕ) (p q : Nat.Primes) (i j : Fin 4) :
    gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q i j =
      Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q i) *
        gammaSewnCriticalPrimeDepthPacket_PluckerCovarianceMatrix e p q i j *
          Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node e p q j) := by
  unfold gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix
    gammaSewnCriticalPrimeDepthPacket_nodeSqrtDiagonal
  simp only [Matrix.diagonal_conjTranspose, star_trivial,
    Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- Spectral matrix is genuinely non-diagonal in the bare reciprocal-gap basis. -/
theorem exists_gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_offDiagonal_ne_zero
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    ∃ i j : Fin 4, i ≠ j ∧
      gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q i j ≠ 0 := by
  obtain ⟨i, j, hij, hcov⟩ :=
    exists_gammaSewnCriticalPrimeDepthPacket_PluckerCovariance_offDiagonal_ne_zero hpq
  refine ⟨i, j, hij, ?_⟩
  rw [gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_apply]
  exact mul_ne_zero
    (mul_ne_zero
      (Real.sqrt_ne_zero'.2 (gammaSewnCriticalPrimeDepthPacket_node_pos e p q i))
      hcov)
    (Real.sqrt_ne_zero'.2 (gammaSewnCriticalPrimeDepthPacket_node_pos e p q j))

/-- P-G92 pole movement: coupled operator has a nonzero zero-mode, while zero is absent from
every positive bare reciprocal-gap node. -/
theorem gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix_zeroMode_off_bareNodeGrid
    {e : ℕ} {p q : Nat.Primes} (hpq : (p : ℕ) < (q : ℕ)) :
    (∃ x : Fin 4 → ℝ, x ≠ 0 ∧
      (gammaSewnCriticalPrimeDepthPacket_PluckerSpectralMatrix e p q).mulVec x = 0) ∧
      ∀ i : Fin 4, gammaSewnCriticalPrimeDepthPacket_node e p q i ≠ 0 := by
  exact ⟨⟨gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector e p q,
      gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector_ne_zero e p q,
      gammaSewnCriticalPrimeDepthPacket_PluckerSpectralKernelVector_mulVec_eq_zero hpq⟩,
    fun i => (gammaSewnCriticalPrimeDepthPacket_node_pos e p q i).ne'⟩

end RHTower.HedenmalmThetaSource
