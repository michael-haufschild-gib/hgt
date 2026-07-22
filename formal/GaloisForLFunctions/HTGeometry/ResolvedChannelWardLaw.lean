import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Resolved-channel commutant classification and Ward law

Commuting with every coordinate projection is equivalent to diagonal action, with no finiteness
or continuity assumption.  In finite dimension, the sum of squared Frobenius norms of all
coordinate-projection commutators counts every off-diagonal coefficient exactly twice.  Thus the
resolved Ward energy is a faithful detector of channel mixing.

This separates two requirements that cannot be imposed simultaneously on a source incidence:
literal preservation of every resolved channel and nontrivial off-diagonal channel mixing.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The amplitude `z` supported in the single resolved channel `i`. -/
def resolvedChannelAtom (i : ι) (z : ℂ) : ι → ℂ :=
  fun j => if j = i then z else 0

/-- Coordinate projection onto the resolved channel `i`. -/
def resolvedChannelProjection (i : ι) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun x j := if j = i then x j else 0
  map_add' x y := by
    funext j
    by_cases h : j = i <;> simp [h]
  map_smul' z x := by
    funext j
    by_cases h : j = i <;> simp [h]

/-- A map preserves resolved channels when it commutes with every coordinate projection. -/
def PreservesResolvedChannels (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) : Prop :=
  ∀ i x, T (resolvedChannelProjection i x) = resolvedChannelProjection i (T x)

theorem resolvedChannelProjection_eq_smul_atom (i : ι) (x : ι → ℂ) :
    resolvedChannelProjection i x = x i • resolvedChannelAtom i 1 := by
  funext j
  by_cases h : j = i <;> simp [resolvedChannelProjection, resolvedChannelAtom, h]

/-- Every resolved-channel-preserving map acts pointwise by its diagonal coefficients. -/
theorem apply_eq_resolvedDiagonal
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (hT : PreservesResolvedChannels T)
    (x : ι → ℂ) (i : ι) :
    T x i = x i * T (resolvedChannelAtom i 1) i := by
  calc
    T x i = resolvedChannelProjection i (T x) i := by
      simp [resolvedChannelProjection]
    _ = T (resolvedChannelProjection i x) i := by
      rw [hT i x]
    _ = T (x i • resolvedChannelAtom i 1) i := by
      rw [resolvedChannelProjection_eq_smul_atom]
    _ = x i * T (resolvedChannelAtom i 1) i := by
      rw [LinearMap.map_smul]
      rfl

/-- Exact channel preservation forbids every off-diagonal transfer. -/
theorem resolvedChannelAtom_offDiagonal_eq_zero
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (hT : PreservesResolvedChannels T)
    {i j : ι} (hij : i ≠ j) (z : ℂ) :
    T (resolvedChannelAtom j z) i = 0 := by
  rw [apply_eq_resolvedDiagonal T hT]
  simp [resolvedChannelAtom, hij]

/-- **Resolved-channel commutant classification.** Commuting with every coordinate projection is
equivalent to diagonal pointwise action.  This holds for arbitrary channel types. -/
theorem preservesResolvedChannels_iff_diagonal
    (T : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) :
    PreservesResolvedChannels T ↔
      ∀ x i, T x i = x i * T (resolvedChannelAtom i 1) i := by
  constructor
  · exact fun h => apply_eq_resolvedDiagonal T h
  · intro h i x
    funext j
    by_cases hji : j = i
    · subst j
      rw [h (resolvedChannelProjection i x) i]
      simpa [resolvedChannelProjection] using (h x i).symm
    · rw [h (resolvedChannelProjection i x) j]
      simp [resolvedChannelProjection, hji]

variable [Fintype ι]

/-- Matrix of the coordinate projection onto channel `i`. -/
def resolvedChannelProjectionMatrix (i : ι) : Matrix ι ι ℂ :=
  fun j k => if j = i ∧ k = i then 1 else 0

/-- Commutator of a channel matrix with the coordinate projection onto `i`. -/
def resolvedChannelMatrixCommutator (A : Matrix ι ι ℂ) (i : ι) :
    Matrix ι ι ℂ :=
  A * resolvedChannelProjectionMatrix i - resolvedChannelProjectionMatrix i * A

/-- Squared Frobenius energy of a finite complex matrix. -/
def resolvedChannelFrobeniusEnergy (A : Matrix ι ι ℂ) : ℝ :=
  ∑ j, ∑ k, Complex.normSq (A j k)

theorem resolvedChannelMatrixCommutator_apply
    (A : Matrix ι ι ℂ) (i j k : ι) :
    resolvedChannelMatrixCommutator A i j k =
      (if k = i then A j i else 0) - (if j = i then A i k else 0) := by
  by_cases hki : k = i <;> by_cases hji : j = i <;>
    simp [resolvedChannelMatrixCommutator, resolvedChannelProjectionMatrix,
      Matrix.mul_apply, hki, hji]

theorem normSq_resolvedChannelMatrixCommutator_apply
    (A : Matrix ι ι ℂ) (i j k : ι) :
    Complex.normSq (resolvedChannelMatrixCommutator A i j k) =
      (if j = i ∧ k ≠ i then Complex.normSq (A i k) else 0) +
      (if j ≠ i ∧ k = i then Complex.normSq (A j i) else 0) := by
  rw [resolvedChannelMatrixCommutator_apply]
  by_cases hji : j = i <;> by_cases hki : k = i <;>
    simp [hji, hki]

/-- The commutator at one channel sees exactly its incoming and outgoing coefficients. -/
theorem resolvedChannelFrobeniusEnergy_commutator
    (A : Matrix ι ι ℂ) (i : ι) :
    resolvedChannelFrobeniusEnergy (resolvedChannelMatrixCommutator A i) =
      (∑ j ∈ Finset.univ.erase i, Complex.normSq (A i j)) +
      ∑ j ∈ Finset.univ.erase i, Complex.normSq (A j i) := by
  have hsumErase (f : ι → ℝ) :
      (∑ j, if j ≠ i then f j else 0) =
        ∑ j ∈ Finset.univ.erase i, f j := by
    rw [← Finset.sum_filter]
    rw [Finset.filter_ne']
  have hrow :
      (∑ j, ∑ k, if j = i ∧ k ≠ i then Complex.normSq (A i k) else 0) =
        ∑ k ∈ Finset.univ.erase i, Complex.normSq (A i k) := by
    calc
      _ = ∑ j, if j = i then
            (∑ k ∈ Finset.univ.erase i, Complex.normSq (A i k)) else 0 := by
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hji : j = i
        · subst j
          simpa only [true_and, if_true] using
            hsumErase (fun k => Complex.normSq (A i k))
        · simp [hji]
      _ = _ := by simp
  have hcolumn :
      (∑ j, ∑ k, if j ≠ i ∧ k = i then Complex.normSq (A j i) else 0) =
        ∑ j ∈ Finset.univ.erase i, Complex.normSq (A j i) := by
    calc
      _ = ∑ j, if j ≠ i then Complex.normSq (A j i) else 0 := by
        apply Finset.sum_congr rfl
        intro j _hj
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      _ = _ := hsumErase (fun j => Complex.normSq (A j i))
  rw [resolvedChannelFrobeniusEnergy]
  simp_rw [normSq_resolvedChannelMatrixCommutator_apply,
    Finset.sum_add_distrib]
  rw [hrow, hcolumn]

/-- Squared energy of all off-diagonal channel coefficients. -/
def resolvedChannelOffDiagonalEnergy (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (A i j)

/-- Incoming-plus-outgoing Ward energy summed over resolved channels. -/
def resolvedChannelWardEnergy (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ((∑ j ∈ Finset.univ.erase i, Complex.normSq (A i j)) +
    ∑ j ∈ Finset.univ.erase i, Complex.normSq (A j i))

/-- Total coordinate-projection commutator energy. -/
def resolvedChannelTotalCommutatorEnergy (A : Matrix ι ι ℂ) : ℝ :=
  ∑ i, resolvedChannelFrobeniusEnergy (resolvedChannelMatrixCommutator A i)

theorem resolvedChannelTotalCommutatorEnergy_eq_wardEnergy
    (A : Matrix ι ι ℂ) :
    resolvedChannelTotalCommutatorEnergy A = resolvedChannelWardEnergy A := by
  rw [resolvedChannelTotalCommutatorEnergy, resolvedChannelWardEnergy]
  apply Finset.sum_congr rfl
  intro i _hi
  exact resolvedChannelFrobeniusEnergy_commutator A i

theorem resolvedChannelWardEnergy_eq_two_mul_offDiagonalEnergy
    (A : Matrix ι ι ℂ) :
    resolvedChannelWardEnergy A = 2 * resolvedChannelOffDiagonalEnergy A := by
  rw [resolvedChannelWardEnergy, resolvedChannelOffDiagonalEnergy]
  rw [Finset.sum_add_distrib]
  have hswap :
      (∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (A j i)) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (A i j) := by
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (A j i)) =
          ∑ i, ((∑ j, Complex.normSq (A j i)) - Complex.normSq (A i i)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_erase_add Finset.univ
          (fun j => Complex.normSq (A j i)) (Finset.mem_univ i)]
        ring
      _ = (∑ i, ∑ j, Complex.normSq (A j i)) -
          ∑ i, Complex.normSq (A i i) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i, ∑ j, Complex.normSq (A i j)) -
          ∑ i, Complex.normSq (A i i) := by
        rw [Finset.sum_comm]
      _ = ∑ i, ((∑ j, Complex.normSq (A i j)) - Complex.normSq (A i i)) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, Complex.normSq (A i j) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← Finset.sum_erase_add Finset.univ
          (fun j => Complex.normSq (A i j)) (Finset.mem_univ i)]
        ring
  rw [hswap]
  ring

theorem resolvedChannelOffDiagonalEnergy_nonneg (A : Matrix ι ι ℂ) :
    0 ≤ resolvedChannelOffDiagonalEnergy A := by
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj => Complex.normSq_nonneg (A i j)

theorem resolvedChannelOffDiagonalEnergy_eq_zero_iff
    (A : Matrix ι ι ℂ) :
    resolvedChannelOffDiagonalEnergy A = 0 ↔
      ∀ i j, i ≠ j → A i j = 0 := by
  constructor
  · intro hzero i j hij
    have hrow : ∑ k ∈ Finset.univ.erase i, Complex.normSq (A i k) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _hk =>
        Finset.sum_nonneg fun l _hl => Complex.normSq_nonneg (A k l))).mp hzero
        i (Finset.mem_univ i)
    have hentry : Complex.normSq (A i j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _hk =>
        Complex.normSq_nonneg (A i k))).mp hrow j
        (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    exact Complex.normSq_eq_zero.mp hentry
  · intro hoff
    apply Finset.sum_eq_zero
    intro i _hi
    apply Finset.sum_eq_zero
    intro j hj
    exact Complex.normSq_eq_zero.mpr
      (hoff i j (Ne.symm (Finset.ne_of_mem_erase hj)))

theorem resolvedChannelWardEnergy_eq_zero_iff
    (A : Matrix ι ι ℂ) :
    resolvedChannelWardEnergy A = 0 ↔
      ∀ i j, i ≠ j → A i j = 0 := by
  rw [resolvedChannelWardEnergy_eq_two_mul_offDiagonalEnergy,
    mul_eq_zero, resolvedChannelOffDiagonalEnergy_eq_zero_iff]
  norm_num

/-- **Resolved-channel Ward law.** Summing squared Frobenius norms of all coordinate-projection
commutators counts every off-diagonal matrix coefficient exactly twice. -/
theorem resolvedChannelTotalCommutatorEnergy_eq_two_mul_offDiagonalEnergy
    (A : Matrix ι ι ℂ) :
    resolvedChannelTotalCommutatorEnergy A =
      2 * resolvedChannelOffDiagonalEnergy A := by
  rw [resolvedChannelTotalCommutatorEnergy_eq_wardEnergy,
    resolvedChannelWardEnergy_eq_two_mul_offDiagonalEnergy]

theorem resolvedChannelMatrixCommutators_eq_zero_iff_diagonal
    (A : Matrix ι ι ℂ) :
    (∀ i, resolvedChannelMatrixCommutator A i = 0) ↔
      ∀ i j, i ≠ j → A i j = 0 := by
  constructor
  · intro hcomm i j hij
    have hentry := congrFun (congrFun (hcomm j) i) j
    rw [resolvedChannelMatrixCommutator_apply] at hentry
    simpa [hij] using hentry
  · intro hoff i
    funext j k
    rw [resolvedChannelMatrixCommutator_apply]
    by_cases hki : k = i <;> by_cases hji : j = i
    · subst k
      subst j
      simp
    · simp [hki, hji, hoff j i hji]
    · have hik : i ≠ k := Ne.symm hki
      simp [hki, hji, hoff i k hik]
    · simp [hki, hji]

/-- Total Ward energy vanishes exactly when every resolved projection commutator vanishes. -/
theorem resolvedChannelTotalCommutatorEnergy_eq_zero_iff
    (A : Matrix ι ι ℂ) :
    resolvedChannelTotalCommutatorEnergy A = 0 ↔
      ∀ i, resolvedChannelMatrixCommutator A i = 0 := by
  rw [resolvedChannelTotalCommutatorEnergy_eq_two_mul_offDiagonalEnergy,
    mul_eq_zero, resolvedChannelMatrixCommutators_eq_zero_iff_diagonal,
    ← resolvedChannelOffDiagonalEnergy_eq_zero_iff]
  norm_num

/-- Weighted coherent off-diagonal channel response. -/
def resolvedChannelWeightedCoherence
    (K : Matrix ι ι ℝ) (u : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, K i j * u i * u j

/-- Squared off-diagonal energy of a real channel matrix. -/
def resolvedChannelRealOffDiagonalEnergy (K : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (K i j) ^ 2

/-- Off-diagonal pair energy of a channel weight vector. -/
def resolvedChannelOffDiagonalWeightEnergy (u : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (u i * u j) ^ 2

/-- Cauchy--Schwarz on the off-diagonal incidence set. -/
theorem sq_resolvedChannelWeightedCoherence_le
    (K : Matrix ι ι ℝ) (u : ι → ℝ) :
    resolvedChannelWeightedCoherence K u ^ 2 ≤
      resolvedChannelRealOffDiagonalEnergy K *
        resolvedChannelOffDiagonalWeightEnergy u := by
  let s : Finset (Σ _ : ι, ι) :=
    Finset.univ.sigma (fun i => Finset.univ.erase i)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun ij => K ij.1 ij.2) (fun ij => u ij.1 * u ij.2)
  simpa [s, resolvedChannelWeightedCoherence,
    resolvedChannelRealOffDiagonalEnergy,
    resolvedChannelOffDiagonalWeightEnergy, Finset.sum_sigma, mul_assoc] using hcs

theorem resolvedChannelOffDiagonalEnergy_ofReal
    (K : Matrix ι ι ℝ) :
    resolvedChannelOffDiagonalEnergy (fun i j => (K i j : ℂ)) =
      resolvedChannelRealOffDiagonalEnergy K := by
  simp [resolvedChannelOffDiagonalEnergy,
    resolvedChannelRealOffDiagonalEnergy, Complex.normSq, pow_two]

theorem resolvedChannelOffDiagonalWeightEnergy_le_sq_sum (u : ι → ℝ) :
    resolvedChannelOffDiagonalWeightEnergy u ≤ (∑ i, (u i) ^ 2) ^ 2 := by
  have hrow (i : ι) :
      (∑ j ∈ Finset.univ.erase i, (u i * u j) ^ 2) ≤
        ∑ j, (u i * u j) ^ 2 := by
    rw [← Finset.sum_erase_add Finset.univ (fun j => (u i * u j) ^ 2)
      (Finset.mem_univ i)]
    exact le_add_of_nonneg_right (sq_nonneg (u i * u i))
  calc
    resolvedChannelOffDiagonalWeightEnergy u ≤
        ∑ i, ∑ j, (u i * u j) ^ 2 := by
      exact Finset.sum_le_sum fun i _hi => hrow i
    _ = (∑ i, (u i) ^ 2) ^ 2 := by
      simp_rw [mul_pow]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

theorem resolvedChannelTotalCommutatorEnergy_nonneg
    (A : Matrix ι ι ℂ) :
    0 ≤ resolvedChannelTotalCommutatorEnergy A := by
  rw [resolvedChannelTotalCommutatorEnergy_eq_two_mul_offDiagonalEnergy]
  exact mul_nonneg (by norm_num) (resolvedChannelOffDiagonalEnergy_nonneg A)

/-- **Ward--Schur capacity law.** A positive lower bound on weighted off-diagonal coherence
forces resolved coordinate-commutator energy. -/
theorem resolvedChannelWardSchurCapacity_lower
    (K : Matrix ι ι ℝ) (u : ι → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hcoherence : L ≤ resolvedChannelWeightedCoherence K u) :
    2 * L ^ 2 ≤
      resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) *
        resolvedChannelOffDiagonalWeightEnergy u := by
  have hcs := sq_resolvedChannelWeightedCoherence_le K u
  have hcoherence0 : 0 ≤ resolvedChannelWeightedCoherence K u :=
    hL.trans hcoherence
  have hsq : L ^ 2 ≤
      resolvedChannelRealOffDiagonalEnergy K *
        resolvedChannelOffDiagonalWeightEnergy u := by
    have : L ^ 2 ≤ resolvedChannelWeightedCoherence K u ^ 2 := by
      nlinarith
    exact this.trans hcs
  calc
    2 * L ^ 2 ≤ 2 * (resolvedChannelRealOffDiagonalEnergy K *
        resolvedChannelOffDiagonalWeightEnergy u) := by nlinarith
    _ = resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) *
        resolvedChannelOffDiagonalWeightEnergy u := by
      rw [resolvedChannelTotalCommutatorEnergy_eq_two_mul_offDiagonalEnergy,
        resolvedChannelOffDiagonalEnergy_ofReal]
      ring

/-- Coarser Ward--Schur capacity law using only total squared channel weight. -/
theorem resolvedChannelWardSchurCapacity_simple_lower
    (K : Matrix ι ι ℝ) (u : ι → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hcoherence : L ≤ resolvedChannelWeightedCoherence K u) :
    2 * L ^ 2 ≤
      resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) *
        (∑ i, (u i) ^ 2) ^ 2 := by
  calc
    2 * L ^ 2 ≤
        resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) *
          resolvedChannelOffDiagonalWeightEnergy u :=
      resolvedChannelWardSchurCapacity_lower K u L hL hcoherence
    _ ≤ resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) *
        (∑ i, (u i) ^ 2) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (resolvedChannelOffDiagonalWeightEnergy_le_sq_sum u)
        (resolvedChannelTotalCommutatorEnergy_nonneg _)

end

end HTGeometry
