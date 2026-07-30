import GaloisForLFunctions.RHTower.GammaOddJacobiCapacity
import GaloisForLFunctions.RHTower.ZeroEstimate
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Strict finite-packet definiteness of the Gamma conductor Schur residual

The normalized Gamma cyclic covariance loses two Jacobi coordinates when its mean and centered
second-moment conductor are removed: degrees zero and two.  This file proves the exact surviving
Mercer law.  Degree one and every degree at least three remain with their source Jacobi weights.

The consecutive tail beginning at degree three is already a weighted Vandermonde family.
Consequently the Schur residual is strictly positive definite on every injective finite packet of
positive frequencies.  This strengthens entrywise positivity to faithfulness of the full finite
Gamma-projected Gram.  No Xi zero, Riemann-hypothesis premise, target positivity hypothesis, or
numerical computation is used.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set
open scoped BigOperators Nat Real

namespace RHTower

/-- Real Jacobi feature of a Gamma Fourier mode after removing its harmless phase. -/
def gammaConductorJacobiFeature (n : ℕ) (t : ℝ) : ℝ :=
  semilocalArchimedeanJacobiNormalization n *
    semilocalArchimedeanCharacteristic t * Real.tanh t ^ n

theorem gammaConductorJacobiFeature_pos
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < gammaConductorJacobiFeature n t := by
  unfold gammaConductorJacobiFeature
  exact mul_pos
    (mul_pos (semilocalArchimedeanJacobiNormalization_pos n)
      (semilocalArchimedeanCharacteristic_pos t))
    (pow_pos (by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos ((Real.sinh_pos_iff).2 ht) (Real.cosh_pos t)) n)

private theorem gammaConductorJacobiNormalization_zero_sq :
    semilocalArchimedeanJacobiNormalization 0 ^ 2 = 1 := by
  rw [semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom]
  norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
    Nat.centralBinom, Nat.choose]

private theorem gammaConductorJacobiNormalization_one_sq :
    semilocalArchimedeanJacobiNormalization 1 ^ 2 = (1 / 2 : ℝ) := by
  rw [semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom]
  norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
    Nat.centralBinom, Nat.choose]

private theorem gammaConductorJacobiNormalization_two_sq :
    semilocalArchimedeanJacobiNormalization 2 ^ 2 = (3 / 8 : ℝ) := by
  rw [semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom]
  norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom,
    Nat.centralBinom, Nat.choose]

private theorem gammaConductorJacobiFeature_mul_eq
    (n : ℕ) (t u : ℝ) :
    gammaConductorJacobiFeature n t * gammaConductorJacobiFeature n u =
      (semilocalArchimedeanCharacteristic t *
        semilocalArchimedeanCharacteristic u) *
      (semilocalArchimedeanJacobiNormalization n ^ 2 *
        (Real.tanh t * Real.tanh u) ^ n) := by
  unfold gammaConductorJacobiFeature
  rw [mul_pow]
  ring

/-- **Gamma conductor deletion law.**  Removing the mean and centered second moment deletes
exactly Jacobi degrees zero and two.  Degree one and the complete consecutive tail from degree
three survive as an exact Mercer expansion. -/
theorem gammaConductorModeSchurResidual_eq_jacobi_one_add_tsum
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    gammaConductorModeSchurResidual t u =
      gammaConductorJacobiFeature 1 t * gammaConductorJacobiFeature 1 u +
        ∑' k : ℕ,
          gammaConductorJacobiFeature (k + 3) t *
            gammaConductorJacobiFeature (k + 3) u := by
  have htanh0 : 0 < Real.tanh t := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos ((Real.sinh_pos_iff).2 ht) (Real.cosh_pos t)
  have hutanh0 : 0 < Real.tanh u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos ((Real.sinh_pos_iff).2 hu) (Real.cosh_pos u)
  let x := Real.tanh t * Real.tanh u
  have hx0 : 0 ≤ x := (mul_pos htanh0 hutanh0).le
  have hx1 : x < 1 := by
    dsimp [x]
    calc
      Real.tanh t * Real.tanh u < Real.tanh t * 1 :=
        mul_lt_mul_of_pos_left (Real.tanh_lt_one u) htanh0
      _ < 1 := by simpa using Real.tanh_lt_one t
  have hxabs : |x| < 1 := by simpa [abs_of_nonneg hx0] using hx1
  let f : ℕ → ℝ := fun n =>
    semilocalArchimedeanJacobiNormalization n ^ 2 * x ^ n
  have hsum := hasSum_semilocalArchimedeanJacobiNormalization_sq_mul_pow hxabs
  have hsplit := hsum.summable.sum_add_tsum_nat_add 3
  rw [hsum.tsum_eq] at hsplit
  have hfirst :
      ∑ n ∈ Finset.range 3, f n =
        1 + (1 / 2 : ℝ) * x + (3 / 8 : ℝ) * x ^ 2 := by
    rw [show ∑ n ∈ Finset.range 3, f n = f 0 + f 1 + f 2 by
      simp [Finset.sum_range_succ]]
    dsimp [f]
    rw [gammaConductorJacobiNormalization_zero_sq,
      gammaConductorJacobiNormalization_one_sq,
      gammaConductorJacobiNormalization_two_sq]
    ring
  rw [hfirst] at hsplit
  rw [gammaConductorModeSchurResidual_eq ht hu,
    gammaConductorSchurResidualBracket]
  rw [gammaConductorJacobiFeature_mul_eq]
  rw [show
      (∑' k : ℕ,
        gammaConductorJacobiFeature (k + 3) t *
          gammaConductorJacobiFeature (k + 3) u) =
        (semilocalArchimedeanCharacteristic t *
          semilocalArchimedeanCharacteristic u) *
          ∑' k : ℕ, f (k + 3) by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      rw [gammaConductorJacobiFeature_mul_eq]]
  dsimp [x] at hsplit ⊢
  rw [gammaConductorJacobiNormalization_one_sq]
  have htail :
      (1 - Real.tanh t * Real.tanh u) ^ (-(1 : ℝ) / 2) -
          1 - (3 / 8 : ℝ) * (Real.tanh t * Real.tanh u) ^ 2 =
        (1 / 2 : ℝ) * (Real.tanh t * Real.tanh u) +
          ∑' k : ℕ, f (k + 3) := by
    linarith
  rw [htail]
  ring

/-- Every quadratic form of the Gamma Schur residual is the sum of squared surviving Jacobi
coordinates. -/
theorem gammaConductorModeSchurResidual_quadratic_eq
    {n : ℕ} (t c : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    (∑ i, ∑ j,
        c i * gammaConductorModeSchurResidual (t i) (t j) * c j) =
      (∑ i, c i * gammaConductorJacobiFeature 1 (t i)) ^ 2 +
        ∑' k : ℕ,
          (∑ i, c i * gammaConductorJacobiFeature (k + 3) (t i)) ^ 2 := by
  let g : Fin n → Fin n → ℕ → ℝ := fun i j k =>
    c i * (gammaConductorJacobiFeature (k + 3) (t i) *
      gammaConductorJacobiFeature (k + 3) (t j)) * c j
  have hg (i j : Fin n) : Summable (g i j) := by
    have hbase :=
      (hasSum_semilocalArchimedeanJacobiNormalization_sq_mul_pow
        (show |Real.tanh (t i) * Real.tanh (t j)| < 1 by
          have hi0 : 0 < Real.tanh (t i) := by
            rw [Real.tanh_eq_sinh_div_cosh]
            exact div_pos ((Real.sinh_pos_iff).2 (ht i)) (Real.cosh_pos (t i))
          have hj0 : 0 < Real.tanh (t j) := by
            rw [Real.tanh_eq_sinh_div_cosh]
            exact div_pos ((Real.sinh_pos_iff).2 (ht j)) (Real.cosh_pos (t j))
          rw [abs_of_pos (mul_pos hi0 hj0)]
          calc
            Real.tanh (t i) * Real.tanh (t j) < Real.tanh (t i) * 1 :=
              mul_lt_mul_of_pos_left (Real.tanh_lt_one (t j)) hi0
            _ < 1 := by simpa using Real.tanh_lt_one (t i))).summable
    have htail := hbase.comp_injective
      (show Function.Injective (fun k : ℕ => k + 3) by
        intro k l h
        exact Nat.add_right_cancel h)
    have hscaled := htail.mul_left
      (c i * c j * semilocalArchimedeanCharacteristic (t i) *
        semilocalArchimedeanCharacteristic (t j))
    convert! hscaled using 1
    funext k
    dsimp [g]
    rw [gammaConductorJacobiFeature_mul_eq]
    ring
  calc
    (∑ i, ∑ j,
        c i * gammaConductorModeSchurResidual (t i) (t j) * c j) =
        ∑ i, ∑ j,
          (c i * (gammaConductorJacobiFeature 1 (t i) *
            gammaConductorJacobiFeature 1 (t j)) * c j + ∑' k, g i j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [gammaConductorModeSchurResidual_eq_jacobi_one_add_tsum
        (ht i) (ht j)]
      dsimp [g]
      rw [mul_add, add_mul, ← tsum_mul_left, ← tsum_mul_right]
    _ =
        (∑ i, ∑ j,
          c i * (gammaConductorJacobiFeature 1 (t i) *
            gammaConductorJacobiFeature 1 (t j)) * c j) +
        ∑ i, ∑ j, ∑' k, g i j k := by
      simp only [Finset.sum_add_distrib]
    _ =
        (∑ i, ∑ j,
          c i * (gammaConductorJacobiFeature 1 (t i) *
            gammaConductorJacobiFeature 1 (t j)) * c j) +
        ∑ i, ∑' k, ∑ j, g i j k := by
      apply congrArg (fun z => _ + z)
      apply Finset.sum_congr rfl
      intro i _
      rw [Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => hg i j)]
    _ =
        (∑ i, ∑ j,
          c i * (gammaConductorJacobiFeature 1 (t i) *
            gammaConductorJacobiFeature 1 (t j)) * c j) +
        ∑' k, ∑ i, ∑ j, g i j k := by
      apply congrArg (fun z => _ + z)
      have hgi (i : Fin n) : Summable (fun k => ∑ j, g i j k) :=
        summable_sum (s := Finset.univ) (fun j _ => hg i j)
      rw [Summable.tsum_finsetSum (s := Finset.univ) (fun i _ => hgi i)]
    _ =
        (∑ i, c i * gammaConductorJacobiFeature 1 (t i)) ^ 2 +
        ∑' k : ℕ,
          (∑ i, c i * gammaConductorJacobiFeature (k + 3) (t i)) ^ 2 := by
      congr 1
      · calc
          ∑ i, ∑ j,
              c i * (gammaConductorJacobiFeature 1 (t i) *
                gammaConductorJacobiFeature 1 (t j)) * c j =
              (∑ i, c i * gammaConductorJacobiFeature 1 (t i)) *
                (∑ j, c j * gammaConductorJacobiFeature 1 (t j)) := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
          _ = _ := by ring
      · apply tsum_congr
        intro k
        dsimp [g]
        calc
          ∑ i, ∑ j,
              c i * (gammaConductorJacobiFeature (k + 3) (t i) *
                gammaConductorJacobiFeature (k + 3) (t j)) * c j =
              (∑ i, c i * gammaConductorJacobiFeature (k + 3) (t i)) *
                (∑ j, c j * gammaConductorJacobiFeature (k + 3) (t j)) := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
          _ = _ := by ring

/-- A nonzero finite coefficient packet has a nonzero surviving Gamma-Jacobi tail coordinate.
The consecutive degrees starting at three form a diagonally weighted Vandermonde system. -/
theorem exists_gammaConductorJacobiTail_sum_ne_zero
    {n : ℕ} (t c : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) (hc : c ≠ 0) :
    ∃ k : Fin n,
      ∑ i, c i * gammaConductorJacobiFeature ((k : ℕ) + 3) (t i) ≠ 0 := by
  let μ : Fin n → ℂ := fun i => (Real.tanh (t i) : ℂ)
  let d : Fin n → ℂ := fun i =>
    (c i * semilocalArchimedeanCharacteristic (t i) * Real.tanh (t i) ^ 3 : ℝ)
  have hμ : Function.Injective μ := by
    intro i j hij
    apply hinj
    apply Real.tanh_injective
    exact Complex.ofReal_injective hij
  have hd : d ≠ 0 := by
    intro hd
    apply hc
    funext i
    have hi := congrFun hd i
    have hireal :
        c i * semilocalArchimedeanCharacteristic (t i) *
          Real.tanh (t i) ^ 3 = 0 := by
      exact Complex.ofReal_eq_zero.mp (by simpa [d] using hi)
    have hchar : semilocalArchimedeanCharacteristic (t i) ≠ 0 :=
      (semilocalArchimedeanCharacteristic_pos (t i)).ne'
    have htanh : Real.tanh (t i) ^ 3 ≠ 0 := by
      apply pow_ne_zero
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_ne_zero
        ((Real.sinh_pos_iff).2 (ht i)).ne'
        (Real.cosh_pos (t i)).ne'
    exact (mul_eq_zero.mp hireal).resolve_right htanh |>
      (mul_eq_zero.mp ·) |>.resolve_right hchar
  obtain ⟨k, hk⟩ :=
    GaloisForLFunctions.vandermonde_initial_moment_nonzero_of_nonzero_coeff hμ hd
  have hreal :
      ∑ i,
        c i * semilocalArchimedeanCharacteristic (t i) *
          Real.tanh (t i) ^ 3 * Real.tanh (t i) ^ (k : ℕ) ≠ 0 := by
    intro hzero
    apply hk
    calc
      ∑ i, d i * μ i ^ (k : ℕ) =
          ((∑ i,
            c i * semilocalArchimedeanCharacteristic (t i) *
              Real.tanh (t i) ^ 3 * Real.tanh (t i) ^ (k : ℕ) : ℝ) : ℂ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro i _
        dsimp [d, μ]
        push_cast
        ring
      _ = 0 := by rw [hzero]; norm_num
  refine ⟨k, ?_⟩
  rw [show
      (∑ i, c i *
        gammaConductorJacobiFeature ((k : ℕ) + 3) (t i)) =
        semilocalArchimedeanJacobiNormalization ((k : ℕ) + 3) *
          ∑ i,
            c i * semilocalArchimedeanCharacteristic (t i) *
              Real.tanh (t i) ^ 3 * Real.tanh (t i) ^ (k : ℕ) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      unfold gammaConductorJacobiFeature
      rw [pow_add]
      ring]
  exact mul_ne_zero
    (semilocalArchimedeanJacobiNormalization_pos ((k : ℕ) + 3)).ne'
    hreal

theorem summable_gammaConductorJacobiTail_sum_sq
    {n : ℕ} (t c : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    Summable (fun k : ℕ =>
      (∑ i, c i * gammaConductorJacobiFeature (k + 3) (t i)) ^ 2) := by
  let g : Fin n → Fin n → ℕ → ℝ := fun i j k =>
    c i * (gammaConductorJacobiFeature (k + 3) (t i) *
      gammaConductorJacobiFeature (k + 3) (t j)) * c j
  have hg (i j : Fin n) : Summable (g i j) := by
    have hbase :=
      (hasSum_semilocalArchimedeanJacobiNormalization_sq_mul_pow
        (show |Real.tanh (t i) * Real.tanh (t j)| < 1 by
          have hi0 : 0 < Real.tanh (t i) := by
            rw [Real.tanh_eq_sinh_div_cosh]
            exact div_pos ((Real.sinh_pos_iff).2 (ht i)) (Real.cosh_pos (t i))
          have hj0 : 0 < Real.tanh (t j) := by
            rw [Real.tanh_eq_sinh_div_cosh]
            exact div_pos ((Real.sinh_pos_iff).2 (ht j)) (Real.cosh_pos (t j))
          rw [abs_of_pos (mul_pos hi0 hj0)]
          calc
            Real.tanh (t i) * Real.tanh (t j) < Real.tanh (t i) * 1 :=
              mul_lt_mul_of_pos_left (Real.tanh_lt_one (t j)) hi0
            _ < 1 := by simpa using Real.tanh_lt_one (t i))).summable
    have htail := hbase.comp_injective
      (show Function.Injective (fun k : ℕ => k + 3) by
        intro k l h
        exact Nat.add_right_cancel h)
    have hscaled := htail.mul_left
      (c i * c j * semilocalArchimedeanCharacteristic (t i) *
        semilocalArchimedeanCharacteristic (t j))
    convert! hscaled using 1
    funext k
    dsimp [g]
    rw [gammaConductorJacobiFeature_mul_eq]
    ring
  have hdouble : Summable (fun k => ∑ i, ∑ j, g i j k) :=
    summable_sum (s := Finset.univ) (fun i _ =>
      summable_sum (s := Finset.univ) (fun j _ => hg i j))
  convert hdouble using 1
  funext k
  dsimp [g]
  calc
    (∑ i, c i * gammaConductorJacobiFeature (k + 3) (t i)) ^ 2 =
        (∑ i, c i * gammaConductorJacobiFeature (k + 3) (t i)) *
          (∑ j, c j * gammaConductorJacobiFeature (k + 3) (t j)) := by ring
    _ = ∑ i, ∑ j,
        c i * (gammaConductorJacobiFeature (k + 3) (t i) *
          gammaConductorJacobiFeature (k + 3) (t j)) * c j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- **Strict Gamma Schur faithfulness.**  The mean-and-conductor projected Gamma covariance has a
strictly positive quadratic form on every nonzero finite packet of distinct positive
frequencies. -/
theorem gammaConductorModeSchurResidual_quadratic_pos
    {n : ℕ} (t c : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) (hc : c ≠ 0) :
    0 < ∑ i, ∑ j,
      c i * gammaConductorModeSchurResidual (t i) (t j) * c j := by
  obtain ⟨k, hk⟩ :=
    exists_gammaConductorJacobiTail_sum_ne_zero t c ht hinj hc
  have htail :
      0 < ∑' m : ℕ,
        (∑ i, c i * gammaConductorJacobiFeature (m + 3) (t i)) ^ 2 := by
    exact (summable_gammaConductorJacobiTail_sum_sq t c ht).tsum_pos
      (fun m => sq_nonneg _) (k : ℕ) (sq_pos_of_ne_zero hk)
  rw [gammaConductorModeSchurResidual_quadratic_eq t c ht]
  nlinarith [sq_nonneg (∑ i, c i * gammaConductorJacobiFeature 1 (t i))]

theorem gammaConductorModeSchurResidual_comm
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    gammaConductorModeSchurResidual t u =
      gammaConductorModeSchurResidual u t := by
  rw [gammaConductorModeSchurResidual_eq_jacobi_one_add_tsum ht hu,
    gammaConductorModeSchurResidual_eq_jacobi_one_add_tsum hu ht]
  congr 1
  · ring
  · apply tsum_congr
    intro k
    ring

/-- Matrix form of strict Gamma Schur faithfulness. -/
theorem gammaConductorModeSchurResidual_matrix_posDef
    {n : ℕ} (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (hinj : Function.Injective t) :
    Matrix.PosDef
      (fun i j : Fin n => gammaConductorModeSchurResidual (t i) (t j)) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact gammaConductorModeSchurResidual_comm (ht j) (ht i)
  · intro c hc
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm] using
      gammaConductorModeSchurResidual_quadratic_pos t c ht hinj hc

end RHTower
