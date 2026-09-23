import GaloisForLFunctions.HTGeometry.ModularCubicProjectionTransgression
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Two-site modular holonomy escape

The retained block of a two-site source-frame modular commutator is the identity plus the
normalized Gram capacity multiplying the relative frame mismatch. For cubic-Cauchy source
columns that capacity is amplitude-free and singular exactly at rate collision.
-/

open Complex Matrix
open scoped Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev TwoSiteChannelIndex := Fin 2 × Fin 2

/-- Two completion-channel blocks over two source sites. -/
def twoSiteBlockDiagonal {K : Type*} [Zero K] [DecidableEq (Fin 2)]
    (P Q : Matrix (Fin 2) (Fin 2) K) :
    Matrix TwoSiteChannelIndex TwoSiteChannelIndex K :=
  fun i j => if _h : i.1 = j.1 then if i.1 = 0 then P i.2 j.2 else Q i.2 j.2 else 0

/-- Symmetric scalar source density, acting identically on the completion channels. -/
def twoSiteScalarDensity {K : Type*} [CommRing K]
    (d g e : K) : Matrix TwoSiteChannelIndex TwoSiteChannelIndex K :=
  modularTwoBlockDensity d g g e ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K)

/-- Explicit inverse of the symmetric scalar source density on both completion channels. -/
def twoSiteScalarDensityInv {K : Type*} [Field K]
    (d g e : K) : Matrix TwoSiteChannelIndex TwoSiteChannelIndex K :=
  modularTwoBlockDensityInv d g g e ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K)

/-- Exact retained block of the two-site source-frame modular product. -/
theorem twoSite_modularHolonomy_retained_block
    {K : Type*} [Field K]
    (d g e : K) (hdet : d * e - g ^ (2 : ℕ) ≠ 0)
    (P Q Pi Qi : Matrix (Fin 2) (Fin 2) K)
    (hPPi : P * Pi = 1) (r s : Fin 2) :
    (twoSiteScalarDensityInv d g e * twoSiteBlockDiagonal P Q *
        twoSiteScalarDensity d g e * twoSiteBlockDiagonal Pi Qi)
        ((0, r) : TwoSiteChannelIndex) ((0, s) : TwoSiteChannelIndex) =
      ((d * e) • (1 : Matrix (Fin 2) (Fin 2) K) - g ^ (2 : ℕ) • (Q * Pi)) r s /
        (d * e - g ^ (2 : ℕ)) := by
  have hPPi_rs := congrArg (fun M => M r s) hPPi
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hPPi_rs
  have hdet' : e * d - g * g ≠ 0 := by
    simpa [pow_two, mul_comm] using hdet
  fin_cases r <;> fin_cases s <;>
    simp [twoSiteScalarDensityInv, twoSiteScalarDensity, twoSiteBlockDiagonal,
      modularTwoBlockDensityInv, modularTwoBlockDensity, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two] at hPPi_rs ⊢ <;>
    ring_nf at hPPi_rs ⊢ <;>
    linear_combination (e * d * (e * d - g ^ (2 : ℕ))⁻¹) * hPPi_rs

/-- The retained block is identity plus Gram capacity times relative frame mismatch. -/
theorem twoSite_modularHolonomy_retained_block_eq_one_add
    {K : Type*} [Field K]
    (d g e : K) (hdet : d * e - g ^ (2 : ℕ) ≠ 0)
    (P Q Pi Qi : Matrix (Fin 2) (Fin 2) K)
    (hPPi : P * Pi = 1) (r s : Fin 2) :
    (twoSiteScalarDensityInv d g e * twoSiteBlockDiagonal P Q *
        twoSiteScalarDensity d g e * twoSiteBlockDiagonal Pi Qi)
        ((0, r) : TwoSiteChannelIndex) ((0, s) : TwoSiteChannelIndex) =
      ((1 : Matrix (Fin 2) (Fin 2) K) +
        (g ^ (2 : ℕ) / (d * e - g ^ (2 : ℕ))) •
          ((1 : Matrix (Fin 2) (Fin 2) K) - Q * Pi)) r s := by
  rw [twoSite_modularHolonomy_retained_block d g e hdet P Q Pi Qi hPPi r s]
  fin_cases r <;> fin_cases s <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp [hdet] <;>
    ring

/-- Difference-of-cubes factorization of cubic-Cauchy loss of correlation. -/
theorem cubicCauchyDenominator_factor (x y : ℝ) :
    (x + y) ^ (6 : ℕ) - 64 * x ^ (3 : ℕ) * y ^ (3 : ℕ) =
      (x - y) ^ (2 : ℕ) *
        ((x + y) ^ (4 : ℕ) + 4 * x * y * (x + y) ^ (2 : ℕ) + 16 * x ^ (2 : ℕ) * y ^ (2 : ℕ)) := by
  ring

theorem cubicCauchyDenominator_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    0 < (x + y) ^ (6 : ℕ) - 64 * x ^ (3 : ℕ) * y ^ (3 : ℕ) := by
  rw [cubicCauchyDenominator_factor]
  have hdiff : 0 < (x - y) ^ (2 : ℕ) := sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)
  have hsum : 0 < x + y := by positivity
  have hQ : 0 < (x + y) ^ (4 : ℕ) + 4 * x * y * (x + y) ^ (2 : ℕ) + 16 * x ^ (2 : ℕ) * y ^ (2 : ℕ) := by
    positivity
  positivity

/-- Amplitudes cancel exactly from normalized cubic-Cauchy Gram capacity. -/
theorem cubicCauchyGramCapacity_eq
    {A B x y : ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    let d := A ^ (2 : ℕ) * 2 / (2 * x) ^ (3 : ℕ)
    let e := B ^ (2 : ℕ) * 2 / (2 * y) ^ (3 : ℕ)
    let g := A * B * 2 / (x + y) ^ (3 : ℕ)
    g ^ (2 : ℕ) / (d * e - g ^ (2 : ℕ)) =
      64 * x ^ (3 : ℕ) * y ^ (3 : ℕ) /
        ((x + y) ^ (6 : ℕ) - 64 * x ^ (3 : ℕ) * y ^ (3 : ℕ)) := by
  dsimp
  have hx0 : x ≠ 0 := hx.ne'
  have hy0 : y ≠ 0 := hy.ne'
  have hsum0 : x + y ≠ 0 := (add_pos hx hy).ne'
  have hden0 : (x + y) ^ (6 : ℕ) - 64 * x ^ (3 : ℕ) * y ^ (3 : ℕ) ≠ 0 :=
    (cubicCauchyDenominator_pos hx hy hxy).ne'
  field_simp [hA, hB, hx0, hy0, hsum0, hden0]
  ring

/-- Cubic-Cauchy capacity in relative rate-displacement coordinates. -/
def cubicCauchyRelativeCapacity (u : ℝ) : ℝ :=
  (1 - u ^ (2 : ℕ)) ^ (3 : ℕ) / (1 - (1 - u ^ (2 : ℕ)) ^ (3 : ℕ))

/-- Quantitative escape of cubic-Cauchy capacity near a rate collision. -/
theorem cubicCauchyRelativeCapacity_gt
    {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (husmall : u < 1 / (8 * (M + 1))) :
    M < cubicCauchyRelativeCapacity u := by
  have hM1 : 1 ≤ M + 1 := by linarith
  have hdenM : 0 < 8 * (M + 1) := by positivity
  have hscaled : u * (8 * (M + 1)) < 1 :=
    (lt_div_iff₀ hdenM).mp (by simpa using husmall)
  have hu_lt : u < 1 := by nlinarith
  have hu2pos : 0 < u ^ (2 : ℕ) := sq_pos_of_pos hu
  have hu2lt : u ^ (2 : ℕ) < 1 := by nlinarith
  have hbasepos : 0 < 1 - u ^ (2 : ℕ) := by linarith
  have hbaselt : 1 - u ^ (2 : ℕ) < 1 := by linarith
  have hdenpos : 0 < 1 - (1 - u ^ (2 : ℕ)) ^ (3 : ℕ) := by
    nlinarith [mul_self_lt_mul_self (by linarith : 0 ≤ 1 - u ^ (2 : ℕ)) hbaselt,
      mul_pos hbasepos hbasepos]
  have hnum : 1 / 2 < (1 - u ^ (2 : ℕ)) ^ (3 : ℕ) := by
    have hu_eighth : u < 1 / 8 := by nlinarith
    nlinarith [sq_nonneg (u ^ (2 : ℕ)), sq_nonneg (1 - u ^ (2 : ℕ))]
  have hden_le : 1 - (1 - u ^ (2 : ℕ)) ^ (3 : ℕ) ≤ 3 * u ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (u ^ (2 : ℕ)), mul_nonneg hu2pos.le (by nlinarith : 0 ≤ 3 - u ^ (2 : ℕ))]
  have hMu : 6 * M * u ^ (2 : ℕ) < 1 := by
    have hscaled0 : 0 ≤ u * (8 * (M + 1)) := by positivity
    have hsquare : (u * (8 * (M + 1))) ^ (2 : ℕ) < 1 := by
      nlinarith [mul_self_lt_mul_self hscaled0 hscaled]
    nlinarith [sq_nonneg M]
  have hMfrac : M < (1 / 2) / (3 * u ^ (2 : ℕ)) := by
    rw [lt_div_iff₀ (by positivity : 0 < 3 * u ^ (2 : ℕ))]
    nlinarith
  rw [cubicCauchyRelativeCapacity]
  refine lt_of_lt_of_le hMfrac ?_
  exact div_le_div₀ (by positivity) hnum.le hdenpos hden_le

theorem cubicCauchyRelativeCapacity_abs_sub_div_add_eq
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    cubicCauchyRelativeCapacity (|x - y| / (x + y)) =
      64 * x ^ (3 : ℕ) * y ^ (3 : ℕ) /
        ((x + y) ^ (6 : ℕ) - 64 * x ^ (3 : ℕ) * y ^ (3 : ℕ)) := by
  have hsum0 : x + y ≠ 0 := (add_pos hx hy).ne'
  have hden0 : (x + y) ^ (6 : ℕ) - 64 * x ^ (3 : ℕ) * y ^ (3 : ℕ) ≠ 0 :=
    (cubicCauchyDenominator_pos hx hy hxy).ne'
  rw [cubicCauchyRelativeCapacity, div_pow, sq_abs]
  field_simp [hsum0, hden0]
  ring

end

end GaloisForLFunctions.HTGeometry
