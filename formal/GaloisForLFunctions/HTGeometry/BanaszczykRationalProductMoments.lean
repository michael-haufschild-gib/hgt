import GaloisForLFunctions.HTGeometry.BanaszczykRationalDensity
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product moments for the vector-balancing rational density

The tangent variables in Lemma 2.4 of Guo--Fang--Lu are independent with
density `2 / (π (1 + t²)²)`.  This file verifies the finite product law,
computes its covariance exactly, and closes the paper's elementary
Cauchy--Schwarz fallback

`E |∑ᵢ uᵢ Tᵢ| ≤ sqrt (∑ᵢ uᵢ²)`.

The sharper `sqrt (2 / π)` factor uses the paper's Gaussian--chi-square
mixture and is deliberately separated from this unconditional moment layer.
-/

noncomputable section

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

def rationalProductDensity (d : ℕ) (t : Fin d → ℝ) : ℝ :=
  ∏ i, banaszczykRationalDensity (t i)

def rationalProductVolume (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => (volume : Measure ℝ)

theorem rationalProductDensity_nonneg (d : ℕ) (t : Fin d → ℝ) :
    0 ≤ rationalProductDensity d t := by
  unfold rationalProductDensity
  exact Finset.prod_nonneg fun i _ => banaszczykRationalDensity_nonneg (t i)

theorem continuous_rationalProductDensity (d : ℕ) :
    Continuous (rationalProductDensity d) := by
  unfold rationalProductDensity
  exact continuous_finsetProd _ fun i _ =>
    continuous_banaszczykRationalDensity.comp (continuous_apply i)

theorem integrable_rationalProductDensity (d : ℕ) :
    Integrable (rationalProductDensity d) (rationalProductVolume d) := by
  unfold rationalProductDensity rationalProductVolume
  exact Integrable.fintype_prod fun _ => integrable_banaszczykRationalDensity

@[simp]
theorem integral_rationalProductDensity (d : ℕ) :
    ∫ t, rationalProductDensity d t ∂(rationalProductVolume d) = 1 := by
  unfold rationalProductDensity rationalProductVolume
  rw [integral_fintype_prod_eq_pow, integral_banaszczykRationalDensity]
  simp

private def rationalCrossFactor {d : ℕ} (i j k : Fin d) (x : ℝ) : ℝ :=
  (if k = i then x else 1) * (if k = j then x else 1) *
    banaszczykRationalDensity x

private theorem integrable_rationalCrossFactor {d : ℕ} (i j k : Fin d) :
    Integrable (rationalCrossFactor i j k) := by
  unfold rationalCrossFactor
  by_cases hki : k = i
  · subst i
    by_cases hkj : k = j
    · subst j
      simpa [pow_two] using integrable_sq_mul_banaszczykRationalDensity
    · simpa [hkj] using integrable_id_mul_banaszczykRationalDensity
  · by_cases hkj : k = j
    · subst j
      simpa [hki] using integrable_id_mul_banaszczykRationalDensity
    · simpa [hki, hkj] using integrable_banaszczykRationalDensity

private theorem cross_mul_density_eq_prod {d : ℕ} (i j : Fin d) (t : Fin d → ℝ) :
    t i * t j * rationalProductDensity d t =
      ∏ k, rationalCrossFactor i j k (t k) := by
  unfold rationalProductDensity rationalCrossFactor
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

theorem integrable_cross_mul_rationalProductDensity {d : ℕ} (i j : Fin d) :
    Integrable (fun t : Fin d → ℝ => t i * t j * rationalProductDensity d t)
      (rationalProductVolume d) := by
  have hprod : Integrable (fun t : Fin d → ℝ => ∏ k, rationalCrossFactor i j k (t k))
      (rationalProductVolume d) := by
    unfold rationalProductVolume
    exact Integrable.fintype_prod fun k => integrable_rationalCrossFactor i j k
  apply hprod.congr
  exact Filter.Eventually.of_forall fun t => (cross_mul_density_eq_prod i j t).symm

private theorem integral_rationalCrossFactor_same {d : ℕ} (i k : Fin d) :
    ∫ x : ℝ, rationalCrossFactor i i k x = 1 := by
  by_cases hki : k = i
  · subst i
    simpa [rationalCrossFactor, pow_two] using integral_sq_mul_banaszczykRationalDensity
  · simp [rationalCrossFactor, hki]

private theorem integral_rationalCrossFactor_left {d : ℕ} {i j : Fin d} (hij : i ≠ j) :
    ∫ x : ℝ, rationalCrossFactor i j i x = 0 := by
  simp [rationalCrossFactor, hij]

/-- Exact covariance matrix of the rational product density: the identity. -/
@[simp]
theorem integral_cross_mul_rationalProductDensity {d : ℕ} (i j : Fin d) :
    ∫ t : Fin d → ℝ, t i * t j * rationalProductDensity d t
        ∂(rationalProductVolume d) = if i = j then 1 else 0 := by
  rw [show (fun t : Fin d → ℝ => t i * t j * rationalProductDensity d t) =
      fun t => ∏ k, rationalCrossFactor i j k (t k) by
    funext t
    exact cross_mul_density_eq_prod i j t]
  unfold rationalProductVolume
  rw [integral_fintype_prod_eq_prod]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact Finset.prod_eq_one fun k _ => integral_rationalCrossFactor_same i k
  · rw [if_neg hij]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact integral_rationalCrossFactor_left hij

def rationalLinearForm {d : ℕ} (u t : Fin d → ℝ) : ℝ :=
  ∑ i, u i * t i

private theorem rationalLinearForm_sq_expand {d : ℕ} (u t : Fin d → ℝ) :
    rationalLinearForm u t ^ 2 =
      ∑ i, ∑ j, (u i * u j) * (t i * t j) := by
  unfold rationalLinearForm
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrable_weighted_rationalLinearForm_sq {d : ℕ} (u : Fin d → ℝ) :
    Integrable (fun t : Fin d → ℝ =>
      rationalProductDensity d t * rationalLinearForm u t ^ 2)
      (rationalProductVolume d) := by
  have hterm : ∀ i j : Fin d, Integrable
      (fun t : Fin d → ℝ => (u i * u j) *
        (t i * t j * rationalProductDensity d t)) (rationalProductVolume d) :=
    fun i j => (integrable_cross_mul_rationalProductDensity i j).const_mul _
  have hsum : Integrable
      (fun t : Fin d → ℝ => ∑ i, ∑ j, (u i * u j) *
        (t i * t j * rationalProductDensity d t)) (rationalProductVolume d) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hterm i j
  have hfun : (fun t : Fin d → ℝ =>
      rationalProductDensity d t * rationalLinearForm u t ^ 2) =
      fun t => ∑ i, ∑ j, (u i * u j) *
        (t i * t j * rationalProductDensity d t) := by
    funext t
    rw [rationalLinearForm_sq_expand]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun]
  exact hsum

/-- Exact variance of every linear form under the rational product density. -/
@[simp]
theorem integral_weighted_rationalLinearForm_sq {d : ℕ} (u : Fin d → ℝ) :
    ∫ t : Fin d → ℝ, rationalProductDensity d t * rationalLinearForm u t ^ 2
        ∂(rationalProductVolume d) = ∑ i, u i ^ 2 := by
  have hterm : ∀ i j : Fin d, Integrable
      (fun t : Fin d → ℝ => (u i * u j) *
        (t i * t j * rationalProductDensity d t)) (rationalProductVolume d) :=
    fun i j => (integrable_cross_mul_rationalProductDensity i j).const_mul _
  have hfun : (fun t : Fin d → ℝ =>
      rationalProductDensity d t * rationalLinearForm u t ^ 2) =
      fun t => ∑ i, ∑ j, (u i * u j) *
        (t i * t j * rationalProductDensity d t) := by
    funext t
    rw [rationalLinearForm_sq_expand]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfun, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hterm i j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hterm i j)]
  rw [show (∑ j, ∫ t : Fin d → ℝ,
      (u i * u j) * (t i * t j * rationalProductDensity d t)
        ∂(rationalProductVolume d)) = u i ^ 2 by
    rw [show (fun j => ∫ t : Fin d → ℝ,
        (u i * u j) * (t i * t j * rationalProductDensity d t)
          ∂(rationalProductVolume d)) = fun j => if i = j then u i ^ 2 else 0 by
      funext j
      rw [integral_const_mul, integral_cross_mul_rationalProductDensity]
      by_cases hij : i = j
      · subst j
        simp
        ring
      · simp [hij]]
    simp]

/-- Cauchy--Schwarz fallback from the paper: without the Gaussian mixture,
the absolute first moment of a rational linear form is bounded by its
Euclidean coefficient norm. -/
theorem integral_abs_rationalLinearForm_le_sqrt {d : ℕ} (u : Fin d → ℝ) :
    (∫ t : Fin d → ℝ,
      rationalProductDensity d t * |rationalLinearForm u t|
        ∂(rationalProductVolume d)) ≤ Real.sqrt (∑ i, u i ^ 2) := by
  have hcs := sq_integral_weighted_le
    (μ := rationalProductVolume d)
    (w := rationalProductDensity d)
    (g := fun t => |rationalLinearForm u t|)
    (rationalProductDensity_nonneg d)
    (continuous_rationalProductDensity d).aestronglyMeasurable
    (by
      unfold rationalLinearForm
      exact (continuous_finsetSum _ fun i _ =>
        continuous_const.mul (continuous_apply i)).abs.aestronglyMeasurable)
    (integrable_rationalProductDensity d)
    (by
      convert integrable_weighted_rationalLinearForm_sq u using 1
      funext t
      rw [sq_abs])
  have habsfun : (fun t : Fin d → ℝ =>
      rationalProductDensity d t * |rationalLinearForm u t| ^ 2) =
      fun t => rationalProductDensity d t * rationalLinearForm u t ^ 2 := by
    funext t
    rw [sq_abs]
  rw [integral_rationalProductDensity, habsfun,
    integral_weighted_rationalLinearForm_sq, one_mul] at hcs
  exact Real.le_sqrt_of_sq_le hcs

end GaloisForLFunctions.HTGeometry
