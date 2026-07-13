import Mathlib
import GaloisForLFunctions.HTGeometry.ParaorthogonalBlaschkeRoot

/-!
# Finite Blaschke products: boundary modulus and disk analyticity

A finite Blaschke product `∏ᵢ (z - aᵢ)/(1 - \bar{aᵢ} z)` with parameters `aᵢ` in the open unit
disk is holomorphic on the closed disk and has modulus `1` on the unit circle.  These are the
inner-factor properties used in the Riesz factorization `H¹ = H² · H²` underlying the F.&M. Riesz
theorem.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- The Blaschke denominator `1 - \bar a z` is nonzero on the closed unit disk when `‖a‖ < 1`. -/
theorem blaschkeFactor_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - star a * z ≠ 0 := by
  intro h
  have h1 : star a * z = 1 := by linear_combination -h
  have h2 := congrArg norm h1
  rw [norm_mul, norm_star, norm_one] at h2
  nlinarith [norm_nonneg a, norm_nonneg z,
    mul_le_mul ha.le hz (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 1)]

/-- A single Blaschke factor has modulus `1` on the unit circle. -/
theorem norm_blaschkeFactor_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖(z - a) / (1 - star a * z)‖ = 1 := by
  have hden : 1 - star a * z ≠ 0 := blaschkeFactor_den_ne_zero ha hz.le
  rw [norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)]
  have hz1 : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz]; norm_num
  have hsq : Complex.normSq (z - a) = Complex.normSq (1 - star a * z) := by
    have hb := blaschke_normSq_sub a z
    rw [hz1] at hb; linarith
  have : ‖z - a‖ ^ 2 = ‖1 - star a * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, hsq]
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - star a * z)]

/-- **A finite Blaschke product has boundary modulus one.**  With all parameters in the open disk,
the product has modulus `1` on the unit circle. -/
theorem norm_finBlaschke_eq_one {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∏ i, ((z - a i) / (1 - star (a i) * z))‖ = 1 := by
  rw [norm_prod, Finset.prod_eq_one]
  intro i _
  exact norm_blaschkeFactor_eq_one (ha i) hz

/-- **A finite Blaschke product is holomorphic on the closed disk.** -/
theorem differentiableOn_finBlaschke {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ < 1) :
    DifferentiableOn ℂ (fun z => ∏ i, ((z - a i) / (1 - star (a i) * z)))
      (Metric.closedBall 0 1) := by
  refine DifferentiableOn.fun_finsetProd (fun i _ => ?_)
  refine DifferentiableOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  exact blaschkeFactor_den_ne_zero (ha i)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

/-- On the closed disk, a Blaschke factor vanishes exactly at its parameter. -/
theorem blaschkeFactor_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    (z - a) / (1 - star a * z) = 0 ↔ z = a := by
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linear_combination h
    · exact absurd h (blaschkeFactor_den_ne_zero ha hz)
  · intro h; left; rw [h]; ring

/-- A finite Blaschke product vanishes on the closed disk exactly at its parameters. -/
theorem finBlaschke_eq_zero_iff {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (∏ i, ((z - a i) / (1 - star (a i) * z))) = 0 ↔ ∃ i, z = a i := by
  rw [Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, (blaschkeFactor_eq_zero_iff (ha i) hz).mp hi⟩
  · rintro ⟨i, hi⟩; exact ⟨i, (blaschkeFactor_eq_zero_iff (ha i) hz).mpr hi⟩

/-- A Blaschke factor maps the closed disk into itself (Schwarz–Pick bound). -/
theorem norm_blaschkeFactor_le_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖(z - a) / (1 - star a * z)‖ ≤ 1 := by
  have hden : 1 - star a * z ≠ 0 := blaschkeFactor_den_ne_zero ha hz
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
  have hzsq : Complex.normSq z ≤ 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hasq : Complex.normSq a < 1 := by rw [← Complex.sq_norm]; nlinarith [norm_nonneg a]
  have hb := blaschke_normSq_sub a z
  have hle : Complex.normSq (z - a) ≤ Complex.normSq (1 - star a * z) := by nlinarith
  have h2 : ‖z - a‖ ^ 2 ≤ ‖1 - star a * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]; exact hle
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - star a * z)]

/-- **A finite Blaschke product maps the closed disk into itself.** -/
theorem norm_finBlaschke_le_one {n : ℕ} {a : Fin n → ℂ} (ha : ∀ i, ‖a i‖ < 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖∏ i, ((z - a i) / (1 - star (a i) * z))‖ ≤ 1 := by
  rw [norm_prod]
  calc ∏ i, ‖(z - a i) / (1 - star (a i) * z)‖ ≤ ∏ _i : Fin n, (1 : ℝ) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i _ => norm_blaschkeFactor_le_one (ha i) hz)
    _ = 1 := by simp

/-- A Blaschke product over an arbitrary finite index set has boundary modulus `1`. -/
theorem norm_finsetBlaschke_eq_one {ι : Type*} (s : Finset ι) {a : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∏ i ∈ s, ((z - a i) / (1 - star (a i) * z))‖ = 1 := by
  rw [norm_prod, Finset.prod_eq_one]
  intro i hi
  exact norm_blaschkeFactor_eq_one (ha i hi) hz

/-- A Blaschke product over an arbitrary finite index set maps the closed disk into itself. -/
theorem norm_finsetBlaschke_le_one {ι : Type*} (s : Finset ι) {a : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖∏ i ∈ s, ((z - a i) / (1 - star (a i) * z))‖ ≤ 1 := by
  rw [norm_prod]
  calc ∏ i ∈ s, ‖(z - a i) / (1 - star (a i) * z)‖ ≤ ∏ _i ∈ s, (1 : ℝ) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _)
          (fun i hi => norm_blaschkeFactor_le_one (ha i hi) hz)
    _ = 1 := by simp

/-- A Blaschke product over an arbitrary finite index set is holomorphic on the closed disk. -/
theorem differentiableOn_finsetBlaschke {ι : Type*} (s : Finset ι) {a : ι → ℂ}
    (ha : ∀ i ∈ s, ‖a i‖ < 1) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, ((z - a i) / (1 - star (a i) * z)))
      (Metric.closedBall 0 1) := by
  refine DifferentiableOn.fun_finsetProd (fun i hi => ?_)
  refine DifferentiableOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
  exact blaschkeFactor_den_ne_zero (ha i hi)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

end GaloisForLFunctions.HTGeometry
