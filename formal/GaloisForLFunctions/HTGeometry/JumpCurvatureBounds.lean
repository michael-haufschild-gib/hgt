import GaloisForLFunctions.HTGeometry.JumpBochner
import Mathlib.Tactic.Linarith

/-!
# Degree bounds for variable-rate jump curvature

Completing the two-step square expresses iterated energy as a nonnegative square
sum, a precise degree defect and half the squared generator. Nonnegative rates
with total rate at most `D` satisfy `Γ₂ ≥ (Lf)²/2 − DΓ`, hence `Γ₂ ≥ −DΓ`.
No commutation or nonnegative-curvature hypothesis is needed.
-/

noncomputable section
open scoped BigOperators
namespace HTGeometry.JumpBochner
variable {ι X : Type*}

def degree (s : Finset ι) (rate : ι → X → ℝ) (x : X) : ℝ := ∑ i ∈ s, rate i x

theorem gammaTwo_eq_degree_defect (s : Finset ι) (rate : ι → X → ℝ)
    (shift : ι → X → X) (f : X → ℝ) (x : X) :
    gammaTwo s rate shift f x =
      (∑ i ∈ s, ∑ j ∈ s, rate i x * rate j (shift i x) *
        (difference shift j f (shift i x) - difference shift i f x)^2) / 4 -
    (∑ i ∈ s, rate i x * (degree s rate (shift i x) + degree s rate x) *
        (difference shift i f x)^2) / 4 + (generator s rate shift f x)^2 / 2 := by
  have hdiag : (∑ i ∈ s, ∑ j ∈ s, rate i x * rate j x * (difference shift j f x)^2) =
      ∑ i ∈ s, ∑ j ∈ s, rate i x * rate j x * (difference shift i f x)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hpair := gammaTwo_eq_pairSum s rate shift f x
  simp only [Finset.sum_sub_distrib] at hpair
  rw [Finset.sum_comm] at hpair
  rw [hpair]
  unfold degree generator
  simp only [pow_two, mul_sub, sub_mul, mul_add, add_mul, Finset.sum_div,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring_nf
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul _ _ (1/4 : ℝ),
    ← Finset.sum_mul _ _ (-1/4 : ℝ), ← Finset.sum_mul _ _ (1/2 : ℝ),
    ← Finset.sum_mul _ _ (-1/2 : ℝ)]
  simp only [mul_assoc, mul_left_comm, mul_comm] at hdiag ⊢
  rw [hdiag]
  ring

theorem generator_sq_sub_degree_mul_energy_le_gammaTwo
    (s : Finset ι) (rate : ι → X → ℝ) (shift : ι → X → X)
    (hr : ∀ i ∈ s, ∀ y, 0 ≤ rate i y) (D : ℝ) (hD : ∀ y, degree s rate y ≤ D)
    (f : X → ℝ) (x : X) :
    (generator s rate shift f x)^2 / 2 - D * energyDensity s rate shift f f x ≤
      gammaTwo s rate shift f x := by
  have hs : 0 ≤ (∑ i ∈ s, ∑ j ∈ s, rate i x * rate j (shift i x) *
      (difference shift j f (shift i x) - difference shift i f x)^2) / 4 := by
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
      mul_nonneg (mul_nonneg (hr i hi x) (hr j hj (shift i x))) (sq_nonneg _)
  have hb : (∑ i ∈ s, rate i x * (degree s rate (shift i x) + degree s rate x) *
      (difference shift i f x)^2) ≤ 2 * D * ∑ i ∈ s, rate i x * (difference shift i f x)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_right (add_le_add (hD (shift i x)) (hD x))
      (mul_nonneg (hr i hi x) (sq_nonneg (difference shift i f x)))
    nlinarith
  have he : energyDensity s rate shift f f x =
      (∑ i ∈ s, rate i x * (difference shift i f x)^2) / 2 := by
    unfold energyDensity
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [gammaTwo_eq_degree_defect, he]
  linarith

theorem gammaTwo_ge_neg_degree_mul_energy
    (s : Finset ι) (rate : ι → X → ℝ) (shift : ι → X → X)
    (hr : ∀ i ∈ s, ∀ y, 0 ≤ rate i y) (D : ℝ) (hD : ∀ y, degree s rate y ≤ D)
    (f : X → ℝ) (x : X) :
    -D * energyDensity s rate shift f f x ≤ gammaTwo s rate shift f x := by
  have h := generator_sq_sub_degree_mul_energy_le_gammaTwo s rate shift hr D hD f x
  nlinarith [sq_nonneg (generator s rate shift f x)]


end HTGeometry.JumpBochner
