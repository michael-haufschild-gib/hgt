import GaloisForLFunctions.RHTower.XiWardEdgeReChannelDeposit
import GaloisForLFunctions.RHTower.WardAnnulusCrossKernelGappedClusters

/-!
# The Ward family energy difference is the cross-kernel quadratic form

For a finite family of strict-right zero copies at a common depth, the quadratic Ward energy at an
Euler shift is an explicit double Lorentzian sum.  Subtracting the energies at two shifts produces
exactly the annulus cross kernel, so the mass, window, ceiling, deficit and gapped-cluster laws all
apply verbatim to the energy difference the programme actually uses.
-/

open MeasureTheory Real
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

private theorem integrable_lorentzHalf {x : ℝ} (hx : 0 < x) (β : ℝ) :
    Integrable (fun t : ℝ => x / (x ^ (2 : ℕ) + (t + β) ^ (2 : ℕ))) := by
  have h : (fun t : ℝ => x / (x ^ (2 : ℕ) + (t + β) ^ (2 : ℕ))) =
      fun t : ℝ => Real.pi * halfPlanePoisson x (t + β) := by
    funext t
    unfold halfPlanePoisson
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [h]
  exact ((integrable_halfPlanePoisson hx).comp_add_right β).const_mul _

private theorem lorentzHalf_le {x : ℝ} (hx : 0 < x) (β t : ℝ) :
    ‖x / (x ^ (2 : ℕ) + (t + β) ^ (2 : ℕ))‖ ≤ x⁻¹ := by
  have hden : (0 : ℝ) < x ^ (2 : ℕ) + (t + β) ^ (2 : ℕ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_eq_one_div,
    div_le_div_iff₀ hden hx]
  nlinarith [sq_nonneg (t + β)]

private theorem integrable_lorentzHalf_mul {x : ℝ} (hx : 0 < x) (β₁ β₂ : ℝ) :
    Integrable (fun t : ℝ =>
      (x / (x ^ (2 : ℕ) + (t + β₁) ^ (2 : ℕ))) * (x / (x ^ (2 : ℕ) + (t + β₂) ^ (2 : ℕ)))) := by
  have hcont : Continuous fun t : ℝ => x / (x ^ (2 : ℕ) + (t + β₁) ^ (2 : ℕ)) := by
    refine continuous_const.div (by fun_prop) fun t => ?_
    positivity
  exact (integrable_lorentzHalf hx β₂).bdd_mul (c := x⁻¹) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => lorentzHalf_le hx β₁ t)

/-- Quadratic Ward energy of a finite family of equal-width Lorentzian responses. -/
def wardFamilyEnergy {J : Type*} (F : Finset J) (m γ : J → ℝ) (x : ℝ) : ℝ :=
  ∫ t : ℝ, (∑ q ∈ F, m q * (x / (x ^ (2 : ℕ) + (t + γ q) ^ (2 : ℕ)))) ^ (2 : ℕ)

/-- The Ward family energy is the explicit double Lorentzian sum in the ordinate differences. -/
theorem wardFamilyEnergy_eq {J : Type*} (F : Finset J) (m γ : J → ℝ) {x : ℝ} (hx : 0 < x) :
    wardFamilyEnergy F m γ x =
      ∑ q ∈ F, ∑ q' ∈ F,
        m q * m q' * (2 * Real.pi * x / (4 * x ^ (2 : ℕ) + (γ q - γ q') ^ (2 : ℕ))) := by
  classical
  have hpt : ∀ t : ℝ,
      (∑ q ∈ F, m q * (x / (x ^ (2 : ℕ) + (t + γ q) ^ (2 : ℕ)))) ^ (2 : ℕ) =
        ∑ q ∈ F, ∑ q' ∈ F, m q * m q' *
          ((x / (x ^ (2 : ℕ) + (t + γ q) ^ (2 : ℕ))) *
            (x / (x ^ (2 : ℕ) + (t + γ q') ^ (2 : ℕ)))) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring
  unfold wardFamilyEnergy
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finsetSum _ (fun q _ =>
    MeasureTheory.integrable_finsetSum _ (fun q' _ =>
      ((integrable_lorentzHalf_mul hx (γ q) (γ q')).const_mul (m q * m q'))))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun q' _ =>
    ((integrable_lorentzHalf_mul hx (γ q) (γ q')).const_mul (m q * m q')))]
  refine Finset.sum_congr rfl fun q' _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_mul_lorentzianHalves hx (γ q) (γ q')]

/-- **Bridge.**  The Ward energy difference at two Euler shifts, for a family at common depth `a`,
is exactly the annulus cross-kernel quadratic form with widths `2h₀` and `2h₁` at advance `2a`. -/
theorem wardFamilyEnergy_sub_eq {J : Type*} (F : Finset J) (m γ : J → ℝ) {a h₀ h₁ : ℝ}
    (ha : 0 < a) (hh₀ : 0 < h₀) (hh₁ : 0 < h₁) :
    wardFamilyEnergy F m γ (h₀ + a) - wardFamilyEnergy F m γ (h₁ + a) =
      Real.pi / 2 * ∑ q ∈ F, ∑ q' ∈ F, m q * m q' *
        annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![2 * h₀, 2 * h₁] (2 * a) (γ q - γ q') := by
  rw [wardFamilyEnergy_eq F m γ (by linarith : (0 : ℝ) < h₀ + a),
    wardFamilyEnergy_eq F m γ (by linarith : (0 : ℝ) < h₁ + a),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q' _ => ?_
  simp only [annulusCrossKernel, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have d0 : (0 : ℝ) < 4 * (h₀ + a) ^ (2 : ℕ) + (γ q - γ q') ^ (2 : ℕ) := by positivity
  have d1 : (0 : ℝ) < 4 * (h₁ + a) ^ (2 : ℕ) + (γ q - γ q') ^ (2 : ℕ) := by positivity
  have e0 : (0 : ℝ) < (2 * a + 2 * h₀) ^ (2 : ℕ) + (γ q - γ q') ^ (2 : ℕ) := by positivity
  have e1 : (0 : ℝ) < (2 * a + 2 * h₁) ^ (2 : ℕ) + (γ q - γ q') ^ (2 : ℕ) := by positivity
  field_simp
  ring

/-- **Gapped count directly from the Ward energies.**  Unit multiplicities, common depth `a`, and a
gapped-cluster geometry below the threshold: the Ward energy difference pays half a quantum per
ordinate. -/
theorem wardFamilyEnergy_sub_ge_of_gapped {J : Type*} (F : Finset J) (γ : J → ℝ)
    {a h₀ h₁ ρ Δ : ℝ} (ha : 0 < a) (hh₀ : 0 < h₀) (hh₁ : 0 < h₁) (hΔ : 0 < Δ)
    (hnn : ∀ D ∈ Set.Icc (-ρ) ρ,
      0 ≤ annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![2 * h₀, 2 * h₁] (2 * a) D)
    (hdich : ∀ j ∈ F, ∀ k ∈ F, |γ j - γ k| ≤ ρ ∨ Δ ≤ |γ j - γ k|)
    (hsmall : 2 * (∑ i ∈ (Finset.univ : Finset (Fin 2)),
        2 * |(![(1 : ℝ), -1]) i| * (2 * a + (![2 * h₀, 2 * h₁]) i)) * (F.card : ℝ) ≤
      annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![2 * h₀, 2 * h₁] (2 * a) 0 * Δ ^ (2 : ℕ)) :
    Real.pi * (F.card : ℝ) *
        annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![2 * h₀, 2 * h₁] (2 * a) 0 / 4 ≤
      wardFamilyEnergy F (fun _ => 1) γ (h₀ + a) - wardFamilyEnergy F (fun _ => 1) γ (h₁ + a) := by
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < 2 * a + (![2 * h₀, 2 * h₁]) i := by
    intro i _
    fin_cases i
    · simpa using by linarith
    · simpa using by linarith
  have hgap := half_card_mul_quantum_le_of_gapped Finset.univ ![(1 : ℝ), -1] ![2 * h₀, 2 * h₁]
    F γ hb hΔ hnn hdich hsmall
  rw [wardFamilyEnergy_sub_eq F (fun _ => 1) γ ha hh₀ hh₁]
  simp only [one_mul]
  have hpi : 0 < Real.pi := Real.pi_pos
  nlinarith [hgap, hpi]

end

end RHTower
