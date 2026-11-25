import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Selection
import GaloisForLFunctions.RHTower.RouteEGibbsUniformCellComparison

/-! # Sharp total variation between two postselected Gibbs laws -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

variable {Ω : Type*}

def weight {Ω : Type*} (β : ℝ) (E : Ω → ℝ) (x : Ω) := Real.exp (-β*E x)

theorem weight_pos {Ω : Type*} (β : ℝ) (E : Ω → ℝ) (x : Ω) : 0 < weight β E x := Real.exp_pos _

/-- Square-root odds ratio for a log-likelihood oscillation η. -/
def halfRatio (η : ℝ) := Real.exp (η/2)

theorem halfRatio_sq (η : ℝ) : halfRatio η^2 = Real.exp η := by
  rw [halfRatio,sq,← Real.exp_add,add_halves]

theorem defect_eq (η : ℝ) : (halfRatio η-1)/(halfRatio η+1) = Real.tanh (η/4) := by
  have H := _root_.RHTower.routeE_two_expHalfRatio_eq_two_tanh_quarter η
  unfold halfRatio
  rw [mul_div_assoc] at H
  exact mul_left_cancel₀ (two_ne_zero : (2:ℝ) ≠ 0) H

theorem cross_le_iff (E : Ω → ℝ) (β γ η : ℝ) (x y : Ω) :
    weight β E x*weight γ E y ≤ halfRatio η^2*weight γ E x*weight β E y ↔ (γ-β)*(E x-E y) ≤ η := by
  simp only [weight,halfRatio_sq,← Real.exp_add,Real.exp_le_exp]
  constructor <;> intro h <;> linarith only [h]

theorem cross_eq_iff (E : Ω → ℝ) (β γ η : ℝ) (x y : Ω) :
    weight β E x*weight γ E y = halfRatio η^2*weight γ E x*weight β E y ↔ (γ-β)*(E x-E y) = η := by
  simp only [weight,halfRatio_sq,← Real.exp_add,Real.exp_injective.eq_iff]
  constructor <;> intro h <;> linarith only [h]

private theorem pair_bound [DecidableEq Ω] (E : Ω → ℝ) {U A : Finset Ω} (hA : A ⊆ U) (β γ D : ℝ)
    (hD : ∀ x ∈ U, ∀ y ∈ U, |E x-E y| ≤ D) :
    ∀ x ∈ A, ∀ y ∈ U \ A, weight β E x*weight γ E y ≤ halfRatio (|β-γ| * D)^2*weight γ E x*weight β E y := by
  intro x hx y hy
  apply (cross_le_iff E β γ _ x y).mpr
  calc _ ≤ |(γ-β)*(E x-E y)| := le_abs_self _
       _ = |β-γ| * |E x-E y| := by rw [abs_mul,abs_sub_comm γ β]
       _ ≤ _ := mul_le_mul_of_nonneg_left (hD x (hA hx) y (Finset.mem_sdiff.mp hy).1) (abs_nonneg _)

/-- The oscillation of the Hamiltonian bounds temperature discrimination after arbitrary selection. -/
theorem thermal_variation (E : Ω → ℝ) {U : Finset Ω} (hU : U.Nonempty) (β γ D : ℝ)
    (hD : ∀ x ∈ U, ∀ y ∈ U, |E x-E y| ≤ D) :
    variation (weight β E) (weight γ E) U ≤ Real.tanh (|β-γ| * D/4) := by
  classical
  obtain ⟨x,hx⟩ := hU
  have hd : 0 ≤ D := (abs_nonneg _).trans (hD x hx x hx)
  have hs (b g : ℝ) : 1 ≤ halfRatio (|b-g| * D) := Real.one_le_exp (div_nonneg (mul_nonneg (abs_nonneg _) hd) zero_le_two)
  apply variation_le
  intro A hA
  have bound (b g : ℝ) := (signed_bound (weight_pos b E) (weight_pos g E) ⟨x,hx⟩ hA (hs b g)
    (pair_bound E hA b g D hD)).trans_eq (defect_eq _)
  have hr := bound γ β
  rw [abs_sub_comm γ β] at hr
  exact abs_le.mpr ⟨by linarith only [hr],bound β γ⟩

/-- Exact maximizers require a balanced reference probability and saturation of every cross-pair. -/
theorem thermal_signed_equality [DecidableEq Ω] (E : Ω → ℝ) {U A : Finset Ω} (hU : U.Nonempty) (hA : A ⊆ U)
    (β γ D : ℝ) (hD : ∀ x ∈ U, ∀ y ∈ U, |E x-E y| ≤ D) (hη : 0 < |β-γ| * D) :
    share (weight β E) U A-share (weight γ E) U A = Real.tanh (|β-γ| * D/4) ↔
      (halfRatio (|β-γ| * D)+1)*share (weight γ E) U A = 1 ∧
      ∀ x ∈ A, ∀ y ∈ U \ A, (γ-β)*(E x-E y) = |β-γ| * D := by
  have hs : 1 < halfRatio (|β-γ| * D) := Real.one_lt_exp_iff.mpr (half_pos hη)
  rw [← defect_eq,signed_equality (weight_pos β E) (weight_pos γ E) hU hA hs (pair_bound E hA β γ D hD)]
  simp only [cross_eq_iff]

/-- Equality in total variation is witnessed by an oriented event. Taking the complement reverses its sign. -/
theorem thermal_variation_equality [DecidableEq Ω] (E : Ω → ℝ) {U : Finset Ω} (hU : U.Nonempty) (β γ D : ℝ)
    (hD : ∀ x ∈ U, ∀ y ∈ U, |E x-E y| ≤ D) (hη : 0 < |β-γ| * D) :
    variation (weight β E) (weight γ E) U = Real.tanh (|β-γ| * D/4) ↔
      ∃ A ⊆ U, (halfRatio (|β-γ| * D)+1)*share (weight γ E) U A = 1 ∧
        ∀ x ∈ A, ∀ y ∈ U \ A, (γ-β)*(E x-E y) = |β-γ| * D := by
  constructor
  · intro H
    obtain ⟨A,hA,he⟩ := Finset.exists_mem_eq_sup' U.powerset_nonempty
      (fun A => |share (weight β E) U A-share (weight γ E) U A|)
    change variation (weight β E) (weight γ E) U = _ at he
    have hv := he.symm.trans H
    have ha := Finset.mem_powerset.mp hA
    by_cases hh : 0 ≤ share (weight β E) U A-share (weight γ E) U A
    · rw [abs_of_nonneg hh] at hv
      exact ⟨A,ha,(thermal_signed_equality E hU ha β γ D hD hη).mp hv⟩
    · rw [abs_of_neg (lt_of_not_ge hh)] at hv
      refine ⟨U \ A,Finset.sdiff_subset,(thermal_signed_equality E hU Finset.sdiff_subset β γ D hD hη).mp ?_⟩
      rw [← one_sub_share (weight_pos β E) hU ha,← one_sub_share (weight_pos γ E) hU ha]
      linarith only [hv]
  · rintro ⟨A,hA,hr⟩
    have he := (thermal_signed_equality E hU hA β γ D hD hη).mpr hr
    exact le_antisymm (thermal_variation E hU β γ D hD) (he.ge.trans ((le_abs_self _).trans (event_le_variation _ _ hA)))

#print axioms thermal_variation
#print axioms thermal_signed_equality
#print axioms thermal_variation_equality

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
