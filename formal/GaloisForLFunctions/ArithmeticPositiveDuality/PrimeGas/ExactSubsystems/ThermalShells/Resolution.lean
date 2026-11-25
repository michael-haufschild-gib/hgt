import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Temperatures

/-! # Exact finite thermometry and the loss of temperature contrast at small energy resolution -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

open Filter Topology

variable {Ω : Type*}

theorem variation_nonneg (w z : Ω → ℝ) (U : Finset Ω) : 0 ≤ variation w z U :=
  (abs_nonneg _).trans (event_le_variation w z (Finset.empty_subset U))

/-- Ratios of two selected single-state probabilities cancel the full partition function. -/
theorem log_odds (E : Ω → ℝ) (β : ℝ) {U : Finset Ω} (hU : U.Nonempty) (x y : Ω) :
    Real.log (share (weight β E) U {x}/share (weight β E) U {y}) = -β*(E x-E y) := by
  have h := mass_pos (weight_pos β E) hU
  rw [share,share,show mass (weight β E) {x} = weight β E x from Finset.sum_singleton _ _,
    show mass (weight β E) {y} = weight β E y from Finset.sum_singleton _ _,div_div_div_cancel_right₀ h.ne',
    Real.log_div (weight_pos β E x).ne' (weight_pos β E y).ne']
  simp only [weight,Real.log_exp]
  ring

/-- At any finite resolution, unequal selected energies determine the inverse temperature exactly. -/
theorem temperature_from_log_odds (E : Ω → ℝ) (β : ℝ) {U : Finset Ω} (hU : U.Nonempty)
    (x y : Ω) (hxy : E x ≠ E y) :
    -Real.log (share (weight β E) U {x}/share (weight β E) U {y})/(E x-E y) = β := by
  rw [log_odds E β hU,neg_mul,neg_neg,mul_div_cancel_right₀ _ (sub_ne_zero.mpr hxy)]

/-- Zero total variation at unequal temperatures is equivalent to constant selected energy. -/
theorem variation_zero_iff (E : Ω → ℝ) {U : Finset Ω} (hU : U.Nonempty) (β γ : ℝ) :
    variation (weight β E) (weight γ E) U = 0 ↔ β = γ ∨ ∀ x ∈ U, ∀ y ∈ U, E x = E y := by
  constructor
  · intro hz
    by_cases hh : β = γ
    · exact Or.inl hh
    right
    have hprob (x : Ω) (hx : x ∈ U) : share (weight β E) U {x} = share (weight γ E) U {x} := by
      have H := event_le_variation (weight β E) (weight γ E) (Finset.singleton_subset_iff.mpr hx)
      rw [hz] at H
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))
    intro x hx y hy
    by_contra hxy
    have H := temperature_from_log_odds E β hU x y hxy
    rw [hprob x hx,hprob y hy,temperature_from_log_odds E γ hU x y hxy] at H
    exact hh H.symm
  · rintro (rfl | h)
    · apply le_antisymm _ (variation_nonneg _ _ _)
      exact variation_le fun _ _ => by rw [sub_self,abs_zero]
    · have H := thermal_variation E hU β γ 0 (fun x hx y hy => by rw [h x hx y hy,sub_self,abs_zero])
      rw [mul_zero,zero_div,Real.tanh_zero] at H
      exact le_antisymm H (variation_nonneg _ _ _)

theorem small_contrast {ι : Type*} {l : Filter ι} {η : ι → ℝ} (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun i => Real.tanh (η i/4)) l (𝓝 0) := by
  have hh := hη.div_const 2
  rw [zero_div] at hh
  have he := Real.continuous_exp.continuousAt.tendsto.comp hh
  rw [Real.exp_zero] at he
  have H := (he.sub_const 1).div (he.add_const 1) (by positivity)
  rw [sub_self,zero_div] at H
  exact H.congr fun i => defect_eq (η i)

/-- The product of thermal contrast and energy width controls arbitrary drifting experiments,
even when the selected finite configuration spaces change. -/
theorem variation_tendsto_zero {ι : Type*} {l : Filter ι} {X : ι → Type*} (E : ∀ i, X i → ℝ)
    (U : ∀ i, Finset (X i)) (β γ D : ι → ℝ) (hU : ∀ᶠ i in l, (U i).Nonempty)
    (hD : ∀ᶠ i in l, ∀ x ∈ U i, ∀ y ∈ U i, |E i x-E i y| ≤ D i)
    (hη : Tendsto (fun i => |β i-γ i| * D i) l (𝓝 0)) :
    Tendsto (fun i => variation (weight (β i) (E i)) (weight (γ i) (E i)) (U i)) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun i => variation_nonneg _ _ _) _ (small_contrast hη)
  filter_upwards [hU,hD] with i hU' hD'
  exact thermal_variation (E i) hU' _ _ _ hD'

#print axioms temperature_from_log_odds
#print axioms variation_zero_iff
#print axioms variation_tendsto_zero

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
