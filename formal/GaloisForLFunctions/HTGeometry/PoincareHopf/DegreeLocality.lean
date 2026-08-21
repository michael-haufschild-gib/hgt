import GaloisForLFunctions.HTGeometry.PoincareHopf.DegreeConjugation

/-!
# The degree only depends on the map near the closure of the domain

Two maps agreeing on the closure of a bounded open set have the same degree there: the admissible
radii coincide, because they only constrain the map on the boundary, and the degree integrand
coincides on the open set, because agreeing on an open set forces the Jacobians to agree.

This is what makes the degree a local invariant, so that a map defined only near a compact set may
be replaced by a globally smooth one without changing any degree in sight.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f₁ f₂ : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)} {y : Fin n → ℝ}

theorem jac_congr (hΩ : IsOpen Ω) (heq : ∀ x ∈ Ω, f₁ x = f₂ x) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    jac f₁ x = jac f₂ x := by
  have hev : f₁ =ᶠ[nhds x] f₂ := by
    filter_upwards [hΩ.mem_nhds hx] with z hz
    exact heq z hz
  funext a b
  rw [jac, jac, Matrix.of_apply, Matrix.of_apply, hev.fderiv_eq]

theorem degIntegral_congr (hΩ : IsOpen Ω) (heq : ∀ x ∈ Ω, f₁ x = f₂ x)
    (φ : (Fin n → ℝ) → ℝ) : degIntegral f₁ Ω φ = degIntegral f₂ Ω φ := by
  refine MeasureTheory.setIntegral_congr_fun hΩ.measurableSet fun x hx => ?_
  rw [heq x hx, jac_congr hΩ heq hx]

theorem admissibleRadius_congr {ρ : ℝ} (heq : ∀ x ∈ closure Ω, f₁ x = f₂ x) :
    AdmissibleRadius f₁ Ω y ρ ↔ AdmissibleRadius f₂ Ω y ρ := by
  constructor <;> intro h <;> refine ⟨h.1, fun x hx => ?_⟩
  · rw [← heq x (frontier_subset_closure hx)]
    exact h.2 x hx
  · rw [heq x (frontier_subset_closure hx)]
    exact h.2 x hx

/-- **Locality of the degree.** -/
theorem degree_congr (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (heq : ∀ x ∈ closure Ω, f₁ x = f₂ x) :
    degree f₁ Ω y = degree f₂ Ω y := by
  classical
  by_cases hex : ∃ ρ, AdmissibleRadius f₁ Ω y ρ
  · obtain ⟨ρ, hadm⟩ := hex
    have hadm₂ : AdmissibleRadius f₂ Ω y ρ := (admissibleRadius_congr heq).mp hadm
    rw [degree_eq_degIntegral hf₁ hΩ hΩb hadm (bumpWeight_contDiff hadm.1)
        (bumpWeight_eq_zero hadm.1) (bumpWeight_integral hadm.1),
      degree_eq_degIntegral hf₂ hΩ hΩb hadm₂ (bumpWeight_contDiff hadm.1)
        (bumpWeight_eq_zero hadm.1) (bumpWeight_integral hadm.1)]
    exact degIntegral_congr hΩ (fun x hx => by rw [heq x (subset_closure hx)]) _
  · have hex₂ : ¬ ∃ ρ, AdmissibleRadius f₂ Ω y ρ := by
      rintro ⟨ρ, h⟩
      exact hex ⟨ρ, (admissibleRadius_congr heq).mpr h⟩
    rw [degree, degree, dif_neg hex, dif_neg hex₂]

end GaloisForLFunctions.HTGeometry.PoincareHopf
