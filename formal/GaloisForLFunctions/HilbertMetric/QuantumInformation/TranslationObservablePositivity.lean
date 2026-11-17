import GaloisForLFunctions.HilbertMetric.QuantumInformation.TranslationObservableAlgebra
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram

/-!
# Positivity in every auxiliary dimension for the closed translation average

The averaged operator Gram is the scalar integral of an actual Hilbert Gram.
Expanding its quadratic form gives an integral of a squared Hilbert norm.
Only the scalar coefficients require integrability, already proved on the
concrete closed observable algebra; no vector-orbit measurability is assumed.
-/

noncomputable section
open MeasureTheory Matrix ContinuousLinearMap
open scoped BigOperators ComplexConjugate ComplexOrder
namespace GaloisForLFunctions.HilbertMetric.ShiftAverage

private theorem integral_hilbertGram_posSemidef {n : ℕ} (f : Fin n → ℝ → Space)
    (hprod : ∀ i j, IntegrableOn (fun t => inner ℂ (f i t) (f j t)) (Set.Ioc 0 1)) :
    Matrix.PosSemidef (fun i j => ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (f i t) (f j t)) := by
  have hh : Matrix.IsHermitian
      (fun i j => ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (f i t) (f j t)) := by
    ext i j
    change conj (∫ t : ℝ in Set.Ioc 0 1, inner ℂ (f j t) (f i t)) = _
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => inner_conj_symm _ _
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro c
  let F : ℝ → Space := fun t => ∑ i, c i • f i t
  have hex (t : ℝ) : inner ℂ (F t) (F t) =
      ∑ i, ∑ j, conj (c i) * c j * inner ℂ (f i t) (f j t) := by
    simp only [F, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hterm (i j : Fin n) : IntegrableOn
      (fun t => conj (c i) * c j * inner ℂ (f i t) (f j t)) (Set.Ioc 0 1) :=
    (hprod i j).const_mul _
  have hquad : star c ⬝ᵥ ((fun i j => ∫ t : ℝ in Set.Ioc 0 1,
      inner ℂ (f i t) (f j t)) *ᵥ c) =
        ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (F t) (F t) := by
    calc
      _ = ∑ i, ∑ j, conj (c i) * c j *
          ∫ t : ℝ in Set.Ioc 0 1, inner ℂ (f i t) (f j t) := by
        simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, ∫ t : ℝ in Set.Ioc 0 1,
          conj (c i) * c j * inner ℂ (f i t) (f j t) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [integral_const_mul]
      _ = ∫ t : ℝ in Set.Ioc 0 1,
          ∑ i, ∑ j, conj (c i) * c j * inner ℂ (f i t) (f j t) := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum _ (fun j _ => hterm i j)]
      _ = _ := by simp_rw [hex]
  rw [hquad]
  have hint : IntegrableOn (fun t => inner ℂ (F t) (F t)) (Set.Ioc 0 1) := by
    simp_rw [hex]
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hterm i j))
  have hcast (t : ℝ) : inner ℂ (F t) (F t) = ((‖F t‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    change (‖F t‖ : ℂ) ^ 2 = ((‖F t‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
  have hr : IntegrableOn (fun t => ‖F t‖ ^ 2) (Set.Ioc 0 1) := by
    have h := hint.re
    change IntegrableOn (fun t => (inner ℂ (F t) (F t)).re) (Set.Ioc 0 1) at h
    simpa only [hcast, Complex.ofReal_re] using h
  have he : (∫ t : ℝ in Set.Ioc 0 1, inner ℂ (F t) (F t)) =
      ((∫ t : ℝ in Set.Ioc 0 1, ‖F t‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hcast]
    exact Complex.ofRealCLM.integral_comp_comm hr
  rw [he]
  exact Complex.zero_le_real.mpr (integral_nonneg fun t => sq_nonneg _)

/-- Actual adjoint-product observable inside the concrete closed algebra. -/
def observableGramProduct (A B : ObservableDomain) : ObservableDomain :=
  ⟨adjoint (A : Observable) * (B : Observable),
    observableDomain_mul_mem ⟨adjoint (A : Observable), observableDomain_adjoint_mem A⟩ B⟩

/-- Every shifted Gram coefficient is integrable on the averaging interval. -/
theorem observableGram_coefficient_integrable (A B : ObservableDomain) (u v : Space) :
    IntegrableOn (fun t => inner ℂ ((A : Observable) (shift t u))
      ((B : Observable) (shift t v))) (Set.Ioc 0 1) := by
  have h := observableDomain_coefficient_integrable (observableGramProduct A B) u v
  change IntegrableOn (fun t => inner ℂ (shift t u)
    (adjoint (A : Observable) ((B : Observable) (shift t v)))) (Set.Ioc 0 1) at h
  simpa only [adjoint_inner_right] using h

/-- Averaged adjoint products are the actual scalar integrals of shifted Hilbert Grams. -/
theorem closedObservableAverage_gram_integral (A B : ObservableDomain) (u v : Space) :
    inner ℂ u (closedObservableAverage (observableGramProduct A B) v) =
      ∫ t : ℝ in Set.Ioc 0 1, inner ℂ ((A : Observable) (shift t u))
        ((B : Observable) (shift t v)) := by
  rw [← closedObservableAverage_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change inner ℂ (shift t u) (adjoint (A : Observable) ((B : Observable) (shift t v))) = _
    exact adjoint_inner_right _ _ _

/-- Closed-domain averaging preserves operator Grams in every finite auxiliary dimension. -/
theorem closedObservableAverage_gram_posSemidef {n : ℕ}
    (A : Fin n → ObservableDomain) (u : Fin n → Space) :
    Matrix.PosSemidef (fun i j =>
      inner ℂ (u i) (closedObservableAverage (observableGramProduct (A i) (A j)) (u j))) := by
  simp_rw [closedObservableAverage_gram_integral]
  exact integral_hilbertGram_posSemidef
    (fun i t => (A i : Observable) (shift t (u i)))
    (fun i j => observableGram_coefficient_integrable (A i) (A j) (u i) (u j))

#print axioms observableGram_coefficient_integrable
#print axioms closedObservableAverage_gram_integral
#print axioms closedObservableAverage_gram_posSemidef
end GaloisForLFunctions.HilbertMetric.ShiftAverage
