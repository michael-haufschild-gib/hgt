import GaloisForLFunctions.RHTower.PaperFermiFourierProfiles

/-! # The proven Fourier endpoint on the literal FZZ approximation family

The exceptional set is fixed before selecting finite complex coefficients. The
source generators, Haar target and their residuals keep their actual representatives.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology Set GaloisForLFunctions.HTGeometry
open scoped BigOperators

theorem paperFermiFourier_common_span {κ : Type*} [Countable κ] (a : κ → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (S : Finset (Option κ)) (c : Option κ → ℂ),
        Tendsto (fun N => fourierPartialSum
          (fun t => ∑ j ∈ S, c j * paperFermiFourierFamily a j t) N x)
          atTop (𝓝 (∑ j ∈ S, c j * paperFermiFourierFamily a j x)) :=
  paperUnitIntervalMemLp_common_span_convergence _ (paperFermiFourierFamily_memLp a)

/-- One exceptional set works for every complex coefficient vector on these scales. -/
theorem paperFermiResidual_all_coefficients {n : ℕ} (a : Fin n → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ c : Fin n → ℂ,
        Tendsto (fun N => fourierPartialSum (paperFermiResidual c a) N x)
          atTop (𝓝 (paperFermiResidual c a x)) := by
  classical
  obtain ⟨E, hm, hz, hc⟩ := paperFermiFourier_common_span a
  refine ⟨E, hm, hz, ?_⟩
  intro x hx he c
  let d : Option (Fin n) → ℂ := fun j => match j with
    | none => 1
    | some j => -c j
  have hf : (fun t => ∑ j : Option (Fin n), d j * paperFermiFourierFamily a j t) =
      paperFermiResidual c a := by
    funext t
    simp [Fintype.sum_option, d, paperFermiFourierFamily, paperFermiResidual,
      fermiNymanCombination, Finset.sum_neg_distrib, sub_eq_add_neg]
  simpa only [hf, congrFun hf x] using hc x hx he Finset.univ d

/-- The number of terms and their physical scales may vary along a countable history. -/
theorem paperFermiResidual_common_span {κ : Type*} [Countable κ] (n : κ → ℕ)
    (c : (j : κ) → Fin (n j) → ℂ) (a : (j : κ) → Fin (n j) → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ (S : Finset κ) (d : κ → ℂ),
        Tendsto (fun N => fourierPartialSum
          (fun t => ∑ j ∈ S, d j * paperFermiResidual (c j) (a j) t) N x)
          atTop (𝓝 (∑ j ∈ S, d j * paperFermiResidual (c j) (a j) x)) :=
  paperUnitIntervalMemLp_common_span_convergence _
    (fun j => paperFermiResidual_memLp (c j) (a j))

theorem paperFermiResidual_common_convergence {κ : Type*} [Countable κ] (n : κ → ℕ)
    (c : (j : κ) → Fin (n j) → ℂ) (a : (j : κ) → Fin (n j) → ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ volume E = 0 ∧
      ∀ x ∈ Ioc (0 : ℝ) 1, x ∉ E → ∀ j,
        Tendsto (fun N => fourierPartialSum (paperFermiResidual (c j) (a j)) N x)
          atTop (𝓝 (paperFermiResidual (c j) (a j) x)) := by
  classical
  obtain ⟨E, hm, hz, hc⟩ := paperFermiResidual_common_span n c a
  exact ⟨E, hm, hz, fun x hx he j => by simpa using hc x hx he {j} (fun _ => 1)⟩

end
end RHTower
