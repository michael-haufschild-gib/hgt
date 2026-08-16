import GaloisForLFunctions.RHTower.SuzukiOnePrimeOneBlockEstimate
import GaloisForLFunctions.HTGeometry.GraphFluxStabilityEstimate
import GaloisForLFunctions.HTGeometry.DyadicLatticeCover

/-!
# `(24)` and `(3)`: from the one-block estimate to finite weighted energy on the aperture

The two rough primitives cancel before coercivity, so the complete flux is the sum of the two
complementary branches and the shifted-Gamma numerical range converts a bound on that sum into a
bound on the weighted derivative.  Finitely many dyadic orbit charts cover the aperture, and a finite
union of finite energies is finite: that is the local-to-global step behind `(3)`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **`(23)`--`(24)`: complementary fluxes cancel before coercivity.**  If the complete flux is the
sum of the two branch fluxes and the shifted numerical range is coercive on the profile, the profile
is bounded by the sum of the two branch bounds — no derivative of a rough primitive is estimated. -/
theorem norm_le_of_complementaryFlux_coercive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {c a b : ℝ} {u y₁ y₂ w : E} (hsum : y₁ + y₂ = w)
    (h₁ : ‖y₁‖ ≤ a) (h₂ : ‖y₂‖ ≤ b) (hco : c * ‖u‖ ^ 2 ≤ inner ℝ u w) :
    c * ‖u‖ ≤ a + b := by
  refine le_trans (norm_le_of_coercive hco) ?_
  rw [← hsum]
  exact le_trans (norm_add_le _ _) (add_le_add h₁ h₂)

/-- A finite cover keeps finite energy finite. -/
theorem lintegral_ne_top_of_finset_cover {ι : Type*} {f : ℝ → ℝ≥0∞} {s : Finset ι}
    {W : ι → Set ℝ} {S : Set ℝ} (hcov : S ⊆ ⋃ i ∈ s, W i)
    (h : ∀ i ∈ s, (∫⁻ x in W i, f x) ≠ ⊤) :
    (∫⁻ x in S, f x) ≠ ⊤ := by
  have hmain : ∀ (t : Finset ι), (∀ i ∈ t, (∫⁻ x in W i, f x) ≠ ⊤) →
      (∫⁻ x in ⋃ i ∈ t, W i, f x) ≠ ⊤ := by
    intro t
    classical
    induction t using Finset.induction with
    | empty =>
      intro _
      simp
    | insert j t hj ih =>
      intro hall
      have hunion : (⋃ i ∈ insert j t, W i) = W j ∪ ⋃ i ∈ t, W i := by
        ext x
        simp only [Finset.mem_insert, Set.mem_iUnion, Set.mem_union, exists_prop]
        constructor
        · rintro ⟨i, hi | hi, hx⟩
          · exact Or.inl (hi ▸ hx)
          · exact Or.inr ⟨i, hi, hx⟩
        · rintro (hx | ⟨i, hi, hx⟩)
          · exact ⟨j, Or.inl rfl, hx⟩
          · exact ⟨i, Or.inr hi, hx⟩
      rw [hunion]
      refine ne_top_of_le_ne_top ?_ (lintegral_union_le f (W j) (⋃ i ∈ t, W i))
      refine ENNReal.add_ne_top.mpr ⟨hall j (Finset.mem_insert_self j t), ?_⟩
      exact ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
  refine ne_top_of_le_ne_top (hmain s h) ?_
  exact lintegral_mono' (Measure.restrict_mono hcov le_rfl) le_rfl

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **`(3)`: the aperture carries finite energy.**  Every dyadic orbit chart of the covering has
finite weighted energy — that is `(24)` read in the chart — and the aperture is covered by finitely
many of them, so the completed profile has finite energy on the whole aperture.  With the two signed
half-log traces vanishing, its zero extension has vanishing Sobolev endpoint traces. -/
theorem lintegral_energy_ne_top_of_chart_cover {ι : Type*} {f : ℝ → ℝ≥0∞} {s : Finset ι}
    {W : ι → Set ℝ} {a : ℝ} (hcov : Ioo (-a) a ⊆ ⋃ i ∈ s, W i)
    (hchart : ∀ i ∈ s, (∫⁻ x in W i, f x) ≠ ⊤) :
    (∫⁻ x in Ioo (-a) a, f x) ≠ ⊤ :=
  lintegral_ne_top_of_finset_cover hcov hchart

end GaloisForLFunctions.RHTower
