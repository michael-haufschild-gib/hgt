import GaloisForLFunctions.RHTower.Sieve.MenonSharpIntervalUniformKernel

/-!
# Case-II coloring with variable sharp upper endpoints

Reverse reciprocal/logarithmic Abel selection keeps the lower endpoint fixed but selects a
frequency-dependent upper endpoint.  The ambient kernel majorant lets every such interval enter
the same Case-II label type and the same amplitude threshold, without coloring by its endpoint.
-/

namespace RHTower.Sieve

noncomputable section

/-- Explicit ambient-scale kernel constant built from the single absolute derivative bound. -/
def menonSharpIntervalAmbientKernelMajorant (C0 : ℝ) (X : ℕ) (sigma : ℝ) : ℝ :=
  let Z : ℝ := (X : ℝ) + 2
  let M0 : ℝ := Z ^ sigma / sigma
  let M2 : ℝ := 4 * C0 * Z ^ (2 : ℕ) * Z ^ sigma
  1 + 4 * (M0 + M2)

/-- The explicit ambient constant controls every sharp subinterval of `[1,X]`. -/
theorem exists_menonSharpIntervalAmbientKernelMajorant :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ {X a b : ℕ} {sigma : ℝ},
        1 ≤ a → a ≤ b → b ≤ X → 0 < sigma →
        1 ≤ menonSharpIntervalAmbientKernelMajorant C0 X sigma ∧
        ∀ y : ℝ,
          ‖menonSharpIntervalMellinKernel (a : ℝ) (b : ℝ) sigma y‖ ≤
            menonSharpIntervalAmbientKernelMajorant C0 X sigma * (1 + y ^ (2 : ℕ))⁻¹ := by
  obtain ⟨C0, hC0, hmajorant⟩ := exists_menonSharpIntervalUniformKernelMajorant
  refine ⟨C0, hC0, ?_⟩
  intro X a b sigma ha hab hbX hsigma
  simpa only [menonSharpIntervalAmbientKernelMajorant] using
    hmajorant ha hab hbX hsigma

/-- One absolute kernel constant colors sharp intervals whose upper endpoint varies with the
exceptional frequency.  The endpoint is never added to the finite label. -/
theorem exists_absolute_menonHeathBrownCaseIISelection_variableUpper_coloring :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ (L X a cells : ℕ) (T0 t : ℝ)
          (B sigma V Δ : ℝ) (S : Finset ℕ) (upper : ℕ → ℕ) (tau : ℕ → ℝ),
        X < (L + 1) ^ (3 : ℕ) → 1 < T0 →
        ((2 ^ (6 : ℕ) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ) →
        (64 : ℝ) ^ (8 : ℕ) ≤ (a : ℝ) → 1 ≤ L →
        (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ) →
        1 < sigma → 0 ≤ V → 0 < Δ → 0 < cells →
        2 * V = (cells : ℝ) * Δ →
        (∀ r ∈ S, a ≤ upper r) →
        (∀ r ∈ S, upper r ≤ X) →
        let C : ℝ := menonSharpIntervalAmbientKernelMajorant C0 X sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan V)) /
            ((cells : ℝ) * Δ * C)
        0 < Q →
        (∀ r ∈ S, B < ‖(2 * Real.pi : ℝ) •
          (∑ n ∈ Finset.Ioc a (upper r), vonMangoldtTwist (tau r) n)‖) →
        ∃ color : ℕ → MenonHeathBrownCaseIILabel L X cells,
          ∃ selectedY : ℕ → ℝ, ∀ r ∈ S,
            IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
              (selectedY r) (color r) := by
  obtain ⟨C0, hC0, hkernel⟩ := exists_menonSharpIntervalAmbientKernelMajorant
  refine ⟨C0, hC0, ?_⟩
  intro L X a cells T0 t B sigma V Δ S upper tau hXL hT0 hscale ha hL hcut
    hsigma hV hΔ hcells hgrid hupperLo hupperHi
  dsimp only
  intro hQ hlarge
  let C : ℝ := menonSharpIntervalAmbientKernelMajorant C0 X sigma
  let Q : ℝ :=
    (B - heathBrownWindowRelevantFixedPolylogBound L X 3 (a : ℝ) sigma * C *
        (Real.pi - 2 * Real.arctan V)) /
      ((cells : ℝ) * Δ * C)
  have haOne : 1 ≤ a := by
    have haReal : (1 : ℝ) ≤ (a : ℝ) := by
      calc
        (1 : ℝ) ≤ (64 : ℝ) ^ (8 : ℕ) := by norm_num
        _ ≤ (a : ℝ) := ha
    exact_mod_cast haReal
  have hpoint : ∀ r : ℕ, r ∈ S →
      ∃ label : MenonHeathBrownCaseIILabel L X cells, ∃ y : ℝ,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
          y label := by
    intro r hr
    have har := hupperLo r hr
    have hrX := hupperHi r hr
    have hC := (hkernel (X := X) (a := a) (b := upper r) (sigma := sigma)
      haOne har hrX (by linarith)).1
    have hkernelR := (hkernel (X := X) (a := a) (b := upper r) (sigma := sigma)
      haOne har hrX (by linarith)).2
    exact exists_menonHeathBrownCaseIISelection_of_vonMangoldtTwist_Ioc_gt
      L X a (upper r) cells hXL har hrX T0 t (tau r) hT0 hscale ha hL hcut
      hsigma hC hkernelR hV hΔ hcells hgrid (by simpa only [Q, C] using hQ)
      (hlarge r hr)
  choose selected selectedY hselected using hpoint
  let fallback : MenonHeathBrownCaseIILabel L X cells :=
    Classical.choice (nonempty_menonHeathBrownCaseIILabel L X cells hcells)
  let color : ℕ → MenonHeathBrownCaseIILabel L X cells := fun r =>
    if hr : r ∈ S then selected r hr else fallback
  let ordinate : ℕ → ℝ := fun r =>
    if hr : r ∈ S then selectedY r hr else 0
  refine ⟨color, ordinate, ?_⟩
  intro r hr
  simpa only [color, ordinate, dif_pos hr] using hselected r hr

end

end RHTower.Sieve
