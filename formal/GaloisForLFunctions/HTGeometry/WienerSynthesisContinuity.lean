import GaloisForLFunctions.HTGeometry.WienerSynthesisMixed

/-!
# Continuity of a synthesis in the event

The coordinate interface of the corpus asks for partial derivatives that are continuous on the whole
chart, so every synthesis occurring in the construction — the field and each of its derivatives —
has to be continuous jointly in time and space.

They all have the same shape: a family of densities, continuous in the frequency, continuous in time,
and dominated on each time interval by a constant multiple of the weight. That is exactly the
hypothesis of dominated convergence for a continuous parameter, and it gives joint continuity in one
step.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

open scoped RealInnerProductSpace FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- **A dominated family of densities has a jointly continuous synthesis.** -/
theorem continuous_kgSynthesis_param {g : ℝ → E → ℂ}
    (hdim : (Module.finrank ℝ E : ℝ) < N)
    (hcontξ : ∀ t : ℝ, Continuous (g t))
    (hcontt : ∀ ξ : E, Continuous fun t : ℝ => g t ξ)
    (hbound : ∀ T : ℝ, ∃ B : ℝ, ∀ t : ℝ, |t| ≤ T → ∀ ξ : E,
      ‖g t ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * B) :
    Continuous fun p : ℝ × E => kgSynthesis (g p.1) p.2 := by
  refine continuous_iff_continuousAt.mpr fun p₀ => ?_
  obtain ⟨t₀, x₀⟩ := p₀
  set T : ℝ := |t₀| + 1 with hT
  obtain ⟨B, hB⟩ := hbound T
  have hTmem : ∀ᶠ p : ℝ × E in nhds (t₀, x₀), |p.1| ≤ T := by
    have hcont : ContinuousAt (fun p : ℝ × E => |p.1|) (t₀, x₀) :=
      (continuous_abs.comp continuous_fst).continuousAt
    have hlt : |t₀| < T := by
      rw [hT]
      linarith
    exact hcont.eventually (eventually_le_nhds hlt)
  refine continuousAt_of_dominated (μ := (volume : Measure E))
    (F := fun p : ℝ × E => fun ξ : E => kgChar p.2 ξ * g p.1 ξ)
    (bound := fun ξ : E => (kgFreq ξ ^ N)⁻¹ * B)
    (Filter.Eventually.of_forall fun p =>
      ((continuous_kgChar' p.2).mul (hcontξ p.1)).aestronglyMeasurable)
    ?_ ((integrable_kgFreq_inv_pow (E := E) hdim).mul_const B) ?_
  · filter_upwards [hTmem] with p hp
    filter_upwards with ξ
    rw [norm_mul, norm_kgChar, one_mul]
    exact hB p.1 hp ξ
  · filter_upwards with ξ
    have h1 : ContinuousAt (fun p : ℝ × E => kgChar p.2 ξ) (t₀, x₀) :=
      ((continuous_kgChar_point ξ).comp continuous_snd).continuousAt
    have h2 : ContinuousAt (fun p : ℝ × E => g p.1 ξ) (t₀, x₀) :=
      ((hcontt ξ).comp continuous_fst).continuousAt
    exact h1.mul h2

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derived densities of a dominated family are again dominated, with one power of the weight
spent. -/
theorem norm_kgDirDensity_le_weight {g : E → ℂ} {N : ℕ} {B : ℝ} (v : E)
    (hg : ∀ ξ : E, ‖g ξ‖ ≤ (kgFreq ξ ^ (N + 1))⁻¹ * B) (ξ : E) :
    ‖kgDirDensity v g ξ‖ ≤ (kgFreq ξ ^ N)⁻¹ * (2 * Real.pi * ‖v‖ * B) := by
  have hpos : (0 : ℝ) < kgFreq ξ := kgFreq_pos ξ
  have hstep := norm_kgDirDensity_le v g ξ
  have hfin : 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖g ξ‖)
      ≤ (kgFreq ξ ^ N)⁻¹ * (2 * Real.pi * ‖v‖ * B) := by
    have hg' : kgFreq ξ * ‖g ξ‖ ≤ kgFreq ξ * ((kgFreq ξ ^ (N + 1))⁻¹ * B) :=
      mul_le_mul_of_nonneg_left (hg ξ) hpos.le
    have hcalc : kgFreq ξ * ((kgFreq ξ ^ (N + 1))⁻¹ * B) = (kgFreq ξ ^ N)⁻¹ * B := by
      rw [pow_succ]
      field_simp
    rw [hcalc] at hg'
    have hcoef : (0 : ℝ) ≤ 2 * Real.pi * ‖v‖ := by positivity
    calc 2 * Real.pi * ‖v‖ * (kgFreq ξ * ‖g ξ‖)
        ≤ 2 * Real.pi * ‖v‖ * ((kgFreq ξ ^ N)⁻¹ * B) := mul_le_mul_of_nonneg_left hg' hcoef
      _ = (kgFreq ξ ^ N)⁻¹ * (2 * Real.pi * ‖v‖ * B) := by ring
  exact hstep.trans hfin

end GaloisForLFunctions.HTGeometry
