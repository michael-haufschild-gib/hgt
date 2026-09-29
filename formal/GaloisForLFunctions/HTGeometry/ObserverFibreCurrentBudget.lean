import GaloisForLFunctions.HTGeometry.ResolutionAmplification

/-!
# Observer-fibre current budget

Let `π : X → Q` be a measurable observer onto a finite discrete target with a section `s`.  For an
effect `e : X → [0, 1]` let `Ω_π(e) = sup {|e x - e x'| : π x = π x'}` be its within-fibre
oscillation.  The visible part `e ∘ s ∘ π` is a pulled-back function on `Q`, so it carries at most
`TV(π_*μ₀, π_*μ₁)` of contrast; the hidden part `e - e ∘ s ∘ π` is bounded by `Ω_π(e)`, so it
carries at most `2Ω_π(e)`.  Hence `∫ e d(μ₁ - μ₀) ≤ TV(π_*μ) + 2Ω_π(e)`, and the effect of an
exact formation must oscillate inside some fibre by at least half the unfinanced target contrast.
Along an observer chain `X → Q → R` with the composite section the hidden currents add exactly.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X Q R : Type*} [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace R]

/-- **(RP.16a).**  The within-fibre oscillation `Ω_π(e)`. -/
def fibreOscillation (π : X → Q) (e : X → ℝ) : ℝ :=
  ⨆ p : {p : X × X // π p.1 = π p.2}, |e p.1.1 - e p.1.2|

omit [MeasurableSpace X] [MeasurableSpace Q] in
theorem abs_sub_le_fibreOscillation (π : X → Q) {e : X → ℝ} (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1)
    {x x' : X} (h : π x = π x') : |e x - e x'| ≤ fibreOscillation π e := by
  have hbdd : BddAbove (Set.range fun p : {p : X × X // π p.1 = π p.2} => |e p.1.1 - e p.1.2|) :=
    ⟨1, by
      rintro _ ⟨p, rfl⟩
      obtain ⟨h0, h1⟩ := heb p.1.1
      obtain ⟨h0', h1'⟩ := heb p.1.2
      rw [abs_le]
      constructor <;> linarith⟩
  exact le_ciSup hbdd ⟨(x, x'), h⟩

omit [MeasurableSpace X] [MeasurableSpace Q] in
theorem fibreOscillation_nonneg (π : X → Q) {e : X → ℝ} (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1)
    [Nonempty X] : 0 ≤ fibreOscillation π e := by
  obtain ⟨x⟩ := ‹Nonempty X›
  exact (abs_nonneg _).trans (abs_sub_le_fibreOscillation π heb (x := x) (x' := x) rfl)

theorem integrable_of_mem_Icc (μ : Measure X) [IsFiniteMeasure μ] {g : X → ℝ}
    (hg : Measurable g) {a b : ℝ} (hgb : ∀ x, g x ∈ Icc a b) : Integrable g μ :=
  integrable_of_bound hg (C := |a| + |b|) fun x => by
    obtain ⟨h1, h2⟩ := hgb x
    rw [abs_le]
    constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith

theorem hahnEffectCurrent_add (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {f g : X → ℝ} (hf : Integrable f P) (hf' : Integrable f Q) (hg : Integrable g P)
    (hg' : Integrable g Q) :
    hahnEffectCurrent P Q (f + g) = hahnEffectCurrent P Q f + hahnEffectCurrent P Q g := by
  rw [hahnEffectCurrent, hahnEffectCurrent, hahnEffectCurrent, Pi.add_def,
    integral_add hf' hg', integral_add hf hg]
  ring

section Budget

variable [Finite Q] [MeasurableSingletonClass Q]

/-- **Theorem 5.1 (RP.16c).**  With a section `s` of `π`, the decision current splits exactly into
visible and hidden parts, and the hidden part is bounded by the fibre oscillation. -/
theorem hahnEffectCurrent_visible_hidden (P Q' : Measure X) [IsFiniteMeasure P]
    [IsFiniteMeasure Q'] {π : X → Q} (hπ : Measurable π) {s : Q → X} (hs : ∀ q, π (s q) = q)
    {e : X → ℝ} (he : Measurable e) (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    hahnEffectCurrent P Q' e
        = hahnEffectCurrent P Q' (e ∘ s ∘ π) + hahnEffectCurrent P Q' (e - e ∘ s ∘ π) ∧
      ∀ x, |(e - e ∘ s ∘ π) x| ≤ fibreOscillation π e := by
  haveI : Countable Q := Finite.to_countable
  have hvis : Measurable (e ∘ s ∘ π) := (measurable_of_countable (e ∘ s)).comp hπ
  have hvb : ∀ x, (e ∘ s ∘ π) x ∈ Icc (0 : ℝ) 1 := fun x => heb _
  have hhid : Measurable (e - e ∘ s ∘ π) := he.sub hvis
  have hhb : ∀ x, (e - e ∘ s ∘ π) x ∈ Icc (-1 : ℝ) 1 := fun x => by
    simp only [Pi.sub_apply, Function.comp_apply]
    obtain ⟨h0, h1⟩ := heb x
    obtain ⟨h0', h1'⟩ := heb (s (π x))
    constructor <;> linarith
  refine ⟨?_, fun x => ?_⟩
  · rw [← hahnEffectCurrent_add P Q' (integrable_of_mem_Icc P hvis hvb)
      (integrable_of_mem_Icc Q' hvis hvb) (integrable_of_mem_Icc P hhid hhb)
      (integrable_of_mem_Icc Q' hhid hhb)]
    congr 1
    funext x
    simp
  · simp only [Pi.sub_apply, Function.comp_apply]
    exact abs_sub_le_fibreOscillation π heb (hs (π x)).symm

/-- **Theorem 5.1 (RP.16b).**  `∫ e d(μ₁ - μ₀) ≤ TV(π_*μ₀, π_*μ₁) + 2Ω_π(e)`. -/
theorem hahnEffectCurrent_le_observer_add (P Q' : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q'] {π : X → Q} (hπ : Measurable π) (hsurj : Function.Surjective π)
    {e : X → ℝ} (he : Measurable e) (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    hahnEffectCurrent P Q' e
      ≤ measurableHahnTV (P.map π) (Q'.map π) + 2 * fibreOscillation π e := by
  haveI : Countable Q := Finite.to_countable
  obtain ⟨s, hs⟩ : ∃ s : Q → X, ∀ q, π (s q) = q := ⟨Function.surjInv hsurj,
    Function.surjInv_eq hsurj⟩
  obtain ⟨hsplit, hbound⟩ := hahnEffectCurrent_visible_hidden P Q' hπ hs he heb
  haveI : IsProbabilityMeasure (P.map π) := Measure.isProbabilityMeasure_map hπ.aemeasurable
  haveI : IsProbabilityMeasure (Q'.map π) := Measure.isProbabilityMeasure_map hπ.aemeasurable
  have hvis : hahnEffectCurrent P Q' (e ∘ s ∘ π)
      ≤ measurableHahnTV (P.map π) (Q'.map π) := by
    have h := hahnEffectCurrent_comp P Q' hπ (measurable_of_countable (e ∘ s))
    rw [show e ∘ s ∘ π = (e ∘ s) ∘ π from rfl, h]
    exact hahnEffectCurrent_le_measurableHahnTV _ _ (measurable_of_countable _) fun q => heb _
  have hhid : hahnEffectCurrent P Q' (e - e ∘ s ∘ π) ≤ 2 * fibreOscillation π e := by
    have hmeas : Measurable (e - e ∘ s ∘ π) := he.sub ((measurable_of_countable (e ∘ s)).comp hπ)
    have hint : ∀ (μ : Measure X) [IsProbabilityMeasure μ],
        |∫ x, (e - e ∘ s ∘ π) x ∂μ| ≤ fibreOscillation π e := by
      intro μ _
      have h := norm_integral_le_of_norm_le_const (μ := μ) (f := e - e ∘ s ∘ π)
        (C := fibreOscillation π e) (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact hbound x)
      simpa [Real.norm_eq_abs] using h
    have h1 := hint Q'
    have h2 := hint P
    rw [hahnEffectCurrent]
    have := abs_sub (∫ x, (e - e ∘ s ∘ π) x ∂Q') (∫ x, (e - e ∘ s ∘ π) x ∂P)
    linarith [le_abs_self (∫ x, (e - e ∘ s ∘ π) x ∂Q' - ∫ x, (e - e ∘ s ∘ π) x ∂P)]
  linarith

/-- **Theorem 5.1 (RP.16d).**  The effect of an exact formation oscillates in some fibre by at
least half the target contrast the observer cannot finance. -/
theorem fibreOscillation_formation_ge {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] (P Q' : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q'] {π : X → Q} (hπ : Measurable π) (hsurj : Function.Surjective π)
    (p₀ p₁ : Measure Y) [IsProbabilityMeasure p₀] [IsProbabilityMeasure p₁] {d : ℕ}
    (K : ProbabilityTheory.Kernel X (Fin d → Y)) [ProbabilityTheory.IsMarkovKernel K]
    (h₀ : IsExactFormation P K p₀) (h₁ : IsExactFormation Q' K p₁) {B : Set (Fin d → Y)}
    (hNP : IsNeymanPearson p₀ p₁ B) :
    max 0 ((measurableHahnTV (Measure.pi fun _ : Fin d => p₀) (Measure.pi fun _ : Fin d => p₁)
        - measurableHahnTV (P.map π) (Q'.map π)) / 2)
      ≤ fibreOscillation π (formationEffect K B) := by
  obtain ⟨hB, hNPv⟩ := hNP
  have hcur := (hahnEffectCurrent_formation P Q' p₀ p₁ K h₀ h₁ hB hNPv).1
  have h := hahnEffectCurrent_le_observer_add P Q' hπ hsurj (measurable_formationEffect K hB)
    (formationEffect_mem K B)
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure P
  refine max_le (fibreOscillation_nonneg π (formationEffect_mem K B)) ?_
  linarith

end Budget

omit [MeasurableSpace R] in
/-- **Theorem 5.2 (RP.16e).**  Along an observer chain with the composite section, the hidden
currents add: `𝒱_{ρ∘π}(e) = 𝒱_π(e) + 𝒱_{π_*μ, ρ}(e ∘ s_π)`. -/
theorem hiddenCurrent_comp (P Q' : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q']
    [Countable Q] [MeasurableSingletonClass Q] {π : X → Q} (hπ : Measurable π) (ρ : Q → R)
    (sπ : Q → X) (sρ : R → Q) {e : X → ℝ} (he : Measurable e)
    (heb : ∀ x, e x ∈ Icc (0 : ℝ) 1) :
    hahnEffectCurrent P Q' (e - e ∘ (sπ ∘ sρ) ∘ (ρ ∘ π))
      = hahnEffectCurrent P Q' (e - e ∘ sπ ∘ π)
        + hahnEffectCurrent (P.map π) (Q'.map π) (e ∘ sπ - (e ∘ sπ) ∘ sρ ∘ ρ) := by
  have hf : Measurable (e ∘ sπ) := measurable_of_countable _
  have hg : Measurable (e ∘ sπ - (e ∘ sπ) ∘ sρ ∘ ρ) := measurable_of_countable _
  rw [← hahnEffectCurrent_comp P Q' hπ hg]
  have hA : Measurable (e - e ∘ sπ ∘ π) := he.sub (hf.comp hπ)
  have hAb : ∀ x, (e - e ∘ sπ ∘ π) x ∈ Icc (-1 : ℝ) 1 := fun x => by
    simp only [Pi.sub_apply, Function.comp_apply]
    obtain ⟨h0, h1⟩ := heb x
    obtain ⟨h0', h1'⟩ := heb (sπ (π x))
    constructor <;> linarith
  have hB : Measurable ((e ∘ sπ - (e ∘ sπ) ∘ sρ ∘ ρ) ∘ π) := hg.comp hπ
  have hBb : ∀ x, ((e ∘ sπ - (e ∘ sπ) ∘ sρ ∘ ρ) ∘ π) x ∈ Icc (-1 : ℝ) 1 := fun x => by
    simp only [Function.comp_apply, Pi.sub_apply]
    obtain ⟨h0, h1⟩ := heb (sπ (π x))
    obtain ⟨h0', h1'⟩ := heb (sπ (sρ (ρ (π x))))
    constructor <;> linarith
  rw [← hahnEffectCurrent_add P Q' (integrable_of_mem_Icc P hA hAb)
    (integrable_of_mem_Icc Q' hA hAb) (integrable_of_mem_Icc P hB hBb)
    (integrable_of_mem_Icc Q' hB hBb)]
  congr 1
  funext x
  simp

end GaloisForLFunctions.HTGeometry
