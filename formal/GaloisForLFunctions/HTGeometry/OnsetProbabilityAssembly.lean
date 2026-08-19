/-
# Assembling an onset bound from a capture floor and a split of the integrals

The plateau-onset estimate has one shape.  On the event to be bounded, a *capture floor* says that
a fixed positive margin is dominated by a finite sum of non-negative observables; each of those
observables has an integral split into a diagonal part and a deviation; the diagonal parts sum to a
small multiple of the margin, and so do the deviations.  Integrating the floor over the event turns
the two sums into the two terms of the bound.

The complementary form is the same statement read on the complement, with the exceptional event
removed by a union bound.

Main results:
* `mul_measureReal_le_of_capture` — integrating the capture floor.
* `measureReal_le_of_capture_split` — the onset bound in the form the card uses.
* `one_sub_le_measureReal_compl` — its complementary reading.
-/
import GaloisForLFunctions.HTGeometry.AggregatedOscillatoryMass

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {Ω Z : Type*} [MeasurableSpace Ω] [Fintype Z]

/-- **Integrating the capture floor.**  A margin dominated on the event by a finite sum of
non-negative integrable observables is dominated by the total of their integrals. -/
theorem mul_measureReal_le_of_capture (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) {F : Z → Ω → ℝ}
    (hFint : ∀ z, Integrable (F z) μ) (hFnn : ∀ z ω, 0 ≤ F z ω)
    {κ : ℝ} (hcap : ∀ ω ∈ S, κ ≤ ∑ z, F z ω) {b : ℝ}
    (hb : ∑ z, ∫ ω, F z ω ∂μ ≤ b) :
    κ * μ.real S ≤ b := by
  classical
  have hsumInt : Integrable (fun ω => ∑ z, F z ω) μ :=
    integrable_finsetSum _ fun z _ => hFint z
  have hnn : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => ∑ z, F z ω :=
    Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun z _ => hFnn z ω
  have h1 : ∫ _ω in S, κ ∂μ = μ.real S * κ := by
    rw [setIntegral_const, smul_eq_mul]
  have h2 : ∫ _ω in S, κ ∂μ ≤ ∫ ω in S, (∑ z, F z ω) ∂μ := by
    refine setIntegral_mono_on (integrableOn_const) hsumInt.integrableOn hS hcap
  have h3 : ∫ ω in S, (∑ z, F z ω) ∂μ ≤ ∫ ω, (∑ z, F z ω) ∂μ :=
    setIntegral_le_integral hsumInt hnn
  have h4 : ∫ ω, (∑ z, F z ω) ∂μ = ∑ z, ∫ ω, F z ω ∂μ :=
    integral_finsetSum _ fun z _ => hFint z
  rw [h1] at h2
  have := h2.trans (h3.trans (le_of_eq h4))
  linarith [hb, this]

/-- **The onset bound.**  With the integrals split into a diagonal part and a deviation, each
summing to the margin times a small number, the event has measure at most the sum of those two
numbers. -/
theorem measureReal_le_of_capture_split (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) {F : Z → Ω → ℝ}
    (hFint : ∀ z, Integrable (F z) μ) (hFnn : ∀ z ω, 0 ≤ F z ω)
    {κ : ℝ} (hκ : 0 < κ) (hcap : ∀ ω ∈ S, κ ≤ ∑ z, F z ω)
    {d e : Z → ℝ} (hsplit : ∀ z, ∫ ω, F z ω ∂μ ≤ d z + e z)
    {A q : ℝ} (hd : ∑ z, d z ≤ κ * A) (he : ∑ z, e z ≤ κ * q) :
    μ.real S ≤ A + q := by
  classical
  have hb : ∑ z, ∫ ω, F z ω ∂μ ≤ κ * (A + q) := by
    calc ∑ z, ∫ ω, F z ω ∂μ ≤ ∑ z, (d z + e z) := Finset.sum_le_sum fun z _ => hsplit z
      _ = (∑ z, d z) + ∑ z, e z := Finset.sum_add_distrib
      _ ≤ κ * A + κ * q := add_le_add hd he
      _ = κ * (A + q) := by ring
  have hmain := mul_measureReal_le_of_capture μ hS hFint hFnn hcap hb
  exact le_of_mul_le_mul_left hmain hκ

/-- **The complementary reading.**  Removing the exceptional event by a union bound turns an onset
bound into a lower bound on the complement. -/
theorem one_sub_le_measureReal_compl (μ : Measure Ω) [IsProbabilityMeasure μ]
    {G S : Set Ω} (hS : MeasurableSet S) {ε₁ ε₂ : ℝ}
    (hGc : μ.real Gᶜ ≤ ε₁) (hGS : μ.real (G ∩ S) ≤ ε₂) :
    1 - ε₁ - ε₂ ≤ μ.real Sᶜ := by
  have hsub : S ⊆ (G ∩ S) ∪ Gᶜ := by
    intro ω hω
    by_cases hG : ω ∈ G
    · exact Or.inl ⟨hG, hω⟩
    · exact Or.inr hG
  have hle : μ.real S ≤ ε₂ + ε₁ :=
    le_trans (measureReal_mono hsub) (le_trans (measureReal_union_le _ _) (add_le_add hGS hGc))
  have hsum : μ.real S + μ.real Sᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hS, probReal_univ]
  linarith

end GaloisForLFunctions.HTGeometry
