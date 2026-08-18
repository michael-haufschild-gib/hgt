import GaloisForLFunctions.RHTower.RouteBDyadicCore
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIAmplitudeCells
import GaloisForLFunctions.RHTower.Sieve.MaynardAmplitudeCells

namespace RHTower.Sieve

/-- A two-factor dyadic amplitude cell. -/
noncomputable def matomakiTeravainenAmplitudeCell
    {α : Type*} [DecidableEq α] (S : Finset α) (F₁ F₂ : α → ℝ)
    (V₁ V₂ : ℝ) {J₁ J₂ : ℕ} (ij : Fin J₁ × Fin J₂) : Finset α :=
  S.filter fun q =>
    (2 : ℝ) ^ (ij.1 : ℕ) * V₁ ≤ F₁ q ∧
    F₁ q < (2 : ℝ) ^ ((ij.1 : ℕ) + 1) * V₁ ∧
    (2 : ℝ) ^ (ij.2 : ℕ) * V₂ ≤ F₂ q ∧
    F₂ q < (2 : ℝ) ^ ((ij.2 : ℕ) + 1) * V₂

/-- Logarithmic exponent of the lower edge of one dyadic amplitude cell. -/
noncomputable def matomakiTeravainenAmplitudeSigma
    (M V : ℝ) {J : ℕ} (i : Fin J) : ℝ :=
  -maynardAmplitude 0 M ((2 : ℝ) ^ (i : ℕ) * V)

theorem rpow_neg_matomakiTeravainenAmplitudeSigma
    {M V : ℝ} (hM : 1 < M) (hV : 0 < V) {J : ℕ} (i : Fin J) :
    M ^ (-matomakiTeravainenAmplitudeSigma M V i) =
      (2 : ℝ) ^ (i : ℕ) * V := by
  have hlevel : 0 < (2 : ℝ) ^ (i : ℕ) * V := by positivity
  simpa [matomakiTeravainenAmplitudeSigma] using
    (rpow_maynardAmplitude_sub_abscissa (c := (0 : ℝ)) hM hlevel)

/-- Every amplitude in a cell lies below twice its exact logarithmic lower edge. -/
theorem matomakiTeravainenAmplitudeCell_upper
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {M₁ M₂ V₁ V₂ : ℝ} (hM₁ : 1 < M₁) (hM₂ : 1 < M₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) {J₁ J₂ : ℕ} (ij : Fin J₁ × Fin J₂)
    {q : α} (hq : q ∈ matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂ ij) :
    F₁ q ≤ 2 * M₁ ^ (-matomakiTeravainenAmplitudeSigma M₁ V₁ ij.1) ∧
      F₂ q ≤ 2 * M₂ ^ (-matomakiTeravainenAmplitudeSigma M₂ V₂ ij.2) := by
  rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter] at hq
  rw [rpow_neg_matomakiTeravainenAmplitudeSigma hM₁ hV₁,
    rpow_neg_matomakiTeravainenAmplitudeSigma hM₂ hV₂]
  constructor
  · calc
      F₁ q ≤ (2 : ℝ) ^ ((ij.1 : ℕ) + 1) * V₁ := hq.2.2.1.le
      _ = 2 * ((2 : ℝ) ^ (ij.1 : ℕ) * V₁) := by rw [pow_succ]; ring
  · calc
      F₂ q ≤ (2 : ℝ) ^ ((ij.2 : ℕ) + 1) * V₂ := hq.2.2.2.2.le
      _ = 2 * ((2 : ℝ) ^ (ij.2 : ℕ) * V₂) := by rw [pow_succ]; ring

/-- The product of the two finite dyadic grids covers every point whose amplitudes lie between
their base thresholds and terminal dyadic caps. -/
theorem subset_biUnion_matomakiTeravainenAmplitudeCell
    {α : Type*} [DecidableEq α] {S : Finset α} {F₁ F₂ : α → ℝ}
    {V₁ V₂ : ℝ} (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) {J₁ J₂ : ℕ}
    (hlow₁ : ∀ q ∈ S, V₁ ≤ F₁ q) (hlow₂ : ∀ q ∈ S, V₂ ≤ F₂ q)
    (hhigh₁ : ∀ q ∈ S, F₁ q < (2 : ℝ) ^ J₁ * V₁)
    (hhigh₂ : ∀ q ∈ S, F₂ q < (2 : ℝ) ^ J₂ * V₂) :
    S ⊆ (Finset.univ : Finset (Fin J₁ × Fin J₂)).biUnion
      (matomakiTeravainenAmplitudeCell S F₁ F₂ V₁ V₂) := by
  classical
  intro q hq
  have hratio₁ : 1 ≤ F₁ q / V₁ := (le_div_iff₀ hV₁).2 (by simpa using hlow₁ q hq)
  have hratio₂ : 1 ≤ F₂ q / V₂ := (le_div_iff₀ hV₂).2 (by simpa using hlow₂ q hq)
  have hratioHigh₁ : F₁ q / V₁ < (2 : ℝ) ^ J₁ :=
    (div_lt_iff₀ hV₁).2 (by simpa [mul_comm] using hhigh₁ q hq)
  have hratioHigh₂ : F₂ q / V₂ < (2 : ℝ) ^ J₂ :=
    (div_lt_iff₀ hV₂).2 (by simpa [mul_comm] using hhigh₂ q hq)
  obtain ⟨i, hiJ, hiLow, hiHigh⟩ :=
    _root_.RHTower.exists_dyadic_cover hratio₁ hratioHigh₁
  obtain ⟨j, hjJ, hjLow, hjHigh⟩ :=
    _root_.RHTower.exists_dyadic_cover hratio₂ hratioHigh₂
  let ij : Fin J₁ × Fin J₂ := (⟨i, hiJ⟩, ⟨j, hjJ⟩)
  rw [Finset.mem_biUnion]
  refine ⟨ij, Finset.mem_univ _, ?_⟩
  rw [matomakiTeravainenAmplitudeCell, Finset.mem_filter]
  refine ⟨hq, ?_, ?_, ?_, ?_⟩
  · exact (le_div_iff₀ hV₁).1 hiLow
  · exact (div_lt_iff₀ hV₁).1 hiHigh
  · exact (le_div_iff₀ hV₂).1 hjLow
  · exact (div_lt_iff₀ hV₂).1 hjHigh

end RHTower.Sieve
