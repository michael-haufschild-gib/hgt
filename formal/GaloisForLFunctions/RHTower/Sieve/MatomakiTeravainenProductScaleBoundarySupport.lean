import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProductScaleBoundary

/-!
# Coarse support of product-scale boundary errors

The paper's endpoint collars lie inside `(Y/4,8Y]` whenever their common relative dilation is at
most two.  This support statement is independent of the later mean-square estimate.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- One product-scale boundary component is supported in the paper's coarse error interval. -/
theorem mtProductScaleBoundaryErrorAF_support_four_eight
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (F : ι → ArithmeticFunction ℂ) (M : ι → ℝ)
    {Y eta : ℝ} (hY : 0 < Y) (heta : 0 ≤ eta) (hetaOne : eta ≤ 1)
    (hsupport : ∀ i ∈ S,
      MTRealScaleSupported (F i) (M i) ((1 + eta) * M i))
    {n : ℕ} (hn : mtProductScaleBoundaryErrorAF S F M Y n ≠ 0) :
    Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y := by
  rcases mtProductScaleBoundaryErrorAF_support_endpointCollars
      S F M Y eta heta hsupport hn with hlower | hupper
  · constructor
    · linarith
    · calc
        (n : ℝ) ≤ (1 + eta) * (Y / 2) := hlower.2
        _ ≤ 8 * Y := by nlinarith
  · constructor
    · linarith
    · calc
        (n : ℝ) ≤ (1 + eta) * (4 * Y) := hupper.2
        _ ≤ 8 * Y := by nlinarith

/-- Four signed boundary components preserve a common support interval. -/
theorem sub_add_sub_support_four
    (e₀ e₁ e₂ e₃ : ArithmeticFunction ℂ) {L U : ℝ}
    (h₀ : ∀ {n : ℕ}, e₀ n ≠ 0 → L < (n : ℝ) ∧ (n : ℝ) ≤ U)
    (h₁ : ∀ {n : ℕ}, e₁ n ≠ 0 → L < (n : ℝ) ∧ (n : ℝ) ≤ U)
    (h₂ : ∀ {n : ℕ}, e₂ n ≠ 0 → L < (n : ℝ) ∧ (n : ℝ) ≤ U)
    (h₃ : ∀ {n : ℕ}, e₃ n ≠ 0 → L < (n : ℝ) ∧ (n : ℝ) ≤ U)
    {n : ℕ} (hn : (e₀ - e₁ + e₂ - e₃) n ≠ 0) :
    L < (n : ℝ) ∧ (n : ℝ) ≤ U := by
  by_contra hout
  have he₀ : e₀ n = 0 := by
    by_contra hne
    exact hout (h₀ hne)
  have he₁ : e₁ n = 0 := by
    by_contra hne
    exact hout (h₁ hne)
  have he₂ : e₂ n = 0 := by
    by_contra hne
    exact hout (h₂ hne)
  have he₃ : e₃ n = 0 := by
    by_contra hne
    exact hout (h₃ hne)
  apply hn
  change e₀ n - e₁ n + e₂ n - e₃ n = 0
  simp [he₀, he₁, he₂, he₃]

end

end RHTower.Sieve
