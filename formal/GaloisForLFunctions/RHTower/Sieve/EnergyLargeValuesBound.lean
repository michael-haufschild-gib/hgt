import GaloisForLFunctions.RHTower.Sieve.HuxleyDensityThreshold

/-!
# Large-values exponents for Lemma 4.1 in energy form

`EnergyLargeValuesBound cap` says that Matomäki–Teräväinen's Lemma 4.1 holds, in the energy form
used by Proposition 4.2, for every amplitude exponent `σ ∈ [5ε, cap - 5ε]`: a one-separated set
of ordinates of diameter `≤ 2T` on which a dyadic polynomial of length `N ∈ [T^{9/11-10ε}, T^{1-ε}]`
and energy `‖a‖² ≤ Q/N` exceeds `N^{-σ}` has at most `T^{2σ-ε²/5}` points.  Huxley's estimate
gives `cap = 7/32`.
-/

namespace RHTower.Sieve

open scoped InnerProductSpace

/-- Lemma 4.1 in energy form up to the amplitude exponent `cap`. -/
def EnergyLargeValuesBound (cap : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 → ∃ T₀ : ℝ, 1 ≤ T₀ ∧
    ∀ (T : ℝ) (N : ℕ) (sigma Q : ℝ) (a : EuclideanSpace ℂ (Fin N)) (S : Finset ℝ),
      T₀ ≤ T → 1 ≤ Q → Q ^ 3 ≤ T ^ (eps ^ 2) →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ (N : ℝ) → (N : ℝ) ≤ T ^ (1 - eps) →
      5 * eps ≤ sigma → sigma ≤ cap - 5 * eps →
      ‖a‖ ^ 2 ≤ Q / (N : ℝ) →
      2400 * Q ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - 2 * sigma) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ x ∈ S, (N : ℝ) ^ (-sigma) ≤ ‖⟪dyadicDirRow N x, a⟫_ℂ‖) →
      (S.card : ℝ) ≤ T ^ (2 * sigma - eps ^ 2 / 5)

/-- Huxley's large-values estimate gives Lemma 4.1 up to `7/32`. -/
theorem energyLargeValuesBound_huxley : EnergyLargeValuesBound (7 / 32) := by
  intro eps heps hepss
  obtain ⟨T₀, hT₀1, hT₀⟩ := exists_lemma41_largeness (eps := eps) (D := (1 : ℝ)) heps
  refine ⟨T₀, hT₀1, ?_⟩
  intro T N sigma Q a S hT hQ1 hQ3 hNlo hNhi hsl hsh hmass hthr hsep hspread hbig
  obtain ⟨hC, hL, _⟩ := hT₀ T hT
  have hT1 : 1 ≤ T := hT₀1.trans hT
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hT1 (by linarith)) hNlo
    exact_mod_cast this
  exact lemma41_huxley_energy_slack a S hN1 heps hepss hT1 hC hL hQ1 hQ3 hNlo hNhi hsl hsh
    hmass hthr hsep hspread hbig

end RHTower.Sieve
