import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum

set_option autoImplicit false

/-!
# Heath-Brown's pair-sum bound as a statement

Guth–Maynard (arXiv 2405.20552), Theorem 1.6 (Heath-Brown, J. London Math. Soc. 1979, Theorem 1):
for a `1`-separated set `𝒯` in an interval of length `T` and coefficients `|a_n| ≤ T^{o(1)}`,

`Σ_{t₁,t₂ ∈ 𝒯} |Σ_{N < n ≤ 2N} a_n n^{i(t₁ − t₂)}|² ≤ T^{o(1)} (|𝒯|² N + |𝒯| N² + |𝒯|^{5/4} T^{1/2} N)`.

`HeathBrownPairSumBound` is this statement with `|a_n| ≤ 1` and `T^{o(1)}` written as `C_ε T^ε`
(constant chosen before all data). The phase is `n^{iu} = exp(i u log n)`, the convention of
`lagSum`. The Section 11 energy bounds of Guth–Maynard that need the full theorem (Lemmas 11.5,
1.5, 11.6, 11.9 and Propositions 11.1, 11.2) take this single proposition as their hypothesis.
-/

namespace RHTower.GuthMaynard

/-- **Heath-Brown's theorem on difference sets** (Guth–Maynard Theorem 1.6): for every `ε > 0`
there is `C ≥ 0` such that for every `1`-separated `𝒯 ⊆ [T₀, T₀ + T]` (`T ≥ 2`), every `N ≥ 1` and
all `|a_n| ≤ 1`,
`Σ_{t₁,t₂ ∈ 𝒯} |Σ_{N < n ≤ 2N} a_n n^{i(t₁−t₂)}|² ≤ C T^ε (|𝒯|² N + |𝒯| N² + |𝒯|^{5/4} T^{1/2} N)`. -/
def HeathBrownPairSumBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝒯 : Finset ℝ) (N : ℕ) (a : ℕ → ℂ) (T T₀ : ℝ),
    2 ≤ T → 1 ≤ N → (∀ n, ‖a n‖ ≤ 1) → (∀ t ∈ 𝒯, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 𝒯 →
    ∑ t₁ ∈ 𝒯, ∑ t₂ ∈ 𝒯,
        ‖∑ n ∈ Finset.Ioc N (2 * N), a n * Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2
      ≤ C * T ^ ε * ((𝒯.card : ℝ) ^ 2 * N + 𝒯.card * (N : ℝ) ^ 2
        + (𝒯.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N)

end RHTower.GuthMaynard
