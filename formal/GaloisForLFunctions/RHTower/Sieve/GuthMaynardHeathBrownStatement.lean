import GaloisForLFunctions.RHTower.Sieve.GuthMaynardLagSum

set_option autoImplicit false

/-!
# Heath-Brown's pair-sum bound as a statement

Guth–Maynard (arXiv 2405.20552), Theorem 1.6 (Heath-Brown, J. London Math. Soc. 1979, Theorem 1):
for a `1`-separated set `𝒯` in an interval of length `T` and coefficients `|a_n| ≤ T^{o(1)}`,

`Σ_{t₁,t₂ ∈ 𝒯} |Σ_{N < n ≤ 2N} a_n n^{i(t₁ − t₂)}|² ≤ T^{o(1)} (|𝒯|² N + |𝒯| N² + |𝒯|^{5/4} T^{1/2} N)`.

* `HeathBrownPairSumBound` is this statement for every block length `N ≥ 1`, with `|a_n| ≤ 1` and
  `T^{o(1)}` written as `C_ε T^ε` (constant chosen before all data). The phase is
  `n^{iu} = exp(i u log n)`, the convention of `lagSum`.
* `HeathBrownBlockBound N T K` is the same inequality at one block length `N` and one scale `T`
  with an explicit factor `K`. The Section 11 lemmas are proved from this per-block form, so that
  each of them can be fed either by the full statement (`HeathBrownPairSumBound.blockBound`) or by
  the unconditional ranges of the theorem (`GuthMaynardHeathBrownBlocks`).
-/

namespace RHTower.GuthMaynard

noncomputable section

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

/-- The Heath-Brown right-hand side `X² M + X M² + X^{5/4} T^{1/2} M`. -/
def heathBrownMajorant (X M T : ℝ) : ℝ :=
  X ^ 2 * M + X * M ^ 2 + X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M

theorem heathBrownMajorant_nonneg {X M T : ℝ} (hX : 0 ≤ X) (hM : 0 ≤ M) (hT : 0 ≤ T) :
    0 ≤ heathBrownMajorant X M T := by
  unfold heathBrownMajorant; positivity

theorem heathBrownMajorant_mono {X M M' T : ℝ} (hX : 0 ≤ X) (hM : 0 ≤ M) (hMM' : M ≤ M')
    (hT : 0 ≤ T) : heathBrownMajorant X M T ≤ heathBrownMajorant X M' T := by
  unfold heathBrownMajorant
  have h5 : 0 ≤ X ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by positivity
  have := pow_le_pow_left₀ hM hMM' 2
  gcongr

/-- **Heath-Brown's bound at one block length**: for every `1`-separated `𝒯 ⊆ [T₀, T₀ + T]` and
all `|a_n| ≤ 1`, `Σ_{t₁,t₂} |Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ≤ K (|𝒯|²N + |𝒯|N² + |𝒯|^{5/4}T^{1/2}N)`. -/
def HeathBrownBlockBound (N : ℕ) (T K : ℝ) : Prop :=
  ∀ (𝒯 : Finset ℝ) (a : ℕ → ℂ) (T₀ : ℝ), (∀ n, ‖a n‖ ≤ 1) →
    (∀ t ∈ 𝒯, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 𝒯 →
    ∑ t₁ ∈ 𝒯, ∑ t₂ ∈ 𝒯,
        ‖∑ n ∈ Finset.Ioc N (2 * N), a n * Complex.exp (Complex.I * (t₁ - t₂) * Real.log n)‖ ^ 2
      ≤ K * heathBrownMajorant 𝒯.card N T

theorem HeathBrownBlockBound.mono {N : ℕ} {T K K' : ℝ} (h : HeathBrownBlockBound N T K)
    (hKK' : K ≤ K') (hT : 0 ≤ T) : HeathBrownBlockBound N T K' := fun 𝒯 a T₀ ha h𝒯 hsep =>
  (h 𝒯 a T₀ ha h𝒯 hsep).trans (mul_le_mul_of_nonneg_right hKK'
    (heathBrownMajorant_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) hT))

/-- The full statement gives the per-block bound with factor `C T^ε` at every block length. -/
theorem HeathBrownPairSumBound.blockBound (hHB : HeathBrownPairSumBound) {ε : ℝ} (hε : 0 < ε) :
    ∃ C, 0 ≤ C ∧ ∀ (N : ℕ) (T : ℝ), 2 ≤ T → 1 ≤ N → HeathBrownBlockBound N T (C * T ^ ε) := by
  obtain ⟨C, hC, h⟩ := hHB ε hε
  exact ⟨C, hC, fun N T hT hN 𝒯 a T₀ ha h𝒯 hsep => h 𝒯 N a T T₀ hT hN ha h𝒯 hsep⟩

end

end RHTower.GuthMaynard
