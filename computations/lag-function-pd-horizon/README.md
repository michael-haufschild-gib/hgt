# Positive-definiteness horizon of the prime-truncated Weil lag function

**Object.** `Φ(L) = Σ_ρ e^{L(ρ−1/2)}/(ρ(1−ρ))` (even, continuous, absolutely convergent, `Φ(0) = 2+γ−log 4π`,
Lean-certified value). RH ⟺ Φ positive-definite ⟺ `|Φ| ≤ Φ(0)`. Prime side for `L>0`, `X=e^L`:
`Φ(L) = e^{−L/2}(X−ψ(X)) + e^{L/2}(Σ_{n≤X}Λ(n)/n − L + γ) − e^{−L/2}B(X)`,
`B(X) = log 2π − 1 + ½log(1−X^{−2}) + X artanh(1/X)`; i.e. an archimedean germ plus a convex kink
`2Λ(n)n^{−1/2}sinh((L−log n)/2)_+` at every prime power. `Φ_P` keeps only prime powers `≤ P`.

**Computation** (`pd_horizon.py`, runpod, 16 cores, < 1 min). (1) Sanity: prime-side `Φ` against the zero side
`2Σ_{γ≤γ_1500} cos(γL)/(¼+γ²)`: agreement to `10⁻⁶` for `0.3 ≤ L ≤ 12` (the `10⁻³` gap at `L=0` is the missing zero tail).
(2) For 42 truncation points `P`, the largest `L` with the `300×300` Toeplitz matrix of `Φ_P` on `[0,L]` positive
semidefinite (`L_pd`), and the largest `L` with `|Φ_P| ≤ Φ(0)` on `[0,L]` (`L_sup`), compared with `log n₁`, `n₁` the next
prime power.

**Result** (`pd_horizon.log`, `pd_horizon.json`). `L_pd − log n₁ ∈ [0.013, 0.050]` for every `P`; `L_sup − log n₁ ∈ [0.040, 0.19]`,
larger exactly when the omitted weight `Λ(n₁)/√n₁` is small (powers of 2 and 3). Positive-definiteness detects each
omitted prime power within a lag of a few hundredths.

**Interpretation.** Under RH this is a theorem in its two-by-two form: `Φ(L) ≤ Φ(0)` and the omitted kink grows like
`Λ(n₁)n₁^{−1/2}(L − log n₁)`, so the truncation crosses `−Φ(0)` within `2 arcsinh(Φ(0)√n₁/Λ(n₁))`; the observed horizons
are much tighter because `Φ` sits near its negative dips at prime powers (Landau's bias). Consequence recorded as
MUST-233: the positivity budget `Φ(0) ≈ 0.046` is exhausted within a fixed small lag past any omitted prime power; the
prime side of a positive-definite lag function is tight at every prime power. See also `lag-function-pd-rigidity/`.
