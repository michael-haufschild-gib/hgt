# The Route J beat-mode law and Laplace–Heine asymptotics of Legendre polynomials in Lean

**Stage:** 3 (formalized), 2026-09-03.  Closes MUST-150.  Six new modules, all wired into
`RHTower.lean` after `SemilocalDiagonalLegendre`, axioms `[propext, Classical.choice, Quot.sound]`,
lint clean.  Continues `route-j-scaling-profile-lean.md` (Φ, the scaling regime `2k/p → X`).

**Main theorem** (`RHTower.RouteJBeatMode.tendsto_beatMode_profile`).  For every fixed rapidity
`δ > 0`, with `σ = 1/cosh δ`, `τ = tanh δ`, `φ = arccos σ` (so `cos φ = σ`, `sin φ = τ`):

    residualJetOf (cosineModeDeterminantJet δ) k / k^{3/2}
        − 32 √(2/π) σ^{3/2} τ^{5/2} sin((4k + 9/2) φ − π/4)  →  0      (k → ∞).

`residualJetOf (cosineModeDeterminantJet δ) k` is the exact first-order response of the Route J
four-radius critical residual to the multiplier `1 + 2ε cos(δ s)` of the archimedean Gamma measure.
At `δ = log(p₂/p₁)` this is the two-prime cross term of the semilocal measure (report §3.5): it
oscillates with beat frequency `4 arccos(sech δ)` per unit of `k` and grows like `k^{3/2}`, with the
constant `32 √(2/π)` and the phase `−π/4` derived.  Ratio to the numerics `1.0005` at `k = 3200`
(`beat_mode_precert.py`).

**Legendre identification** (`SemilocalDiagonalLegendre.cosineDiagonalMoment_eq_legendre`,
formalised in the previous batch): `∫ p_n² cos(δ s) dμ = (cosh δ)^{-1/2} P_{2n}(sech δ)`, so the
residual jet is the exact combination

    (cosh δ)^{-1/2} [ r_{2k} r_{2k+1} (P_{4k+4} − P_{4k}) − 2 r_{2k+1}² (P_{4k+4} − P_{4k+2})
                     − 2 r_{2k+2}² (P_{4k+6} − P_{4k+4}) + r_{2k+2} r_{2k+3} (P_{4k+8} − P_{4k+4}) ](sech δ).

| module | content |
|---|---|
| `LegendreGeneratingFunction` | explicit `legendre N x` (guarded coefficients, Mathlib has none); the three-term recurrence; `Σ P_N(x) w^N = (1 − 2xw + w²)^{-1/2}` for `|x| ≤ 1`, `‖w‖ < 1/4` (ODE → derivative recurrence → Cauchy Taylor theorem) |
| `LegendreConvolution` | `Σ C_j u^j = (1−u)^{-1/2}`; the exact convolution `P_N(cos φ) = Σ_{k≤N} C_k C_{N−k} cos((N−2k)φ)`, `C_k = binom(2k,k)/4^k` |
| `CentralBinomialAbelBounds` | `C_k² ≤ 1/(2k+1)`, `Σ_{k<K} C_k ≤ 2√(2K+1)`; Abel/Dirichlet summation bounds for `Σ a_k η^k` on `|η| = 1`; Dirichlet's test; Abel's limit theorem gives `Σ C_k η^k = (1−η)^{-1/2}` on the circle (`η ≠ 1`) with tail `≤ 2C_K/|1−η|` |
| `LegendreHalfSumEstimate` | `C_{N−k} ≤ C_N (1 + 8k/N)` for `2k ≤ N+2`; the half convolution `Σ_{k<K} C_k C_{N−k} η^k` is `C_N (1−η)^{-1/2} + O(1/(|1−η| N))` with explicit constant `400` |
| `LegendreLaplaceHeine` | `(1 − e^{±2iφ})^{-1/2} = (2 sin φ)^{-1/2} e^{±i(π/4 − φ/2)}`; **`legendre_laplaceHeine`**: for `0 < φ < π`, `N ≥ 8`, `|P_N(cos φ) − 2 C_N (2 sin φ)^{-1/2} cos((N+½)φ − π/4)| ≤ 400/(N sin φ)` |
| `RouteJBeatModeProfile` | `φ = arccos(sech δ)` with `sin φ = tanh δ`; Wallis `√k C_{4k} → 1/(2√π)`; `C_{4k+j}/C_{4k} → 1`; `r_{2k+a} r_{2k+b}/k² → 4`; the trigonometric identity `−cos(χ−4φ) + 2cos(χ−2φ) − 2cos(χ+2φ) + cos(χ+4φ) = 8 sin 2φ sin²φ sin χ`; the amplitude identity `32√(2/π)σ^{3/2}τ^{5/2} = (cosh δ)^{-1/2}·64 (2 sin φ)^{-1/2} sin 2φ sin²φ /(2√π)`; the assembly |

**Mechanism.**  The Laplace–Heine proof is elementary: split the exact convolution at `N/2`, replace
`C_{N−k}` by `C_N` with the ratio bound (variation `|d_{k+1} − d_k| ≤ 16 C_k/N`, Abel summation), and
identify the boundary value of the half-series through Abel's limit theorem.  This avoids the
Darboux/steepest-descent contour of Szegő §8.21 and gives an explicit constant, which is what the
uniform statement needs.  In the beat-mode assembly the leading `4k²` part of the radius products
selects the second-difference combination `−P_{4k} + 2P_{4k+2} − 2P_{4k+6} + P_{4k+8}`, and the
trigonometric identity turns it into a single sine at the phase `(4k + 9/2)φ − π/4`; the `O(k)`
corrections of `r r`, the differences `C_{4k+j} − C_{4k}` and the Laplace–Heine errors are all
`o(k^{3/2})`.

**Relation to the scaling profile.**  In the scaling regime `2k sech δ → X` (`σ → 0`, `φ → π/2`,
`τ → 1`) the beat amplitude is `32√(2/π)(2k σ)^{3/2}/... = 32√(2/π) X^{3/2}`, i.e. exactly the
`−8X^{3/2} sin 4X` term of `Φ(X) = 4√(2/π)[√X cos 4X − 8X^{3/2} sin 4X]`; the `√X cos 4X` term is the
next order (`k^{1/2}`) of the beat expansion, which is why a *uniform* two-term law is the next
question (MUST-170).

**Numerical pre-certification:** `2-fully-proven/computations/routej-semilocal-scale/beat_mode_precert.py`
(Legendre identification `10⁻³⁰`, convolution identity, Laplace–Heine `N·error` bounded, exact
Legendre form of the residual `10⁻²⁹`, ratio of the residual to the beat law → 1).
