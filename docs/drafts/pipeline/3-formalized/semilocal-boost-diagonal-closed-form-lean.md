# Closed form of the diagonal boost matrix elements of the semilocal Jacobi matrix (Lean)

**Stage:** 3 (formalized), 2026-09-03.  Closes the analytic core of MUST-148 (the paper theorem
F415).  Seven modules, all wired into `RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`,
lint clean:

| module | content |
|---|---|
| `SemilocalJacobiMeixnerPollaczekGeneratingFunction` | `Σ c_n p_n(s) w^n = (1−iw)^{−1/4+is/2}(1+iw)^{−1/4−is/2}`, real form `(1+w²)^{−1/4} e^{s arctan w}` |
| `SemilocalGammaComplexRapidityCharacteristic` | `∫ e^{zs} dμ = (cos z)^{−1/2}` on `|Re z| < π/2` (identity theorem on Mathlib's `complexMGF`); two-variable boost integral in cosine form |
| `ScalarPowerSeriesUniqueness` | coefficient uniqueness on a disc, real-axis uniqueness, Taylor coefficients `aₙ = f⁽ⁿ⁾(0)/n!`, complex binomial series `(1−u)^{−a} = Σ ((−a) choose n)(−u)^n` |
| `SemilocalJacobiCoefficientCauchyBound` | `‖G_s(w)‖ ≤ (3/4)^{−1/2} e^{|s|/2}` on `‖w‖ ≤ 1/4` (sector argument lemma of the corpus) and the Cauchy bound `|c_m p_m(s)| ≤ (3/4)^{−1/2} e^{|s|/2} 4^m` |
| `SemilocalBoostCoefficientInterchange` | `e^{κ|s|}` integrable for `|κ| < π/2`; polynomial × `e^{|s|/2}` integrable; dominated term-by-term integration `Σ_m w^m ∫ c_m p_m g = ∫ G(w) g` for `‖w‖ < 1/4`; the two instances `g = G(z)e^{its}` and `g = p_m e^{its}` |
| `SemilocalBoostGeneratingFunctionClosedForm` | `∫ G_s(w)G_s(z)e^{its} dμ = (cosh t)^{−1/2}(1 − wz − i tanh t (w+z))^{−1/2}`; factorization by the Möbius ratio `q(z) = (z+iτ)/(1−iτz)`; boost row coefficients `∫ c_m p_m G(z) e^{its} = (cosh t)^{−1/2}(1−iτz)^{−1/2}(−½ choose m)(−q(z))^m` |
| `SemilocalBoostRowTaylorIdentification` | `M_{mn}(t) = ∫ p_m p_n e^{its} dμ`; `c_n M_{mn} = R_m^{(n)}(0)/n!` with `R_m(z) = K_m (z+iτ)^m (1−iτz)^{−(m+½)}`; Taylor coefficients of `(z+c)^m` and `(1−cz)^{−a}` |
| `SemilocalBoostDiagonalClosedForm` | Leibniz evaluation; `∫ p_n² e^{its} dμ = (cosh t)^{−1/2} Σ_{l≤n} C(n,l)·((−(n+½)) choose l)·tanh^{2l} t`; real form `cosineDiagonalMoment_eq` for the response module's `m_n(δ)` |

**Main theorem** (`RHTower.MeixnerPollaczek.cosineDiagonalMoment_eq`): for every real `δ` and `n`,

    ∫ p_n(s)² cos(δ s) dμ(s) = (cosh δ)^{−1/2} · Σ_{l=0}^{n} C(n,l) · Ring.choose(−(n+½), l) · tanh^{2l} δ,

i.e. `(cosh δ)^{−1/2} ₂F₁(−n, n+½; 1; tanh² δ) = (cosh δ)^{−1/2} P_n^{(0,−1/2)}(1 − 2 tanh² δ)` (the
generalized binomial coefficient is `(−1)^l (n+½)_l / l!`).  Combined with
`hasDerivAt_cosineModeJacobiRadius` (`SemilocalCosineModeFirstOrderResponse`), the first-order
response of the Jacobi radii to `1 + 2ε cos(δ s)` is now a fully explicit Lean expression.

**Method.**  No two-variable power series: the closed form is expanded in `w` for fixed real `z`,
compared by real-axis uniqueness with the term-by-term integral; the resulting row function is
expanded in `z` by Cauchy's Taylor theorem and compared again; the coefficients are evaluated by
the Leibniz rule.  Tilt integrability uses the corpus's sharp majorant
`semilocalArchimedeanGammaDensity_le_exponentialMajorant` (rate `π/2`).

**Remaining for the Route J profile `Φ` (MUST-149).**  The Mehler–Heine limit of
`S_n(τ) := Σ_l C(n,l) Ring.choose(−(n+½), l) τ^{2l}` at `τ = tanh(log p)`, `n = xp`:
`S_n → (−1)^n (πn)^{−1/2} cos(4x)`; then the residual jet `residualJetOf` with
`m_n = (cosh log p)^{−1/2} S_n` gives `Φ(x) = 4√(2/π)[√x cos 4x − 8x^{3/2} sin 4x]`.
