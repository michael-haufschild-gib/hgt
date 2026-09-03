# Route J: first-order response of the semilocal Jacobi data to a cosine mode (Lean)

**Stage:** 3 (formalized).  **Module:** `formal/GaloisForLFunctions/RHTower/SemilocalCosineModeFirstOrderResponse.lean`
(namespace `RHTower.CosineModeResponse`, wired into `RHTower.lean` after
`SemilocalProlateFirstEulerCriticalJet`; axioms `[propext, Classical.choice, Quot.sound]`; lint clean).

**Statement.**  Let `μ` be the archimedean Gamma measure `|Γ(1/4 + is/2)|² ds` (normalized), `p_n`
its orthonormal Jacobi polynomials with radii `r_n = √((n+½)(n+1))`, and `δ, ε ∈ ℝ`.  Define the
diagonal cosine moment `m_n(δ) = ∫ p_n² cos(δ s) dμ` (`cosineDiagonalMoment`) and the cosine tangent
`T_n(δ)_{ij} = 2 ∫ p_i p_j cos(δ s) dμ` (`cosineModeTangent`).

1. `cosineModeGram_eq`: the Gram matrix of `p_0..p_n` for the measure `(1 + 2ε cos(δ s)) μ` is
   `1 + ε T_n(δ)`.
2. `hasDerivAt_cosineModeDeterminantPath`: its determinant has jet `tr T_n(δ) = 2 Σ_{j ≤ n} m_j(δ)`
   at `ε = 0`.
3. General transfer with an arbitrary jet sequence `J`: `hasDerivAt_squaredJacobiRadiusPathOf_jet`,
   `hasDerivAt_jacobiRadiusPathOf_jet`, `hasDerivAt_criticalResidualPathOf_jet` — the Hankel
   quotient `r_n² Δ_{n−1}Δ_{n+1}/Δ_n²` has jet `r_n² (J_{n−1} + J_{n+1} − 2J_n)`, the radius has jet
   that over `2 r_n`, and the Route J four-radius residual has the jet `residualJetOf J n`.  (The
   corpus's first-Euler transfer is the special case `J = normalizedHankelDeterminantJet`.)
4. **First-order response** (`hasDerivAt_cosineModeJacobiRadius`):
   `[ε] a_n(ε) = r_n (m_{n+1}(δ) − m_n(δ))`; and `hasDerivAt_cosineModeCriticalResidual` for the residual.
5. `hasDerivAt_beatModeJacobiRadius`: the instance `δ = log(p₂/p₁)` (`beatFrequency`), the two-prime
   beat mode of Connes–Consani–Moscovici's semilocal measure; the one-prime harmonics are the
   instances `δ = d log p`, `ε = q^{d/2}/(1 − q)`.

**Why it matters.**  The computations in
`2-fully-proven/computations/routej-semilocal-scale/README.md` (§3.5–3.7) show that (a) the two-prime
cross term is exactly this response at the beat frequency, (b) the one-prime deviation is this
response at `δ = log p` to 0.1 %, and (c) with the closed form
`m_n(t) = (cosh t)^{−1/2} P_n^{(0,−1/2)}(1 − 2 tanh² t)` (paper theorem from the Meixner–Pollaczek
generating function, verified numerically) the residual jet of item 4 has the Mehler–Heine limit
`Φ(x) = 4√(2/π)[√x cos 4x − 8 x^{3/2} sin 4x]`, the universal Route J profile.

**Open (paper-proved, not yet Lean):** the generating function
`Σ c_m c_n M_{mn}(t) w^m z^n = (cosh t)^{−1/2}(1 − wz − i tanh t (w+z))^{−1/2}` and the diagonal
closed form; the Mehler–Heine limit of `P_n^{(−1/2,0)}`.
