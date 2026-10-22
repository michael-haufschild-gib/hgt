# Route J (semilocal Jacobi matrix) — working log

Route-specific working log for the semilocal one-prime / finite-`S` Jacobi-matrix programme
(Connes–Consani–Moscovici semilocal measure, archimedean Jacobi radii, Euler deformations).
Moved here on 2026-09-04 from `universal-law-field/STATUS.md`, where it did not belong: STATUS.md
records only what the solution object MUST be / do / have and what it CANNOT be / do / have.

The labels `Fnnn` / `MUST-nnn` below are historical (they were STATUS.md ledger numbers at the time
of writing; some numbers were also used by other agents for unrelated facts).  In this log a
`MUST-nnn` entry is a **route task**, not a constraint on the object.  New entries use `RJ-T<n>` for
tasks and `RJ-<n>` for results.

Related: cards in `3-formalized/` (`route-j-*.md`, `semilocal-*.md`), numerics and README in
`2-fully-proven/computations/routej-semilocal-scale/`.

---

## 2026-09-03 (xiii) — Route J: the critical degree is `n ≈ p`
F410 — Computation (`computations/routej-semilocal-scale/`): for the one-prime semilocal Jacobi
matrix of Connes–Consani–Moscovici, the exact Euler deformation of the four-radius residual is
order one at degree `n ≈ p` (`qn ≈ 1`), not at the first-jet scale `p²` nor the third-jet scale
`p^{6/5}`; the corpus's Lean-proved jets are confirmed in their regimes and overtaken beyond.
MUST-146 — Route J survivor target 2 is settled numerically: the fixed Euler orders do not share
a scale; the natural variable of the finite-`q` semilocal Jacobi problem is `x = n/p`. Analytic
work on the one-prime boundary layer should be organized around `qn`.
F411 — Computation: Route J scaling law `D_k(q) = q^{1/2}Φ(qn) + O(q)`, universal profile `Φ`
with zeros `0.159, 0.823, 1.586, 2.369` and extrema `−10.0, +35.4, −72.5`; odd Lean-proved jets
are its Taylor coefficients, even jets are subleading corrections. Order-one threshold at
`n ~ p^{6/5}` (third-jet scale), refining F410.
F412 — Computation: the profile `Φ` is a modulated sinusoid, `Φ(x) ≈ −26 x^{1.45} sin(4.06x − 0.19)`
(rms 0.4 %), so the order-one degree is `n* ≈ p^{4/3}/8.8`; for two primes the cross term is the
linear response to the beat mode `2(p₁p₂)^{−1/2} cos(s log(p₂/p₁))` (correlation 1.0000) and
dominates the one-prime terms by a factor `~p`.
MUST-147 — The finite-`S` semilocal Jacobi problem is governed by the pairwise beat frequencies
`log(p_i/p_j)`, not by one-prime boundary layers; Route J survivor target 3 is settled
numerically, and the analytic target is the first-order response `H(n, δ)` of the
Meixner–Pollaczek Jacobi matrix to `1 + 2ε cos(δ s)`. The frequency `4` of `Φ` in `n/p` is
unexplained.
F413 — Lean (`SemilocalCosineModeFirstOrderResponse.lean`): for the archimedean semilocal Jacobi
matrix, the Gram matrix of the measure `(1 + 2ε cos(δ s)) μ` in the orthonormal basis is
`1 + ε T_n(δ)`, the normalized Hankel determinant has jet `2 Σ_{j≤n} m_j(δ)`
(`m_j(δ) = ∫ p_j² cos(δ s) dμ`), and the Jacobi radii respond at first order by
`[ε] a_n = r_n (m_{n+1}(δ) − m_n(δ))`, the Route J residual by `residualJetOf`.  The transfer
theorems are stated for an arbitrary jet sequence and contain the first-Euler jet as a special
case.  Beat-mode instance `δ = log(p₂/p₁)` recorded.
F414 — Computation: the exact one-prime deviation of the Route J residual equals the first-order
response to the single mode `cos(s log p)` of amplitude `p^{−1/2}` to 0.1–0.4 % (correlation
≥ 0.999996 for `p = 211..1511`, `n ≤ 2.6 p`); higher harmonics and orders are `O(q)`.
F415 — Paper theorem (numerically verified to `10⁻⁹`): generating function of all boost matrix
elements `Σ c_m c_n ⟨p_m, e^{its} p_n⟩ w^m z^n = (cosh t)^{−1/2}(1 − wz − i tanh t (w+z))^{−1/2}`,
diagonal `m_n(t) = (cosh t)^{−1/2} P_n^{(0,−1/2)}(1 − 2 tanh² t)`.  Mehler–Heine at rapidity
`log p` gives `m_n ≈ (−1)^n √(2/(πpn)) cos(4n/p)`, hence
`Φ(x) = 4√(2/π)[√x cos 4x − 8 x^{3/2} sin 4x]` (1 % rms against the data, extrema to three digits,
exact Lean jets `c₁ = 4√(2/π)`, `c₃ = −160√(2/π)` as Taylor coefficients, prediction
`c₅ = 384√(2/π)`, threshold `n* = p^{4/3}/8.66`).  The frequency `4` of MUST-147 is the
Mehler–Heine angle `2 sech(log p)`.
MUST-148 — Formalize F415: the Meixner–Pollaczek generating function of the archimedean Jacobi
polynomials, the two-variable boost generating function, the diagonal closed form, and the
Mehler–Heine limit of `P_n^{(−1/2,0)}`; then the Route J profile `Φ` becomes a Lean theorem
through F413.  Route J's boundary question is closed on paper: there is no prime-scale boundary
layer, only the Bessel regime of the SU(1,1) boost elements.
F416 — Lean (`SemilocalJacobiMeixnerPollaczekGeneratingFunction.lean`): the corpus's archimedean
semilocal Jacobi polynomials are Meixner–Pollaczek: `Σ c_n p_n(s) w^n = (1 − iw)^{−1/4+is/2}(1 + iw)^{−1/4−is/2}`
for `‖w‖ < 1`, real form `(1 + w²)^{−1/4} exp(s arctan w)`; proved through the ODE
`(1 + w²)G′ = (s − w/2)G`, its `n`-fold derivative recurrence at `0`, and Cauchy's Taylor theorem.
First brick of MUST-148; remaining bricks listed in
`3-formalized/semilocal-jacobi-meixner-pollaczek-generating-function-lean.md`.
F417 — Lean (`SemilocalGammaComplexRapidityCharacteristic`): the archimedean characteristic
function continues to `∫ e^{zs} dμ = (cos z)^{−1/2}` on the strip `|Re z| < π/2` (Mathlib
`complexMGF` analyticity + identity theorem, corpus majorant of rate `π/2`); two-variable boost
integral `∫ G_s(w)G_s(z)e^{its} dμ` in cosine form.
F418 — Lean (`ScalarPowerSeriesUniqueness`, `SemilocalJacobiCoefficientCauchyBound`,
`SemilocalBoostCoefficientInterchange`): coefficient uniqueness on discs and on the real diameter,
Taylor coefficients, complex binomial series; Cauchy bound `|c_m p_m(s)| ≤ (3/4)^{−1/2} e^{|s|/2} 4^m`;
term-by-term integration of the generating function against `e^{|s|/2}`-integrable weights.
F419 — Lean (`SemilocalBoostGeneratingFunctionClosedForm`): the two-variable boost generating
function `∫ G_s(w)G_s(z)e^{its} dμ = (cosh t)^{−1/2}(1 − wz − i tanh t (w+z))^{−1/2}` (real `|w|,|z| < 1`)
and its `w`-coefficients `(cosh t)^{−1/2}(1−iτz)^{−1/2}(−½ choose m)(−q(z))^m`.
F420 — Lean (`SemilocalBoostRowTaylorIdentification`, `SemilocalBoostDiagonalClosedForm`): the boost
matrix entries `M_{mn}(t) = ∫ p_m p_n e^{its} dμ` are the Taylor coefficients of
`K_m (z+iτ)^m (1−iτz)^{−(m+½)}`; diagonal closed form
`∫ p_n² e^{its} dμ = (cosh t)^{−1/2} Σ_{l≤n} C(n,l)((−(n+½)) choose l) tanh^{2l} t`, i.e.
`(cosh t)^{−1/2} P_n^{(0,−1/2)}(1 − 2tanh² t)`; real form `cosineDiagonalMoment_eq` for the response
module.  F415's paper theorem is Lean.  MUST-148 items (i)–(iv) closed.
MUST-149 — Mehler–Heine limit of `S_n(τ) = Σ_l C(n,l) Ring.choose(−(n+½), l) τ^{2l}` at
`τ = tanh(log p)`, `n = xp`: `S_n ≈ (−1)^n (πn)^{−1/2} cos(4x)`; then the residual jet
`residualJetOf` gives the Route J profile `Φ(x) = 4√(2/π)[√x cos 4x − 8x^{3/2} sin 4x]` in Lean.
Card: `3-formalized/semilocal-boost-diagonal-closed-form-lean.md`.
F421 — Lean (`ScaledTerminatingHypergeometricLimit`): the Mehler–Heine mechanism for terminating
hypergeometric sums: `₂F₁(−n_j, n_j+d; c; σ_j²) → Σ_l (−1)^l w^{2l}/((c)_l l!)` when `n_j → ∞`,
`n_j σ_j → w` (Tannery), with the limits `cos 2w` (`c = ½`) and `sin 2w / 2w` (`c = 3/2`).
F422 — Lean (`SemilocalDiagonalPfaffTransformation`, `SemilocalBoostContiguousRelations`): the Pfaff
transformation of the diagonal cosine moments to the bounded `σ`-form
`m_n(δ) = (cosh δ)^{-1/2}(−1)^n C_n ₂F₁(−n, n+½; ½; sech² δ)` (Chu–Vandermonde), and the two
contiguous relations `(2n+1)F_{n+1} + 2(n+1)F_n = (4n+3)(1−x)H_n`, `H_{n+1} − H_n = −(4n+5)xK_n`.
F423 — Lean (`RouteJResidualFirstDifferenceForm`): the Route J residual jet is exactly
`(cosh δ)^{-1/2}[r_{2k}r_{2k+1}ΔQ_{2k} + 2Δ(r²Q)_{2k+1} + r_{2k+2}r_{2k+3}ΔQ_{2k+2}]` with the smooth
`Q_n = C_n(4n+3)(1−x)H_n/(2(n+1))`, and the differences are closed forms in `H_n, K_n` with a factor
`x = sech² δ` in front of `K_n`.
F424 — Lean (`RouteJScalingProfileLimits`, `RouteJScalingProfile`, `RouteJResidualNormalizationLimit`):
**the Route J profile is a theorem**: along `p_j → ∞`, `2k_j/p_j → X > 0`,
`residualJetOf (cosineModeDeterminantJet (log p_j)) k_j → Φ(X) = 4√(2/π)[√X cos 4X − 8X^{3/2} sin 4X]`,
and `R_k(0) → 1`, so the relative first-order deviation has the same limit.  MUST-149 closed.  Card:
`3-formalized/route-j-scaling-profile-lean.md`.
MUST-150 — The beat-mode profile: the two-prime cross term is the first-order response at fixed
`δ = log(p₂/p₁)` (report §3.5); its large-`n` law needs the Darboux (fixed-argument) asymptotics of
`₂F₁(−n, n+½; ½; sech² δ)`, i.e. the oscillation `cos(n θ_δ + φ)` with `θ_δ = 2 arcsin(sech δ)`; the
Tannery route does not apply (the terms are not individually bounded), so this is a new mechanism.
F551 — Lean (`LegendreGeneratingFunction`, `LegendreConvolution`, `CentralBinomialAbelBounds`,
`LegendreHalfSumEstimate`, `LegendreLaplaceHeine`): Legendre polynomials built explicitly (Mathlib has
none), their generating function, the exact convolution `P_N(cos φ) = Σ C_k C_{N−k} cos((N−2k)φ)`, and
**Laplace–Heine with an explicit constant**: `|P_N(cos φ) − 2C_N(2 sin φ)^{-1/2}cos((N+½)φ − π/4)| ≤
400/(N sin φ)` for `0 < φ < π`, `N ≥ 8` (Abel summation + Abel's limit theorem, no contour).
F552 — Lean (`SemilocalDiagonalLegendre`): `∫p_n² cos(δs)dμ = (cosh δ)^{-1/2} P_{2n}(sech δ)`; the Route
J residual jet is an exact combination of `P_{4k}, …, P_{4k+8}(sech δ)`.
F553 — Lean (`RouteJBeatModeProfile`): **the beat-mode law is a theorem**: for fixed `δ > 0`,
`residualJetOf (cosineModeDeterminantJet δ) k / k^{3/2} − 32√(2/π) σ^{3/2} τ^{5/2}
sin((4k+9/2)φ − π/4) → 0`, `σ = sech δ`, `τ = tanh δ`, `φ = arccos σ`.  The Darboux mechanism of
MUST-150 is replaced by the convolution/Abel route.  MUST-150 closed.  Card:
`3-formalized/route-j-beat-mode-profile-lean.md`.
MUST-170 — The uniform two-term law: one asymptotic formula for the first-order residual response
`J_k(δ)` valid for all `δ ≥ δ₀`, `k → ∞`, whose leading term is the beat law and whose second term
(`k^{1/2}`, from the `O(k)` corrections of `r_{2k+a}r_{2k+b}` and the Szegő second Laplace–Heine term
`O(1/(N sin φ))`) reproduces the `√X cos 4X` term of `Φ` in the scaling regime `2k sech δ → X`.
Needs the second-order Laplace–Heine expansion with explicit error and the `1/k` expansion of the
radius products; then `Φ` and the beat law are two limits of a single theorem.
F554 — Lean (`LegendreShiftReduction`, `RouteJTwoIndexResidual`): **exact two-index form of the Route J
residual**: `J_k(δ) = (cosh δ)^{-1/2}[a(k,σ) P_{4k+3}(σ) + b(k,σ) P_{4k+4}(σ)]` with explicit rational
coefficients (`a = R₁a₁ + R₂a₂ + a₀`, `R₁ = r_{2k}r_{2k+1}`, …), obtained by eliminating
`P_{4k}, P_{4k+2}, P_{4k+6}, P_{4k+8}` through the three-term recurrence; all cancellations of the
five-term form (a third difference and a `(1,2,1)` smoothing) are performed algebraically.
F555 — Lean (`RouteJUniformLaw`): **the uniform law**: for all `δ > 0`, `k ≥ 2`,
`|J_k(δ) − M_k(δ)| ≤ (cosh δ)^{-1/2}(|a| + |b|)·400/(sin φ·(4k+3))` with the closed-form main term
`M_k(δ) = (cosh δ)^{-1/2}·2(2 sin φ)^{-1/2}[a C_{4k+3} cos θ_{k,3} + b C_{4k+4} cos θ_{k,4}]`.  The
second-order Laplace–Heine term is not needed: the exact rewriting removes the cancellation, so the
owned first-order estimate with constant 400 is uniform.
F556 — Lean (`RouteJUniformLawCoefficients`, `RouteJUniformLawLimits`): `a/k² → 64σ(1−σ²)`,
`b/k² → −64σ²(1−σ²)` (fixed σ); `a/k → 64X`, `b/k → 8` (scaling); **both limits from one theorem**:
`tendsto_beatMode_profile_of_uniform` (beat law) and `tendsto_residual_profile_of_uniform` (`Φ`)
are corollaries of F555.  MUST-170 closed.  Card: `3-formalized/route-j-uniform-law-lean.md`.
MUST-171 — The bilinear (ε₁ε₂) response.  The two-prime cross term of the semilocal measure is
`ε₁ε₂[J_k(log(p₂/p₁)) + J_k(log(p₁p₂))]` (first-order responses to the difference and sum modes of
the product of Euler factors) plus the *bilinear second-order response* of the Jacobi radii to two
separate modes, which first-order theory does not see.  Compute it (the second-order Christoffel
variation of the recurrence coefficients under `w ↦ w(1+2ε₁cos δ₁s)(1+2ε₂cos δ₂s)`), prove the
structure of the ε₁ε₂ coefficient, and quantify its size against the beat-law term
`32√(2/π)k^{3/2}σ^{3/2}τ^{5/2}`; report §3.5 suggests it is subleading.
F559 — Lean (`SemilocalTwoModeBilinearResponse`): **the bilinear response of the semilocal Hankel
determinants**: for the two-mode weight `(1+2ε₁cos δ₁s)(1+2ε₂cos δ₂s)`, the Gram matrix is
`1 + ε₁T(δ₁) + ε₂T(δ₂) + ε₁ε₂(T(δ₁+δ₂) + T(δ₁−δ₂))` and `∂₁∂₂ log D_n|₀ = J_{δ₁+δ₂}(n) + J_{δ₁−δ₂}(n)
− tr(T(δ₁)T(δ₂))` (`deriv_deriv_log_twoModeDeterminant`), an iterated `deriv` of a genuine
two-parameter determinant family.  The product-mode first-order response cancels exactly against
the diagonal part of the second-order term (covariance of linear statistics, `tr(Kf₁(1−K)f₂K)`).
F560 — Lean (`SemilocalTwoModeRadiusResponse`): transfer through the Hankel quotient:
`∂₁∂₂ a_n²|₀ = r_n²(B_{n−1} + B_{n+1} − 2B_n) + [ε₁]a_n²[ε₂]a_n²/r_n²` (`deriv_deriv_twoModeSquaredRadius`).
Numerics (211, 421): the truncation defect `tr(T₁T₂)` is 17 % of the beat term at `n = 20` and 92 %
at `n = 150` at the determinant level, but smooth in `n`, so at the radius level the `ε₁ε₂` jet is
the beat-mode radius jet to 1–3 % — the mechanism of report §3.5.  MUST-171 closed (structure).
Card: `3-formalized/semilocal-two-mode-bilinear-response-lean.md`.
MUST-173 — The large-rapidity boost bound.  Prove `|M_{ij}(t)| ≤ (cosh t)^{-1/2} c_i c_j · K(i+j, e^{−t})`
with explicit `K → 1` for `i + j ≪ e^{t}` (the sharp form without `K` is false at small `t`; the
naive coefficient majorant is exponential; the route is the `tanh t = 1` factorization
`(1−iw)^{-1/2}(1−iz)^{-1/2}` of the boost kernel and a series in `1 − tanh t`), and deduce
`|ΔΔ tr(T(δ₁)T(δ₂))| ≤ C (cosh δ₁ cosh δ₂)^{-1/2} √n`, i.e. the two-prime cross term is the beat-mode
radius jet up to relative `O(ε√n)`, `ε = (p₁p₂)^{-1/2}`.  Then the one-prime `ε²` self-response
(harmonic `cos(2δs)` plus the variance term `tr(T(δ)²)`) with the same tools.
F566 — Lean (`SemilocalBoostEntryBound`): **separable expansion and large-rapidity bound of the boost
matrix elements**: `c_n M_{mn}(t) = (cosh t)^{-1/2} c_m Σ_k binom(m,k) σ^{2k} (iτ)^{m+n−2k} (k+½)_{n−k}/(n−k)!`
(binomial theorem for `z + iτ = σ²z + iτ(1−iτz)`, Taylor coefficients of shifted binomials,
power-series uniqueness) and `|M_{mn}(t)| ≤ (cosh t)^{-1/2} c_m c_n τ^{m+n} exp(2mn/sinh² t)`
(`norm_boostMatrixEntry_le`, equality at (0,0)).
F567 — Lean (`SemilocalTruncationDefectBound`): `T(δ)_{ij} = 2 Re M_{ij}(δ)`, entry bounds
`|T_{ij}| ≤ 2E(δ;i,j)`, the exact row increment of the truncation defect `tr(T₁T₂)` and
`|D_{n+1} − D_n| ≤ 8 Σ_{i≤n+1} E₁(i,n+1)E₂(i,n+1)`.
F568 — Lean (`abs_bilinearSquaredRadiusJet_sub_beat_le`): **the two-prime cross term at the
squared-radius level is the beat-mode jet up to an explicit error** built from
`E(δ; i,j) = (cosh δ)^{-1/2} c_i c_j exp(2ij/sinh²δ)` — for `δ_a = log p_a` a relative `O(εn)` with
`ε = (p₁p₂)^{-1/2}`, `n ≪ p`.  MUST-173 closed.  Card: `3-formalized/semilocal-boost-entry-bound-lean.md`.
MUST-176 — The one-prime second-order response.  The true Euler factor
`1/(1 − 2ε cos δs + ε²) = 1 + 2ε cos δs + ε²(2 cos 2δs + 1) + O(ε³)`, so `[ε²]` of the residual is the
first-order harmonic jet at `2δ` plus the *self*-bilinear term of `SemilocalTwoModeBilinearResponse`
at `δ₁ = δ₂ = δ` (`tr T(2δ) + tr T(0) − tr(T(δ)²)`, `T(0) = 2·1`, the variance of the linear statistic)
plus the quadratic term of the Hankel quotient.  Compute it, prove the exact structure with the
owned tools, and bound it with the boost bound: this decides whether the one-prime deviation
`√q Φ(qn)` is the whole story to `O(q)` or whether the variance term contributes at `O(q)`.
CANNOT-254 — POINH's strict `||T||<1` cannot be transported by a bounded unital channel: actual P-G98
completion is singular, `E_eps(T)=T(eps+T)^(-1) -> I` strongly while `||E_eps(T)-I||=1`.  The earlier
norm-gap landing used the wrong category.
F573 — Lean (`SemilocalOnePrimeSecondOrderResponse`): **the one-prime second-order response**:
`|1/(1−2εcos x+ε²) − (1 + 2εcos x + ε²(1+2cos 2x))| ≤ 60ε³`; for the quadratic weight the Gram matrix is
`1 + εT(δ) + ε²(1 + T(2δ))`, `(log D_n)''(0) = 2(n+1) + 2J_{2δ}(n) − tr(T(δ)²)`
(`deriv_deriv_log_eulerQuadraticDeterminant`) and `(a_n²)''(0) = r_n²(ΔΔ(log D)'' + (ΔΔJ_δ)²)`
(`deriv_deriv_eulerQuadraticSquaredRadius`): `[ε²]a_n² = r_n²(ΔΔJ_{2δ} − ½ΔΔ tr(T(δ)²) + ½(ΔΔJ_δ)²)`.
F574 — Lean (`abs_onePrimeSecondOrder_le`): `|[ε²]a² − [ε]a²|_{2δ}| ≤ r²(4ΣE² + 4ΣE² + 2(E+E)²)` with the
boost bound `E`: for `δ = log p` the second-order term of the one-prime deviation is `O(q²)` against
the first-order `O(q)` — **the variance term does not contribute at O(q); `√qΦ(qn) + O(q)` is
first-order in the Euler mode to `O(q²)`**.  Numerics: formula vs the true Euler weight to `10⁻⁷`;
second/first `= 2·10⁻³` at `p = 211`.  MUST-176 closed.  Card:
`3-formalized/semilocal-one-prime-second-order-lean.md`.
MUST-178 — The finite-`S` second-order assembly.  For `S = {p₁,…,p_k}` with the polynomial weight
`∏_a (1 + 2ε_a cos δ_a s + ε_a²(1 + 2cos 2δ_a s))`, prove the exact second-order expansion of the
squared radii, `[ε_a²]` = the one-prime jets (F573), `[ε_aε_b]` = the bilinear jets
(`deriv_deriv_twoModeSquaredRadius`), no other second-order terms (the general multi-parameter
`log det` Hessian `tr T_{ab} − tr(T_aT_b)`), and with the boost bounds the size hierarchy: one-prime
`O(q_a)`, cross `O(√(q_aq_b))·[beat jet]`, second-order self `O(q_a²)`, uniformly for `n ≪ min p`.
Then transfer the `60ε³` agreement to the true Euler product (Lipschitz `det` near the identity).
F582 — Lean (`SemilocalQuadraticPathSecondOrder`, `SemilocalFinitePrimeSecondOrder`): **the finite-`S`
second-order assembly**: along the ray `ε = tv` the degree-two Gram matrix is `1 + tM₁ + t²M₂`
(`M₁ = Σv_aT(δ_a)`, `M₂ = ½ΣΣ v_av_b(T(δ_a+δ_b)+T(δ_a−δ_b)) + ½Σ v_a²T(2δ_a)`), the log-det second
derivative is the quadratic form `Σ_{a,b}v_av_bB_{ab} + Σ_a v_a²J_{2δ_a}` in the bilinear jets, and at the
squared-radius level `(a_n²)'' = Σ_a v_a²·[one-prime jet]_a + Σ_{a≠b} v_av_b·[bilinear jet]_{ab}`
(`deriv_deriv_raySquaredRadius_assembly`, diagonal identity `bilinearSquaredRadiusJet_diag_add_harmonic`):
no three-body term at second order; every piece carries its boost-bound estimate.
F583 — Lean (`abs_prod_sub_quadratic_le`): `|∏(1 + tx_a + t²y_a) − (1 + tΣx + t²(Σy + ½((Σx)² − Σx²)))|
≤ |t|³ ∏(1+w_a)(1+Σw_a)³`, `w_a = |x_a|+|y_a|`, `|t| ≤ 1` — the finite Euler product agrees with its
quadratic truncation to third order at the weight level.  Numerics (101, 211, 307): quadratic form vs
the true product to `10⁻⁷`, first+second order vs exact to `10⁻⁵`, pairwise beat terms dominant.
MUST-178 closed.  Card: `3-formalized/semilocal-finite-prime-second-order-lean.md`.
MUST-180 — The determinant-level Taylor remainder.  Transfer the weight-level third-order agreement
(`60ε³` per Euler factor, `abs_prod_sub_quadratic_le` for the product) to the Hankel quotient: for
the true Euler product, `|a_n²(v) − (r_n² + (a_n²)'(0) + ½(a_n²)''(0))| ≤ C_n · (Σ_a v_a)³` with
explicit `C_n` (entrywise Gram bound via Cauchy–Schwarz, Lipschitz `det` on a neighbourhood of the
identity, the quotient `Δ_{n−1}Δ_{n+1}/Δ_n²`).  With it the second-order theory of the finite-`S`
semilocal residual becomes a theorem with remainder, and the order-one threshold `n ~ p^{4/3}` can be
attacked as the failure of the remainder bound.
F589 — Lean (`MatrixEntryNormLogDetRemainder`): **the determinant-level Taylor remainder**: for a real
matrix with `ℓ¹` entry norm `‖N‖₁ < 1`, `|log det(1+N) − tr N + ½ tr N²| ≤ d(d+1)‖N‖₁³/(1−‖N‖₁)²`
(`abs_log_det_one_add_sub_jet_le`; Neumann bound `‖(1+N)⁻¹‖₁ ≤ d/(1−‖N‖₁)`, `det(1+N) > 0`, two
mean-value estimates along `1 + tN`), and the decomposition form for `N = M₁ + M₂ + E`
(`abs_log_det_sub_secondOrderJet_le`).
F590 — Lean (`SemilocalEulerProductLogDetRemainder`): for the **true** Euler product
`W = ∏(1 − 2ε_a cos δ_a s + ε_a²)⁻¹` (`ε_a ≤ 1/6`, `V = Σε_a ≤ 1/4`): weight-level cubic bound
`|W − (1 + A + B)| ≤ (3/2)^k 60Σε³ + 12800V³` (telescoping product + cubic quadratic-truncation lemma
`|∏(1+x+y) − trunc| ≤ 200(Σ(|x|+√|y|))³`), Gram entry bounds from orthonormality, and
**`abs_log_det_eulerProductGram_sub_jet_le`**: `log det G_n(W) = Σε_aJ_{δ_a} + ½(ΣΣ ε_aε_bB_{ab} +
Σε_a²J_{2δ_a}) + O(V³)` with an explicit constant, valid for `(n+1)²(2V + 3V² + ρ) < 1`; radius level
`|log(a²_{n+1}/r²_{n+1}) − ΔΔ jet| ≤ K_n + K_{n+2} + 2K_{n+1}` (`abs_log_eulerProductSquaredRadius_sub_jet_le`).
Numerics (101, 211, 307): remainder ratio `≈ 8` under `ε → ε/2`.  MUST-180 closed.  Card:
`3-formalized/semilocal-euler-product-logdet-remainder-lean.md`.
MUST-182 — The `n`-uniform remainder and the order-one threshold.  The `ℓ¹` entry norm costs `(n+1)²`
(true `‖N‖_op ≈ 0.16` vs `‖N‖₁ ≈ 1.1` at `n = 10`).  Prove `‖G_W − 1‖_op ≤ sup_s |W(s) − 1| ≤ 3V`
by the quadratic form `⟨(G_W − 1)u, u⟩ = ∫(W − 1)|Σu_ip_i|²` in the orthonormal basis (symmetric
matrix: operator norm = sup of the quadratic form), redo the Neumann and trace estimates with
`|tr A| ≤ (n+1)‖A‖_op`, so the smallness condition becomes `3V < 1` independent of `n` and the
remainder `(n+1)·O(V³)`.  Then locate the order-one threshold `n ~ p^{4/3}` (fine.log) as the first
`n` at which the second-order jet's own size reaches the remainder — the first analytic handle on the
threshold law.
