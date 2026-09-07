# Lag ratio law: sampling sets with `n_{j+1}/n_j → 1`

**Status:** conjecture, 2026-09-06. Companion of `integer-lag-law-notes.md` (MUST-250–255, CANNOT-328).

## Conjecture (ratio law)

For every infinite `N ⊆ ℕ` with `n_{j+1}/n_j → 1`: `sup_{n ∈ N} a_n < ∞ ⟹ RH`, where
`a_n = Φ(log n) = Σ_ρ n^{ρ−½}/(ρ(1−ρ))`.

Known cases: gaps `≤ √n · n^{o(1)}` (Lipschitz route, MUST-250), primes and prime powers (Landau with the
strip `Θ ≤ ¾`, MUST-251/254), `k`-th powers and every support with a ζ-like counting series (MUST-252/253).
Sets like `{⌊e^{√m}⌋}` (gaps `n/(2 log n)`, no usable counting series) are open.

## The attained case is elementary

If `Θ = sup Re ρ > ½` is attained, let `ρ_1, …, ρ_k` be the zeros with `Re ρ_j = Θ` (finitely many by the count
bound in any bounded region? no — the top line can carry infinitely many zeros; assume finitely many, or truncate by
height with the weights `w_ρ ≪ γ^{−2}` making the far top zeros negligible). Then
`a_n = n^{Θ−½} P(log n) + O(n^{Θ−½−δ})` with `P(L) = Σ_j 2|w_j| cos(γ_j L + φ_j)`, a real trigonometric polynomial
with positive coefficients, mean zero, not identically zero, hence `sup P > 0`, and by Bohr almost periodicity the
set `{L : P(L) > sup P / 2}` is relatively dense (Lean tool: `exists_fin_simultaneous_integer_approximation_quantitative`
gives the simultaneous translation numbers). Since `log n_{j+1} − log n_j → 0`, the log-image of `N` meets every long
interval, so `a_n ≥ (sup P / 2) n^{Θ−½} − O(n^{Θ−½−δ}) → ∞` along `N`.

## The non-attained case is where the conjecture lives (and where abstract configurations fail)

For abstract configurations (symmetric under `ρ ↦ ρ̄`, `ρ ↦ 1 − ρ`, local count `≪ log T`, weights `1/(ρ(1−ρ))`)
the ratio law is false. Sketch: take `β_j = Θ − 2^{−j}`, `γ_j = exp(4^j)`, weights `|w_j| ≍ γ_j^{−2}`. The
`j`-th quadruple dominates `Φ_Z(L)` on the window `L ∈ [L_j, L_{j+1}]` with `L_j ≍ 8^j`, with geometric domination
over the others, and there `Φ_Z(L) ≈ 2|w_j| e^{L(β_j−½)} cos(γ_j L + φ_j)`. The negative arcs of the two
dominant cosines have `n`-length `≍ n/γ_{j+1} ≫ 1` for `n = e^L ≥ e^{8^j} ≫ γ_{j+1} = e^{4^{j+1}}` (`j ≥ 3`), so one
can choose integers `n ∈ N` inside them with consecutive ratios `1 + O(1/γ_{j+1}) → 1`, and `Φ_Z ≤ O(1)` on `N`
while `Θ > ½`. Consequently:

- **CANNOT (analysis):** no configuration-free proof of the ratio law exists; any proof must use ζ-specific
  input — either that `Θ` is attained (open), or a bound on the frequencies of near-top zeros relative to their
  weights (a "spectral regularity"). The integer lag law's Lipschitz bound `|a_m − a_n| ≤ 8(m−n+1)(log m+2)²/√n`
  is exactly such an input (it fails for the configuration above), but it is useless for gaps `> √n`.
- The Landau route circumvents the problem for supports with a counting series, because the ray argument uses a
  single pole and never needs the top to be attained.

## Verdict

`SURVIVES PRELIMINARY ATTACK` for ζ (no known counterexample; the abstract obstruction only shows what a proof
must use). Not a producer: RH-equivalent receiver. Lean target for the attained case: Bohr relative density of
positivity sets of trigonometric polynomials with positive coefficients (from the corpus simultaneous
approximation lemma); not built.

## Update 2026-09-06: attained case in Lean

`LagRatioLawAttained.exists_lag_gt_of_attainedTop_of_logDense` (STATUS MUST-256) proves the attained case for every
log-dense `N` (ratio → 1 suffices), with the mean-value route above (no Kronecker/Dirichlet approximation needed: the
window mean square of a real trigonometric polynomial with the conjugation symmetry is bounded below by half the sum
of squared moduli, and positivity is extracted from mean ≈ 0 and mean square ≥ m). The non-attained case remains the
open core; the abstract obstruction stands.

## Update 2026-09-08: the Weil-form analogue of the attained case is Lean

`ConstrainedWeilApertureWindowMean.exists_aperture_twistedOddTest_neg_of_attainedTop` (STATUS MUST-259):
if the top excess `Θ` is attained at `ρ₀ = ½ ± Θ + iγ₀`, the constrained Weil form of `cos(γ₀x)ψ_a` is
`≤ −c e^{2Θa}` at some aperture of every window `[A, A + L₀]`, `A ≥ ½`. The mechanism is the aperture
analogue of the Bohr window mean used here for integers: every ray term is an exact exponential polynomial
in `a` (plateau profile), the constant term isolates the top copies, and everything else averages out at
rate `2D/L`. The non-attained case is open in both settings, for the same reason (no constant term to isolate).

## Bohr-mean conjecture for the twisted plateau family (2026-09-08, paper)

**Conjecture.** For every centre `γ`, `sup_L |(1/L)∫_{½}^{½+L} Re Q(cos(γx)ψ_a) da| < ∞` if and only if RH.
Under RH the mean converges to the Parseval sum `M(γ) = Σ_q (Σ_j |C_{q,j}|²)/(4 z_q²) > 0` over the on-line
copies (each ray term is `(Im(A_q+A'_q))²/(4z_q²)` with `A_q + A'_q` an exponential polynomial with purely
imaginary exponents; Bohr–Parseval for its window mean). If RH fails with an attained top, MUST-259 gives
means `≍ −e^{2ΘL}`. `[OPEN CORE]`: the non-attained case, which needs the Laplace transform of `Q` in the
aperture (poles at `2c₁(q) = 2θ_q + 2i(Re z_q − γ)`, isolated because zero ordinates are locally finite;
residue `−(1/4)κ(c₁)²/z_q²`, nonzero for generic `γ` since `κ` is a nonzero entire function of the frequency)
and the corpus Widder–Landau engine transported from the test parameter to the aperture. Verdict: BRIDGE
(same mechanism class as Bombieri–Yoshida with a weaker hypothesis on one explicit family); not pursued as a
build because it adds a receiver, not a source sign. See STATUS CANNOT-331.

## Quantitative Bombieri–Yoshida: the plan (2026-09-08)

Target: `(∀ t ≥ 0, −C e^{εt} ≤ Re Φ_h(t)) → ∀ q, |Im z_q| ≤ ε` for the polar-weighted screw divisor
`Φ_h = Σ' M(z_q)²(1 − cos(z_q t))/z_q²`, and the transfer `μ₀(A) ≥ −Ce^{εA} ∀A ⟹ Φ_h(t) ≥ −C'e^{εt}` through
the two-bump sequence (its aperture is `≈ t + 2h + 2`, so the constant `1` rather than `½` appears).
Mechanism: `Φ_h(t) + C e^{εt} ≥ 0`; its Laplace transform is the atom series `+ C/(s − ε)`; the Landau
measure `e^{−rt}(Φ_h + Ce^{εt})dt` is positive; the halving argument of `WeightedScrewLandauEngine`
(`weightedScrewMomentsAbove_half`) descends the abscissa of exponential moments from `½` towards the
first real singularity, now `ε` instead of `0`; the Laplace transform is then analytic on `Re s > ε`, equals
the continuation on the punctured half-plane `{Re s > ε} ∖ spectralPoleSet`, and the pole contradiction of
`WeightedScrewPoleContradiction` applies to any spectral pole `s₀ = i z_q` with `Re s₀ = −Im z_q > ε`
(and to `−i z_q` for the other sign). Lean plan: generalise the engine by a threshold parameter `σ₀`
(`WeightedScrewMomentsAbove W b` for `b > σ₀`, halving `b ↦ (b + σ₀)/2`, continuation with the extra term
`C/(s − σ₀)`), ~1000 lines by transcription of the two modules. Consequence: `RH ⟺ ∀ ε > 0, ∃ C, ∀ A,
μ₀(A) ≥ −Ce^{εA}` (sub-exponential negativity criterion); with MUST-260 the growth rate of `−μ₀` is exactly
`2Θ` when `Θ` is attained and lies in `[2Θ, 2Θ]`… i.e. equals `2Θ` in general modulo the factor `½`/`1`
of the two-bump aperture accounting.
