# 89 — The real open core: the on-line slice of the window

Steps 1–2 (the finite Hardy identity and the off-line χ-decay) are now Lean theorems. They are
infrastructure. This doc names — precisely, not vaguely — the single place where a **significant ×
novel** result must come from, and lays out the two honest routes into it.

## The object

On the critical line the certificate carrier is a **finite Hardy function**
(HardyCarrier.lean, PROVEN):

    gN(½+iτ) = 2 e^{iφ(τ)/2} · |D(τ)| · cos(α(τ) − φ(τ)/2),   D := dirichletPoly N(½+iτ),

with `α = arg D`, `φ = arg zetaChi(½+iτ)`, `|zetaChi| = 1`. So the real Hardy carrier

    H_N(τ) := e^{−iφ/2} gN(½+iτ) = 2 |D(τ)| cos(α(τ) − φ(τ)/2)   ∈ ℝ,

and **‖gN(½+iτ)‖ = |H_N(τ)|** (PROVEN). The on-line zeros of gN are exactly the sign changes of H_N.

The circle/pinning gates need a floor `‖gN‖ > ε` on a window around a hypothetical off-line zero ρ₀.
Off the line the χ-factor decays (`‖zetaChi‖<1`, PROVEN) and one AFE half dominates → a genuine floor
(step 2). **But every window that reaches the critical line contains a slice of the line, and on that
slice H_N genuinely vanishes** — those are ξ's line-zeros, which RH *requires* to be there. This is the
open core: the floor cannot be gotten on the on-line slice by domination; it needs the window's on-line
segment to sit *between* two consecutive zeros of H_N.

The floor route did not remove the RH difficulty; it **relocated** it, exactly, to: *control the zeros
of the finite Hardy function H_N on the critical line.*

## Route (a) — zero-spacing / gap control [SEARCH-GRADE]

Place a window of on-line radius `R` between consecutive zeros of H_N. Zeros occur where
`α − φ/2 ≡ π/2 (mod π)`; consecutive zeros are spaced by `≈ π / (½φ′ + α′-fluctuation)`. The
archimedean phase velocity is `φ′(τ) ≈ log(τ/2π)` (the Riemann–Siegel theta derivative — the same
`re_digamma_vertical_bound_uncond` now supplies it unconditionally), so the **mean gap is `≈ 2π/log τ`**
— the mean spacing of ξ zeros. A window survives if `R < min-gap` over its height range.

The obstruction is the **lower** bound on the gap: small gaps between Hardy zeros. That is
Montgomery-pair-correlation / simple-zeros territory — `[OPEN CORE]`, and it does **not** pass the
novelty gate: a competent search produces exactly this framing (gap estimates, GUE spacing, no-small-gaps
conjectures). Route (a) is honest plumbing; it cannot be the contribution. Its *quantitative* input is
what step 4 (the anti-concentration → density lane) partially supplies: `|D|` is large at a positive
proportion of heights, so the amplitude factor of H_N is generically non-degenerate — but the `cos`
factor (the zeros) is untouched by any single-polynomial density argument.

## Route (b) — the monodromy weight-mismatch invariant [MOONSHOT — passes the novelty gate]

The lane's actual thesis. Frame the on-line slice not as an analytic gap problem but as a **monodromy**
problem. A hypothetical off-line zero ρ₀ is never alone: the completed ξ's two symmetries force the
**quadruple**

    Q(ρ₀) = { ρ₀,  1 − ρ₀,  ρ̄₀,  1 − ρ̄₀ }        (functional equation Λ(s)=Λ(1−s) × Schwarz ξ(s̄)=ξ̄(s)),

a genuine 4-point orbit off the line, degenerating to a **2-point** orbit `{ρ, ρ̄}` (and `1−ρ = ρ̄` when
`Re ρ = ½`) on the line. Attach to each zero the **local monodromy weight** — the winding class of the
Kummer/deck tower `RHLadder k` at that zero (ModulusHolography: the circle-average slope = the vanishing
order; the ℤ₂ tower assigns a parity). The claim to make precise:

> **[CONJECTURE — weight mismatch]** The total monodromy weight of `Q(ρ₀)`, summed with the tower's
> ℤ₂ grading, has a **parity that is even iff `Re ρ₀ = ½`**. The RH_{2^k} parity ladder + the
> defect-recurrence forces the global weight to be even; a genuinely off-line ρ₀ contributes the odd
> class, contradicting the forced parity.

Concretely, the **weight** is the `q62`-style transposition weight (weight-6 Rankin–Cohen / the seam
`∂_s`-vs-`{σ_p}` grading of `𝓜⁺`): the on-line quadruple is a *self-paired* configuration (ρ ↔ ρ̄ under
one symmetry, ρ ↔ 1−ρ under the other, and these coincide), so the two symmetry-transpositions commute
into an **even** permutation of Q; the off-line quadruple has them acting as a genuine **4-cycle** (odd).
This transposition-parity IS the "weight mismatch" — a monodromy invariant of the zero, not an analytic
size estimate.

Why (b) passes the novelty gate: it does **not** reduce to zero-density / gap / pair-correlation. It
bridges the zero-location question to the **deck-tower monodromy grading** already built here
(CoherentTower, ModulusHolography, ParityCounting, RHLadder) — an object outside the classical corpus of
RH methods. The mismatch is a *constraint* (the parity is fixed by the tower), not a *flow* — exactly the
lane's generative metaphor. This is where to spend the next real research, and it is the only part of
steps 1–4 that is a moonshot rather than infrastructure.

## The next generative move

Formalize the weight of a single zero as the tower's ℤ₂-class (already have
`xi_circleAverage_slope_eq_order`, `rhLadder_iff_...`), then the **parity of the symmetry-transposition
of `Q(ρ₀)`**, and test the conjecture on-line vs off-line: does the 4-cycle really force the odd class?
If yes, wire it against the forced-even ladder parity for the contradiction. This is a construction, not
a search — build the invariant, then attack it as false (is there an off-line configuration whose
transposition is secretly even? — the honest refutation test first).
