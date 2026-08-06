# The Landau route is pinned at κ = 1 under *polynomial* growth — and exactly how to break it

## The optimisation

Landau's lemma (`landau_logDeriv`, `RHTower/Sieve/LandauLemma.lean`) at radius `R` about `1 + it`:

    ζ'/ζ(s) = ∑_{ρ in the disc} 1/(s−ρ) + O( log M(R) / R ),   M(R) = max_{|z−(1+it)| ≤ R} |ζ(z)|.

Through de la Vallée Poussin (`dlvp_inequality`) this gives a region of width
`≍ 1 / (log M(R)/R)`.  Everything hinges on minimising `log M(R)/R` over `R`.

## Polynomial growth is useless — including Lindelöf

For any bound of the shape `|ζ(σ+it)| ≪ t^{θ(1−σ)}` (θ = 1/2 convexity, 1/3 subconvexity,
ε **Lindelöf**):

    log M(R) ≍ θ·R·log t   ⟹   log M(R)/R ≍ θ·log t,   **independent of R**,

and for `R ≲ 1/log t` (disc inside `σ ≥ 1 − 1/log t`, where `|ζ| ≪ log t`) it is
`≳ log t·loglog t` — worse.  So the width is `≍ 1/(θ log t)`: **κ = 1 exactly, for every θ**.
Even Lindelöf would improve only the constant.  In particular the corpus's own line bound
`norm_riemannZeta_line_rate_clean : ‖ζ(1+it)‖ ≪ log t/loglog t`
(`RHTower/Sieve/ZetaLineRate.lean`) cannot help: it lives on the line, the width depends on a disc,
and the only regime where it would dominate is the ruled-out `R ≲ 1/log t`.

## What DOES break it — the exponent `(1−σ)^{3/2}`

A **Vinogradov–Korobov**-shaped bound `|ζ(σ+it)| ≪ t^{A(1−σ)^{3/2}}·log^{2/3}t` is *not* of that
form, and it changes the optimisation completely:

    log M(R)/R ≍ A·R^{1/2}·log t + loglog t/R,
    minimised at R ≍ (loglog t/log t)^{2/3},
    giving log M(R)/R ≍ log^{2/3}t · loglog^{1/3}t,

i.e. width `≍ 1/(log^{2/3}t · loglog^{1/3}t)` — **κ = 2/3 < 1**, exactly the VK region, and exactly
what `mem:zero-free-region-exponent-is-the-mr-wall` needs for the corridor.

**So the Landau/DLVP machinery in the corpus is already the right frame.  The single missing input
is a growth bound sub-linear in `(1−σ)` in the exponent.**  The route to it is van der Corput's
`d`-th derivative test / Vinogradov's method.  Lead:
`arXiv:2407.02094` "Explicit van der Corput's d-th derivative estimate" — explicit constants
`A_d < 7.5`, `B_d < 5.8`, `C_d < 10.9` for `d ≥ 2`, correcting van der Corput's 1937 papers.

## The other elementary route is worse

Direct 3-4-1 in multiplicative form (`three_four_one_log_zeta_const`,
`RHTower/Sieve/ZetaThreeFourOne.lean`) plus segment transport needs a `ζ'` bound; Cauchy at radius
`1/log t` from `ζ ≪ log t` gives `ζ' ≪ log²t`, and optimising `δ` yields `1−β ≫ (log t)^{-9}` —
κ = 9, worse than the Landau route already gives.

## Do not attempt

Shrinking the Landau radius with the *existing* bounds; re-deriving the line growth bound (already
built); the direct 3-4-1 route; hoping subconvexity or Lindelöf rescues it.

## Do attempt

The `d`-th derivative test, then the `(1−σ)^{3/2}` growth bound, then feed it into the **existing**
`landau_logDeriv` + `dlvp_inequality` frame with `R ≍ (loglog t/log t)^{2/3}`.
