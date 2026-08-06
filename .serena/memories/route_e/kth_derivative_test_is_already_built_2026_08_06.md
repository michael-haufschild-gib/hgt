# The `k`-th derivative test is ALREADY BUILT — κ < 1 is much closer than the memories say

Two corrections to `mem:route_e/landau_route_is_pinned_at_kappa_one_2026_08_06` and to
`mem:zero-free-region-exponent-is-the-mr-wall`.  **Check these before planning any zero-free-region
work.**

## What the corpus already owns

    RHTower.Sieve.kth_derivative_test   (RHTower/Sieve/KthDerivativeTest.lean)
      k ≥ 2, phase chain `G`, `N` unit-spaced points, `0 < λ ≤ 1 ≤ h`,
      `g^{(k)}` pinned in `[λ, hλ]`  ⟹
      ‖∑_{n<N} e(g(x₀+n))‖ ≤ 256·( N·(h²λ)^{1/(2^k−2)} + N^{1−4/2^k}·λ^{−2/2^k} )

    RHTower.Sieve.dirichlet_block_bound  (RHTower/Sieve/LogPhaseBlock.lean)
      the same, applied to `n^{-it} = e(g_t(n))`, `g_t(x) = −(t/2π)log x`, on a dyadic block:
      ‖∑_{block} n^{-it}‖ ≤ 256·( L·(4^k λ)^{1/(2^k−2)} + L^{1−4/2^k}·λ^{−2/2^k} ),
      λ = (t/2π)(k−1)!/(2N)^k,   **for every k ≥ 2**.

Van der Corput's full derivative-test family is therefore formalised and already wired to the
Dirichlet series.  Neighbouring modules: `SecondDerivativeTest`, `WeylDifferencing`,
`KuzminLandau`, `KuzminLandauInterval`, `ExpSumBernstein`, `LargeSieveExpSum`,
`DirichletBlockAbel`.

**Do not rebuild any of this, and do not go looking for van der Corput in mathlib or in
`arXiv:2407.02094`.**

## What is actually missing

The Z1–Z9 chain (`DirichletOrderChoice`, `DirichletOrderRate`, → `norm_riemannZeta_line_rate_clean`)
uses the family only to reach `ζ(1+it) ≪ log t/loglog t`.  To break κ = 1 one needs, instead:

1. **choose `k` per dyadic block** (growing with `N`, the Vinogradov-style optimisation) rather than
   a fixed order, bounding `∑_{n∼N} n^{−σ−it}` for `σ` near 1;
2. **sum the blocks** into a growth bound whose exponent is **sub-linear in `(1−σ)`**, e.g.
   `|ζ(σ+it)| ≪ t^{A(1−σ)^{3/2}}·log^{2/3}t`;
3. feed that into the **existing** `landau_logDeriv` + `dlvp_inequality` frame at radius
   `R ≍ (loglog t/log t)^{2/3}`.

Step 3's arithmetic is done (see the other memory): it turns the `(1−σ)^{3/2}` shape into width
`≍ 1/(log^{2/3}t·loglog^{1/3}t)`, i.e. **κ = 2/3 < 1** — what the MR corridor needs.  Even the
weaker van der Corput/Chudakov outcome `κ = 3/4` would suffice.

**Only step 1–2 remain.**  That is an optimisation over `k`, not a new analytic theory.

## Standing no-go (unchanged)

Polynomial growth `|ζ| ≪ t^{θ(1−σ)}` — convexity, subconvexity, **Lindelöf** — gives
`log M(R)/R ≍ θ log t` independent of `R`, hence κ = 1 exactly.  The escape is the sub-linear
exponent, nothing else.
