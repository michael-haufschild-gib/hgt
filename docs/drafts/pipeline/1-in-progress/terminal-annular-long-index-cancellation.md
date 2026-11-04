# Long-index cancellation on growing logarithmic annuli

- **ID:** terminal-annular-long-index-cancellation
- **Stage:** 1-in-progress
- **Type:** THEOREM, paper proof awaiting Lean
- **Parent:** [sources beyond the logarithmic packet](terminal-sources-beyond-the-logarithmic-packet.md)
- **Verdict:** `BRIDGE`. Quantitative periodic cancellation, not a new positivity theorem.

## Exact statement

Let F vanish on `x≤1/2`, with `|F|≤B_F` and Lipschitz constant L_F.
Let K be bounded by B_K with Lipschitz constant L_K. Let p have positive
integer period q, zero period mean and `|p|≤B`. For

    c≥1, T≥1, 0≤α≤β≤T, 8Tc≤N,
    C_W(T)=20B_F B_K+64B_F L_K T+4B_K L_F,
    C_K(T)=64L_K T+4B_K,

the target finite bound is

    |endpointNearPairSum(K,F,α,β,c/N,N,1,p)/c|
      ≤ [8qBT C_W(T)+8B_F B C_K(T)T²c]/N.

The period may exceed overlap. No relation between q and c is assumed.
The estimate concerns the literal logarithmic kernel and both triangles.

## Internal attack

Existing periodic interval estimates already supply cancellation. The
missing transfer is the moving logarithmic selector and its explicit
dependence on T. Fixed-T convergence does not imply this finite bound.
The proposed remainder allows T to grow while staying below N/(8c).
Its loss is quadratic in T in the periodic term and cubic in T in the
kernel replacement. No all-conductor Gram approximation follows.

## Dependency-closed paper proof

For a positive integer gap d, put

    ℓ_d(n)=log(n+d)−log n,
    S_d={1≤n≤N−d : αc/N<ℓ_d(n)≤βc/N}.

The function `ℓ_d(n)=log(1+d/n)` decreases for n≥1. Hence S_d is empty
or the integer interval between its minimum and maximum. If n belongs
to S_d, the inequality `(j−n)/j≤log(j/n)`, with j=n+d≤N, gives d≤Tc.
The diagonal is absent since α≥0. Thus reindexing both triangles leaves
only `1≤d≤floor(Tc)` and the interval S_d.

Replace each actual pair by its reciprocal model

    [F(n/N)p(n+d)+F((n+d)/N)p(n)] K(dN/(cn))/n.

For θ=d/c≤T, the clamped reciprocal weight
`F(x)I(x)K(θI(x))`, `I(x)=1/max(1/4,x)`, is bounded by `4B_F B_K`
and has Lipschitz constant `64B_F L_K T+16B_F B_K+4B_K L_F`.
The shifted profile has the same constants. Wherever either receiver
is nonzero, `8Tc≤N` and d≤Tc give n/N≥1/4, so clamping changes no term.
The interval version of periodic summation costs `4qB C_W(T)/N`
for each triangle, hence `8qB C_W(T)/N` for their sum.

Apply the existing logarithm/Jacobian replacement estimate with
macroscopic constant 4 and gap bound Tc. Its kernel error is
`C_K(T)Tc/N`. The combined receiver coefficient divided by n is at most
`8B_F B/N`. Summing at most N indices therefore costs
`8B_F B C_K(T)Tc/N` for each gap. There are at most Tc gaps; division
by c proves the displayed bound. Empty selector intervals contribute zero.

Equivalently, the existing near-offset error estimate applies with overlap
Tc and kernel `s↦K(Ts)`; this avoids reproving the analytic replacement.

## Application boundary

Clamp the near Gamma profile to [0,2] and the separated profile to
[2,T]; existing Lipschitz constants give the required global extensions.
The actual entry errors are O(c/N). The checked separated tail is
`O(B²/T+B²c/N)` after division by c. Taking T=N^(1/8) would give a
power-saving nonpolar Gamma estimate. The complete terminal source still
requires matching the full center, completed divisor jet and remaining
channels with their conductor dependence. This card does not claim that
assembly or the parent polynomial-packet conjecture.

**Lean status:** `TerminalLogarithmicAnnuliCancelAlongTheLongIndex.lean`
implements the selector, triangle reindexing, rescaled error and final
bound. Actual-path audit pending; no endpoint is counted as checked.
