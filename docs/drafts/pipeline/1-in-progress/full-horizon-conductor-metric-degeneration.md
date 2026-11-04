# Full-horizon conductor energy loses its diagonal comparison

- **ID:** full-horizon-conductor-metric-degeneration
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [critical-ratio continuation](critical-ratio-continuation.md)

## Exact target

Let L=log N, c_N≥1, c_N⁸/L→R>0, B_N the complete tilted-spline
matrix and E_m its completed conductor energy. Fix a nonzero compact
C² window with F(x)=h(log x) supported inside (1/2,1). Define

    a_m(N)=Σ_(1≤d≤N; m|d) F(d/N)/d,
    b_m(N)=√L √φ(m) a_m(N),
    D_N=Σ_(1≤m≤N) E_m(c_N)b_m(N)².

The proposed classification is

    Σ_(1≤m≤N)b_m(N)v_m(N)=x_h(N),
    D_N/c_N→+∞,
    ⟨B_N x_h(N),x_h(N)⟩/D_N→0.

Consequently no fixed positive fraction of the diagonal conductor energy
can lower-bound the complete form on the full conductor packet, even at
a critical ratio within the established whole-space positive band.
This predicts failure of that comparison, not negative complete energy.

## Internal attack

**Verdict: BRIDGE.** Full-horizon spanning already follows from
`exists_horizon_normalizedRamanujan_expansion` and
`mem_full_horizon_conductorSubspace`; it is not a new conjecture.
The content to audit is the explicit terminal coefficient formula and
the quantitative degeneration of the particular diagonal energy used
by the logarithmic-packet continuation. Targeted corpus searches found
no exact producer of that degeneration; this is not an exhaustive
absence or external novelty claim.

The logarithmic packet has a checked half-energy floor at every fixed R.
That does not contradict the proposed full-horizon counterfamily: its
essential coefficients reach conductors comparable to N. Nor would a
vanishing sum of individual nonpolar source squares extend the floor.

## Proof reduction

**Finite reconstruction.** Exchange the m,d sums and use
`Σ_(m|d)c_m(n)=d[ d|n ]`. For n≤N every proper divisor d of n satisfies
2d≤n≤N, so F(d/N)=0. Only d=n remains. If N<2m≤2N, the only positive
multiple of m through N is m itself, hence a_m=F(m/N)/m. These are
dependency-closed finite arguments; their Lean transfer is pending.

**Diagonal cost.** The existing conductor floor is

    E_m(c)≥log m−log c+min(0,self_φ(1)).

The existing unconditional Landau bound
`RHTower.eventually_div_totient_le_landau` gives
m/φ(m)≤C log log m eventually, with C=exp(γ)+1. Thus, uniformly for
N/2<m≤N and sufficiently large N,

    E_m(c_N)≥L/2,     φ(m)/m≥1/(C log log N).

Nonnegativity of every remaining diagonal summand then gives

    D_N ≥ L²/[2C log log N] · Σ_(1≤n≤N) F(n/N)²/n.

The last sum tends to ∫h²>0 by `tendsto_sum_horizonWeights_sq`.
The critical clock gives c_N log log N/L²→0. Hence D_N/c_N→∞.
The checked critical-window limit bounds the complete energy by O(c_N),
which proves the proposed ratio limit.

`TerminalWindowsHaveExplicitFullConductorCoordinates.lean` implements
the finite reconstruction, the top-half coefficient and its normalized
square. `TheFullConductorDiagonalOverpricesTerminalWindows.lean`
implements the uniform energy and totient reserves, the sufficient
weaker bound `D_N≥L/[2C]·ΣF(n/N)²/n`, eventual positivity of D_N,
`c_N/D_N→0`, and the complete-energy/diagonal ratio limit. The weaker
reserve already settles the proposed degeneration because c_N/L→0.
Both modules await their actual-path Lean audits; no new endpoint in
this card is kernel-credited yet.

## Positive survivor and next question

The survivor is an explicit exact arithmetic reconstruction and a
quantified change of energy metric. Larger packets must retain their
collective off-diagonal cancellation. A continuation based only on
extending the current diagonal floor cannot reach the full horizon.
Locate the conductor range where this comparison first degenerates,
and determine the complete signed form there. Neither the precise
transition scale nor an all-R positivity conclusion follows here.
