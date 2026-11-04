# Full-horizon conductor energy loses its reference diagonal comparison

- **ID:** full-horizon-conductor-metric-degeneration
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [critical-ratio continuation](../1-in-progress/critical-ratio-continuation.md)

## Exact target

Let L=log N, c_N≥1, c_N⁸/L→R>0, B_N the complete tilted-spline
matrix and E_m its completed conductor energy. Fix a nonzero compact
C² window with F(x)=h(log x) supported inside (1/2,1). Define

    a_m(N)=Σ_(1≤d≤N; m|d) F(d/N)/d,
    b_m(N)=√L √φ(m) a_m(N),
    D_N=Σ_(1≤m≤N) E_m(c_N)b_m(N)².

The checked classification is

    Σ_(1≤m≤N)b_m(N)v_m(N)=x_h(N),
    D_N>0 eventually, c_N/D_N→0,
    ⟨B_N x_h(N),x_h(N)⟩/D_N→0.

Consequently no fixed positive fraction of the reference diagonal conductor energy
can lower-bound the complete form on the full conductor packet, even at
a critical ratio within the established whole-space positive band.
This proves failure of that comparison, not negative complete energy.
The concrete nonnegative terminal spline gives `b_m(N)≥0` for every m,
so restricting conductor coefficients to the nonnegative cone does not
restore the proposed diagonal floor.

## Internal attack

**Verdict: BRIDGE.** Full-horizon spanning already follows from
`exists_horizon_normalizedRamanujan_expansion` and
`mem_full_horizon_conductorSubspace`; it is not a new conjecture.
The content is the explicit terminal coefficient formula and
the quantitative degeneration of the particular diagonal energy used
by the logarithmic-packet continuation. Targeted corpus searches found
no exact producer of that degeneration; this is not an exhaustive
absence or external novelty claim.

The logarithmic packet has a checked half-energy floor at every fixed R.
That does not contradict the full-horizon counterfamily: its
essential coefficients reach conductors comparable to N. Nor would a
vanishing sum of individual nonpolar source squares extend the floor.

## Proof reduction

**Finite reconstruction.** Exchange the m,d sums and use
`Σ_(m|d)c_m(n)=d[ d|n ]`. For n≤N every proper divisor d of n satisfies
2d≤n≤N, so F(d/N)=0. Only d=n remains. If N<2m≤2N, the only positive
multiple of m through N is m itself, hence a_m=F(m/N)/m. These are
dependency-closed finite arguments, now checked in Lean.

**Diagonal cost.** The existing conductor floor is

    E_m(c)≥log m−log c+min(0,self_φ(1)).

The existing unconditional Landau bound
`RHTower.eventually_div_totient_le_landau` gives
m/φ(m)≤C log log m eventually, with C=exp(γ)+1. Its weaker consequence
m/φ(m)≤C log N suffices here. Uniformly for N/2<m≤N and large N,

    E_m(c_N)≥L/2,     φ(m)/m≥1/(C L).

Nonnegativity of every remaining diagonal summand then gives

    D_N ≥ L/[2C] · Σ_(1≤n≤N) F(n/N)²/n.

The last sum tends to ∫h²>0 by `tendsto_sum_horizonWeights_sq`.
The critical clock gives c_N/L→0. Hence D_N>0 eventually and c_N/D_N→0.
The checked critical-window limit bounds the complete energy by O(c_N),
which proves the ratio limit.

`TerminalWindowsHaveExplicitFullConductorCoordinates.lean` implements
the finite reconstruction, the top-half coefficient and its normalized
square. `TheFullConductorDiagonalOverpricesTerminalWindows.lean`
implements the uniform energy and totient reserves, the sufficient
weaker bound `D_N≥L/[2C]·ΣF(n/N)²/n`, eventual positivity of D_N,
`c_N/D_N→0`, and the complete-energy/diagonal ratio limit. The weaker
reserve already settles the proposed degeneration because c_N/L→0.
Both modules pass their actual-path Lean audits. All four reconstruction
endpoints and all six audited degeneration endpoints use exactly
`[propext, Classical.choice, Quot.sound]`. Both modules are wired into the
programme umbrella. The last endpoint supplies the nonnegative coefficient
counterfamily without an assumed nonzero test.

## Positive survivor and next question

The survivor is an explicit exact arithmetic reconstruction and a
quantified failure of the reference energy metric. Here E_m is the
completed reference energy, not the literal finite-horizon diagonal
`⟨B_Nv_m,v_m⟩`. Moreover the vectors v_m need not have norm near one
when m is comparable to N. This result alone does not identify
off-diagonal cancellation as the cause of the failure.

A continuation based only on extending this reference diagonal floor
cannot reach the full horizon. Locate where the comparison first
degenerates, and separate three effects: changing column norms,
changes in individual complete energies, and collective mixed terms.
Neither the transition scale nor an all-R positivity conclusion
follows here.
