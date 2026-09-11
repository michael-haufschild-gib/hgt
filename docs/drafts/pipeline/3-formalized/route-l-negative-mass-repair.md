# Route L: negative-mass cost of a complete coherent repair

Status: formalized; scratch Lean, targeted build, all-theorem axiom audit and repository lint passed.
Date: 2026-09-11.
Module: `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanNegativeMassRepair`.

## Exact source and result

Fix the genuine trace-normalized Big-Witt row `r_(a,n)` at the original prime
`p=nthPrimeSubtype a`. Let `M_n` be its actual raw row mass and
`K_n=1/(p*M_n)`. Subtract one complete coherent packet `R(b,S)` and set
`g_n=r_(a,n)-R(b,S)`. Its total negative real edge mass is

`delta(g)=sum_(i in support(g)) max(-Re(g(i)),0)`.

No sign condition on the repaired coefficients is assumed in the finite laws:

- Removed anchor mass `rho=Re(m_(R(b,S))(p))` satisfies
  `-delta(g_n)<=rho<=2*(K_n+delta(g_n))`.
- Retained anchor mass lies in
  `[1-2*(K_n+delta(g_n)), 1+delta(g_n)]`.
- For every `A>=0`, the original reciprocal reader satisfies
  `Re E_A(g)>= (A/p)*Re(m_g(p))-(A/2)*delta(g)`.
- For the unit reciprocal reader,
  `1-2*K_n-p*Re E_1(g_n)<=(2+p/2)*delta(g_n)`.

Arbitrary moving profiles and finite sets are allowed. If their corrected
negative mass tends to zero, the anchor mass tends to one and the energy
cannot tend to zero for any `A>0`. Conversely, if unit reciprocal energy tends
to zero, `delta(g_n)>=1/(p+4)` eventually, without assuming a negative-mass
limit. These are universally quantified implications, not assumptions about
the unconstructed physical comparison.

The explicit C10 coherent-star corrected row satisfies that persistent
negative-mass lower bound unconditionally. It has trace one, marginal
variation one, the original singular graph limit and vanishing reciprocal
energy, yet carries a positive total negative edge cost eventually.

## Dependency-closed paper proof

Let `L=S\{p}`, `k=card(L)` and `t_q=Re(b(p)-b(q))`. If the anchor is absent,
its coherent marginal is zero. If `L` is empty, its sum is zero. Otherwise
choose exactly `m=ceil(k/2)` leaves with integer prime label at least `m`.
Fewer than `m` positive integer labels lie below `m`; finite injection and
subset selection prove existence. Thus `m>=1` and `k<=2m`.

Write `T` for this selected set and `w_q` for the original outgoing row real
coefficient. The literal bound `w_q<=K_n/q` gives `sum_T w_q<=K_n`.
Let `D_out=sum_L max(t_q-w_q,0)` and
`D_leaf=sum_(q,r in L) max(t_r-t_q,0)`. The complete potential satisfies

`m*sum_L t - k*sum_T t = sum_(q in T,r in L)(t_r-t_q)<=D_leaf`.

Also `sum_T t<=K_n+D_out`. Since `k>=1`, these imply
`m*rho<=k*(K_n+D_out+D_leaf)<=2m*(K_n+D_out+D_leaf)`.
Anchor-to-leaf and leaf-to-leaf edges are disjoint; their negative costs are
exactly `D_out` and `D_leaf`. Finite-support accounting places their sum below
`delta(g_n)`. Division by `m` proves the upper removal bound.

Incoming leaf-to-anchor real coefficients are exactly `t_q`, because the
original row has no coefficients with a different left label. Their negative
mass bounds `-sum_L t`, giving the lower removal bound. The original anchor
marginal is one, yielding the retention interval.

For the energy comparison, separate anchor edges. Every other reciprocal
weight lies in `[0,A/2]`; a negative coefficient contributes at least
`-(A/2)*max(-Re(g(i)),0)`. Sum over the full finite support. Substituting the
retention lower bound and multiplying the unit-reader inequality by `p`
gives the finite tradeoff. The existing raw mass divergence gives `K_n->0`.
Taking limits proves retention when negative mass vanishes; taking an eventual
half-unit margin proves the persistent cost when energy vanishes.

Finally, every coherent star has one complete-packet representation. Apply
the energy-erasure cost to its already proved vanishing unit reciprocal
reader to obtain the unconditional concrete example.

## Mathematical boundary

This strengthens the exact positive one-packet domain to small *total* negative
real mass. It is not a claim about arbitrary sums of complete packets; the
positive transposed assembly still lies outside joint complete coherence.
A bound on contracted marginal variation does not replace this edge-mass
bound, as the explicit coherent-star example shows.

No actual fixed physical comparison with vanishing negative mass has been
constructed. No agreement with the original Burnol/Deninger reader, zero
conormal defect, critical-line placement or RH follows from this module alone.
No optimality of the constants is claimed.

The resulting full-edge `L1` distance bound is now
[formalized](route-l-coherent-distance.md): the positive transposed repair
stays at least `(1-2*K_n)/3` from every single complete coherent packet,
and eventually at least `1/6` uniformly over all profiles and finite sets.

## Verification

- `lake env lean /tmp/route_l_negative_repair.lean` — passed without warnings.
- `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanNegativeMassRepair` — passed; only the target required rebuilding.
- `lake env lean /tmp/route_l_negative_repair_axioms.lean` — all 17 theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/formal_tools.py lint` — passed.
- Umbrella import wired; no full or umbrella build ran. All C13 Lean processes completed.
