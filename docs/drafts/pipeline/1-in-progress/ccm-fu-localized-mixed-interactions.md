# CCM-FU: source support bounds for mixed prime interactions

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], quantitative actual-source estimate
- **Goal:** Uniform complete signed Abel bound and RH remain open.
- **Parent:** [exact successor extension](ccm-fu-exact-successor-extension.md).

## Paper estimate

For a processed prime set P, put `A(P)=2^(max(card(P)-1,0))`.
Every actual retained fibre has absolute value at most
`(3/5)*A(P)*sqrt(M)`. At the empty state, this is the proved unsigned
channel ceiling. The first prime takes a difference of two numbers in the
same interval `[0,(3/5)*sqrt(M)]`, so it does not double the bound. Each
further prime difference at most doubles it. Labels containing an already
processed prime vanish exactly.

The gain from an unprocessed prime q has the all-cutoff estimate

`|Q_(P+q)-Q_P| <= (18/25)*A(P)^2*M*floor((M-1)/q)`.

Only labels R with `q*product(R)<M` can contribute. Distinct prime labels
have distinct positive products, so there are at most the displayed
integer quotient many contributing labels. Bound the two actual fibres
on that support before summing. This retains the clipped source through
its exact product-birth threshold and changes the prime dependence from
the unlocalized square-root loss to `1/q`.

For distinct unprocessed p,q, the exact two-prime mixed term is
`C_pq=sum_R(a_R*d_R+b_R*c_R)`, over all p,q-free labels. The same argument
is intended to give

`|C_pq| <= (9/25)*A(P)^2*M*`
`  (floor((M-1)/(p*q))+floor((M-1)/max(p,q)))`.

The first overlap requires `p*q*product(R)<M`. The second requires both
`p*product(R)<M` and `q*product(R)<M`. These are different support costs;
neither complete term may be discarded.

## Scope and remaining comparison

These are estimates for arbitrary already mixed actual fields, not only
the original source or a fixed two-prime family. They are not a complete
extension proof. The factor A(P)^2 can grow with the processed set, and the
bound loses the signs that select a successful prime. It must not be used
as a uniform constant along an exhaustive order. The successor target
still requires one p satisfying
`Delta_p+Delta_q+2*C_pq<=B-Q_P` simultaneously for every q.

No numerical experiment is needed or planned: the support counts and
amplitude estimates follow analytically from the literal source identities.
