# DR construction rejected: fixed-width joint Hurwitz root tube

Verdict: FALSE. This retires only this proposed construction, not DR.

The candidate was to continue holomorphic d-th roots, d>1, throughout a
fixed positive complex shift disk around a=1 over 1/2<Re(s)<1, then restrict
to the anchor slice. It fails unconditionally. A critical-line Xi zero
produces a local analytic Hurwitz zero graph a=A(s), and the nearby shift
zeros are simple. For every fixed disk radius, those simple branch points
enter the disk at exponents strictly inside the right half-strip. A root
would force its degree to divide the simple zero's order one.

## Exact positive survivor

For every Xi zero rho, including multiple zeros, the actual Hurwitz source
has a local holomorphic zero graph with A(rho)=1, simple shift zeros along
the graph, and

    ord_rho(A-1) = ord_rho(zeta) = ord_rho(Xi).

Thus smoothing the joint divisor preserves the entire slice ramification
as contact with the arithmetic anchor. This is the exact obstruction that
a successful source-specific transport must address. A shrinking shift
tube cannot be assumed to avoid this divisor: doing so at every interior
anchor would already assume the required zero-free conclusion.

Paper proof and exact Lean theorem are complete:
`../3-formalized/route-dr-hurwitz-anchor-zero-graph-2026-10-15.md`.
Main declarations:

- `RHTower.exists_analytic_hurwitz_zero_graph_with_contact_order`
- `RHTower.exists_simple_hurwitz_shift_zero_in_right_half_strip`
- `RHTower.not_forall_exists_hurwitz_shift_disk_power_root`

All new current-source checks pass. Final axiom/lint audit is recorded on
the positive-survivor card. No numerical experiment, external novelty
search, simplicity assumption, or RH premise was used.

Novelty assessment: exact source geometry added to this corpus; proof uses
standard local holomorphic geometry. No new scientific principle or
zero-free certificate is claimed. DR's main problem remains active.
