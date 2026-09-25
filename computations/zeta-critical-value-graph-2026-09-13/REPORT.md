# Critical values and the zero connection graph

**Question.** Which zeros are connected by the two inverse branches leaving a zero of zeta prime, when its critical value is moved straight toward 0?

**Outcome.**189 specified Newton starts in 63 zero gaps produced 82 successful two-branch lifts, representing 42 numerically distinct critical points.107 starts escaped the declared Newton search domain; they are failed starts, not evidence that a critical point is absent.41 of 42 distinct accepted critical points connected neighboring positive zeros. One connected zeros 57 and 60, bypassing 58 and 59 in zero order.

That point is approximately s_c=(1.5503456423977028198083, 162.66556369569605710332) in(real,imaginary)coordinates. Its value zeta(s_c) is approximately(1.1448495588861500296406, 0.1071106023577795304735). The two branches were started using the local quadratic expansion, corrected against zeta, then lifted along w=(1-epsilon)*(1-u)*zeta(s_c).

**Validation.** Critical seeds 9,13,59 repeated at 100/160 digits; epsilon 1 e-5 and 1 e-7 crossed with parametersteps.012 and.006. All 12 two-branch runs completed with unchanged endpoint pairs. Explicit Euler--Maclaurin sums with two truncations independently checked 7 locations per branch. For the nonadjacent pair 57/60, worst 160-digit independent target residual was below 1.5 e-151. The coordinate is refined from 50-digit discovery, not treated as exact input. No complete critical-point census or certified path enclosure.

**Interpretation for the landscape and RH.** The sampled inverse geometry has connections that cannot be read from nearest-neighbor zero spacing alone. This supplies a concrete nonlocal relation between actual zeros. It does not force their real parts: RH concerns the zero fibre, whereas these paths pass through nonzero target values. A useful new route would need an arithmetic restriction on the entire critical-value graph plus a proved implication to zero-fibre confinement. No such implication was established.

**Positive salvage and next test.** A neighbor-only graph claim fails numerically for this specified lifting convention. Its survivor is a mostly adjacent graph with an explicit exceptional connection. Test critical-point-to-zero access-path dependence and compare other L-functions before treating the graph as arithmetic-specific. Merely finding generic square-root branching would be an implementation check.

**Reproduction.** `python guard.py experiment.py`;189 starts are deterministic. Full critical coordinates, source values, endpoint distances, paths and failed starts retained. Companion challenge has the 12 refinements and independent formula checks.

Evidence: finite numerical observation, no Lean builds or interval certificate. Original zeta evaluated; no physical HB action, corrections or boundary terms have been identified. Numerical continuation can miss sheet switching between nodes, despite refinement and independent function checks. Searches have partial/source-only coverage; this report makes no priority or new-theorem claim.
