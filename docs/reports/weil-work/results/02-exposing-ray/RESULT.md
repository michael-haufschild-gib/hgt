# WP02 result — tail repair and compact-primitive source bounds

## Latest result: literal exposing tail (cycle 5)

Verified source: `formal/GaloisForLFunctions/RHTower/WeilWorkExposingRayTailAsymptotic.lean`. Final `lake --old env lean` exits 0 without warnings; all eight audited capstones use only propext, Classical.choice and Quot.sound. RHTower umbrella import wired.

Write kappa=2*pi*exp(-2). The actual exposing weights are eventually strictly positive and satisfy

    log(exposingWeight n) / n -> -kappa.

For every 0<r<kappa there is C>0 such that `exposingTail N <= C*exp(-r*N)` for every N. Also `0 < exposingTail N` for every finite N. No sign assumption, zero-location assumption or added axiom enters these statements.

The proof retains the literal infinite mixture. Its outermost positive shift has distance two, while all negative shifts have distance at most one; sharp theta-autocorrelation envelopes force the positive outer shift to dominate. See TAIL-SIGN-PROOF.md.

This strengthens the existing repair estimate from a summable polynomial majorant to its exponential source scale. For cutoff N near exp(2A), this literal tail budget is doubly exponential in aperture A. This is not a necessary accuracy barrier for every RH argument: a compactness argument may first establish RH from more slowly vanishing slack. It does **not** prove the universal matched-family archimedean lower bound. Main WP02 objective remains OPEN. Scientific novelty beyond the source-specific synthesis is not certified.

**Verdict: CONDITIONAL ADVANCE. Main problem OPEN.**

Unconditional results now cover exact exposing-tail repair, coefficient-uniform packet coercivity, and a source inequality with an explicit primitive penalty for arbitrary smooth compact primitives. The cofinal positivity estimate needed for RH is unproved. Scientific novelty verdict: **BRIDGE / source-class boundary**; no claim of a new general uncertainty principle or an RH breakthrough.

## Smooth compact source result

For every existing smooth compact primitive G, its actual polar source F=G''-G/4, and every real b, the direct source theorem proves

    (b-C_a) * M(F) <= archEnergy(F) + exp(b)^4 * M(G)/4,

where M is Fourier squared mass and C_a is an explicit digamma constant. The theorem uses the existing `CCMComplexSmoothInteriorSource.polarMultiplier`; there is no positivity, arithmetic, packet-expansion or separation premise. A separate theorem covers arbitrary finite overlapping packets.

This explains the failed transfer from separated packets: approximating a fixed broad primitive by narrower overlapping bumps does not force M(G) to shrink like the fourth power of the bump width. `OVERLAP-PROOF.md` gives the energy-topology counterargument on paper. The no-go itself is not claimed as a Lean theorem; its strongest source-inequality survivor is formalized.

Capstone: `exposingCompact_archimedean_primitive_bound` in `WeilWorkExposingRayPacketCoercivity.lean`. Scratch axiom audit and final `lake --old env lean` source audit passed, with only propext, Classical.choice and Quot.sound. EVIDENCE.md records exact scope.

**Limit:** the explicit primitive penalty is unpaid on the full matched exposing ray. The proof also uses coarse source constants and discards positive remainders, so it does not identify the sharp exposed endpoint. No completion of the C² matched-cone inequality is asserted.

## Collective packet result

For every natural N and arbitrary complex coefficient function c, put w=1/(N+1) and F=resonator(N,c,w). The new theorem proves

    (log(N+1)-C) * integral |paperFT(F)|^2 <= archEnergy(F),

with one explicit finite constant C independent of N and c. There is no Weil-positivity premise. N=0 and the zero vector are included.

The proof keeps all Fourier cross terms. The exact compact primitive G satisfies Fhat=-(tau^2+1/4)Ghat and

    integral |Ghat|^2 <= R*w^4*integral |Fhat|^2.

Disjoint physical supports prove this inverse-mass bound; the proved digamma lower bound and a scalar logarithmic inequality then prove coercivity. The lower bound complements the existing packet upper-bound mechanism and rules out bounded-energy, mass-retaining near-null sequences within these shrinking packet spaces. General polar tests need not obey the inverse-mass bound, so no passage to the full matched cone is claimed.

Paper proof: `PACKET-PROOF.md`. Lean module: `WeilWorkExposingRayPacketCoercivity.lean`; capstones `exposingPacket_inverse_mass` and `exposingPacket_archimedean_coercivity`. Final targeted source audit exited 0 without warnings, using default heartbeats. Scratch axiom audit passed: multiplier, inverse-mass and coercivity capstones use only propext, Classical.choice and Quot.sound. EVIDENCE.md records details.

## Exact tail-repair statement

For every pair of natural cutoffs N,M, the explicit finite family indexed by
`max(2,N+1) <= n <= M` consists of smooth compactly supported polar tests with nonnegative mixture coefficients. At every integer m>=2, including all omitted coefficients, its dual atom trace is exactly

    exposingWeight(m) * 1_{N<m<=M}.

Its archimedean energy is at most the sum of the exposing majorant over that interval. When N<=M, this budget equals

    exposingTail(N) - exposingTail(M).

For all N,M, energy is at most exposingTail(N), hence has a uniformly vanishing upper bound in M as N tends to infinity. This is an upper bound on energy, not an assertion of absolute-value convergence or positivity.

If M<=floor(exp(2B)), every repair test has aperture at most B+1. The construction retains the polar constraints, nonnegative mixture coefficients and exact atom normalization `2*pi`.

## Consequence and unpaid estimate

Appending the repair, scaled by t>=0, carries a family matched to t*w_N to one matched to t*w_M. If a cofinal family of full dual bounds were proved at levels admitting those repair tests, with lower bound E-tau(M)-epsilon and epsilon tending to zero, the exact WP02 inequality would follow at every fixed cutoff and aperture. PROOF.md supplies the complete passage, including t=0.

**Unpaid:** source-derived archimedean lower bound on the whole matched-test cone at the cofinal levels. No positive producer, endpoint attainment or RH proof is supplied.

## Lean evidence

Module: `formal/GaloisForLFunctions/RHTower/WeilWorkExposingRayTailRepair.lean`.

Main declarations:

- `RHTower.exposingRepair_sum_atoms`
- `RHTower.exposingRepair_mass_eq_tail_sub`
- `RHTower.exposingRepair_energy_le_tail_sub`
- `RHTower.exposingRepair_uniform_vanishing`
- `RHTower.exposingRepair_level_le`

`lake --old env lean GaloisForLFunctions/RHTower/WeilWorkExposingRayTailRepair.lean` exited 0. Scratch axiom audit exited 0; audited capstones use only `propext`, `Classical.choice`, `Quot.sound`. No added axioms, numerical computation, heartbeat increase or full build. The module is wired into RHTower under the user's explicit instruction.

Latest formal lint exited 1 on twelve unrelated umbrella-reachability errors; neither WP02 module is named. EVIDENCE.md records their scope. Existing work was preserved.

## hgtl7 assessment

- **New scientific knowledge beyond literature and corpus?** Not established. Tail repair quantifies an existing internal mechanism. The collective packet lower bound was not found in the inspected corpus sources, but its uncertainty parent is classical and retrieval coverage was incomplete.
- **Rediscovery?** Yes: the ground-state identity was already formalized; a proposed logarithmic-cost argument meets known logarithmic-Laplacian/uncertainty theory. These are not counted as breakthroughs.
- **Theatre?** Reporting this as RH progress through a new positivity estimate would be theatre. The actual deliverable is a verified extension budget required by the first milestone.
- **Frontier moved?** Cutoff transport is explicit in Lean; the collective packet family has a uniform source lower bound, and the whole smooth compact primitive interface has an explicit mass-penalty inequality. The hard positivity frontier for arbitrary matched mixtures remains unchanged.
- **Avoiding the hard problem?** The source sign was investigated but not proved. No effort estimate was used to exclude it. Further work must target the collective constrained source inequality.
- **Next cycle:** return to the exact gamma/arithmetic residual on the matched cone. Test whether the compact-primitive Green representation and all integer traces provide a sharp signed estimate; reject bounds that merely add a fixed loss. Existing ground-state variance countermodels must be included in that attack.
