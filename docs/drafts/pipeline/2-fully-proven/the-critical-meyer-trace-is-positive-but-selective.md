# The critical Meyer trace is positive but selective

- **ID:** the-critical-meyer-trace-is-positive-but-selective
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Q-II; actual trace admission, critical character degrees, and invariant majorants.
- **Statement:** Summing actual zeroth Mellin values over all critical Xi multiplicity copies defines a positive linear degree on genuine Meyer cohomology. Its square kernel consists exactly of classes vanishing at all critical Xi values. It dominates the original mixed trace exactly under RH, and is faithful on genuine sharp squares exactly under RH and Xi simplicity.
- **Status:** Dependency-closed paper proof; Complete Lean draft present, unverified. External novelty unverified.

## Construction and exact convergence

For an actual all-weight source g define

    tau_crit(g)=sum_(q critical Xi copy) M_g(q).

The existing full-Hasse trace theorem proves absolute summability over all Xi
multiplicity copies for every actual source. Restricting to the critical subtype
therefore preserves summability. Termwise addition and scalar multiplication
make tau_crit complex-linear. Every genuine Poisson boundary has all its Xi
values zero, so this linear map descends to the actual quotient.

At each critical Xi point rho, arithmetic sharp satisfies
M_(g#)(rho)=conjugate(M_g(rho)). Hence the exact square formula is

    Re tau_crit(g*g#)=sum_(q critical Xi copy) |M_g(q)|² >= 0.

This series is summable: it is the real part of the admitted diagonal trace of
the actual product g*g#, restricted to the same critical subtype. No arbitrary
positive functional is passed through an infinite expansion.

## Exact loss of information

The nonnegative sum is zero exactly when each critical value vanishes. A nonzero
critical value gives a strictly positive term at its zeroth multiplicity copy;
conversely vanishing every critical value kills every term. The same condition
kills every mixed tau_crit reading. Thus the degree sees the entire reduced
critical value carrier, while forgetting all higher jets and off-line values.
Hardy's critical point supplies a source with strictly positive square reading.

This extends the finite critical-weight construction to a canonical infinite
degree. It does not classify arbitrary positive degrees or eliminate their
possible algebraic infinite residual. The selector uses critical Xi points, so
it is not the independent prime-side source construction required to finish Q-II.

## Exact comparison and faithfulness boundaries

Centered flow leaves the literal mixed sharp product unchanged. Thus the square
energy above is invariant. If it majorizes the original real mixed trace for
all actual sources, the already proved invariant-majorant criterion forces RH.
Under RH every Xi point is critical, so tau_crit is exactly ordinary trace;
ordinary Cauchy–Schwarz supplies the majorant. Therefore this domination is
exactly RH, despite unconditional positivity and descent of tau_crit itself.

If tau_crit is strictly positive on every nonprincipal sharp square, it is one
faithful positive cohomological degree, so the existing sharp-root criterion
forces RH and Xi simplicity. Conversely under these two conditions the degree
is ordinary trace, whose square is strictly positive off genuine boundaries.
This establishes the exact faithfulness criterion without assuming either
condition. A positive descended degree is therefore available globally; matching
the original pairing and detecting genuine classes remain separate obligations.

## Corpus audit

Search found the existing full critical-locus resolvent/Poisson trace in
`XiWeilHardyCriticalLocusPoissonReserve`, but not this degree on actual all-weight
convolution cohomology. The new proof uses the existing actual diagonal trace
summability, boundary division, and exact centered mixed-product transport.
The finite critical-value and character results explain its precise kernel.
No new operator admission or positive representation is assumed.

Draft: `/tmp/QIICriticalMeyerTraceDegreeDraft.lean`. API probes: `/tmp/QIICriticalTraceAPIs.lean`; not yet run. The draft includes the exact critical square kernel, mixed radical, nontriviality, flow invariance, original-trace majorant criterion, and faithful-degree criterion.
