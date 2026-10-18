# Uniform cofinal cancellation of the literal Möbius prefix

- **ID:** BVI-UNIFORM-COFINAL-PREFIX-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Statement:** For every epsilon>0 there exists K such that, simultaneously
  for all N,M>=K, both |L_N(M)|<=epsilon M and |S_N(M)|<=epsilon M.

## Arithmetic objects and quantifiers

Use the literal truncated Möbius source, not a tapered replacement:

    s_N(k)=sum_{d<=N,d|k}mu(d),
    S_N(M)=sum_{k=1}^M s_N(k),
    H_N=sum_{d=1}^N mu(d)/d,
    L_N(M)=sievePrefixDiscrepancy N M moebiusReal=S_N(M)-M H_N.

N and M grow independently. A single threshold K works for every pair
above it. No fixed-cutoff-first limit, full-period average, receiver budget,
square-root saving, or critical unsigned-energy claim is involved.

## Dependency-closed paper proof

Fix a natural number B. For 1<=M<=(B+1)N, the existing complementary
quotient compression gives

    S_N(M)=1-sum_{q=1}^B sum_{N<d<=floor(M/q)}mu(d).

To verify this identity, write each source value as its complete Möbius
divisor sum minus its high-divisor tail. The complete sums give one.
For each high divisor d of k<=M, its complementary quotient q=k/d
lies in [1,B]. Exchange the two finite sums and use the bijection k=q*d.
Empty windows contribute zero, so no extra ordering premise is needed.

Let U(X)=max_{0<=t<=X}|sum_{d<=t}mu(d)|. Every window in the formula
has modulus at most 2U((B+1)N). Thus the exact finite arithmetic estimate is

    |S_N(M)| <= 1+2B U((B+1)N),       1<=M<=(B+1)N.

The corpus proves U(X)/X->0 and H_N->0 unconditionally. Consequently
the displayed majorant is o_B(N). For a given epsilon, choose fixed B
with 1/(B+1)<epsilon. On N<=M<=(B+1)N, combine the majorant with
L_N(M)=S_N(M)-M H_N, splitting epsilon between the two terms. On
M>(B+1)N, use the direct fractional-part estimate

    |L_N(M)|<=sum_{d<=N}|mu(d)|<=N<epsilon M.

This proves the uniform estimate for every M>=N. If M<N, complete
Möbius inversion gives S_N(M)=1 and L_N(M)=1-M H_N. Taking both N
and M sufficiently large proves the unrestricted joint cofinal estimate.
Finally S_N(M)=L_N(M)+M H_N gives the same estimate for the source
prefix, splitting epsilon in half. **[PROVED HERE]**, dependency-closed.

## Corpus inputs and scope

- `ComplementaryQuotientAndSecondOctaveLaw.lean`: exact quotient geometry.
- `CompositeSquarefreeStepAndMultiOctaveL2Energy.lean`: finite multiple
  bijection used to exchange the quotient windows.
- `RHTower.Sieve.tendsto_mertensSup_div`: unconditional maximal Mertens
  cancellation, derived from the corpus's proved Möbius PNT.
- `PNTPlus.Consequences.mu_pnt_alt`: unconditional harmonic Möbius limit.
- Existing fractional-part discrepancy bound and sub-horizon inversion.

The PNT and divisor identities are classical inputs, not novelty claims.
The result is their uniform cofinal transfer to the actual BVI prefix,
with an explicit finite quotient-window majorant. Deep corpus search
returned no matching cofinal theorem; predominantly source-only coverage
does not establish external publication novelty. No numerical experiments.

The previously formalized linear gradient floor still applies. Signed
first-moment cancellation does not imply sublinear microscopic gradient
energy, critical unsigned-energy control, or an interior martingale bound.

## Verification checkpoint

- C6 scratch session 79190: exit 0, empty diagnostics.
- Joint-cofinal C7 strengthening added after its paper proof above.
- Canonical source:
  `formal/GaloisForLFunctions/BezoutValuationIncidence/UniformCofinalMobiusPrefixDiscrepancy.lean`.
- Original-source `lake --old env lean -j 1`, session 6514: exit 0,
  empty diagnostics; matching `.olean` and `.ilean` emitted.
- SHA-256: `32d6a67042394eb7a8c31a17e411334e622321dc1796739540a48eb57bb4a304`.
- All eight public declarations audited in session 84742: exit 0,
  only `propext`, `Classical.choice`, `Quot.sound`.
- Leaf wired into BVI umbrella; index regeneration passed. No umbrella
  build or full build was run.
- Global lint exited 1 for concurrent unrelated
  `BiScaleUncertainty.PrimeRawMomentContrasts` reachability and root
  `TransHorizonIncidenceMechanics.lean` placement. No error names this
  task's three leaves. Other work was preserved.
- Evidence archived in `logs/bvi-uniform-cofinal-2026-10-18-*`:
  source manifest, canonical diagnostics, complete axiom output,
  index output, and complete lint output.
- All owned Lean jobs terminal; completed C6-C7 scratch removed.
