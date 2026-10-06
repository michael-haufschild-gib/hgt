# BAG: complete fixed-radius hyperbolic prime cancellation

- **ID:** bag-hyperbolic-prime-full-cancellation-23az
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/bag-hyperbolic-phase-cell-cancellation.md
- **Statement:** For every natural M, the full original sharp hyperbolic prime packet has complex norm o(N/log²N), retaining both contraction exclusions and every allowed p=q collision.

## Result

The literal packet sums the original cubic main entry over ALL primes
p,q,r in (N,2N] with p≠r, q≠r and |p-r||q-r|≤Mr. Lean proves

    (log²N/N) * |chiCubicHyperbolicPrimeFullPacket(N,M)| -> 0

as the REAL scale N tends to infinity, for every natural M. There is no
analytic or arithmetic premise. This completes the full fixed-radius
theorem, beyond the ordered sector established in 22az.

## Proof

Equal gaps force q=p or p+q=2r. Hence each active p,r has at most two
tie primes q. The literal entry norm is at most 2π/N for every positive
real N and actual prime-band triple. Thus every complete tie row has
norm at most 4π/N, with the allowed collision p=q explicitly retained.

Let D=floor(sqrt(2MN)). Every active tie pair has 0<|p-r|≤D.
The exact two-sign prime-gap reindexing and proved prefix sieve give
at most 2A DN/log²N such pairs. Consequently the entire tie packet has
norm at most 8πA D/log²N; its normalized norm is at most
8πA sqrt(2M)/sqrt N and tends to zero.

The literal cubic entry is symmetric in p,q. Partition every finite
triple into the two strict gap orders and the equality sector. Exact
sum commutation proves

    full packet = 2 * original ordered packet + complete tie packet.

The ordered cancellation theorem and the new tie estimate finish the
full packet. A second exact partition proves, at EVERY real N and M,

    original off-diagonal cubic = full packet + full complementary tail.

The tail definition retains ALL triples with Mr<|p-r||q-r| and both
original contraction exclusions. No tail saving or exchange of limits
M→∞ and N→∞ is asserted.

## Lean and audits

- ChiCubicHyperbolicPrimeTies.lean,178 lines: tie definition18,
  actual real-scale entry bound25, complete tie cancellation100.
  Final foreground37784 exit0, empty02az log.
- ChiCubicHyperbolicPrimeFullPacket.lean,149 lines: full definition19,
  exact completion41, full cancellation101, entire tail122, exact
  original cubic decomposition129. Final foreground6429 exit0,
  empty02az log.

Both final audits used `lake --old env lean <leaf> -o <olean>`;
one owned foreground build at a time. Both leaves wired exactly once
into RHTower. Imported axiom audit42526 exit0: all EIGHT public
declarations depend only on propext, Classical.choice, Quot.sound.
No sorry, admission, new axiom or heartbeat override.

Index88869 passed; all eight public LEAN_API rows checked. Authoritative
lint38578 exit1:367 large-file warnings and22 unrelated unreachable
modules; no finding on either new leaf. Global lint is NOT clean.
Evidence logs:

- /tmp/bag-hyperbolic-prime-ties-02az.log
- /tmp/bag-hyperbolic-prime-full-packet-02az.log
- /tmp/bag-hyperbolic-full-packet-axioms-23az.log
- /tmp/bag-hyperbolic-full-packet-index-23az.log
- /tmp/bag-hyperbolic-full-packet-lint-23az.log

No full/umbrella build, numerical experiment, subagent, commit or push.
Full cubic-tail cancellation, growing moments/cofactors, deterministic
common-height self-return and RH remain open. The RH goal stays active.

## Gates

- [x] 0 → 1: literal source and unconditional target.
- [x] 1 → 2: complete finite partition and tie-count proof.
- [x] 2 → 3: both leaf and imported axiom audits passed.
- [ ] 3 → 4: standalone publication review.
