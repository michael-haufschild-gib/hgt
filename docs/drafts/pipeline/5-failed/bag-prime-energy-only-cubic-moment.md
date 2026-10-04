# BAG joint cubic: energy-only estimate and coherent prime packets

- **ID:** BAG-C28.56a
- **Stage:** 5-failed
- **Type:** FALSIFIED ESTIMATE / positive survivor LEAN PROVED
- **Source:** ChiPrimeGaussianCubicMain, ChiPrimePacketFourthMoment, ChiPhysicalStationaryKernel
- **Statement:** Actual flat, unit-energy prime packets have unbounded signed physical adjacent cubic per unit height.

## Route and hard problem

BAG C28.44 requires cancellation of the full signed Gaussian three-prime sum at contraction scale. Test whether a joint coefficient-energy estimate can supply it. This card addresses that proposed mechanism; it does not replace the full-window problem or retire BAG.

## Corpus-derived paper argument

The exact cubic phase recentering is exp(2πi pq/r)=exp(2πi(p-r)(q-r)/r). For every integer triple in [N,N+H], its distance from 1 is at most 2πH²/N. For H≤N/32 the saddle pq/r lies in [5N/6,7N/6]. At physical height T=(4π/3)N the entire saddle lies in the actual W plateau. The complete grade-one stationary theorem supplies amplitude 2π√(pq/r), with both remainders O(1/√N). Thus, for sufficiently large N and 2πH²/N≤1/4, every literal complete physical cubic entry has real part at least π√N/4. Every nonnegative tensor supported in the box retains that positive mass.

The source PNT plus finite pigeonhole already constructs actual primes S⊆[N,N+m⁴], 64m⁸≤N≤128m⁸, M=|S|≥m³, for every sufficiently large m. With P=Σ exp(it log p), expansion gives Re∫WχP²conj(P)≥π√N M³/4. For Q=P/√M, coefficient energy is exactly one, maximum coefficient ≤1/m, and Re∫WχQ²conj(Q)≥π√N M√M/4≥T√m/64. All physical terms remain. This diverges per unit height and refutes every eventual uniform cubic energy-and-flatness-only bound.

## Stronger survivor: contractions removed

Apply the positive tensor theorem to the literal mask p≠r and q≠r. Exactly M(M−1)² triples remain. For M≥2 this is at least M³/4, so after the identical unit-energy normalization the original real physical mass is at least π√N M√M/16≥T√m/256. Thus the obstruction persists in the noncontracting adjacent cubic itself. This strengthening is Lean proved, including the exact polynomial identity P²*conj(P)-(2M-1)P before normalization.

## No-go closure

- **Killing mechanism:** Coherent hyperbolic prime-gap phase in actual dense prime cells; no independent residue averaging is licensed.
- **Positive survivor:** Constructed prime family with positive signed grade-one cubic growth, full physical kernel and both errors retained.
- **New constraint:** A useful joint estimate must exploit actual full-window Gaussian coefficient distribution beyond primality, unit energy, and individual flatness.
- **Killing theorem:** `RHTower.no_uniform_flat_prime_packet_cubic_offDiagonal_bound` in `ChiPrimePacketCubicMoment.lean`.
- **Strongest positive survivor:** `RHTower.eventually_exists_flat_prime_packet_cubic_offDiagonal_large` constructs the actual primes, exact coefficient energy and flatness, and net signed noncontracting mass together. `exists_physicalCubicPacket_positive` supplies the underlying arbitrary nonnegative correlated-tensor law with both full physical errors.
- **Status:** Dependency-closed paper proof and exact Lean survivor both complete. Direct final audits8716 and4748 passed using `lake --old env lean <leaf> -o <olean>`, without warnings. All14 public declaration axiom queries58026 passed using only `propext`, `Classical.choice`, `Quot.sound`. Both leaves wired into RHTower.lean; no umbrella/full build. Exact source index33760 finds both capstones. Lint51430 reports13 unrelated unreachable leaves and zero new BAG errors; global lint is not clean. Full signed Gaussian complement, growing moments, moving cofactors and positive self-target recurrence remain open.

## Log

- 2026-10-03 — Joint Vaughan/reciprocal sources examined. Pointwise estimates followed by absolute outer summation retain known scale loss. Formalizing cubic coherent obstruction before pursuing a universal joint operator estimate. No numerical experiment.

- 2026-10-03 — Both production leaves and all14 axiom audits passed. Energy-only estimate and strongest positive survivor closed together. C28.56b continues the actual full-window joint signed problem, retaining the prime-power correction inside any Vaughan argument.
