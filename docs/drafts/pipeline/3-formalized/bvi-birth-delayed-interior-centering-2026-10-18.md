# Birth-delayed interior centering and uniform pair bounds

- **ID:** BVI-BIRTH-DELAYED-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Problem 4 of `docs/reports/walls/bezout-wall1-programme.md`
- **Statement:** Retaining the initial-value correction and delaying conditional centering bounds each compensated interior/jump pair by `1/d + 2/gcd(d,e)`.

## Goal and exact scope

Remove the linear growth in the interior modulus from the previous bound
`(e/gcd(d,e))/d`. This is a finite-horizon pair estimate for the actual
anchored interior observable. The signed modulus sum and the requested
strict contraction remain open. No numerical experiment is used.

For integers d>=2 and e>=1, put g=gcd(d,e), m=e/g, K=floor(e/d), and

    A_e = (e-1)/(2e),
    J_e(n) = interiorSawtoothAtom e n,
    gamma(d,e) = interiorJumpOrbitMean d e,
    F_e(n) = J_e(n)-A_e,
    n_k = d-1+dk,
    w_d,T(k) = max(1/(d(k+1))-1/(T+1),0),
    R_d,e(k) = F_e(n_k) - 1_(K<=k)(gamma(d,e)-A_e).

For every finite T,L,

    |sum_{k<L} w_d,T(k) R_d,e(k)|
      <= K/e + 2m/(d(K+1))
      <= 1/d + 2/g.

The sharper first bound retains information when d exceeds e. Centering
starts exactly when e<=n_k; the floor condition is a jump-index expression
of the same threshold. This observation does not change the summation
order or silently replace the finite divisor cutoff.

For arbitrary real coefficients c and cutoff N,

    bezoutInteriorSawtoothSum N c n - weightedCenteredSawtoothSum N c 0
      = sum_{1<=e<=N} c(e) F_e(n).

Consequently, subtracting the signed sum of the delayed means gives the
finite-cutoff bound

    |sum_{k<L} w_d,T(k) [
        bezoutInteriorSawtoothSum N c n_k - weightedCenteredSawtoothSum N c 0
        - sum_{1<=e<=N} c(e) 1_(floor(e/d)<=k)(gamma(d,e)-A_e)]|
      <= sum_{1<=e<=N} |c(e)| [1/d + 2/gcd(d,e)].

All cutoff dependence remains displayed. For the horizon-free arithmetic
prefix, the existing exact affine bridge also retains
`n*(selbergMultiplesCoord N c 1 - density)`; this term is not discarded.

## Dependency-closed paper proof

**[PROVED HERE]** Before birth, k<K implies 1<=n_k<e and n_k+1<=e.
The current endpoint e|n_k cannot occur. If the successor endpoint occurs,
then n_k+1=e and F_e(n_k)=-A_e. Otherwise the residue formula gives
F_e(n_k)=-n_k/e. In either case

    |F_e(n_k)| <= d(k+1)/e.

Since 0<=w_d,T(k)<=1/(d(k+1)), each initial-segment term has absolute value
at most 1/e. Its sum is at most K/e.

At and after birth, R_d,e(k)=J_e(n_k)-gamma(d,e). The certified orbit
theorem bounds every prefix of this centered sequence by m. A prefix
starting at K is the difference of two such prefixes, so its absolute value
is at most 2m. The existing nonnegative antitone-weight Abel inequality
then bounds its weighted sum by

    2m*w_d,T(K) <= 2m/(d(K+1)).

Splitting an arbitrary finite range at K proves the first inequality;
when L<=K, only the initial-segment estimate is needed. Euclidean division
gives dK<=e<d(K+1), hence K/e<=1/d and
2m/(d(K+1))<=2/g. This proves the second inequality.

The anchored-observable identity follows from the certified atom
decomposition and the exact sawtooth value at zero, -A_e. Exchange finite
sums and use the triangle inequality to obtain the arbitrary-coefficient
bound. No infinite-limit interchange or analytic assumption is used.

## Research audit and next conjecture

Live corpus queries covered periodic harmonic remainders, sawtooth
progression coherence, and birth-delayed harmonic centering. Candidate
lemmas and source arguments were inspected. The last two queries completed
with no partial stages or search errors; compiler coverage is mostly
source-only, so applicability is checked separately in Lean.

This is a local source audit, not a claim of novelty across mathematics.
Residue formulas, bounded periodic prefixes, and Abel summation are reused.
The change is which observable is centered and when: the initial anchor
must be retained before analyzing conditional jump cancellation.

The next conjecture must couple the signed modulus rows. For small positive
epsilon, replacing c(e)=mu(e)e^(-epsilon) by |c(e)| in the displayed bound
still does not give a cutoff-uniform estimate. The delayed drift and the
linear density correction must also be retained. Raw logarithmic
coherence before birth does not by itself obstruct the original problem.

## Verification

Original named source:
`formal/GaloisForLFunctions/BezoutValuationIncidence/BirthDelayedInteriorJumpCenteringAndUniformPairBounds.lean`
(385 lines, eleven public declarations). The final theorem applies the
bound to `pmBezoutInteriorPrefix` at cutoff `(d+2)*L`, retaining the
linear density term and the complete signed delayed mean.

Original-source `lake --old env lean -j 1` audit passed in session 67436,
exit 0, with no diagnostics. Fresh `.olean` and `.ilean` emitted; umbrella
import added. Evidence: `logs/bvi-birth-delayed-2026-10-18-source.txt`.
The complete public axiom audit passed in session 45245, exit 0. All eleven
public declarations use exactly `propext`, `Classical.choice`, `Quot.sound`.
The same scratch file verified eleven existing cross-depth, predictor and
integer-jump APIs and their axiom closures. Evidence:
`logs/bvi-birth-delayed-2026-10-18-axioms.txt`.

Source SHA-256:
`52988d1381f1a16991d3544fe294e5c4d1bf1e08f59ed26fec5415c4cfa76643`.
Final index refresh passed (30882, exit 0). Final lint (49632, exit 1)
reported seven unrelated CHMD reachability errors, one root-module placement
error, and two generated files stale again after concurrent changes. It
reported no finding on this module. Global lint is not clean. Exact errors,
source/artifact hashes, all 22 axiom closures and search coverage are in
`logs/bvi-birth-delayed-2026-10-18-manifest.json`. Forty-eight owned proof
scratch/search files were archived and removed; other workers' files were
preserved. Original-source and axiom processes are terminal. This task made
no field README edit. Its diff was empty at certificate creation; later
concurrent README additions are preserved.

## Log

- 2026-10-18 — Dependency-closed paper proof recorded; shifted-tail and initial-segment estimates checked in scratch Lean. Full contraction remains open.
- 2026-10-18 — Original source and all eleven public axiom closures passed; promoted to stage 3. Expanded corpus audit changed the next route to reuse existing all-depth and integer-jump machinery.
