# Sixth-order recovery for finite odd-prime mode families

- **Stage:** 2-fully-proven
- **Type:** PROVED ON PAPER; Lean formalization in progress
- **Wall:** 15, support versus orientation; field research only
- **Parent:** [sharp sixth-moment recovery in the even prime-pair sector](../3-formalized/wall15-sixth-moment-recovery-in-the-even-prime-pair-sector.md)

## Question and exact objects

Let S be a finite set of odd primes and choose real coefficients a_p. At any cutoff containing every 2p, use the actual divisor weights

`c_a(d)=Σ_(p∈S) a_p [1_(d=1)−2·1_(d=2)−p·1_(d=p)+2p·1_(d=2p)]`.

The literal response should be

`s_a(n)=(2·1_(2∣n)−1) Σ_(p∈S) a_p(p·1_(p∣n)−1)`.

The multiples coordinates should be exactly `Y(2p)=a_p`, zero elsewhere. This is a finite-dimensional sector of the existing sieve, not an assumed Fourier model. Include empty support and zero coefficients in the statement.

**C1: complete degree-six recovery.** Equality of all affine quadratic data and all translated sixth moments is equivalent to one common coefficient sign. Prove a finite set of explicit sixth Fourier readouts already suffices; do not replace them by assumed pair products.

**C2: sharp lower-order obstruction.** Every independent coefficient sign change preserves every translated moment of degree at most five. Combined with the parent's two-mode witness, six is the sharp uniform degree for this class. A single zero-lag sixth moment should not be assumed sufficient in higher dimension: it aggregates many cross terms.

**C3: one zero-lag sixth moment can still lose signs in dimension three.** Proposed explicit sector S={3,5,7}: choose positive real u,v with u³=5 and v³=2, and compare coefficient vectors `(1,u,−v)` and `(1,−u,v)`. They have identical coordinate squares and are not common-sign multiples. The prime-row third moments are γ_p=(p−1)(p−2). Hence γ_5 u³=12·5=60=30·2=γ_7 v³. The two cross terms involving the prime-3 mode cancel in the sixth-moment difference, while the prime-5/prime-7 cross term has unchanged sign. All even-multiplicity terms agree. Derive this from the actual three-prime CRT expansion; do not count it as a certified counterexample yet. The positive survivor to audit and formalize is C1's full lag-data decoder.

## Proposed mechanism requiring audit

For a factorial period P and an odd prime p, the three frequencies

`P/(2p), P/(2p), (p−2)P/(2p)`

all have additive order 2p and sum to P/2. Pair that triple with the negatives of the corresponding triple for q. The resulting six frequencies sum to zero, so the literal six-point Fourier coefficient should expose `a_p³a_q³` with an explicit nonzero power of P. A general anchored five-lag transform should yield `P^5` times the six coordinate product. Derive normalization from the actual average and check it before claiming recovery.

Real cube injectivity would recover each signed pair product a_p a_q. Existing affine classification supplies the squares. Equality of the full outer-product matrix determines the real coefficient vector up to a common sign, including zeros.

For quartic blindness, expand into prime-row assignments. A term with an odd multiplicity of some prime has either one occurrence of that prime or three occurrences and a lone different prime. CRT averaging kills the lone centered row. Only multiplicities four or two-plus-two survive. The shared odd anti-period `∏_(p∈S)p` should annihilate every odd-degree moment. These structural arguments must be audited on the actual weights and full lag families.

## Dependency-closed paper audit

**Unconditional readout, stronger than C1.** Let P=N!, and write d=2^k p, e=2^k q with p,q positive odd and d,e≤N. Put r=P/d and s=P/e, viewed modulo P. The order of r is exactly d. If p=1, the triple `(r,r,−r)` has three entries of order d and sum P/2^k. If p≥3, use `(r,r,(p−2)r)`. Its sum is again P/2^k; p−2 is odd and coprime to p, so it is coprime to 2^k p and the third entry has order d. The q triple has the same sum. Concatenating the p triple with the negatives of the q triple gives six frequencies of total sum zero, with orders `(d,d,d,e,e,e)`.

For the actual normalized m-lag average M_f(h)=P⁻¹Σ_n∏_i f(n+h_i), define its unnormalized Fourier transform in **all m unanchored lag variables**. Expanding finite sums gives

`DFT_m M_f(r)=1_(Σr_i=0) ∏_i DFT(f)(r_i)`.

Each lag sum contributes `χ(n r_i) DFT(f)(r_i)`; the base-point average of `χ(n Σr_i)` is exactly the zero-frequency indicator. Thus the selected six-frequency coefficient is `P^6 (Y_c(d)Y_c(e))^3`. The factor is P^6 because six unanchored variables are transformed; P^5 belongs to the distinct anchored five-variable convention. This normalization change does not change the given full sixth-lag observation family. No support or nonvanishing assumption enters this actual-sieve identity.

Equality of full sixth-lag data therefore implies equality of every signed pair product within each fixed power-of-two valuation class. Real cube injectivity removes the cube, and P>0 removes the scalar. A real vector is determined up to common sign by its outer-product matrix: if it is zero, diagonal products force the other vector to be zero; otherwise choose a nonzero coordinate, use its square to select a sign, and use its products to recover all other coordinates. This proves the proposed block recovery, including empty and zero blocks.

**Actual finite-prime family.** For each cutoff N, use the finite index set of odd primes p with 2p≤N and arbitrary real coefficients. Expanding the four divisor atoms for each p gives exactly `parity(n)Σ_p a_p R_p(n)` and the multiples profile `Y(2p)=a_p`, zero elsewhere. Consequently, sixth-lag data **alone** determine all coefficients up to common sign. The finitely many explicit pair readouts suffice; affine data are redundant for this recovery theorem. Global sign preserves every sixth moment, proving the reverse implication. This includes every finite odd-prime family by setting unused coefficients to zero.

**C2.** Exact CRT identifies averaging over one full product period with independent uniform residue coordinates at the distinct odd primes; that product divides N!, so complete factorial-period averages agree. Every shifted centered row has zero mean. Expand a four-lag product by assigning a prime to each of its four factors. Unless the assignment is one repeated prime or two repeated pairs, at least one prime appears once, and its independent centered factor kills the term. Surviving coefficient powers are all even, hence every independent coefficient sign change preserves every quartic lag. The degree-two argument is identical. The odd product of supported primes flips the common parity factor and preserves every prime row, annihilating every odd-degree moment. Degree zero is constant. All through-five data are therefore independently sign-blind. Existing affine classification also makes all affine data independently sign-blind because distinct supported indices 2p,2q are incomparable.

**C3 and its positive survivor.** At cutoff N+14, keep only p=3,5,7. Choose positive u,v with u³=5,v³=2; existence follows from the bijectivity of the real cube and positivity follows from the cube signs. Put X=R3 and W=uR5−vR7. The two literal responses are `parity·(X+W)` and `parity·(X−W)`. At degree six the parity factor disappears and

`(X+W)^6−(X−W)^6=12X^5W+40X^3W^3+12XW^5`.

CRT separates X from W. Both first moments vanish; the middle contribution also vanishes because `E[W³]=12u³−30v³=0`. Hence the scalar sixth moments agree. Coordinate squares agree, so all affine data agree; C2 and the anti-period give equality of all through-five and all odd translated data. The vectors `(1,u,−v)` and `(1,−u,v)` cannot differ by a common sign because the first coordinate is one and u>0. The explicit p=3/q=5 sixth Fourier readout differs by `10P^6`, since its signed cubes are +5 and −5. The strongest positive survivor is therefore an explicit observable separating the scalar collision, together with unconditional block recovery and complete finite-family reconstruction.

All arguments use finite bijections, exact divisor sums and symbolic algebra. No period enumeration, numerical experiment or added analytic premise. Lean must certify these exact statements before the route is retired. The bounded frontier searches `/tmp/bsu-family-frontier-r1.json` and `/tmp/bsu-family-fourier-r1.json` were inspected in full (20 candidate and 20 source inventories each; one unrelated continuum-moment ingredient set). Both report `partial=false`, older coverage snapshots, unmeasured semantic coverage and unfinished background refresh. No absence or external novelty claim.

## Earlier bounded frontier evidence

`/tmp/bsu-sixth-next-frontier-r1.json`: query `sixth polyspectrum prime modes relative phase recovery`, scoped to BiScaleUncertainty. All 20 candidates and 20 source arguments inspected. Returned material includes the current two-row sixth polynomial, prior affine/triple/parity certificates and continuum cycle recovery; no direct finite-family sixth readout among returned hits. `partial=false`, older coverage snapshot, semantic coverage unmeasured, background refresh incomplete. No global absence or external novelty claim. Refresh before implementation.

The new issue is arbitrary support size, full lag-data Fourier isolation and a uniform recovery theorem. Generalizing the two-prime numerical constants alone is not a separate contribution. No claim about arbitrary divisor-coordinate supports, stability, or demolition of Wall 15.

No RH work, numerical experiments, new analytic premises/axioms, heartbeat increases or full builds. Both field READMEs and the wall ledger stay read-only.

## Gates

## Task tracker

1. [done] Refresh corpus frontier; audit six-frequency normalization, primitive triples, all finite-support and zero cases, quartic blindness and the three-mode scalar counterexample.
2. [in progress] Formalize the exact actual-sieve theorems, including stronger unconditional readouts. Eight original named-source leaves pass; the ninth actual three-prime scalar witness is checking. One owned foreground Lean process at a time.
3. [pending] Audit all public signatures, definition bodies and axioms; wire leaves; verify complete discovery, index/lint, protected hashes, memory and cleanup.

`update_plan` is unavailable; this card is the durable tracker. The user cleared the previous goal and requested completion of this started package only. Owned scope: this card and its stage move, nine new BiScale leaves, their umbrella imports, generated indexes, direct related-card links, the exact scalar-observation no-go with its positive survivor, memory and cleanup. No next-topic card or new research route. Preserve other workers' modules/cards/counters. Both field READMEs and the wall ledger remain read-only.

**Stronger conjecture exposed during initialization:** For arbitrary actual sieve weights, full sixth-order translated data may recover every pair product of multiples coordinates whose indices have the same power-of-two valuation. Primitive triples with a common sum would give a direct readout. If proved, sixth data alone would recover each such coordinate block up to a common sign, with no support or nonvanishing premise. Audit before upgrading C1; do not substitute this for the outstanding lower-order and scalar-observation claims.

- [x] Refresh frontier and check six-frequency additive orders and Fourier normalization.
- [x] Dependency-closed paper proof for arbitrary finite support and zero cases.
- [ ] Formalize exact actual-object theorem and all lower-order obstruction claims.
- [ ] Named-source checks, public signature/axiom audits, wiring, index/discovery/lint.

## Formalization checkpoint

Eight original named-source leaves now pass without diagnostics and are wired: general Fourier moments, primitive triple resonance, unconditional valuation-block recovery, actual odd-prime atoms, finite CRT and quadratic/quartic calculus, literal translated moments, complete family phase recovery, and symbolic three-prime sixth cancellation. C1 and C2 are formalized, including finite-support zero extension. The ninth leaf connects the scalar collision to actual weights and explicit separating observations; its final check and the complete public/API/axiom and integration audit remain. No full or umbrella build was run. Current durable process/check ledger: `/tmp/bsu-family-phase-session.json`.
