# Sixth-order recovery for finite odd-prime mode families

- **Stage:** 0-backlog
- **Type:** CONJECTURE; no Lean certificate
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

## Evidence and boundaries

`/tmp/bsu-sixth-next-frontier-r1.json`: query `sixth polyspectrum prime modes relative phase recovery`, scoped to BiScaleUncertainty. All 20 candidates and 20 source arguments inspected. Returned material includes the current two-row sixth polynomial, prior affine/triple/parity certificates and continuum cycle recovery; no direct finite-family sixth readout among returned hits. `partial=false`, older coverage snapshot, semantic coverage unmeasured, background refresh incomplete. No global absence or external novelty claim. Refresh before implementation.

The new issue is arbitrary support size, full lag-data Fourier isolation and a uniform recovery theorem. Generalizing the two-prime numerical constants alone is not a separate contribution. No claim about arbitrary divisor-coordinate supports, stability, or demolition of Wall 15.

No RH work, numerical experiments, new analytic premises/axioms, heartbeat increases or full builds. Both field READMEs and the wall ledger stay read-only.

## Gates

- [ ] Refresh frontier and check six-frequency additive orders and Fourier normalization.
- [ ] Dependency-closed paper proof for arbitrary finite support and zero cases.
- [ ] Formalize exact actual-object theorem and all lower-order obstruction claims.
- [ ] Named-source checks, public signature/axiom audits, wiring, index/discovery/lint.
