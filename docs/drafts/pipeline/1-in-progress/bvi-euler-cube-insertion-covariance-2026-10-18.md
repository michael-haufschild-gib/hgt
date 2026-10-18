# Prime-insertion covariance on the actual Euler cube

- **ID:** BVI-EULER-CUBE-INSERTION-COVARIANCE-2026-10-18
- **Stage:** 1-in-progress
- **Session:** Paused at user request; no Lean work started for this candidate.
- **Type:** CONJECTURE / source and paper audit
- **Parent:** `bvi-interior-martingale-coercive-contraction-2026-10-18.md`
- **Full objective:** Strict interior contraction remains open.

## Candidate and its limits

Let f_r be the existing Ramanujan step vector, r>1. For positive e and
squarefree P coprime to r, use the existing coherent Hilbert cube

    F_(e,P,r) = sum_{d|P} mu(d)*d^(-1/2-e)*D_(1/d) f_r.

For a prime p not dividing P*r, test the candidate

    Re <F_(e,P,r), D_(1/p) F_(e,P,r)> >= 0.

This is unproved. A fixed-base estimate, even if established, still needs
transfer to the cofinal actual arithmetic field; it does not complete
Problem 4. No transfer or sign assumption is allowed in a final theorem.

The existing prime-insertion factorization gives

    ||F_(e,pP,r)||^2
      = (1+p^(-1-2e))*||F_(e,P,r)||^2
        -2*p^(-1/2-e)*Re <F_(e,P,r),D_(1/p)F_(e,P,r)>.

The proposed sign would bound each insertion by its square-weight cost.
The local Euler prefactors must also be retained. This would address a
specific missing inequality; the exact norm identity is already known
in the corpus and is not a new result.

## Existing corpus and audit boundary

- `CrossDepthEulerOperatorFactorizationAndPrimePairGramIdentity.lean`:
  exact one-prime and all-depth source factorizations; exact two-mode
  pronic and energy-centered Gram identities; absolute summability of
  the shifted single-prime covariance for each fixed base r.
- `AllDepthHilbertDilationCubeAndHyperCubeGramFactorization.lean`:
  `all_depth_coherent_pmStepVectorTotal_eq` gives the exact signed cube
  above. Its alternating signs must remain in every estimate.
- `TwoPrimeDilationProfileIdentityAndPrimeStarShearCancellation.lean`:
  the off-diagonal prime-star kernel is the actual dilation profile.
- `RamanujanDilationProfileResidueGapBudget.lean`: near-scale profile
  distance has an explicit gap budget. This is relevant to checking the
  candidate already after one prior insertion.

Live deep search for insertion covariance returned 20 candidate statements
and 20 source statements, all inspected. Semantic retrieval timed out:
`partial=true`, error `local runtime deadline expired`; available hits
remain useful but do not establish an exhaustive frontier. The proposed
ingredient plan uses Cauchy-Schwarz and exact Gram identities; neither
proves a sign. A narrowed lexical query for
`pmRamanujanDilationProfile nonneg` returned zero hits, not an absence proof.

Source inspection covered the exact local factorization, the Hilbert cube,
the two-mode profile formula, and the fixed-base prime-summability theorem.
No new Lean code or numerical experiment has been run for this candidate.

## Paper checks remaining when resumed

1. Check whether the base profile itself has the required sign, using its
   actual arithmetic representation rather than positive semidefiniteness.
2. Expand the covariance after one prior prime insertion. Audit the
   near-ratio term against the two distant-scale terms. Keep both signs.
3. If the sign fails, identify the precise obstruction and strongest
   non-trivial surviving bound before closing the route.
4. If it survives, handle every insertion depth and the actual-field
   transfer. A fixed-base or finite-depth result is insufficient.

## Verification gates

- [x] Candidate derived from current corpus identities.
- [ ] Complete paper proof or exact no-go plus positive survivor.
- [ ] Formalize the dependency-closed conclusion, with no open analytic premise.
- [ ] Original-source, axiom, umbrella, index, lint, and scratch-cleanup audits.

Search evidence is archived in
`logs/bvi-uniform-interior-remainder-2026-10-18-search.tar.gz`, including
`bvi-euler-insertion-covariance-corpus-2026-10-18.json`,
`bvi-dilation-profile-sign-corpus-2026-10-18.json`, the broadened sign query,
and the nearby-prime profile query. Archive members were hash-verified
before removing owned `/tmp` copies; the matching manifest records hashes.

## Candidate obstruction and positive classification to audit

The corpus gives substantially more than a generic dilation identity:

- `tendsto_sqrt_mul_pmRamanujanDilationProfile_prime_of_not_isPrimePow`
  proves sqrt(p)*Phi_r(p)->0 for every fixed non-prime-power r>1.
- `PMRamanujanNearbyPrimeResonance` proves continuity at ratio 1,
  Phi_r(1)=G(r,r)>0, and uses the existing `exists_prime_pair_ratio_lt`
  to obtain distinct arbitrarily large primes in arbitrarily narrow
  multiplicative bands. These inputs were read in source.
- `abs_dilationProfile_sub_finite_lag_sectors_le`, at scales m and 1
  and horizon m-1, should give
  `|Phi_r(m)| <= pmRamanujanPrimitiveBound(r)^2/sqrt(m)`:
  the finite jump-pair set is empty because its first jump is at m.
  Check the exact zero-index and horizon conventions in Lean before use.

For F=f_r-alpha*D_(1/q)f_r, alpha=q^(-1/2-e), the real insertion
covariance expands as

    C_r(e;p,q) = (1+alpha^2)*Phi_r(p)
                 -alpha*(Phi_r(p*q)+Phi_r(p/q)).

Thus a near-ratio term may force a negative insertion covariance even
when both distant-scale terms tend to zero. This expansion itself is
not a novel positive survivor.

The stronger proposed classification is as follows. For each fixed
non-prime-power r>1 and c>=0, select p_j<q_j, both prime and greater
than r+j, with q_j/p_j<1+1/(j+1). Put

    e_j = (c+1/(j+1))/log(q_j) > 0.

Then the proposed exact limits are

    sqrt(q_j)*C_r(e_j;p_j,q_j) -> -exp(-c)*G(r,r),

    sqrt(p_j*q_j)*[||F_(e_j,p_j*q_j,r)||^2
        -(1+p_j^(-1-2e_j))*||F_(e_j,q_j,r)||^2]
      -> 2*exp(-2*c)*G(r,r).

Paper mechanism: sqrt(q_j)*Phi_r(p_j)->0 by the existing prime limit
and q_j/p_j->1; Phi_r(p_j*q_j)->0 by the proposed integer-scale bound;
Phi_r(p_j/q_j)->G(r,r) by continuity. Also
sqrt(q_j)*alpha_j=exp(-c-1/(j+1)). The second limit follows from the
exact insertion norm identity and p_j/q_j->1. This classifies the
additional energy cost at the scale of the squared damping weight.

This is a paper argument under audit, not a completed no-go or Lean
theorem. If verified, it refutes uniform nonnegative insertion while
retaining a precise quantitative resonance law. The replacement target
would control the collective negative insertion budget; a sign claim
is stronger than necessary. Do not retire this route until the strongest
dependency-closed positive statement is formalized.
