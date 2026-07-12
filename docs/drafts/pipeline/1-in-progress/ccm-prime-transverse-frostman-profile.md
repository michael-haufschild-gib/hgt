# Prime-complete transverse Frostman profile in CCM local-factor geometry

- **ID:** ccm-prime-transverse-frostman-profile
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Connes--Consani prime-local Blaschke products, their distinguished pole orbits, and prime-log irrationality
- **Statement:** For distinct primes `p,q`, evaluation of the `q`-local Frostman shift along the distinguished `p`-pole orbit has an explicit Poisson-kernel defect whose lower envelope is `((q-1)/(q+1))^2`; hence the marked transverse profile recovers `q` exactly.

## Goal

Replace the prime-blind universal Calkin boundary character by the positive datum a successful CCM construction is forced to retain: the incidence of each local projection/model kernel with the distinguished pole orbit of every other prime. The intended theorem separates unmarked quotient geometry from marked prime-complete geometry inside the same local-factor Hardy system.

## Gates

- [x] 0 → 1 in-progress: explicit source formula, arithmetic density mechanism, recovery formula, and a primary-literature gap identified
- [ ] 1 → 2 fully-proven: complete paper proof of the exact profile, lower-envelope sharpness, and recovery
- [ ] 2 → 3 formalized: all scalar and density theorems in Lean with no project axioms or placeholders
- [ ] 3 → 4 publication-ready: bundle with the all-prime Calkin character only after novelty and significance exceed 90/100

## Candidate theorem

Let `B_q` be the Connes--Consani Blaschke product attached to the `q`-local pole lattice and let `x_p(n)` be the `n`th pole point of the `p`-local factor. Define the normalized transverse model-kernel defect

\[
D_{p\to q}(n):=1-|B_q(x_p(n))|^2.
\]

The explicit Frostman-shift identity predicts

\[
D_{p\to q}(n)
=\frac{(q-1)^2}
 {q^2-2q\cos\!\left(2\pi n\frac{\log q}{\log p}\right)+1}.
\]

For distinct primes, `log q / log p` is irrational. Therefore the marked orbit is dense in the angular variable and

\[
\inf_{n\in\mathbb Z}D_{p\to q}(n)
=\left(\frac{q-1}{q+1}\right)^2,
\qquad
\sup_{n\in\mathbb Z}D_{p\to q}(n)=1.
\]

Writing `m_q` for the lower envelope gives exact recovery:

\[
q=\frac{1+\sqrt{m_q}}{1-\sqrt{m_q}}.
\]

## Positive carrier law

The unmarked polynomial Calkin quotient admits a universal character taking every prime projection to `1`. The marked transverse Frostman profile retains the missing arithmetic coordinate and recovers every target prime. Thus a viable CCM construction must preserve the pole-orbit/model-kernel incidence marking through its semilocal completion; projection algebra or finite quasi-innerness alone is not the full carrier.

## Parent-theory attack

- The scalar identity uses the classical Frostman-shift formula and the standard model-space diagonal kernel.
- Density uses classical irrational rotation.
- The candidate new content is their exact cross-prime assembly for the Connes--Consani local-factor system and the resulting prime-recovery law.
- If the recovery law or an equivalent cross-prime profile appears in the literature, this card must be downgraded to a bridge.

## Open core

1. Formalize the exact complex Frostman value and its defect formula.
2. Formalize irrationality of `log q / log p` for distinct primes from prime-log linear independence.
3. Formalize sharp lower-envelope and upper-envelope approximation along the integer pole orbit.
4. Decide whether to formalize the full Hardy projection identity or state the theorem intrinsically as the normalized model-kernel diagonal.
5. Complete the exact primary-source audit, including Crofoot/Frostman model-space transforms and later Toeplitz-kernel literature.

## Current verdict

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` only provisionally. The formula is not in the inspected Connes--Consani paper and exact web searches found no cross-prime treatment. Current significance estimate: 91/100 if the prime-recovery law and its marked-versus-unmarked consequence survive the full parent-literature audit; otherwise 75/100 as a model-space bridge.
