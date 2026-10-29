# Every prime pattern has actual conductor coordinates

- **ID:** ACP-ALL-PATTERN-ACTUAL-CONDUCTOR-COORDINATES
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; immediate formalization)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** EveryPrimePatternHasActualConductorCoordinates.lean
- **Input:** ../3-formalized/arithmetic-counting-infinite-conductor-mass-boundary.md

## Exact objects and endpoints

For any prime pattern P, let F_N be the flipped primes visible at integer
horizon N. Define v_(P,N) using the existing actual finite-prime horizon
vector for F_N. Its entries are omega_P(n)/(sqrt(n)sqrt(H_N)), since the
full and cutoff signs agree for every n<=N. Let h_(m,N) be the existing
normalized Ramanujan quasimode and a_P(m) the counted coefficient.

The six endpoints assert:

1. ||v_(P,N)||^2=1 for N>=1.
2. Its inner product with h_(m,N) is the literal mixed harmonic count
   divided by H_N sqrt(phi(m)).
3. For every m>=1, that inner product tends to a_P(m).
4. Projecting h_(m,N) onto any fixed positive-width energy window about
   its conductor energy preserves the limiting squared coefficient.
5. Some such window is eventually a singleton actual eigenline, whose
   energy tends to E_m and squared v_(P,N) coordinate tends to a_P(m)^2.
6. There is an actual eigenline index sequence on horizons N+1 realizing
   both limits for all sufficiently large horizons.

These statements cover every P. No finite support, positive Euler density,
assumed spectral coordinate or assumed mass-exhaustion hypothesis is added.

## Actual horizon and exact inner product

The cutoff identity omega_P(n)=omega_(F_N)(n) holds throughout [1,N]. Thus
the existing finite-prime norm calculation applies pointwise with F=F_N,
giving exact unit norm. The existing finite-prime mixed inner-product
identity also applies pointwise. Replacing each finite sign in its finite
sum by omega_P gives exactly the new mixed arithmetic count.

This step uses no fixed-F limit theorem on the growing family F_N. Its
limiting input is instead the independently proved arbitrary-pattern
Ramanujan mean T_P(m,N)/H_N -> c b_P(m). Divide by sqrt(phi(m)) to get
the actual inner-product limit a_P(m).

## Projection transfer

For each m>=1 and fixed width delta>0, the existing conductor quasimode
theorem proves

||h_(m,N)-Pi_(m,N,delta) h_(m,N)|| ->0,
||Pi_(m,N,delta) h_(m,N)||^2 ->1.

These errors are independent of P. Cauchy--Schwarz and exact unit norm give

|<v_(P,N),h_(m,N)-Pi h_(m,N)>| <= ||h_(m,N)-Pi h_(m,N)|| ->0.

Hence the projected inner product has the same limit a_P(m). Squaring and
dividing by the projection norm squared gives limit a_P(m)^2. The limiting
denominator is one, so this does not require a_P(m) to be nonzero.

## Singleton energy window and actual coordinate

The existing simple-conductor-window theorem provides delta>0 such that
the window about E_m is eventually a singleton and its actual eigenvalue
approaches E_m. Its projected quasimode norm is eventually positive.
On such a singleton window with normalized eigenvector e, the projection
is <h,e>e. Therefore

<v,Pi h>^2/||Pi h||^2 = <h,e>^2 <v,e>^2/<h,e>^2 = <v,e>^2.

The cancelled scalar is nonzero because the projected norm is positive.
This proves the actual squared-coordinate limit for every index in the
window. It remains valid when the resulting limit is zero.

For a sequence defined at every N, work on horizon N+1, which has the
index n=1 available. Choose a window member when the window is nonempty,
and this default index otherwise. The eventual singleton property makes
the chosen index a window member eventually. Both uniform-in-window
limits therefore apply to that actual index sequence.

## Dependency and novelty audit

The finite-prime coordinate leaf was read through its norm, inner-product,
projection, singleton-window and index-selection proofs. Its pointwise
identities are reused at F_N. The arbitrary-pattern mixed harmonic mean
supplies the new limiting input, avoiding an invalid exchange of fixed
prime support and growing integer horizon.

Together with the separate zero/unit coefficient-mass theorem this
identifies whether the counted actual conductor coordinates retain unit
mass or vanish at every fixed conductor. No literature-wide priority
claim is made. The contribution is a transfer to actual prime-matrix
coordinates for unrestricted prime support, with every arithmetic and
projection error discharged.

Escape from every fixed conductor packet is distinct from escape from
every bounded energy window. The latter requires completeness of the
bounded-energy spectral count. A full resolvent transfer and optimal-gap
classification are separate obligations. No complete Weil positivity or
zero-gap converse is claimed.

## Formalization

The immediate full six-endpoint draft is
/tmp/acp-all-pattern-actual-conductor-coordinates-check.lean. It imports
the new infinite conductor-mass leaf and the existing finite-coordinate
leaf. The mass leaf passed its canonical and standard-axiom audits. Its first
olean is now required by this actual draft. No existing
olean is rebuilt and no numerical experiment is used.

- [x] Dependency-closed paper argument, including zero coefficients.
- [x] Immediate full Lean draft with the same six endpoints.
- [ ] Scratch and transitive axiom audit.
- [ ] Canonical source check, umbrella and durable evidence.
