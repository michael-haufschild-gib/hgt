# Prime-support boundary jets, stable determinant pencils, and RH

- **ID:** `prime-support-boundary-jet-stability-rh`
- **Status:** `1-in-progress`
- **Type:** `[LARGE OUTLANDISH DETOUR] [PROVED FINITE SOURCE FLOOR] [CONJECTURE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeSupportBoundaryJets.lean`
- **Inputs:** `fermion-number-prime-support-selector-rh.md`,
  `prime-koszul-superdeterminant-cancellation.md`, `PrimeWordSupportSelector.lean`,
  `KoszulCohomology.lean`, `theta-prime-pointed-doubling-fock-carrier.md`,
  `XiLaguerrePolya.lean`

## Claim

The finite marked-Koszul selector is the zeroth boundary jet of a canonical positive deformation,
not an isolated alternating cancellation.  If a word uses `n` distinct prime directions, put

`M_n(t) = n(1-t)^(n-1)`.

For every nonempty support, `M_n(t)>0` on `t<1`.  At the boundary `t=1`, only `n=1` survives.
More strongly,

`M_n^(r)(1) = n(-1)^r r!` when `n=r+1`, and `0` otherwise.                 (1)

Thus the complete normal-jet tower at the scalar cancellation boundary recovers every
mixed-support cardinality exactly.  The scalar no-go loses connected prime data only because it
throws away all positive-order boundary jets.

`[CONJECTURE]` The Euler--Gamma/theta source admits a cofinal determinant-line realization of this
jet tower by Hermitian positive-semidefinite pencils.  Real stability of those finite pencils,
preserved by the marked derivative and by locally uniform cofinal limits, would make the completed
boundary section a Laguerre--Pólya approximation of `Xi`; hence all Xi zeros would be real in the
centered coordinate and RH would follow.

## Proven finite boundary-jet theorem

Define the integral deformation polynomial

`P_n(T)=n(-1)^(n-1)(T-1)^(n-1)=n(1-T)^(n-1)`.

Lean proves:

1. `P_n(t)=n(1-t)^(n-1)` exactly;
2. `P_n(t)>0` over the reals for `n>0` and `t<1`;
3. `P_n(1)=koszulSupportMarkedExponent(n)`, the existing singleton-support selector;
4. the exact all-order derivative formula `(1)`.

The theorem is not merely a cardinality rewrite.  It identifies the former scalar quotient as one
boundary face of a positive one-parameter family and provides exact tomography of every stratum
that the endpoint annihilates.

There is also a multiaffine stable lift.  For a support set `S`,

`B_S(t_p:p in S)=prod_(p in S)(1-t_p)`

has only coordinate hyperplane zeros.  Applying the marked normal derivative
`-sum_(p in S) partial_(t_p)` and then taking the diagonal `t_p=t` gives `M_|S|(t)`.
Differentiation and real specialization preserve real stability.  Therefore the support selector
itself has a canonical stable-polynomial ancestry before any arithmetic amplitudes are inserted.
This parent-theory observation is classical; the arithmetic realization below is the open content.

## The large detour

The proposed two-ended chain is:

```text
actual finite Euler prime-word amplitudes
  -> marked Koszul word complex                           [PROVED]
  -> positive deformation M_|supp w|(t), t<1             [PROVED]
  -> all boundary jets recover every support cardinality  [PROVED IN LEAN]
  -> source-defined PSD determinant pencil D_P(z,t)
       whose word expansion has those marked amplitudes
       [OPEN CORE A: no zero feeding; compatible in P]
  -> real stability of D_P by Hermitian PSD pencil theory
       [OPEN CORE B: the source operator must really be Hermitian/PSD]
  -> Euler--Gamma relative boundary section D_P(z,1)
       and cofinal locally uniform limit D_P(z,1) -> Xi(z)
       [OPEN CORE C: exact completed determinant comparison]
  -> real-rooted polynomial approximants to Xi
  -> Xi belongs to the classical Laguerre--Polya class
  -> every zero of Xi(z)=xi(1/2+iz) is real
  -> RH.
```

The source end is closed: the finite Euler coefficients, the prime-word support, the marked
Koszul character, its two-sided-ideal no-go, and now its full boundary-jet lift are all explicit
and independent of Xi zeros.  The consumer end is also closed: locally uniform limits of
real-rooted polynomials give the required Laguerre--Pólya conclusion, and a real Xi zero coordinate
is exactly a critical-line xi zero.  The remaining work lies only in the three middle source
theorems A--C.

## Why the stable-pencil step is not cosmetic

For Hermitian `A` and positive semidefinite rank-one updates `v_p v_p*`, determinant polynomials of
the form

`det(z I - A - sum_p x_p v_p v_p*)`

are real stable.  Mixed characteristic polynomials and interlacing-family theorems are finite
parent mechanisms for retaining real-rootedness after differentiation and averaging.  The present
route asks for something more rigid: the vectors, base operator, marking, and Gamma relative
boundary must be extracted from the actual Euler/theta source, and their determinant expansion
must equal the completed source section coefficient by coefficient.  Arbitrarily representing an
already-real-rooted Jensen polynomial would be circular and is forbidden.

The corpus supplies two plausible source carriers for the missing pencil:

1. the pointed doubling-Fock theta carrier, which already contains the bounded all-prime channel
   and the exact completed critical trace at one distinguished point;
2. the coupled Sonin prime-residual Gram operator, which retains cross-prime overlaps before the
   scalar marked trace deletes them.

The boundary-jet theorem says what must be retained from either carrier: not one scalar
supertrace, but the entire marked normal germ.

## Hard attacks and positive residues

1. **Scalar endpoint attack.**  At `t=1`, mixed words form a two-sided ideal killed by the selector;
   the endpoint factors through disconnected prime axes and is RH-blind.
   **Positive residue:** the complete boundary germ is support-cardinality faithful by `(1)`.
2. **Positive-weight attack.**  Positivity of `M_n(t)` alone does not make the arithmetic word
   determinant stable or Hermitian.
   **Positive residue:** it removes the earlier sign obstruction and isolates the needed theorem as
   a PSD-pencil realization, not an unspecified positivity claim.
3. **Generic mixed-characteristic attack.**  Every real-rooted polynomial has many representations;
   choosing one after inspecting Xi zeros restates RH.
   **Positive residue:** require one functorial construction from Euler amplitudes and the theta
   boundary, compatible under prime-set inclusions.
4. **Finite-prefix attack.**  Stability for each fixed prime set or finitely many boundary jets
   cannot control all Xi zeros.
   **Positive residue:** the precise limit obligation is locally uniform convergence of the full
   boundary section together with exhaustion independence.
5. **Gamma-only attack.**  The archimedean factor alone has no nontrivial critical-strip divisor.
   **Positive residue:** Gamma is allowed only as the relative boundary condition sewing the
   cofinal prime determinant, never as the spectral source by itself.
6. **Unpointed-matroid attack.**  The corpus proves that an unpointed maximal-HT pro-field and its
   differential matroid are blind to Laguerre--Pólya membership.
   **Positive residue:** the distinguished theta point, Hadamard normalization, and marked normal
   germ are load-bearing data and must survive every construction.

## Exact open cores

- `[OPEN CORE A]` Construct, for every finite prime set `P`, a Hermitian/PSD marked determinant
  pencil from the actual prime-word or coupled-Sonin source whose multivariate expansion realizes
  the full `M_|supp|(t)` deformation, not merely its scalar endpoint.
- `[OPEN CORE B]` Prove compatibility under `P subset Q`, uniform local bounds, and a closed
  exhaustion-independent determinant-line limit retaining all boundary jets.
- `[OPEN CORE C]` Prove before reading the Xi divisor that the Gamma/theta relative boundary value
  of that limit is a nonvanishing real entire factor times `Xi(z)`.
- `[OPEN CORE D]` If the finite objects are operator determinants rather than polynomials, prove a
  stability-preserving polynomial or finite-rank approximation theorem strong enough for the
  classical Laguerre--Pólya limit.

## Kill conditions

Retire the route if the only available pencil is chosen from Xi zeros; if the source matrix is
indefinite and no stable determinant theorem applies; if the cofinal limit depends on prime order;
if only the zeroth boundary trace converges; if the Gamma comparison introduces a zero-bearing
factor; or if the finite stable sections converge only coefficientwise without the local uniform
control needed to preserve zero location.

## Gates

- [x] scalar marked-Koszul selector and two-sided-ideal no-go formalized
- [x] positive interior deformation identified
- [x] exact all-support boundary-jet tomography formalized in Lean
- [x] both-ended RH closure written with explicit non-circularity conditions
- [ ] source-defined finite PSD determinant pencils constructed
- [ ] cofinal determinant-line compatibility and boundary-germ convergence proved
- [ ] Euler--Gamma/theta comparison with Xi proved without zero feeding
- [ ] stable-limit-to-RH capstone composed and formalized
