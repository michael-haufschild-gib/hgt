# Von Mangoldt--Gamma arbitrary-order jet boundary balance

- **ID:** `von-mangoldt-gamma-jet-boundary-balance`
- **Status:** formalized support theorem; arbitrary-depth packet square summability formalized;
  completed source-value identity open
- **Classification:** `[BRIDGE]`; Hermite interpolation and polynomial divisibility are standard,
  and no scientific-novelty claim is made
- **RH status:** does not prove RH

## Source constraint

The affine two-boundary residual cancels the values at `w=+a` and `w=-a`, but it has only three
Cauchy denominators.  Its depth-four source feature no longer decays.  Replacing it by an
arbitrary scalar damping would manufacture positivity and fail the source-effectivity gate.

For order `k`, impose instead the static constraints

1. multiplicity at least `k` at both boundary characters;
2. monic degree at most `2k` before pole normalization;
3. regularized coefficient one at the original Cauchy pole `w=-lambda`.

The first two constraints force the unique polynomial

```text
P_(k,a)(w)=(w^2-a^2)^k=(w-a)^k(w+a)^k.                 (1)
```

Indeed, any admissible monic polynomial is divisible by the right side of `(1)`, and both have
degree `2k`.  Normalization at the source pole then forces

```text
B_(k,a)(w,lambda)
 = P_(k,a)(w)/(P_(k,a)(-lambda)*(w+lambda))
 = ((w^2-a^2)/(lambda^2-a^2))^k/(w+lambda).            (2)
```

This is not an optional regularizer: `(1)` and the pole coefficient determine `(2)` uniquely.

## Hermite interpretation `[PROVED ON PAPER]`

Let `H_(k,a)(w,lambda)` be the degree-less-than-`2k` Hermite interpolant of
`w |-> 1/(w+lambda)` at `+a` and `-a`, matching derivatives through order `k-1`.  Then

```text
1/(w+lambda)-H_(k,a)(w,lambda)=B_(k,a)(w,lambda).       (3)
```

To prove `(3)`, multiply its left side by `w+lambda`.  The result is a polynomial of degree at
most `2k`, has multiplicity `k` at both boundary points, and takes value one at `w=-lambda`.
The uniqueness argument for `(1)` gives exactly `(2)`.  Thus the construction subtracts the
complete boundary jet forced at order `k`; it does not insert an unrelated target-side weight.

At `k=1`, `(2)` is exactly the previously formalized affine residual.  Successive orders obey

```text
B_(k+1,a)=B_(k,a)*(w^2-a^2)/(lambda^2-a^2).             (4)
```

## Unbounded-depth convergence `[PROVED ON PAPER]`

Fix `a=1/2` and a compact central set `|w|<=b<a`.  For `lambda=log n`, `n>=2`, `(2)` gives

```text
|B_(k,1/2)(w,log n)| <= C_(b,k)*(log n)^(-2k-1).        (5)
```

The oriented depth-`N`, coordinate-`i` Gamma numerator is

```text
sqrt(Lambda(n)/n)*(log n)^i*R_(N-i)(log n),
0<=i<N.                                                 (6)
```

Since the truncated-exponential remainder in `(6)` is a polynomial of degree at most
`N-i-1` plus a bounded exponential term, `(6)` is bounded by
`C_N*sqrt(Lambda(n)/n)*(1+(log n)^(N-1))`.  Hence the squared order-`k` feature is bounded by

```text
C_(N,b,k)*Lambda(n)/n*(log n)^(2N-4k-4).                (7)
```

The canonical source packet matches the boundary multiplicity to the Gamma depth, `k=N`.  This is
the smallest depth-matched choice; taking `N+1` would add an unforced damping factor.  For `N>0`,
which is automatic whenever a coordinate `i:Fin N` exists, `(7)` becomes

```text
C_(N,b)*Lambda(n)/(n*(log n)^(2N+4)).                   (8)
```

Chebyshev's unconditional bound for `psi(x)` and partial summation imply convergence of
`sum Lambda(n)/(n*(log n)^q)` for every `q>1`.  Therefore every fixed Gamma depth has a genuine
cofinal `ell^2` packet, every finite prefix converges strongly, and every finite Gram converges
to a positive semidefinite limit.  This removes the depth-`N>=4` decay obstruction of the affine
packet.

Lean now proves a slightly weaker but still sufficient pointwise bound directly from the exact
Taylor theorem:

```text
|feature_(N,i,N)(w;n)|^2
 <= C_(N,w)*Lambda(n)/(n*(log n)^(2N+2)).                (8a)
```

After `Lambda(n)<=log n`, Cauchy condensation against the already formalized
`sum 1/(n*log(n)^2)` proves square summability for every `i`, and jointly over
`Fin N × Nat`.  Thus existence of the full finite-depth `ell^2` source packet is formalized;
the finite Gram is proved to be the literal partial sum of one common infinite kernel, and every
entry is proved to converge to that kernel.

## RH impact

The source side now supplies positive, boundary-cancelled, cutoff-compatible packets at arbitrary
finite jet depth.  The remaining RH-bearing arrow is not positivity or convergence.  It is the
completed value identity identifying the limiting Hermite-balanced Euler packet with the
inverse-tilted prime--archimedean moment jet.

There is an essential index firewall.  The positive kernel

```text
K_N(z,w)=sum_(n,i) A_(N,i,N)(z;n) conjugate(A_(N,i,N)(w;n))
```

is indexed by Cauchy parameters `z,w`; the Gamma coordinate `i` is summed inside the Hilbert
norm.  It is not the Hankel index.  On every closed disc of radius less than `1/2`, the same
majorant used above is uniform in `z,w`, so the packet is Hilbert-valued analytic and its mixed
Taylor-jet matrix is positive semidefinite.

This `K_N` is still the von Mangoldt anomaly channel.  The corpus separately proves that the
actual central `gammaRealLogConnection` jet is a positive quarter-shift spectral clock.  The
rational polar modes are also explicit.  Therefore the next object must be the completed kernel
`K_N^comp` obtained by coupling these channels with the signs forced by
`continuedPrimeArchSourceRelativeTrace`; equating the prime kernel alone with the completed moment
germ would omit real source data.  The correctly typed missing identity is

```text
(1/(r!*s!)) d_z^r d_conj(w)^s K_N^comp(z,w)|_(z=w=0)
  = normalizedPrimeArchMoment(r+s),
0<=r,s<N.                                                (9)
```

Equation `(9)` must include the polar and archimedean boundary-jet contribution subtracted in
`(3)`.  Assuming `(9)`, the positive mixed jet Gram and the existing positive-moment endpoint
yield RH.  Nothing in the present card proves `(9)`.  Merely relabelling the internal Gamma
coordinate as a moment index, or dropping the separate polar--Gamma channel, would be invalid.

## Lean certificate

Formal file:

`formal/GaloisForLFunctions/RHTower/VonMangoldtGammaJetBoundaryBalance.lean`

Convergence file:

`formal/GaloisForLFunctions/RHTower/VonMangoldtGammaJetBoundaryConvergence.lean`

Principal declarations:

- `twoBoundaryCauchyJetPolynomial_factor`
- `twoBoundaryCauchyJetPolynomial_unique`
- `twoBoundaryCauchyJetNormalizer_eq_polynomial_ratio`
- `twoBoundaryCauchyJetNormalizer_at_pole`
- `twoBoundaryCauchyJetResidual_succ`
- `twoBoundaryCauchyJetResidual_one_eq_affine`
- `finiteVonMangoldtAllDepthJetBalancedCauchyVector_prefix`
- `finiteVonMangoldtAllDepthJetBalancedCauchyGram_posSemidef`
- `finiteVonMangoldtAllDepthOrderGrowingCauchyVector_prefix`
- `finiteVonMangoldtAllDepthOrderGrowingCauchyGram_posSemidef`
- `summable_vonMangoldtInverseLogPowerWeight`
- `normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature_le`
- `summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyFeature`
- `summable_normSq_finiteVonMangoldtAllDepthOrderGrowingCauchyPacket`
- `finiteVonMangoldtAllDepthOrderGrowingCauchyGram_eq_kernel`
- `finiteVonMangoldtAllDepthOrderGrowingCauchyGram_tendsto`
- `infiniteVonMangoldtAllDepthOrderGrowingCauchyGram_posSemidef`

## Gates

- [x] exact two-boundary divisor factorization
- [x] uniqueness under monicity, degree, and boundary-multiplicity constraints
- [x] exact pole normalization
- [x] order-one recovery of the affine source balance
- [x] arbitrary-order boundary vanishing
- [x] actual von Mangoldt--Gamma specialization
- [x] cutoff-prefix compatibility
- [x] finite Gram positivity
- [x] exact target build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] no numerical computation
- [x] formalize a sufficient fixed-parameter decay bound `(8a)`
- [x] formalize the complete finite-depth packet square summability
- [x] package finite-prefix Gram convergence as a named limit theorem
- [x] prove the limiting finite packet Gram remains positive semidefinite
- [ ] formalize local-uniform analyticity and the mixed center-jet Gram
- [ ] couple the existing positive Gamma clock and rational polar modes with the prime kernel
- [ ] prove the completed source-value identity `(9)`
- [ ] RH
