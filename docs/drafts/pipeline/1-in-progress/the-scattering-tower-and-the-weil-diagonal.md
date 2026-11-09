# The scattering tower and Weil's diagonal

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B133: an independent geometric normalization of the diagonal.

Let `S_geom(u)` be `(u−1)/u` times the actual zero-Fourier scattering
coefficient of the modular Poincaré series. This definition uses the
geometric series, not zeros of ζ or Weil's form. The corpus proves
`S_geom(u)=ξ(2u−1)/ξ(2u)` in the absolute chamber.

## Target

For `Re s>1`, establish the normalized infinite identity

`lim_N [½ Σ_{n<N} (S_geom'/S_geom)((s+n+1)/2)
         +½ log((s+N)/(2π))] = ξ'(s)/ξ(s)`.

The finite sum telescopes. The analytic input is the additive, rather than
relative, asymptotic `ξ'/ξ(z)−½log(z/(2π))→0` on fixed horizontal rays.
The Gamma normalization fixes the counterterm.

The actual Maass–Selberg diagonal `truncatedPairing_diag` expresses each
scattering derivative through a truncated geometric pairing and explicit
cusp terms. Derive the normalized tower directly from these pairings and
then identify its action on smoothed packets with the full Weil distribution.
The right-chamber logarithmic-derivative identity alone does not establish
the packet identity or a Green kernel on the split-torus quotient.

At cutoff height one, put `A(u)=Λ(1+2u)`, `B(u)=Λ(2u)` and let `P(u)`
be the actual truncated diagonal pairing. The geometric quantity

`D(u)=(A(u)²−B(u)²)/(4uA(u)B(u))−P(u)/(2A(u)B(u))`

equals `Λ'/Λ(2u)−Λ'/Λ(1+2u)`. Summing `D((s+n)/2)` therefore
recovers `Λ'/Λ(s)` after the same large-parameter subtraction. The two
rational boundary terms `1/s+1/(s−1)` give the completed ξ symbol.
The existing bound `|ψ(z)−log z|≤3/|z|` on the right half-plane controls
the Gamma remainder uniformly; the Euler remainder decays with the shift.

## Scalar normalization and packet target

For `s=c+it`, choose the scalar counterterm
`r(c+N)=½log((c+N)/2)−½log π`. If `c+N≥4`, the error of the
completed geometric tower is bounded by

`2^(−N) M_c + (3+|t|/2)/(c+N)`,

where `M_c=Σ_m Λ(m)m^(−c)` is finite for `c>1`.
The Gamma estimate follows from the half-plane digamma bound and
`|log z−log(Re z)|≤|Im z|/Re z`. The latter is the mean-value bound
for `1/z` on a right half-plane. Conjugation of the actual truncated
Eisenstein model supplies both halves of the integration line.

For a compactly supported C² autocorrelation, its symmetrized Mellin
transform decays as `(1+t²)^(−2)`. Thus the error bound is integrable,
and the corpus's vertical-line formula identifies the limiting tower
pairing with the full Weil functional. The scalar estimate, pointwise
limit, and packet limit are formalized in
`TheWeilSymbolFromTheGeometricScatteringTower` and
`TheWeilPacketsFromRenormalizedGeometricDiagonals` (standard-three-axiom
audits). The counterterm is exactly `2r(c+N)‖f‖₂²`.

Even that packet identity would not identify a torus-periodized Green
operator on the adelic carrier. The missing geometric comparison is
between the modular scattering tower and the sum of local Green channels
on the split-torus quotient. No positivity conclusion is part of this route.

## Intrinsic geometric normalization

Remove the completed normalization from the construction itself. Let `φ(P)`
be the height-one zero Fourier coefficient of the raw primitive-pair
Poincare series, minus one, and let `P_raw` be its actual truncated pairing.
The target diagonal is

`(φ(P)^(-1)−φ(P))/(4(P.s−1/2)) − P_raw/(2φ(P))`.

The completed zero-Fourier theorem gives `Aφ=B`; actual-to-canonical
Fourier uniqueness gives `P_completed=A²P_raw`. These identities cancel
the completion factor in the diagonal. Transport the packet limit to
this raw geometric definition, which contains no ζ values or zero divisor.

## Sources

- `GaussMayerScatteringNormalization.actualScattering_eq` and
  `TheScatteringMatrixIsABlaschkeProduct.sub_one_div_mul_scatteringEntry`.
- `EisensteinMaassSelbergLineModel.truncatedPairing_diag`.
- `XiLogDerivPositiveRayAsymptotic`, `DigammaPositiveRealAsymptotic`,
  `CompletedPrimeGammaAllOrderFarRight`.
