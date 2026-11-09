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

## Sources

- `GaussMayerScatteringNormalization.actualScattering_eq` and
  `TheScatteringMatrixIsABlaschkeProduct.sub_one_div_mul_scatteringEntry`.
- `EisensteinMaassSelbergLineModel.truncatedPairing_diag`.
- `XiLogDerivPositiveRayAsymptotic`, `DigammaPositiveRealAsymptotic`,
  `CompletedPrimeGammaAllOrderFarRight`.
