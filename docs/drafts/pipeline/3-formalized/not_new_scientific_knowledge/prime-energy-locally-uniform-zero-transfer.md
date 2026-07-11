# Finite-prime energy transfer through locally uniform zero approximation

- **ID:** `prime-energy-locally-uniform-zero-transfer`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [RH-SUFFICIENT BRIDGE]`
- **Statement:** Locally uniform entire approximants to `XiC` prove RH if their zero fibres have a
  uniform `o((log N)^2)` envelope for the explicit reflected finite-prime energy.

## Source-pure implication chain

For entire approximants `F_N`, assume

```text
F_N -> XiC locally uniformly,
F_N is eventually entire,
E_N -> 0,
F_N(z)=0 -> primeClockCutoffEnergy(N, Im z)/(log N)^2 <= E_N.
```

Then Lean proves

```text
uniform sub-log-square prime energy on approximant zero fibres
  -> every selected approximant-zero displacement tends to zero
  -> every XiC zero is real
  -> RiemannHypothesis.
```

The upstream hypothesis does not assert that any zero is real and does not quantify over zeros of
`XiC`. The energy is the explicit finite prime sum

```text
sum_(p <= N) (p^(-(1/2+epsilon)) - p^(-(1/2-epsilon)))^2.
```

Thus this is a quantitative prime-source condition rather than a renamed zero-location criterion.

## Proof

Fix a zero `z` of `XiC` and suppose `Im z != 0`. Analytic isolation supplies a circle around `z`
whose radius is at most `|Im z|/4` and whose boundary is zero-free. The locally uniform Hurwitz
theorem gives, for every sufficiently large `N`, a zero `w_N` of `F_N` in that closed ball.

The uniform zero-fibre envelope and nonnegativity of the finite-prime energy squeeze

```text
primeClockCutoffEnergy(N, Im w_N)/(log N)^2 -> 0.
```

The previously formalized logarithmic-boundary theorem then gives `Im w_N -> 0`. But every `w_N`
remains within `|Im z|/4` of `z`, contradicting `Im z != 0`. Hence every zero of `XiC` is real. The
standard centered change of variables transfers this statement to mathlib's `RiemannHypothesis`.

## Lean certificate

File:

```text
formal/GaloisForLFunctions/RHTower/PrimeEnergyZeroTransfer.lean
```

Declaration:

```text
RHTower.riemannHypothesis_of_XiC_locally_uniform_localPrimeEnergy_approximants
RHTower.riemannHypothesis_of_XiC_locally_uniform_cofinalLocalPrimeEnergy_approximants
RHTower.riemannHypothesis_of_XiC_locally_uniform_primeEnergy_approximants
RHTower.riemannHypothesis_of_xiCTaylorApprox_localPrimeEnergy
RHTower.riemannHypothesis_of_xiCTaylorApprox_primeEnergy
```

The theorem composes:

```text
RHTower.eventually_exists_zero_closedBall_of_tendstoLocallyUniformly
RHTower.tendsto_horizontalDisplacement_zero_of_energy_div_log_sq_tendsto_zero
RHTower.rh_iff_xi_ne_zero_right
```

## Canonical source approximants

The same Lean module defines

```text
xiCTaylorApprox n z = (cauchyPowerSeries XiC 0 1).partialSum n z.
```

It proves unconditionally that every `xiCTaylorApprox n` is entire and that the sequence converges
locally uniformly to `XiC` on the whole complex plane. Hence the fully concrete chain is

```text
compact-locally uniform sub-log-square prime energy on zeros of xiCTaylorApprox n
  -> general prime-energy zero transfer
  -> RiemannHypothesis.
```

The Taylor family is defined from the Cauchy coefficients of `XiC`; it does not enumerate or import
the `XiC` divisor.

## Remaining open source theorem

For every fixed radius `R`, prove a vanishing envelope `E_(R,N)` for the zeros of
`xiCTaylorApprox N` in `closedBall 0 R`. No condition is required on spurious Taylor-section zeros
escaping to infinity. Finite real-rootedness is not required: compact-local, asymptotically
sub-log-square reflected prime energy suffices. Alternative self-adjoint or determinant
approximants remain eligible under the general theorem.

For a cofinal prime cutoff sequence `N_j -> infinity`, the generalized theorem replaces every
occurrence of `N` in the energy by `N_j`. This is the exact interface required by the paper-proved
pointed theta-cusp screen family: after its transforms are formalized, their compact-local
sub-log-square zero-fibre energy implies RH directly.

## Gates

- [x] source-pure quantitative condition identified
- [x] finite-prime energy converted to horizontal zero pinning
- [x] locally uniform zero persistence combined with pinning
- [x] RH conclusion formalized in Lean
- [x] construct a source-defined concrete approximant family
- [x] prove its locally uniform convergence and holomorphy
- [x] localize the zero-fibre hypothesis to fixed compact balls
- [x] generalize the transfer to arbitrary cofinal prime cutoffs
- [ ] prove the compact-local zero-fibre energy envelope
