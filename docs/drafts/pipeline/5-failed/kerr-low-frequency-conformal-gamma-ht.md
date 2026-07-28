# Standard low-frequency Kerr conformal response does not carry generic Gamma HT

- **ID:** `kerr-low-frequency-conformal-gamma-ht`
- **Stage:** 5-failed
- **Type:** NO-GO / KERR / HIDDEN CONFORMAL SYMMETRY / HYPERTRANSCENDENCE
- **Failed claim:** generic low-frequency Kerr graviton response is HT because its retarded
  correlator contains Gamma ratios
- **Positive survivor:** the leading hidden-conformal response lies on an exact
  integer-conformal-weight DA locus; any Kerr HT transition must enter beyond that limit
- **Formal status:** parent Gamma-ratio boundary and both physical low-frequency channel
  specializations are unconditionally Lean-formalized

## Tempting claim

For spin `s`, the low-frequency Kerr retarded Green function contains

```text
G_R^s ~ Gamma(1-2h)/Gamma(2h-1)
  * Gamma(h-s-z_L)/Gamma(1-h+s-z_L)
  * Gamma(h-z_R)/Gamma(1-h-z_R).                             (1)
```

A superficial reading treats each Gamma ratio as a generic HT frequency response.

## Exact obstruction

In the standard low-frequency angular equation, the spin-weighted spherical-harmonic separation
constant gives

```text
h = ell + 1,                                                 (2)
```

up to the paper's shifted convention for `ell`. Hence the two same-orientation Gamma separations
in `(1)` are

```text
Delta_L = 1 - 2h + 2s,
Delta_R = 1 - 2h.                                            (3)
```

For integral angular momentum and spin, both are integers. Gamma recurrence therefore reduces
each frequency-dependent ratio to a rational Pochhammer factor. The existing unconditional theorem

```text
differentiallyAlgebraicOver_reducedVenezianoAmplitudeMero_iff_integerShift
```

proves exactly this DA/HT boundary. Thus the ordinary hidden-conformal Kerr response is in the DA
sector, not the generic HT sector.

The dedicated specializations are:

```text
differentialAlgebraicOver_kerrLowFrequencyLeftGammaRatioMero
differentialAlgebraicOver_kerrLowFrequencyRightGammaRatioMero
```

in `HTGeometry/KerrLowFrequencyGammaCollapse.lean`.

The frequency-independent prefactor in `(1)` can be singular at integral `h`; its regulated value
belongs to channel normalization and does not restore a nonintegral frequency orbit.

## Why the frequency-deformed repair is not yet a result

Xu proposes retaining an additional `4 M^2 omega^2` contribution in the approximate near-region
potential and defines

```text
ell'(omega)
  = 1/2 + 1/2 sqrt((2 ell - 1)^2 - 16 M^2 omega^2).           (4)
```

The corresponding response contains

```text
Gamma(-2ell'+1)/Gamma(2ell'-1)                               (5)
```

and two further ratios whose separations are `1-2ell'`. This leaves the integer lattice for
nonzero frequency and is a plausible HT carrier on the algebraic two-sheeted cover.

It cannot support a Nature claim:

1. `(4)` comes from a phenomenological low-frequency near-region approximation, not an exact Kerr
   Green function;
2. the physical scattering amplitude also contains far-zone matching Gamma factors and their
   interference, so `(5)` is not an independently normalized observable;
3. the absorption formula uses modulus squares and additional Gamma/reflection factors that can
   alter the differential class;
4. exact spin-2 Kerr Green functions require completion terms absent from the separated
   frequency-domain piece;
5. the corpus lacks algebraic-cover HT descent and a no-cancellation theorem for the full matched
   observable.

## Positive survivor

The obstruction gives a sharp physics classification:

> **Leading Kerr hidden-conformal response is differentially finite because angular-momentum
> quantization pins its conformal weight to the integer Gamma orbit.**

Therefore a genuine Kerr differential-complexity transition, if it exists, must be sourced by at
least one of:

1. finite-frequency spheroidal deformation of the angular eigenvalue;
2. exact confluent-Heun connection data;
3. global near/far matching after physical normalization;
4. nonlinear mode coupling;
5. a nonaxisymmetric sector with a proved nonintegral physical weight.

This is the strongest nontrivial survivor. The failed route narrows the new-math target to
algebraic-pullback HT and full-response orbit-charge cancellation rather than another affine Gamma
specialization.

## Reopening condition

Reopen only with an exact, gauge-invariant Kerr observable whose complete normalization is known
and whose Gamma/Heun connection data are proved to retain a nonzero orbit charge after every
physical cancellation.

## Primary sources

- B. Chen and J. Long, *Real-time Correlators and Hidden Conformal Symmetry in Kerr/CFT
  Correspondence*, <https://arxiv.org/abs/1004.5039>.
- K. Murata, *Conformal weights in the Kerr/CFT correspondence*,
  <https://arxiv.org/abs/1103.5635>.
- J. Xu, *Gravitational radiations of Kerr black hole from warped symmetries*,
  <https://arxiv.org/abs/2310.03532>.
- M. Casals, S. Hollands, A. Pound, and V. Toomani, *Spin-2 Green's Functions on Kerr in
  Radiation Gauge*, <https://arxiv.org/abs/2402.15468>.

## Log

- 2026-07-28 — exact 2010 spin-response formula and conformal weights audited from source.
  Standard low-frequency branch classified DA; 2023 frequency-deformed branch retained only as an
  approximate open problem.
