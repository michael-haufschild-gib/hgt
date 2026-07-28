# Thermal-horizon Gamma phase is invisible to full mode-gauge holonomy

- **ID:** `horizon-bogoliubov-mode-gauge-holonomy`
- **Stage:** 3-formalized
- **Type:** EXACT NO-GO / POSITIVE GAUGE-INVARIANT SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT A NATURE-LEVEL DISCOVERY]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/HorizonBogoliubovModeGaugeHolonomy.lean`

## Exact theorem

For a two-frequency phase `Phi(x,y)`, define its rectangular defect by

```text
D Phi
  = Phi(x1,y1)+Phi(x2,y2)-Phi(x1,y2)-Phi(x2,y1).            (1)
```

Every independent outgoing- and incoming-mode calibration cancels:

```text
D (r(x)+Phi(x,y)+c(y)) = D Phi.                              (2)
```

For the ideal exponential-peeling horizon kernel, use outgoing frequency `x` and logarithmic
incoming frequency `ell`. Its coupled phase is

```text
Phi_kappa(x,ell) = -i kappa^(-1) x ell.                      (3)
```

Then

```text
D Phi_kappa
  = -i kappa^(-1) (x1-x2)(ell1-ell2).                       (4)
```

Exponentiating the phase gives the multiplicative four-frequency holonomy

```text
H(B)
  = B(x1,ell1) B(x2,ell2)
      / (B(x1,ell2) B(x2,ell1)),

H(exp Phi_kappa)
  = exp[-i kappa^(-1)(x1-x2)(ell1-ell2)].                   (5)
```

Equations `(1)`--`(5)` are unconditional algebraic identities.

## Gamma no-go

The thermal moving-mirror/Hawking coefficient has the schematic form

```text
B_kappa(x,ell)
  = R_kappa(x) C(ell) exp[-i kappa^(-1) x ell],              (6)
```

where the output-frequency row factor `R_kappa(x)` contains the Gamma carrier
`Gamma(i x/kappa)`. The corpus proves that its oriented phase and logarithmic derivative are HT.
However, `R_kappa(x)` is a separable row factor, so `(2)` removes it from the fully
incoming/outgoing mode-rephasing-invariant holonomy:

```text
H(B_kappa)
  = exp[-i kappa^(-1)(x1-x2)(ell1-ell2)].                   (7)
```

Thus the Gamma HT phase is not an intrinsic bivariate curvature of the universal ideal thermal
kernel. It is meaningful relative to a chosen outgoing-frequency calibration, and can be measured
in a calibrated interference experiment, but it cannot support a calibration-free universal
statement by itself.

This does not contradict the existing Gamma observability theorem. That theorem fixes the
frequency coordinate and calibration, then proves that intensity cannot reconstruct the resulting
HT phase clock. The present theorem asks a different question: what survives quotienting by all
independent row and column phase conventions?

## Positive survivor

The rectangular holonomy retains an exact observable:

```text
surface gravity = constant mixed input-output phase curvature.                (8)
```

The finite rectangle form avoids derivatives and logarithm branches. An unwrapped infinitesimal
version reads

```text
partial_x partial_ell Phi_kappa = -i/kappa.                  (9)
```

The exponentiated finite holonomy has the usual phase-wrapping ambiguity; no unique global
reconstruction of `kappa` from one rectangle is claimed without a branch or small-rectangle
condition.

Equation `(8)` is structurally clean but not presently a general-journal discovery. Phase slopes,
Bogoliubov-channel tomography, stimulated Hawking interference, and recovery of horizon
temperature from spectral response all have strong parent literatures.

## Extremal survivor and open core

The exact extremal Reissner-Nordstrom coefficient contains the genuinely coupled kernel

```text
K_(1+4 i M x)(4 M sqrt(x(x+y))).
```

Unlike the thermal Gamma row factor, its Bessel order and argument couple outgoing and incoming
frequencies. The live question is therefore:

```text
Is the extremal rectangular holonomy HT in a physical one-parameter scan,
while every nonextremal universal near-horizon holonomy is DA?                (10)
```

If `(10)` is true and survives Kerr, greybody, formation-transient, and measurement audits, it
would be an intrinsic differential-class transition rather than a calibration artifact. It is not
yet proved.

## Lean declarations

- `rectanglePhaseDefect`;
- `rectanglePhaseDefect_separableGauge`;
- `thermalHorizonPhaseExponent`;
- `rectanglePhaseDefect_thermalHorizonPhaseExponent`;
- `rectangleKernelHolonomy`;
- `exponentialKernel`;
- `rectangleKernelHolonomy_exponentialKernel`;
- `rectangleKernelHolonomy_exponential_separableGauge`;
- `rectangleKernelHolonomy_thermalHorizon`.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/HTGeometry/HorizonBogoliubovModeGaugeHolonomy.lean`;
- final module audit:
  `lake build GaloisForLFunctions.HTGeometry.HorizonBogoliubovModeGaugeHolonomy`;
- all five capstone axiom prints report only `propext`, `Classical.choice`, and `Quot.sound`;
- source contains no active `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- no numerical computation was used.

## Primary physics anchors

- M. R. R. Good, P. R. Anderson, and C. R. Evans, *Time dependence of particle creation from
  accelerating mirrors*, <https://arxiv.org/abs/1303.6756>.
- G. Gianfelici and S. Mancini, *Quantum channels from reflections on moving mirrors*,
  <https://arxiv.org/abs/1704.04635>.
- M. R. R. Good and Y. C. Ong, *Particle spectrum of the Reissner-Nordstrom black hole*,
  <https://arxiv.org/abs/2004.03916>.
- M. R. R. Good, *Extremal Hawking radiation*, <https://arxiv.org/abs/2003.07016>.

## Log

- 2026-07-28 - exact row/column gauge cancellation, thermal rectangle law, and exponential
  holonomy formalized; naive use of Gamma HT as calibration-free horizon curvature retired.
