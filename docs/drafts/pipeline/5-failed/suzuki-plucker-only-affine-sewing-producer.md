# Failed Suzuki Plücker-only affine-sewing producer

- **ID:** `suzuki-plucker-only-affine-sewing-producer`
- **Stage:** 5-failed
- **Type:** FALSE REPRESENTATION / AFFINE-CHART LOSS
- **Status:** `[FALSIFIED] [POSITIVE SURVIVOR PAPER-PROVED] [LEAN CORE] [NOT RH]`
- **Failed producer:** homogeneous projective chord alone is complete carrier of weighted affine
  intercept in Suzuki jump sewing.
- **Positive survivor:**
  `../2-fully-proven/new_scientific_knowledge/suzuki-projective-affine-secant-tensor-lift.md`

## Exact killing mechanism

Actual jump source uses

```text
I_(alpha,beta)q=[beta q_alpha-alpha q_beta]/(beta-alpha).
```

Under numerator chart shift `B_delta=B+delta D`, every Plücker minor is unchanged because
`D wedge D=0`, but `q_lambda` and `I_(alpha,beta)q` increase by `delta`.  Therefore no function of
homogeneous exterior blade alone can recover affine-sewn response.

Rank one makes loss physical: Plücker chord records shift slope but not intercept
`L(v)/D(v)`, which actual affine sewing retains exactly.

## Strongest positive survivor

For `u_alpha=Av-beta v`, `u_beta=Av-alpha v`, homogeneous numerator `B(u)+c`, and denominator
`D(u)`, exact marked tensor is

```text
Q=(B(Av)+c)D(Av)
  -(alpha+beta)B(v)D(Av)
  +alpha beta B(v)D(v).
```

Then

```text
I_(alpha,beta)q=Q/[D(u_alpha)D(u_beta)].
```

Its spectral decomposition contains diagonal, symmetric-pair, alternating-pair, and homogeneous
Neumann sectors.  Opposite shifts erase alternating sector while leaving symmetric sector, a
second decisive Plücker-only falsifier.

## New insight

Projective chord is correct for shift difference but jump uses marked affine secant.  Required
Green identity must live in affine tensor space, not positive Grassmannian alone.  Volterra phase
operator `Omega=H_g-H_(r0)A` remains correct source input; its boundary evaluations must be placed
in marked tensor before Pick polarization.

## Status

Paper proof and Lean scalar algebra complete in
`formal/GaloisForLFunctions/RHTower/SuzukiProjectiveAffineSecantTensor.lean`.  Actual marked
prime--Gamma Christoffel--Darboux/Green factorization remains open and RH-bearing.

## Log

- 2026-07-22 — Gauge audit falsified Plücker-only affine-sewing producer; exact marked tensor
  survivor derived and formalized.
