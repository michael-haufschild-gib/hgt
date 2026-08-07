# Failed Suzuki negative-projector triangle producer

- **ID:** `suzuki-negative-projector-triangle-producer`
- **Stage:** 5-failed
- **Type:** FALSE REPRESENTATION / PROJECTIVE MISMATCH
- **Status:** `[FALSIFIED AS PRODUCER] [POSITIVE SURVIVOR PAPER-PROVED] [NOT RH]`
- **Failed producer:** actual two-shift Suzuki quotient correction is canonically the weighted
  negative spectral projector `P_-W` of the restricted-Weil operator
- **Positive survivor:**
  `../3-formalized/new_scientific_knowledge/suzuki/suzuki-homogeneous-projective-resolvent-plucker-lift.md`,
  `../3-formalized/new_scientific_knowledge/suzuki/suzuki-volterra-cartesian-phase-defect.md`
- **RH used:** no
- **Computation used:** no

## Killing mechanism

The weighted negative projector is the correct minimal completion of the **linear** affine
resolvent defect.  Actual Suzuki response is a projective quotient of two boundary evaluations of
the same resolvent orbit:

```text
q_lambda=N(u_lambda)/D(u_lambda),
u_lambda=(A-lambda)^(-1)e.
```

On a one-dimensional invariant spectral line `A=t`, both numerator and denominator contain the
same factor `(t-lambda)^(-1)`, hence

```text
q_lambda=N(e)/D(e)
```

is exactly independent of `lambda`.  Its two-shift Euler--Gamma growth is zero even when `t<0`.
But the linear weighted negative projector `P_-W` is then strictly positive.  Therefore the
projector cannot be the canonical correction of the projective source quotient.  The two objects
already disagree in spectral rank one.

This does not contradict the linear theorem in
`suzuki-negative-projector-coherent-completion.md`; that theorem remains correct.  It kills only
its proposed identification with actual Suzuki quotient/triangle motion.

## Exact reason

Projectivization annihilates common one-mode resolvent scaling.  Two-shift motion begins only on
spectral pairs and is an exterior-square quantity.  Treating it coordinatewise before dividing
creates a spurious `sign(t)` debt which the true quotient does not see.

The affine Neumann channel does survive rank one, but only as a homogeneous projective coordinate.
It must be joined to Euler--Gamma pair curvature before any positivity or Schur analysis.

## Positive survivor

For `v=(A-alpha)^(-1)(A-beta)^(-1)e`, exact replacement is

```text
U_beta wedge U_alpha
 =(beta-alpha)(v,0) wedge (Av,1),
U_lambda=(u_lambda,1).
```

Its `V wedge V` component is Euler--Gamma pair curvature; its `V wedge 1` component is Neumann
projective holonomy.  Actual frontier is a source Christoffel--Darboux identity proving positivity
of the boundary image of this blade, not a one-mode negative-projector completion.

## No-go closure

1. **Killing theorem:** rank-one projective quotient is shift-flat while linear negative debt is
   nonzero at a negative node.
2. **Strongest positive survivor:** exact homogeneous Plücker lift above.
3. **New insight:** Euler--Gamma and Neumann channels are forced components of one decomposable
   blade; source sign lives on spectral pairs.
4. **Status:** both survivors paper-proved and Lean-formalized.  Physical triangle identifies
   concrete boundary operator as relative Volterra phase `H_g-H_r*A`; Neumann phase is rank-one
   moment holonomy.
