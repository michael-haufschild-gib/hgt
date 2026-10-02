# TG C9.11e — bare Gamma addition cannot repair the lost channel

- **Stage:** 5-failed
- **Type:** FALSIFIED proposal
- **Scope:** adding a scalar multiple of the literal untested Gamma logarithmic
  differential to the finite coherent source before the same aperture transition.

## Exact obstruction

The unconditional operator normal form is `LΓ=A₁+R₁-1`. For b≥1,
`LΓ Q_b=-Q_b`. For a≤b, E=Q_a-Q_b, hence `E LΓ Q_b=0` and
`E(H+zLΓ)Q_b=EHQ_b` for every bounded H and complex z.
All subsequent lost/retained channel operations therefore receive the same input.
This proposal cannot change the C9.11d cubic obstruction.

## Positive survivor and new insight

The Schwartz-tested operator is different: `A_g LΓ Q_b=-A_g Q_b` exactly.
The existing trace-class theorem for `A_g LΓ` proves trace class of the actual
continuum dilation source `A_g Q_b`. Thus the nontrivial Gamma source on Sonin is
the continuum operator from testing, not a scalar adjustment of the untested term.
Paper proof and ten Lean theorems: [Gamma normal form](../3-formalized/tg-gamma-sonin-normal-form.md).

## Surviving route

Literal products of Gamma and Euler scattering phases, and tested continuum sources,
remain under investigation. No RH conclusion or cofinal trace/index comparison follows
from the bare-counterterm obstruction.
