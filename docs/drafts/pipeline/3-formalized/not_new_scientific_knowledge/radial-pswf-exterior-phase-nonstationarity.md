# The radial PSWF exterior Liouville phase is uniformly nonstationary

- **ID:** `radial-pswf-exterior-phase-nonstationarity`
- **Stage:** 3-formalized
- **Type:** THEOREM / SPECIAL-FUNCTION INFRASTRUCTURE
- **Scientific status:** `[FULLY PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal source:** `formal/GaloisForLFunctions/RHTower/RadialPSWFExteriorPhase.lean`

## Theorem

For `0<=sigma<=1` and `z>1`, define

```text
v_sigma(z)=sqrt((z^2-sigma^2)/(z^2-1)),

xi_sigma(z)=integral_2^z v_sigma(u)du.
```

Then

```text
xi_sigma'(z)=v_sigma(z),

v_sigma(z)>=1.                                                  (1)
```

Consequently, for every `k>=0` with `k*x>1`,

```text
d/dx xi_sigma(k*x)=k*v_sigma(k*x)>=k,                           (2)
```

and the bandwidth-scaled phase has exact derivative

```text
d/dx [c*xi_sigma(k*x)]=c*k*v_sigma(k*x).                        (3)
```

## Route use

Equations `(2)`--`(3)` supply the concrete phase floor in every exterior radial sector of the
constrained prolate primitive estimate. They remove phase nonstationarity from the open gates. The
remaining analytic work is amplitude control: the endpoint `L2` layer and the exact
interaction-picture variation after the Liouville transform.

## Verification

The phase derivative, dilation chain rule, and derivative floor were checked in the project
toolchain. Their axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
