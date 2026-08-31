# Suzuki higher finite-contact endpoint preservation

- **ID:** SUZ-HFC-ENDPOINT-NOGO
- **Stage:** 5-failed
- **Route class:** fixed nonlinear contact order `m≥2` in shared HB/FZZ-P/PW-B/RBH Suzuki Ward producer
- **Verdict:** KILLED for transition-core-growth plus CCM-abscissa mechanism

## Proposed repair

Replace the RH-equivalent first-contact bounded energy `E_N=O(1)` by bounded nonlinear residual

`E_N^m / C_N^(m-1) = O(1)`

at some fixed order `m≥2`, hoping extra contact absorbs growing transition-core energy while
preserving the RH endpoint.

## Killing theorem

Let `alpha_m=(m-1)/(2m)`. The actual Suzuki identities prove

`P_m=O(1)` → `G_N=O(N^alpha_m)` → `Q(t)=O(exp(alpha_m t))` →
`XiZeroHalfPlaneBound alpha_m`.

Here `0<alpha_m<1/2` for every `m≥2`; only `m=1` has zero width and is equivalent to RH.

This loss is sharp at the algebraic producer. For arbitrary proposed bound `K`, the packet

`R=K+1`, `C=R^(2m)`, `E=R^(2(m-1))`, `G=R^(m-1)`

satisfies `C>0`, `E≥0`, `G^2=E`, and `E^m/C^(m-1)=1`, but `G>K`. Therefore finite-contact
inequalities alone cannot supply the uniform Green/resolvent bound required at the RH endpoint.

## Positive survivor

Exact order-width spectrum:

`bounded order-m residual ⇒ XiZeroHalfPlaneBound ((m-1)/(2m))`.

Paper proof and Lean certificate:
`docs/drafts/pipeline/3-formalized/suzuki-finite-contact-width-classification.md` and
`formal/GaloisForLFunctions/RHTower/SuzukiTransitionCoreFiniteContactWidthClassification.lean`.
The capstones are `suzukiTransitionCore_finiteContact_widthClassification` and
`suzukiFiniteContact_algebraicEndpointNoGo`.

## Survivor condition

A higher-contact proposal remains viable only if it adds a new cancellation invariant that improves
the generated `N^alpha_m` envelope to a uniform bound before the CCM continuation step. Changing
finite contact order alone is retired.

