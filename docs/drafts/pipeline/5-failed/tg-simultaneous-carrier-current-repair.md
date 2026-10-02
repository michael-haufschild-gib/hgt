# TG C9.11j — simultaneous-carrier restriction erases the source

- **Stage:** 5-failed
- **Type:** NO-GO with a formalized positive survivor
- **Route:** TG; this retires one carrier-restriction repair, not the RH route.

## Failed conjecture

Use the nonzero moving carrier E_(S,b)={f∈K_b : A_S f∈K_b} to preserve the finite
Euler-cleared current while avoiding eventual fixed-carrier collapse.

## Exact obstruction

For b≥1, the canonical orthogonal projection P_(S,b) onto that carrier is nonzero,
but `J_S P_(S,b)=0` and `δ_S A_S P_(S,b)=0`. Thus the actual current is removed
before any cubic character can be formed. Nonzero vectors in the restricted
carrier do not retain the relative source. In contrast, on the original carrier,
`J_S Q_b=0 iff P_S≤b`; for P_S>b a genuine boundary channel is being discarded.

## Strongest positive survivor

The exact kernel on K_b is `J_S f=0 iff R_(P_S) f=0`. It follows from the actual
identity `J_S f=−A_S* R₁ A_S f`, adjoint injectivity via `A_S*=V_S A_S`, and the
sharp Fourier-gap theorem. The finite simultaneous carrier remains a canonical
closed nonzero subspace. The exact activation law above follows from Fourier
parity and the noncompact strict aperture transition, not a numerical example.

All these statements are proved in `CCMEulerMovingCarrierRadical`; its foreground
final leaf audit passed with default heartbeats. All twelve public axiom queries
passed with only `propext`, `Classical.choice`, `Quot.sound`. The leaf is wired.

## Surviving construction to attack

Retain the complementary quotient seen by `B_(S,b)=R₁ A_S|K_b` in the graded
four-leg class. C9.11k conjectures that this quotient is exactly an annular
Fourier carrier, with a source-derived inverse combining Sonin annular
surjectivity and finite nilpotent Euler inversion. Its cofinal transitions must
come from actual prime insertion; arbitrary Hilbert-space identifications do
not solve the relative-class or index problem.

References: `tg-euler-moving-carrier-radical` and
`tg-euler-boundary-quotient-realization`. RH, the joint operator continuation,
cubic Hardy-index comparison and sub-unit law remain open.
