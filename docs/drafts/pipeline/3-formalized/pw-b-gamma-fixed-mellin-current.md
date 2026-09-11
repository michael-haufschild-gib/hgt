# PW-B complete current at a fixed Mellin argument

- **ID:** PW-B-GAMMA-FIXED-MELLIN-CURRENT-2026-09-11
- **Stage:** 3-formalized
- **Status:** All six public theorems passed final foreground scratch without diagnostics. Exact checked source promoted and wired once; targeted leaf build passed in28s. All six public names are indexed; final repository formal lint passed.
- **Scope:** Derive the actual mixed current and its admitted integral before testing continuation or Xi incidence. RH remains unproved.

## Conjecture and original-source mechanism

Write u=z+s. The existing complete source has Mellin integral
Gamma(s+1/2)/zeta(u) for Re(s)>-1/2 and Re(u)>1.
Changing z with u fixed changes the Mellin weight. Its original derivative
is the mixed current x^(s-1)*(M'_z-log(x)*M_z), not M'_z alone.
At index n the two logarithms combine exactly to -log(n*x). Hence
substitution t=n*x transports the whole mixed atom to the original
Gamma logarithmic kernel. Its norm mass is a fixed finite log-Gamma
mass times the norm of the original L-series term at u. This avoids
adding a logarithmic arithmetic loss by estimating the two terms separately.

Proved: all mixed-current integrals are admitted on the same open region,
and their full integral equals -Gamma'(s+1/2)/zeta(u). A Gamma-normalized
mixed current therefore has zero integral there. This is neutral transport
at every u in that region; it is not independently forced fixed-grade Ward
balance or a critical-strip continuation theorem.

## Hard obligations and positive direction

The complete combined source equality, full summation/integration exchange
and literal logarithmic integral are proved. The general weighted-source
theorem retains the exact atom norm scaling in its admitted Fubini proof.
All coefficients and the original endpoint domain are retained. The previous
dual-norm obstruction forbids inferring this passage from generic weighted
Hilbert admission. Actual Xi occurrence and the source law forcing its
orientation remain open after this transport identity closes.

## Complete assembly

Define Phi(t)=-log(t)*Q(t) and W_z(t)=t^(-z)*Phi(t).
The admitted log-Gamma Mellin kernel gives
Mellin(Phi,s)=-Gamma'(s+1/2) for Re(s)>-1/2.
The actual complete-source identity is

`sum_n mu(n)*W_z(n*x)=x^(-z)*(M'_z(x)-log(x)*M_z(x))`.

Its proof uses the original source and current summability before subtracting
their series. The zero coefficient remains zero, and for every positive n,
log(n*x)=log(n)+log(x) and the exact complex-power scaling retain the
original phase. The general weighted Möbius Mellin theorem proves absolute
source admission and Fubini before giving its transform. Applied to W_z at
u=z+s, it yields the claimed complete mixed-current value on the same open
region, with no stronger arithmetic collar.

The original fixed-u integrand has actual derivative
x^(u-z-1)*(M'_z-log(x)*M_z). Consequently the completely admitted current

`Gamma(s+1/2)*(M'_z-log(x)*M_z)+Gamma'(s+1/2)*M_z`

has zero Mellin integral in that region. This cancellation is supplied by
Gamma normalization of the fixed-u transport. It does not prove physical
PW partner balance, continue the original integral through its boundary or
identify a nonzero Xi occurrence for the paired skew operator.

## Lean verification

Leaf: `ThetaCuspHawkingParikhWilczekGammaFixedMellinCurrent.lean`.
Scratch: `/tmp/pwb-gamma-fixed-mellin-current.lean`.
Public declarations:

- `pwGammaRayLogCurrent_mellinConvergent`;
- `pwGammaRayLogCurrent_mellin`;
- `pwGammaMobiusFixedMellinCurrent_weighted_source`;
- `pwGammaMobiusFixedMellinCurrent_hasMellin`;
- `pwGammaMobiusFixedMellinCurrent_source_hasDerivAt`;
- `pwGammaMobiusFixedMellinCurrent_normalized_hasMellin`.

No zero-location, Ward-balance or source-continuation premise is used.
The original convergence inequalities are explicit in the integral statements.

The [search record](../1-in-progress/pw-b-gamma-fixed-mellin-searches.json) retains the deep
query's partial coverage732156 and the hybrid query's local-Qdrant timeout.
Applicable methods were verified against the actual Mellin/Gamma source and
the complete weighted Möbius theorem; abstract transport suggestions did not
provide endpoint admission.
