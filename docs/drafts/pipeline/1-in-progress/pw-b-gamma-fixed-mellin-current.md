# PW-B complete current at a fixed Mellin argument

- **Stage:** 1-in-progress
- **Status:** Source-level paper attack; no new Lean theorem claimed yet.
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

Target: all mixed-current integrals are admitted on the same open region,
and their full integral equals -Gamma'(s+1/2)/zeta(u). A Gamma-normalized
mixed current therefore has zero integral there. This is neutral transport
at every u in that region; it is not independently forced fixed-grade Ward
balance or a critical-strip continuation theorem.

## Hard obligations and positive direction

Prove the complete combined source equality, exact atom norm scaling,
full summation/integration exchange and literal logarithmic integral.
Retain all coefficients and the original endpoint domain. The previous
dual-norm obstruction forbids inferring this passage from generic weighted
Hilbert admission. Actual Xi occurrence and the source law forcing its
orientation remain open even if the displayed transport identity closes.
