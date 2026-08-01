# Unrestricted min-entropy route to static complexity growth

- **ID:** static-ensemble-unrestricted-min-entropy
- **Stage:** 5-failed
- **Type:** RETIRED ROUTE
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Status:** false at the strength required for linear growth

## Attempt

For a random static local Hamiltonian, define worst-target small-ball mass

\[
 Q_\varepsilon(t)=\sup_\psi
   \Pr_H\{d(\Phi_H(t),\psi)\leq\varepsilon\}.
\]

The attempted bridge was
`-log Q_epsilon(t) = Omega(t)`, followed by a union bound over all circuits
shorter than time `t`.

## Obstruction

Let the ensemble depend on `m` real coefficients and restrict to a coefficient
ball `K` carrying probability at least `p > 0`.  If the Hamiltonian map is
`L_H`-Lipschitz and the evolution metric obeys the Duhamel bound, then

\[
 d(\Phi_H(t),\Phi_{H'}(t))\leq |t|L_H\|H-H'\|.
\]

An `epsilon/(|t|L_H)`-net of `K` therefore maps to an `epsilon`-cover of the
evolved ensemble.  For an `m`-dimensional radius-`R` coefficient ball this
cover has at most

\[
 N\leq(1+2R|t|L_H/\varepsilon)^m
\]

members.  Some image ball has probability at least `p/N`, hence

\[
 -\log Q_\varepsilon(t)
 \leq m\log(1+2R|t|L_H/\varepsilon)-\log p.
\]

For fixed locality, `m=poly(n)`.  At exponential time this ceiling is only
polynomial in `n`, not linear in `t`.  Unrestricted ensemble min-entropy cannot
prove Brown--Susskind growth.

## Positive survivor

Restrict centers to states preparable by circuits of size `s < t`.  The
covering argument no longer applies because its heavy centers may themselves
have order-`t` complexity.  The surviving target is the computational
small-ball mass

\[
 Q_{\varepsilon,s}^{\rm short}(t)=
 \sup_{C:\,|C|\leq s}
 \Pr_H\{d(\Phi_H(t),C\Phi_0)\leq\varepsilon\}.
\]

`ProjectiveSmallBallComplexityLaw.lean` formally proves the exact finite
dictionary union consequence.  The new open core is a matrix-exponential
Gaussian-chaos bound on `Q_short`, uniform over shallow circuits.  No positive
claim about its decay is made here.
