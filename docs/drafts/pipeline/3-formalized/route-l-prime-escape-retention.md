# Route L source-only prime escape and retention bound

- **ID:** L-PRIME-ESCAPE-2026-09-10
- **Stage:** 3-formalized
- **Type:** Explicit source construction and quantitative retention law
- **Lean:** `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanPrimeEscape`
- **Source:** [completion attack](../1-in-progress/route-l-source-selected-completion-attack.md), C8

## Exact statement

Let `p_n` be the repository's increasing ordinary-prime enumeration and `C` the
norm of its literal raw Big-Witt horizon. In row `n`, choose the least prefix
whose positive trace is at least `(n+1)(C+1)`, then normalize its trace to one.
This defines a single packet sequence `u_n` before any Xi copy or energy
coefficient is supplied. Lean proves:

1. Every coefficient of `u_n` is a nonnegative real number.
2. Its algebraic one-leg trace is exactly one.
3. Its ambient Hilbert norm is at most `1/(n+1)`.
4. Its singular graph admission converges to the nonzero vertical generator.
5. Every bounded range of left-prime labels eventually leaves its support.
6. For every real `A`, its exact energy is `E_A(u_n)=A/p_n`, tending to zero.

For an arbitrary finite complex packet with nonnegative real parts, define
`H_B` as the sum of its real coefficients with left prime at most `B`. Lean also
proves

`(A/B) H_B(f) <= Re E_A(f)` for `A>=0`.

Hence, for `A>0`, every sequence of such packets with `E_A(u_n)->0` has
`H_B(u_n)->0` for every positive finite `B`. This implication needs no
trace normalization or graph-convergence assumption.

## Dependency-closed paper proof

Each raw row has divergent positive trace and ambient norm at most `C`, by the
existing Big-Witt horizon construction. Thus the least prefix meeting the
threshold exists. Dividing its norm bound by its trace gives at most
`C/((n+1)(C+1)) <= 1/(n+1)`. Normalization leaves trace one, so the graph limit
is `(0,1)`. The support keeps left prime exactly `p_n`; monotonic cofinality of
the prime enumeration removes every bounded left-prime range. The existing
literal reporter evaluation gives `A/p_n`, which tends to zero.

For the general bound, every left prime `p<=B` has `A/p>=A/B` when `A>=0`.
Multiply by the nonnegative real packet coefficient and sum. Terms outside
that range are nonnegative and can be retained on the right. For a sequence
whose energy tends to zero, squeeze `(A/B)H_B` between zero and the real energy,
then divide by the fixed positive coefficient.

## Mathematical consequence and limits

The source-only zero-energy prescription exists unconditionally, including at
nonzero free coefficient. It therefore does not force that coefficient to
vanish. The zero output is explained by escape of all finite-prime mass.
The general retention bound proves that this mechanism is necessary for any
nonnegative zero-energy approximation at positive coefficient.

An arithmetic proof would need vanishing readout and retained nonzero
finite-prime mass in the same literal source construction, or another argument
identifying the fixed physical reader. Fixed-left rows supply retention but
read `A/p`; the escape sequence supplies zero limiting energy but loses every
finite left-prime range. No theorem combining these properties is proved here.
No off-line Xi zero is asserted to exist, and RH remains unproved.

## Verification

- Scratch: `lake env lean /tmp/route_l_prime_escape.lean` passed without warnings.
- Axiom audits of positivity, finite-prime escape, graph and energy limits, the
  retention bound and its limit consequence: only `propext`, `Classical.choice`,
  `Quot.sound`.
- New module wired into `GaloisForLFunctions.RHTower`; no umbrella build.
- Scoped final audit: `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanPrimeEscape` passed on 2026-09-11. Only the new module compiled; cached dependency diagnostics were replayed.
- `scripts/formal_tools.py lint` passed; scoped whitespace checks passed. No full or umbrella build was run.
