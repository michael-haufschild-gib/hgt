# The deformation-obstruction calculus

- **ID:** deformation-obstruction
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (organising law) + THEOREM (Lean, first instance)
- **Statement:** Classify every candidate route to RH by the space of objects satisfying its inputs.
  A route can succeed only if that space contains no object with a zero off the critical line. Every
  unconditional input isolated so far has a nonempty such space, and the only known input with an
  empty one already determines `ζ`.

## The law (corrected: three cases, not two)

Let `I` be a set of conditions on a Dirichlet series (or on its completion). Write `Def(I)` for the
set of objects satisfying `I`. Then:

- **(a) `Def(I)` contains an object with a zero off the critical line.** No argument using only `I`
  proves RH, whatever its sharpness.
- **(b) `Def(I)` contains only `ζ`.** Then `I` is a rigidity, by Hamburger essentially "Dirichlet
  series + functional equation", and no reduction has been made.
- **(c) `Def(I)` is large and every member has all zeros on the critical line.** This is the only
  productive case, and it is where every successful proof of an analogous statement lives:
  real-rooted entire functions, the Hermite--Biehler class, spectra of self-adjoint operators, and
  over a finite field the zeta functions of smooth projective curves.

The first version of this card asserted a dichotomy. That was wrong: case (c) is nonempty in
mathematics and is the whole point. What the programme has established is the sharper claim that
in the analytic setting the transition between (a) and (b) is **discontinuous** — no input isolated
so far lands in (c) with a membership test for `ζ` that is not itself RH.

Over a finite field, case (c) is reached by a **construction**, not a verification: the curve yields
a finite-dimensional cohomology, the cohomology carries a nondegenerate pairing, the pairing forces
the absolute values of the Frobenius roots, and the hypothesis is never tested against any single
zeta function. That is the difference the calculus isolates: **verification of `ζ` is impossible;
construction of a class containing it is the only open route.**

The law converts "why did this route fail?" into a computation: exhibit the deformation.

## Verified instances

| input class | deformation | zeros produced | recorded as |
|---|---|---|---|
| finite depth of source moments, positivity, log-concavity | `φ(x)[1 + t(−He₄+He₆−2He₈+He₁₀)(x)]` | size-three determinant `t²(−196+324t+16t²) < 0` | CANNOT-385 |
| moments to order `4m−1`, real Fourier divisor, Schwartz decay | `k_t = source + t·source⁽⁴ᵐ⁾` | packet at radius `t^{−1/(4m)}` | CANNOT-386 |
| coefficient size `≤ C·d(N)` + square-root cancellation of the Kloosterman-weighted sums | `d(N) − 2^θ·d(N/2)` at even `N` | `ζ(s)²(1 − 2^{θ−s})` vanishes at `s = θ`, every real `θ` | **this card**, MUST-389 |

The third instance is the sharpest, and it is now known in its strongest form: iterating the single
Euler-factor step at one prime gives, for **any** finite list of prescribed points at **any**
abscissas, a coefficient sequence dominated by a constant times `d(N)` — hence carrying the full
square-root cancellation with that constant — whose Dirichlet series vanishes at every prescribed
point (`RHTower.exists_weil_compatible_zero_configuration`). The inputs give neither a zero-free
region nor a bound on the number of off-line zeros: their deformation space is everything.

## The Lean theorems

`RHTower.norm_tsum_kloosterman_weighted_le` — Weil's saving holds for **any** coefficient sequence
dominated by the divisor function, with the same constant. The saving is a property of the modulus
alone.

`RHTower.deformedDivisorCoeff`, `RHTower.norm_deformedDivisorCoeff_le`,
`RHTower.hasSum_deformedDivisorCoeff` — the deformation, its size bound `(1 + ‖c‖)d(N)`, and its
Dirichlet series `ζ(s)²(1 − c·2^{−s})`.

`RHTower.norm_tsum_kloosterman_deformed_le` — the deformed family satisfies the identical Weil
bound.

`RHTower.deformed_zero_at`, `RHTower.exists_weil_compatible_zero` — the zero at `s = θ`.

`RHTower.deformation_factor_ne_zero_at_reflection` — the factor `1 − 2^{θ−s}` does **not** vanish at
`s = 1 − θ` unless `θ = 1/2`: the zero set is not symmetric about the critical line. This is the one
input the deformation violates.

## What the law says to do

Stop looking for sharper estimates; look for inputs whose deformation space is empty. The only known
such input is the pair (Dirichlet series, functional equation), which by Hamburger determines `ζ`.
Two consequences:

1. A proof must use the functional equation and the Dirichlet series **simultaneously and exactly**,
   never through an inequality whose hypotheses survive a local deformation.
2. The positivity that settles the analogous question over finite fields lives on a discrete,
   finite-dimensional object with a nondegenerate pairing. `ζ` is the scattering coefficient of the
   continuous spectrum, where no such pairing is known. Every mechanism that borrows discrete
   positivity — square-root cancellation for character sums over finite fields, the Petersson inner
   product on cusp forms, a spectral gap — is a statement about the discrete part, and the
   deformation calculus explains why it cannot cross over.

## Open core

Compute `Def(I)` for the inputs that have not yet been deformed: the explicit formula with a fixed
prime window, the mollified second moment, the Weil positivity criterion. Each is either deformable
(and then retired) or rigid (and then the first candidate for a proof).

## Log
- 2026-09-24 — created; the law stated, the third instance proved and formalized, MUST-389 recorded.
