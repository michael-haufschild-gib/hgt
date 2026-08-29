# Modular seam certificate discovery

Date: 2026-08-29  
Status: exact symbolic computation complete; diagnostic only; forbidden as input to Lean proofs

## Questions

1. Does the first nonzero seam-displacement coefficient of the direct C5 fixed-action Jacobian
   admit a clean sign certificate at the actual self-dual modular scale?
2. Does the exact source-positive projective drift for S6F/TCD point into the positive chamber at
   the modular seam?

The script independently transcribes the polynomial vector fields and jet recurrences in
`PolynomialODEJetRankThreeGeneralClosure.lean` and
`PolynomialODEJetRankThreeSourcePositiveClosure.lean`. It uses exact rational SymPy algebra only.

## Outcome

### C5 fixed-action Jacobian

Let `X=R^2`, and let `A=-L2`, `B=-L4`, `C=-L6`, `D=-L8` be the even seam log-jet coordinates.
The first nonzero displacement coefficient has numerator

```text
N = A^2 D - 18 A^3 C + 36 A^2 B^2 - 5 A B C + 4 B^3
  = 18 A^2 (2 B^2 - A C) + (A^2 D - 5 A B C + 4 B^3).
```

Exact modular elimination gives

```text
N = -3 P12(X) / (4096 (X-6)^6),
P12(X) = 3325 X^12 - 72207 X^11 - 9199464 X^10 + 118872540 X^9
         + 1844694576 X^8 - 21906006336 X^7 + 154724411520 X^6
         - 1373965804800 X^5 + 1641722618880 X^4 + 2020565606400 X^3
         - 859963392000 X^2 - 4807434240000 X + 501645312000.
```

The tempting half-line statement `N>0` for every `X>191/10` is false: the numerator has a later
positive root near `X=56.86` and eventually becomes negative. This kills that overstrong algebraic
shortcut.

The physical statement survives sharply. Corpus already proves
`191/10 < X < 20`. On exactly `[191/10,20]`, the degree-12 Bernstein expansion of the full numerator
`-3 P12(X)` has 13 strictly positive rational coefficients. The smallest is
`2214487347729023423585466546267 / 200000000000`. Thus computation selects a finite, exact,
computation-free paper target: derive the same modular identity independently, prove the Bernstein
identity algebraically, and combine it with existing exact scale bounds.

The older reverse minor `2B^2-AC` has a shifted-positive numerator for all `X>191/10`. The residual
block `A^2D-5ABC+4B^3` does not; compensation is essential even at this first local coefficient.

### S6F/TCD projective drift

The exact source-positive D1 polynomial has degree 24 and 671 terms. Its projective drift has degree
27 and 908 terms. Drift vanishes identically on every algebraic seam state, as parity requires.
Its derivative along the physical modular vector field at a seam state is

```text
3 P14(X) / 274877906944,
```

where `P14` is recorded exactly in `results.json`. After `X=191/10+Y`, all 15 coefficients of
`P14` are strictly positive. Therefore the physical drift points strictly into the positive
direction at the actual seam scale. This does not prove drift positivity on the full interval, but
it removes the unresolved cancellation boundary and supplies the correct computation-free local
theorem to formalize after independent derivation.

A hostile higher-jet test then computed physical-flow derivatives three and five at the seam. Their
shifted polynomials have, respectively, all coefficients strictly negative and all coefficients
strictly positive for `X>191/10`. Thus local absolute monotonicity is false: the first three nonzero
drift derivatives have signs `+,-,+`. The positive survivor is an alternating/Stieltjes-like local
jet law, not coefficientwise positivity of every derivative.

## Research consequences

- C5 direct Jacobian gains an exact local seam target on the already-proved physical scale window.
  Global route still needs compact bulk and large-action control.
- C5 cannot be proved from a scale-half-line sign or from separate positivity of the residual
  eighth-jet block; physical scale localization and signed compensation are structural.
- S6F projective drift has correct exact inward seam orientation. Remaining finite gate is extension
  away from seam, not boundary sign.
- The easy S6F absolute-monotonicity shortcut is killed by its strictly negative third seam
  derivative. Any local certificate should exploit alternating odd jets or a rational/Stieltjes
  representation instead.
- Neither result proves RH or closes cofinal/all-order landing.

## Reproduction

RunPod: Python 3.12.3, SymPy 1.13.3, 128 CPUs exposed. Exact run took about 21 seconds.

```bash
python3 run_experiments.py --output results.json
python3 verify_results.py .
```

`results.json` contains all exact jets, factorizations, root isolations, shifted coefficients, and
Bernstein coefficients. `SHA256SUMS` authenticates downloaded artifacts. No output may be imported
as a Lean premise, certificate, tactic result, or decision procedure.
