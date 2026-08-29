# EWQ-V source-independent diagonal Krein completion

- **ID:** EWQ-V
- **Stage:** 5-failed
- **Type:** `[FALSIFIED] [RETIRED RH ROUTE] [LEAN-PROVED NO-GO]`
- **Source:** `rh-current-frontier-map.md` · route EWQ-V
- **Lean:** `GaloisForLFunctions.RHTower.EulerSquarefreeWickSourceIndependentKreinCompletionNoGo`

## Killed RH chain

`independent Euler vacuum + EWQ forward/inverse incidence`
→ `unequal/mixed/indefinite diagonal completed matrix or jet`
→ `source-independent Hilbert/Krein self-adjoint landing`
→ `orientation`
→ `RH`.

For one Xi divisor write `chi=deltaS(p,rho)`.  Any finite auxiliary matrix retaining literal
entries `(chi, chi^-1)` and self-adjoint for a fixed real diagonal metric `diag(w)` satisfies

`norm(w_reverse) = norm(w_forward) * norm(chi)^2`.

Xi line reflection replaces the character norm by its reciprocal.  Applying the same fixed
nondegenerate metric at both points of one reflection orbit forces `norm(chi)=1`, hence
`Re(rho)=1/2`.  Therefore a global completion of the proposed kind already implies RH; off line,
the reflected pair cannot exist.  Auxiliary dimensions, arbitrary other entries and diagonal
masses, mixed metric signs, lack of positivity, and jet order do not change the obstruction.

## No-go closure

- **Exact killing theorem/mechanism:**
  `riemannHypothesis_of_everyXiEWQSourceIndependentDiagonalKreinCompletion` and
  `not_reflectionPair_ewqSourceIndependentDiagonalKreinCompletions_of_re_ne_half`.
- **Strongest positive survivor:**
  `ewqKrein_reverseWeightNorm_eq_forwardWeightNorm_mul_characterNormSq` proves the unique required
  metric-magnitude repair on each fibre.  It is exactly the modular counterweight `norm(chi)^2`.
- **New insight:** indefinite diagonal data do create magnitude change, but source independence is
  incompatible with reflection: the required metric ratio reverses on the partner fibre.  A
  divisor-dependent metric works only by importing the horizontal Xi coordinate, making it a
  receiver rather than a producer.
- **Status:** declared EWQ-V diagonal completed-matrix/jet chamber retired.  A non-diagonal metric
  that mixes source coefficients, or a non-self-adjoint landing, changes the route and requires a
  new frontier entry rather than reviving EWQ-V.

## Novelty and verification

Corpus search supplied the literal bilateral coefficients, arbitrary-diagonal positive receiver
rigidity, modular counterweight, and Xi reflection involution, but not their fixed-metric
reflection-orbit classification.  Literature audit through August 2026 found classical PSD/Krein
matrix inequalities but no Xi/EWQ source-independent completion theorem.  Paper proof and Lean
proof are dependency-closed.  Targeted module build passes; axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.  Repository lint reports unrelated pre-existing umbrella
reachability failures, none involving this module.

## Log

- 2026-08-29 — EWQ-V retired; exact modular-weight survivor formalized.

