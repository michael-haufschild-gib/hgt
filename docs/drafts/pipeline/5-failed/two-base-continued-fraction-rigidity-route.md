# Two-base continued-fraction rigidity route — retired

- **ID:** `two-base-continued-fraction-rigidity-route`
- **Stage:** 5-failed
- **Type:** FALSIFIED ROUTE (the proposed dichotomy itself remains undecided)
- **Source:** `docs/reports/rhtower_status_constraint_1107.md` · §3
- **Statement:** Continued-fraction return quality by itself does not decide leaf-intrinsic reflection rigidity.

## Retired proposal

`[CONJECTURE — NOT ESTABLISHED]` The two-base cell is rigid exactly for irrational ratios with
unbounded continued-fraction coefficients, with badly approximable and Liouville ratios defining
opposite existence regimes.

This card does **not** prove that dichotomy false.  It proves that the proposed return-time mechanism
does not reach it and must not generate further work without a new carrier-derived estimate.

## Exact route failure

Let `T=2π/α` and `θ=2πβ/α`.  A denominator `q` of a continued-fraction convergent makes
translation by `qT` nearly fix both one-sided flank traces.  For the translated difference

\[
\Delta_qG(z)=G(z+qT)-G(z),
\]

the coefficient multipliers are `e^{-inqθ}-1`, so better rational approximation gives a smaller
flank norm after the absolutely summable tail is separated.

The implication needed by the route is nevertheless missing:

\[
\text{small on both flanks}
\quad\Longrightarrow\quad
\text{controlled in the intervening seam}.
\]

That implication is false for the pure analytic class.  The verified Arakelyan construction in the
parent Goldilocks card gives even entire functions arbitrarily small on both flanks and arbitrarily
large in the seam.  Quiet-crossing and finite-order variants close only after adding an explicit
cross-seam growth/normality budget; the surviving leaf-only cell allows exactly the infinite-order
nonnormal regime where return accuracy has no maximum-principle consequence.

The exact-period Bohr projectors sharpen the failure.  For every irrational ratio—not separately
for badly approximable and Liouville ratios—a positive transverse projector converges to its slice
on one flank and to zero on the reflected flank.  A hypothetical nonconstant weld therefore forces
the same qualitative nonnormal seam separator in every irrational Diophantine class.  Continued
fractions alter only convergence rates toward that mismatch.

## Positive replacement

`[PROVED]` Diophantine return data is a **rate modifier**, not a rigidity invariant, until the carrier
supplies a transverse normality estimate.  Any future Diophantine theorem must have the form

\[
\text{exact semigroup carrier estimate}
\; + \;
\text{return-rate class}
\quad\Longrightarrow\quad
\text{normality or contradiction}.
\]

The carrier estimate must be proved first and independently of continued fractions.

The positive theorem that survives without such an estimate is
[finite-transverse-leaf-reflection-rigidity.md](../2-fully-proven/needs-audit/finite-transverse-leaf-reflection-rigidity.md):
finite transverse spectral width produces a finite shift polynomial, reflection produces its
reciprocal, and coprimality forces exact periodicity.  This replaces approximate returns by an exact
constraint.

## Re-entry gate

Do not re-open the badly-approximable/Liouville split unless one first proves a carrier-intrinsic
bound that controls a cross-seam normal-family seminorm from the exact two-generator coefficient
germ.  A trace-only, geometry-only, or return-time-only bound is excluded by the pure-class
countermodels.

## Scientific verdict

`[BRIDGE, NOT NEW SCIENTIFIC KNOWLEDGE]` The route death combines standard continued-fraction
returns, the project’s already-proved Arakelyan countermodels, and the new Bohr-projector mismatch.
It is a decisive research-direction correction, not a new theorem of science.

## Log

- 2026-07-11 — route retired; the conjectural dichotomy left undecided; positive finite-transverse
  replacement and the carrier-estimate re-entry gate recorded.
