# Sharp stability at a power-order clock mass collision

- **ID:** clock-collision-sharp-stability
- **Stage:** 3-formalized
- **Type:** PROVED / exact feasible-value classification
- **Source:** `ConformalClockContinuousMatrixRecovery` and its distinction between uniqueness
  at a collision and division by a nonzero local spectral gap.
- **Statement:** For integer q>=1, L>=0 and epsilon>=0, the possible origin values a of
  real L-Lipschitz functions with |x|^q |u(x)|<=epsilon for every real x are exactly
  those satisfying q^q |a|^(q+1)<=(q+1)^(q+1) L^q epsilon.

## Why this is the next question

The previous classification recovers continuous scale through isolated scalar-mass
collisions, but proves no quantitative inverse. A mass field diag(x^q,0) reads the
scale error through multiplication by x^q. A Lipschitz prior should recover the
missing origin value with optimal exponent 1/(q+1), rather than a nonexistent
uniform division bound. Even q gives nonnegative diagonal mass data on the whole line.

## Corpus-first audit

`research "Lipschitz weighted vanishing power sharp interpolation" --no-refresh --json`
returned Lipschitz weights, clipped triangular weights and generic graph estimates,
but no exact feasible-origin-value classification. Results have source-only freshness,
an older coverage snapshot and unmeasured semantic coverage. The subsequent
weighted-tent and arithmetic/geometric-mean searches completed the overlap audit.
No external sources may be searched or read.

## Exact theorem and proof

The unconditional Lean statement is an iff with the positive gap order encoded
as `q + 1` and L,epsilon as nonnegative reals. The left side is existence of u with
the complete weighted bound on ALL real x, its Lipschitz certificate, and u(0)=a.
No sampled bound or assumed inverse-stability estimate is allowed.

Set A=|a|. For L>0, Lipschitz continuity forces |u(t)|>=A-L*t for t>=0.
Evaluate at t=q*A/((q+1)*L); the weighted bound gives exactly the proposed inequality.
For sufficiency use u(x)=sign(a)*max(0,A-L*|x|). Its Lipschitz constant is at most L.
The homogeneous Bernoulli argument below supplies the exact all-real bound and
its attaining point without derivatives. A=0 uses the zero function.
For L=0 the function is constant; the unbounded weight forces a=0, and the proposed
inequality also forces a=0. All endpoint cases are included in the formal theorem.

## Attack and remaining work

- [x] Search exact weighted-tent extremum and feasible-value mechanism in corpus.
- [x] Audit general-q and L=0 cases independently of the desired conclusion.
- [x] Write dependency-closed paper proof with exact extrema and Lipschitz constants.
- [x] Formalize the full iff and extremizing witness; no numerical experiments.
- [x] Direct Lean, axiom, umbrella, index and lint audits.

The full general-order classification is Lean-verified. No external scientific-novelty claim.

## Completed reduction and q=1 case (2026-10-08)

`ClockGapEnvelopeRecovery.lean` now proves the exact feasible-anchor classification
for arbitrary nonnegative weights on any pseudometric space. Its division-free form
is `g(x)|a| <= epsilon + g(x)L dist(x,p)` for every x; a single signed distance
tent attains the least absolute envelope everywhere. For g(x)=|x| and p=0 it proves
the full q=1 iff `a^2 <= 4 L epsilon`, including L=0 and epsilon=0. Direct leaf and
all-declaration axiom audits passed. See
`clock-gap-envelope-recovery.md`.

The follow-up query `Lipschitz distance cone weighted recovery` and exact Lean-source
searches found generic Lipschitz/weight estimates and corpus tent constructions,
but no matching exact classification. Only Lean source entries were read. The
general-q task reduced to the scalar polynomial extremum. That remaining obligation
is now discharged by `ClockPowerGapRecovery.lean`.

## Algebraic paper closure (2026-10-08)

The local dependency `Mathlib/Algebra/Order/Ring/Pow.lean` proves homogeneous
Bernoulli: for r>=0 and 2r+b>=0,
`r^n + n r^(n-1)b <= (r+b)^n`. Apply it with n=q+1,
r=(q+1)Lt, and b=qA-r. Its positivity conditions follow from q,A,L,t>=0.
Expanding and cancelling q>0 gives the global polynomial estimate
`(q+1)^(q+1) L^q t^q (A-Lt) <= q^q A^(q+1)`.
This replaces the derivative argument with an exact algebraic proof, valid even
when A-Lt is negative. The positive-part envelope is zero in that latter case.

If L>0, equality holds at t=qA/((q+1)L), proving necessity from the all-real
weighted bound and sufficiency from the polynomial estimate. The existing signed
tent theorem supplies one compatible function for sufficiency.
If L=0 and A>0, take t=(epsilon+1)/A+1>=1; since q>=1, t^q>=t and hence
t^q A>=epsilon+1+A>epsilon, a contradiction. Therefore A=0 is necessary and
sufficient, exactly as the proposed scalar inequality requires.

The corpus query `natural power product maximum weighted arithmetic geometric mean`
returned general arithmetic/geometric mean inequalities and unrelated operator
versions. Only Lean entries were inspected; partial=false, semantic coverage
unmeasured. The proof uses the verified local homogeneous Bernoulli API rather
than importing real-power mean inequalities.

## Final Lean audit (2026-10-08)

`formal/GaloisForLFunctions/HTGeometry/ClockPowerGapRecovery.lean` proves four theorems:
`powerClockGap_polynomial_bound`, `powerClockGap_envelope_iff`,
`powerClockGap_feasible_iff`, and `powerClockGap_extremizer_bound_iff`.
The final direct command
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ClockPowerGapRecovery.olean GaloisForLFunctions/HTGeometry/ClockPowerGapRecovery.lean`
passed without diagnostics. Imported `#print axioms` for all four reported only
`propext`, `Classical.choice`, and `Quot.sound`. No added source premise, axiom,
proof debt, numerical experiment, or heartbeat increase was used.

The umbrella imports this leaf exactly once; index regeneration passed and all four
API rows are present. The leaf has no forbidden declarations or trailing whitespace.
No full or umbrella build was run. Global lint exited 1 on seven unrelated unreachable
modules: `RHTower.XiGaussianOneSidedIdentityLimitRH`, `HTGeometry.ApertureConeCalculus`,
`HTGeometry.ApertureConeWinding`, `HTGeometry.ApertureLogTranslation`,
`HTGeometry.ApertureOpenHistoryIdeal`, `HTGeometry.BoundaryCoronaCStarAlgebra`,
and `HTGeometry.HurwitzOpenSetZeroLocus`. No owned-leaf error was reported.
Owned `/tmp/hgt-power-gap*` scratch is cleaned after recording this evidence.

## Next conjecture

`clock-finite-window-gap-recovery.md` replaces the all-real-line
observation requirement by a finite radius. Its proposed exact criterion combines
an endpoint test with the global sharp test only when the critical point lies inside
the observed window. That finite-window result is now Lean-verified in
`ClockFiniteWindowGapRecovery.lean`.
