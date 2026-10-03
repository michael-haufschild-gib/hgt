# TG C9.11w — admission of the original polar cell error

- **ID:** tg-polar-ground-discretization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** P1 `tg-principal-polar-operator-cancellation`; route TG
- **Statement:** The exact within-cell errors of the original polar ground source are pairwise orthogonal and unconditionally summable in physical L2.
- **Status:** scratch, final production leaf and all eighteen affected public foundation audits pass; wired and indexed; global lint reports ten unrelated unwired modules, none in either affected leaf.

## Hard problem and result

The hard arithmetic problem is vanishing of the full signed prime–polar
ground tails. C9.11u/v identified their actual cumulative energy and
chronological work. This result removes one analytic obstruction to working
with their discrete arithmetic covariance: the original continuous polar
source can be replaced cell by cell by its exact mass, with a provably
convergent correction series.

Let `a>=0`, `B(u)=exp(-u/2) D_exp(u) f_a`, and
`g(u)=(exp(u)+1)/u`. For each integer `x>=2`, define

`alpha_x = integral_[log x,log(x+1)] g(u) du`,

`R_x = integral_[log x,log(x+1)] g(u) (B(u)-B(log x)) du`.

Then distinct `R_x` are orthogonal, their squared norms are summable, and
the vector family `R_x` is unconditionally summable. Each original polar
cell has the exact decomposition

`integral_cell rho(u) D_exp(u) f_a du = alpha_x B(log x) + R_x`,

where `rho(u)=2 cosh(u/2)/u` is the original polar density. Equivalently,
the original native polar-only operator on that cell plus
`alpha_x B(log x)` equals `-R_x`. The entire original correction family
therefore converges in physical L2.

The condition `a>=0` specifies a physical aperture. There is no arithmetic
decay, correlation, RH, limiting-integrability or infinite-sum premise.

## Dependency-closed paper proof

1. The audited entering-vector covariance is
   `<B(u),B(v)>=2a exp(-v)` for `u<=v`. Subtracting it four times gives
   `<B(u)-B(b),B(v)-B(c)>=0` whenever `b<=u<=c<=v`.
2. The same covariance gives the exact difference norm
   `||B(u)-B(b)||^2=2a(exp(-b)-exp(-u))` for `b<=u`.
3. The original entry is strongly continuous, and `g` is continuous on
   each positive compact cell. The defining vector integrands are strongly
   integrable. Moving the inner product through both Bochner integrals in
   step 1 proves pairwise orthogonality of different cell errors.
4. On the x-cell, step 2 gives
   `||B(u)-B(log x)||<=sqrt(2a)/x`.
   Also `0<=g(u)<=(x+2)/log 2`, and the cell length is at most `1/x`.
   The norm of a Bochner integral is at most the integral of its norm.
   Since `(x+2)/x<=2`, this proves
   `||R_x||<=(2 sqrt(2a)/log 2)/x`.
5. The series of squared norms is dominated by a constant times
   `sum_(x>=2) 1/x^2`, hence converges. The one-dimensional spans of the
   `R_x` form an orthogonal family of Hilbert subspaces. The Hilbert
   orthogonal-series theorem now proves unconditional vector summability.
6. The audited identity `rho(u) D_exp(u) f_a=g(u) B(u)` identifies the
   original integrand. Distribute the integral of
   `g(u)(B(u)-B(log x))`; pull the constant vector through its scalar
   integral. This proves the exact cell decomposition, with its unchanged
   mass. The original source operator formula at the empty prime set
   gives the native correction identity and its unconditional summability.

The coarse estimate in step 4 only establishes qualitative admission. No
numerical optimization or computation is used.

## Frontier consequence and limits

The admitted correction is tied to the original source. The exact
`alpha_x` remains in the discrete problem. No asymptotic coefficient,
independence model or selected prime sequence replaces it.

Pairwise orthogonality of the errors does **not** assert orthogonality of
the error sum to the discrete source. In particular this result does not
claim that total prime–polar energy splits into two norm squares.
The finite cell partition and full discrete Cauchy equivalence are paper
consequences still to be formalized if needed; the present leaf proves
the exact individual identities and full correction-series admission.

The required signed arithmetic covariance bound, full-response transport,
Gamma completion, Hardy cubic compatibility and strict sub-unit law remain
open. RH has neither been proved nor falsified.

## Lean evidence

Leaf: `formal/GaloisForLFunctions/RHTower/SoninPolarGroundDiscretization.lean`.
Eight public declarations include the literal error and mass, exact
orthogonality, square summability, vector summability, cell decomposition,
native correction identity and summability of the original corrections.
The existing chronological leaf now also exposes its proved entry
continuity and polar-density identity.

Full scratch audit `/tmp/tg-c911w-cells.log` exits 0 with empty diagnostics.
The existing chronological leaf's foreground production audit also exits
0 with empty diagnostics: `/tmp/tg-c911w-chronological-final.log`.
Final new-leaf audit and all eighteen public foundation queries are
recorded below when complete.

Corpus searches before implementation inspected candidate lemmas, source
arguments and ingredient sets. Covariance and polar-cell searches were
nonpartial; the counting-energy search was partial. They used snapshot
coverage with background refresh incomplete. No applicable original-cell
admission theorem was found among the inspected hits; this is not an
exhaustive novelty claim.

Final foreground new-leaf audit passed with exit 0 and empty diagnostics:
`lake --old env lean GaloisForLFunctions/RHTower/SoninPolarGroundDiscretization.lean
-o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninPolarGroundDiscretization.olean`.
Log: `/tmp/tg-c911w-final.log`. No full or umbrella build was run.

All eighteen public `#print axioms` queries passed, with only `propext`,
`Classical.choice`, and `Quot.sound`: `/tmp/tg-c911w-axioms.lean` and
`/tmp/tg-c911w-axioms.log`. No added axiom, hole, numerical experiment or
heartbeat increase was used.

Index refresh exits 0 (`/tmp/tg-c911w-index.log`); all ten chronological
and eight discretization declarations were verified in `formal/LEAN_API.md`.
Global lint exits 1 with ten unrelated unreachable modules and no finding in
either affected leaf (`/tmp/tg-c911w-lint.log`). These concern six CCM leaves,
two MoebiusMollified leaves, `ThetaMovingShellFirstOrderPhase`, and
`ZetaZeroDensityPowerSaving`. The RH goal remains active and unmet.

Superseded owned proof drafts were removed. Production sources, foundation
audit scratch, final logs and corpus search evidence are retained. All owned
processes have exited.
