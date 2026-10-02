# PM: scalar tail correction fails; centered Mertens window floor survives

- **ID:** PM-MERTENS-WINDOW-VARIANCE
- **Stage:** 5-failed (the specified scalar correction only)
- **Type:** FORMALIZED CONSTRUCTION NO-GO / FORMALIZED POSITIVE SURVIVOR
- **Source:** `rh-current-frontier-map.md`, route PM; literal raw Fermi error and full-half-line coercivity.
- **Statement:** The weighted Mertens energy on `(N,2*N]` has a positive cofinal floor simultaneously for every scalar center. The last-scale harmonic correction of raw Möbius Fermi coefficients does not converge to Haar in the canonical norm.

## Goal

Test the proposed source correction, rather than assume that removing its
known harmonic tail removes its entire canonical error. This is an
obstruction to that construction, not witness half-mass positivity or RH.
The positive survivor isolates oscillation which survives every scalar
centering on a moving multiplicative interval.

## Gates

- [x] Well-posed literal source and attack.
- [x] Dependency-closed paper proof checked against the exact Lean carriers.
- [x] Positive survivor and source obstruction formalized and audited.
- [x] This construction retired after both audits; route PM remains open.

## Exact corrected source

For integer `N >= 1`, put `h_N = sum_(d<=N) mu(d)/d`,
`P(t) = -fermiNymanGen 1 t`, and
`B_N(t) = rawMobiusFermiApprox N t - N*h_N*P(N*t)`.
Its full-half-line auxiliary error is

`E_N(t) = 1_(0,1](t) + sum_(d<=N) mu(d)*{1/(d*t)}
          - N*h_N*{1/(N*t)}`.

Finite floor inversion, already present in the corpus, gives `E_N(t)=0`
for `t>1/N`. For `N <= x < 2*N`, it gives the exact identity

`E_N(1/x) = M(x)-M(N)+N*h_N`.

The literal Fermi error is `E_N(t)-2*E_N(2*t)`. The inspected full-half-line
coercivity theorem bounds the complete auxiliary energy by six times the
Fermi energy. Consequently Fermi-error convergence would imply

`(1/N) * integral_1^2 |M(N*u)-M(N)+N*h_N|^2/u^2 du -> 0`.

Define `m(x)=integral_1^2 M(x*u) du` and
`V(x)=integral_1^2 |M(x*u)-m(x)|^2 du`. The interval has length one.
Variance minimization and `u^2 <= 4` then imply `V(N)/N -> 0`.
This deduction keeps the entire error; it does not set the lower tail to zero.

## Paper obstruction to vanishing intrinsic variance

Let `q=sqrt(2)`. On `[1,2]` define the fixed mean-zero test

`phi(u)=1/u` for `1<u<=q`, and `phi(u)=-1/u` for `q<u<=2`.

Endpoint values do not affect the integrals. Its integral is zero and

`b(s)=integral_1^2 phi(u)*u^s du = -(q^s-1)^2/s`.

For every `Re(s)>0`, `b(s) != 0`: `|q^s|=q^Re(s)>1`.
Set `J(x)=integral_1^2 M(x*u)*phi(u) du`. Cauchy--Schwarz after subtracting
`m(x)` gives `|J(x)| <= ||phi||_2*sqrt(V(x))`.

Vanishing `V(N)/N` for integer N also gives `V(x)/x -> 0` for real x.
For `N=floor(x)` and `1<=u<=2`, bounded Möbius increments give
`|M(x*u)-M(N*u)| <= 2`. Distance to the constant functions changes by at
most two in L2, so `sqrt(V(x)) <= sqrt(V(N))+2`. Hence `J(x)=o(sqrt(x))`.

There are two equivalent ways to close the analytic contradiction.

1. For `Re(s)>1`, the corpus's Mertens Mellin identity and absolute Fubini
   give `F(s)=integral_1^infty J(x)*x^(-s-1) dx
                = b(s)/s * (1/zeta(s)-1)`.
   The finite subtraction uses `M(v)=1` on `1<=v<2` and `integral phi=0`.
   If `J=o(sqrt(x))`, F is analytic on `Re(s)>1/2`, and the cleared
   identity extends there. At a corpus-supplied critical zero rho,
   Abel splitting gives `r*F(rho+r)->0`. Since `zeta(rho+r)/r` has a finite
   limit, the cleared identity would give `b(rho)=0`, a contradiction.
   No simplicity assumption is needed.

2. Reuse the existing bounded-weight critical boundary theorem directly.
   With `ell(t)=max(-log(t),0)` for positive t and
   `v(t)=ell(t)-2*ell(q*t)+ell(2*t)`, v is a bounded continuous logarithmic
   tent supported on `[1/2,1]`, with
   `mellin v s=(1-q^(-s))^2/s^2` for `Re(s)>0`.
   Finite summation gives
   `sum_n mu(n)*v(n/(2*x)) = -J(x)`.
   Thus `J=o(sqrt(x))` contradicts
   `chronologicalMobiusWeightedSource_not_littleO` at a critical zero.
   This route avoids re-proving complex continuation and the Abel lemma.

Nonnegativity and failure of convergence to zero yield
`exists c>0, forall N0, exists N>=N0, c*N <= V(N)`.
This is the proposed unconditional positive survivor, not a numerical
lower-bound optimization. Its Lean bridge is still pending.

## No-go closure

- **Killing mechanism:** A single last-scale harmonic correction leaves
  intrinsic Mertens oscillation on the first omitted interval; its variance
  cannot be little-o of the critical scale.
- **Positive survivor:** Cofinal lower variance after optimal scalar
  centering, witnessed by one fixed logarithmic Haar test.
- **New insight:** Removing the scalar harmonic tail is insufficient.
  Any successful correction must alter nonconstant source oscillation,
  not only its mean or one reciprocal tail coefficient.
- **Status:** Closed for this construction. `PMMertensLogTent.lean` proves
  the general-ratio all-centers floor and integer transfer;
  `PMCorrectedMobiusWindow.lean` proves the exact corrected-source identity,
  its cofinal canonical error floor and non-convergence. Both targeted
  `--old` builds and final real-file `lake env lean` audits passed. All 47
  exported declarations have only `propext`, `Classical.choice`, and
  `Quot.sound` as transitive axioms. Both leaves are wired into RHTower.
  The unweighted optimal-mean variance statement follows on paper from
  the stronger canonical all-centers floor; its separate minimizer formula
  is not needed by the Lean obstruction. RH and witness positivity remain open.

## Corpus audit

- `FermiNymanRawMobiusTailFloor`: literal raw source, floor inversion,
  and full-half-line coercivity (source inspected).
- `Sieve/PartialSumMellinBridge`: Mertens integral for `1/zeta`
  (entire leaf inspected).
- `ChronologicalWeightedBoundary`: bounded measurable weight theorem,
  analytic continuation and critical Abel obstruction (relevant source inspected).
- `ChronologicalRawHeatObstruction`: unconditional critical-zero extraction
  using `exists_riemannZeta_line_zero_dyadic` (relevant source inspected).
- `EulerDeletionCountertermRigidity`: different correction carrier;
  changes a linear reciprocal error, not the last Fermi generator.
- Search58 was partial at reranking. All returned candidate/source statements,
  methods and ingredient groups were inspected. Exponent receivers do not
  exclude little-o at the critical exponent. No exact window-variance floor
  was returned. This is not an exhaustive novelty claim.

## Log

- 2026-10-01: Source correction tested; paper obstruction and positive
  survivor derived. Next step: verify the compact logarithmic tent against
  the existing weighted-source boundary theorem and prove its exact Mertens
  window bridge. RH and witness half-mass positivity remain open.
- 2026-10-01: A scratch Lean check accepted the logarithmic base Mellin pair,
  general-q compact tent Mellin pair, nonvanishing in Re(s)>0 and
  measurability. Active draft:
  `pm-mertens-window-variance-floor/pending-lean/PMMertensLogTent.lean`.
  It contains no variance-floor theorem yet. Next prove the pointwise
  boundedness/support and exact window/source identity, then use the existing
  critical bounded-weight obstruction. Do not wire or label this partial
  draft as a finished module. One early scratch check briefly overlapped an
  API check; it was terminated by its owned process IDs, joined with exit
  143, and subsequent checks were sequential.
- 2026-10-01: Final direct check of the saved draft passed with exit 0 and
  no diagnostics using `lake env lean` on its absolute path. This verifies
  only the draft's Mellin/measurability ingredients. The variance floor,
  source-correction obstruction, axiom audit and umbrella integration are
  not complete. Search outputs and completed API scratch were removed;
  no owned build remains running.

### Canonical weighted form of the positive survivor

2026-10-01 continuation. The tent support, boundedness by log(q), and
unconditional cofinal critical floor of its actual Möbius source now pass
the draft Lean check. The next bridge uses Abel summation directly:
`L(y)=sum_(n<=y) mu(n)*log(y/n)=integral_1^y M(u)/u du`, so

`S_v(1/(q^2*x)) = L(q^2*x)-2*L(q*x)+L(x)
 = integral_(q*x)^(q^2*x) M(u)/u du - integral_x^(q*x) M(u)/u du`.

This avoids proving a second Mellin-continuation theorem. It also yields
the positive survivor directly in the canonical measure: for some c>0,
cofinally many x satisfy, simultaneously for every scalar a,

`c <= integral_x^(q^2*x) (M(u)-a)^2/u^2 du`.

Indeed the two integrals of a/u cancel exactly (both equal a*log(q)).
Cauchy--Schwarz bounds the square of their signed difference by
`(q^2-1)*x` times this energy. The source critical floor bounds that same
square below by a fixed positive multiple of q^2*x. Thus scalar centering
cannot erase the energy. Taking q=sqrt(2) gives the first omitted PM
interval. This weighted all-centers form implies the card's unweighted
intrinsic-variance floor by choosing its minimizing mean and comparing
the interval weights.

To transfer cofinal real x to integer cutoffs, use the same Abel formula:
`|M(u)|<=u` makes L Lipschitz on [1,infinity), hence its three-scale
combination has Lipschitz constant at most `q^2+2*q+1`. Rounding x changes
the signed readout by a bounded amount, which cannot erase a square-root
cofinal floor. This avoids pointwise estimates from small L2 variance.
These bridge/energy/rounding steps are paper proofs awaiting Lean checks.

2026-10-01 continuation: the complete logarithmic-tent leaf now passed a
direct `lake env lean` check, including the real-window floor, Lipschitz
rounding transfer, integer-window floor and its dyadic specialization.
Promoted to `formal/GaloisForLFunctions/RHTower/PMMertensLogTent.lean` and
wired into the RHTower umbrella. Targeted `--old` build, final real-path
audit and axiom audit are in progress. Exact main statement:

`exists C>0, forall N0, exists N>=max(1,N0), forall c:Real,
 C <= integral_(N,2*N] ((M(floor(t))-c)/t)^2 dt`.

This is the positive survivor for scalar centering. It is not RH or witness
half-mass positivity. The corrected raw source's exact first-window formula
and transfer to its canonical Fermi norm still need a separate audited leaf.

Search60 was partial at semantic retrieval (runtime deadline); its coverage
snapshot was older, with mostly pending/stale compiler metadata. Candidate
statements, source arguments and ingredient groups were inspected. The
useful exact input is `FermiNymanFiniteCoefficientError`: arbitrary finite
real coefficients already have full-half-line square integrability and
coercivity in the literal Fermi norm. Reuse that theorem for the last-scale
correction; do not rebuild the analytic coercivity layer.

Completed audit of `PMMertensLogTent.lean`: targeted `lake --old build`
passed; final `lake env lean GaloisForLFunctions/RHTower/PMMertensLogTent.lean`
passed with no diagnostics. All 35 exported declarations were checked
through `/tmp/pm_window_audit.lean`; their only transitive axioms are
`propext`, `Classical.choice`, and `Quot.sound`. The umbrella import is
present. Global `scripts/formal_tools.py lint` exited 1 for 11 unrelated
unwired RHTower leaves (CCM aperture/exponential-ramp leaves, two mollified
Möbius leaves, retained-prime boundary, moving-shell phase, and zero-density
power saving). No clean repository-wide lint result is claimed.

The exact source-correction bridge is now a complete candidate in
`pm-mertens-window-variance-floor/pending-lean/PMCorrectedMobiusWindow.lean`,
including its final non-convergence theorem. It is being checked and is
not yet a finished formal module or an audited no-go.

### Exact corrected-source bridge (now formalized)

Use finite real coefficients
`c_N(d)=mu(d)-1_(d=N)*N*h_N`. The existing
`finiteNymanError N c_N` is precisely the full auxiliary corrected error;
`integral_normSq_finiteNymanError_le_six` supplies its canonical coercivity.

For `N<=x<2*N`, split the full finite floor inversion at N. Each omitted
term has `N<d<=floor(x)`, hence `floor(x/d)=1`; its sum is
`M(floor(x))-M(N)`. Also `floor(x/N)=1`. This gives the exact corrected
identity `E_N(x^-1)=M(floor(x))-M(N)+N*h_N`.

Use `integral_comp_rpow_Ioi` and
`integrableOn_Ioi_comp_rpow_iff` with exponent -1 to retain the full
positive-half-line norm under reciprocal substitution. The dyadic window
energy with center `M(N)-N*h_N` is then bounded by the full auxiliary
energy, which is at most six times the canonical Fermi error. Endpoints
are removed using `integral_Ioc_eq_integral_Ioo`, so the strict upper
endpoint in the floor identity loses no mass. No asymptotic exchange or
new integrability premise is required.

Final closure, 2026-10-01: both finished leaves passed their final direct
real-file audits and targeted `--old` builds. The second leaf's 12 exported
declarations also passed the /tmp axiom audit with exactly the three
standard axioms; together the two leaves expose 47 audited declarations.
The final global lint run still reports 11 unrelated unwired leaves.
The old pending-Lean directory is obsolete; both sources now live in the
formal tree. This construction is retired, with its positive survivor
formalized. The main RH goal remains active and unproved.

Search59 completed retrieval without runtime errors; coverage snapshot
was older and compiler status mostly pending/stale. All candidate/source
arguments and ingredients were checked. Its logarithmic Mertens upper
bounds do not settle this critical little-o endpoint. The additionally
inspected `EulerDeletionFirstTailExponentLaw` concerns a fixed-start
increment energy away from its exponent boundary; it supplies neither
the critical cofinal floor nor invariance under arbitrary scalar centering.
