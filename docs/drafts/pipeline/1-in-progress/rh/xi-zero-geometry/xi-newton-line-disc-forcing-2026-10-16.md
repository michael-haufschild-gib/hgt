# Xi Newton geometry: forcing line-centered invariant discs

Status: LIVE — source forcing unresolved.
Receiver: `RHTower.XiNewtonCriticalLine.riemannHypothesis_iff_newton_invariant_critical_discs`.
Source module: `formal/GaloisForLFunctions/RHTower/XiNewtonSchwarzPickCriticalLine.lean`.

## Objective and constraints

Derive the receiver's disc coverage for the actual completed Xi function without assuming RH,
zero localization, positivity, or another unproved source property. Corpus-only research;
no external search, novelty audit, numerical experiments, or assumed analytic inputs.
Finished results must have complete paper proofs and individual Lean audits.

## Verified source frontier

The receiver already proves:

- A holomorphic Newton self-map of a disc contains at most one zero of a nonzero entire function.
- Reflection across the critical line transports Newton orbits and zeros.
- Every isolated zero has a small invariant disc centered at that zero, including multiple zeros.
- RH is equivalent both to covering every Xi zero by a line-centered invariant disc and to
  every immediate Xi Newton basin meeting the critical line.
- An immediate basin of a zero right of the critical line stays in that half-plane.

Thus local attraction alone supplies no line-centered coverage. The missing result must force
global incidence with the line or prohibit an off-line attracting component using actual Xi data.

## Active plan

1. Search the whole Lean corpus for Newton geometry, Xi derivative control, horizontal source
   identities, zero-free continuation, and mechanisms that force incidence.
2. State exact competing conjectures and attack them against those results.
3. Extract positive structural content from each obstruction; finish its paper proof before Lean.
4. Audit new modules with `lake env lean`, build only required imports with `--old`, wire finished
   modules into RHTower, run formal lint, remove owned scratch artifacts.
5. Continue from each success or failure toward actual Xi disc coverage.

## Cycle 1: local-to-global disc enlargement

Candidate: the invariant disc supplied at an arbitrary Xi zero can be enlarged or moved until its
center reaches the critical line while preserving holomorphy and self-mapping.

Attack in progress: determine whether derivative poles, a second fixed point, or boundary escape
blocks this continuation, and identify the strongest quantitative positive theorem that survives.

Open core: an unconditional actual-Xi mechanism defeating the first obstruction to line incidence.

## Cycle 2: boundedness removes the separate holomorphy gate

Conjecture: for actual Xi, a Newton map bounded on an open neighborhood is automatically
holomorphic there. Consequently disc self-mapping alone supplies both receiver conditions.

Verdict: BRIDGE; complete paper argument below, formalization in progress. This does not prove
disc coverage or claim scientific novelty outside the corpus.

Write `A = xi'` and `N(z) = z - xi(z)/A(z)`. The derivative is not locally identically zero:
the identity theorem would force `A = 0` globally, contradicting the corpus's strict positivity
of `Re(xi'/xi)` at `s = 1`. Thus `A` is nonzero on a punctured neighborhood of each point.
If `N` is locally bounded near `p` and `A(p)=0`, the identity
`xi(z) = (z-N(z)) A(z)` on that punctured neighborhood and continuity give `xi(p)=0`.
At a zero of Xi, the existing isolated-zero factorization gives a holomorphic Newton extension
with value `p`, agreeing with the totalized quotient. At points with `A(p) != 0`, quotient
holomorphy applies directly. These cases exhaust every point.

Define the denominator-free source margin

`Q(c,r,z) = r^2 |xi'(z)|^2 - |(z-c) xi'(z) - xi(z)|^2`.

Where `xi'(z) != 0`, this equals
`|xi'(z)|^2 (r^2 - |N(z)-c|^2)`. At a nonroot critical point it equals
`-|xi(z)|^2 < 0`. At a Xi zero the Newton map fixes `z`. Therefore, on the open disc,

`N(D) subset D` iff every `z in D` satisfies `xi(z)=0 or Q(c,r,z)>0`.

The forward implication uses automatic holomorphy to rule out nonroot critical points;
the reverse implication obtains `xi'(z) != 0` from positive margin whenever `xi(z) != 0`.
This replaces the receiver's two analytic conditions by one explicit source inequality.

Next conjecture: derive this margin on line-centered discs covering all Xi zeros from the actual
source. Attack must distinguish radial Newton control from horizontal log-derivative positivity:
the latter alone supplies neither a radius nor a no-overshoot bound.

## Cycle 3: weak interior margins and the boundary-only trap

Positive survivor: on a disc containing a Xi zero, `Q >= 0` throughout the interior already gives
strict Newton self-mapping. At a point with `xi'=0`, nonnegative Q forces `xi=0`. Else dividing by
`|xi'|^2` puts the Newton image in the closed disc. The holomorphic extension therefore maps the
open disc into the closed disc. An interior image on the boundary would make `N-c` constant by
the maximum modulus principle. Evaluating at the contained Xi zero contradicts its strict interior
location. Thus every image is strictly interior. Paper proof closed; Lean verification pending.

Rejected shortcut: check Q only on the boundary circle. For the exact symmetric polynomial
`f(c+w)=w^2-a^2`, where `c` is on the critical line and `0<a<r`,

`Q(c,r,c+w)=4r^2 |w|^2-|w^2+a^2|^2`.

On `|w|=r`, the triangle inequality gives
`Q >= 4r^4-(r^2+a^2)^2 = (r^2-a^2)(3r^2+a^2)>0`.
At the center, `Q=-a^4<0`; Newton has a genuine pole. Hence even strictly positive boundary
margin does not imply an invariant disc. This is an exact algebraic counterexample, not a
numerical experiment. The useful survivor is the interior critical-value obstruction, not retirement
of the Newton route.

The same family shows why one fixed invariant disc cannot be continued through root splitting:
at `a=0` Newton is `c+w/2`; every nonzero arbitrarily small `a` creates a central pole. A source
continuation proof must control splitting into distinct discs as well as their boundary margins.

## Cycle 4: compact source gate and pole exclusion

The margin Q is continuous on the whole plane. For positive radius, its nonnegativity on the
open disc extends to the closed disc. Conversely the closed-disc condition restricts to the
interior. Together with cycle 3, this gives the same RH receiver using one compact-disc inequality.

At any `p` with `xi'(p)=0` and `xi(p)!=0`, `Q(c,r,p)=-|xi(p)|^2<0` for every center and radius.
Every certified disc therefore keeps all such critical points strictly outside its closure.
In particular, the corpus proves `xi'(1/2)=0` and `xi(1/2)!=0`; hence no invariant disc can contain
`1/2` even on its boundary. The totalized formula fixes `1/2`, but that fixed point is unbounded
in every neighborhood and cannot be used as a root or a holomorphic anchor.

Paper proof is dependency-closed. Formalization:
`formal/GaloisForLFunctions/RHTower/XiNewtonCriticalPoleExclusion.lean` (audit pending).

Current hard conjecture: the actual Xi first-jet source produces a family of line-centered compact
discs covering its zero divisor on which Q is nonnegative. A proof must produce those discs and
their interior margin; neither boundary-only positivity nor a locally bounded limit may be assumed.

## Audit record

`formal/GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean` passed
`lake --old env lean -j 1 GaloisForLFunctions/RHTower/XiNewtonDiscSourceMargin.lean`
with exit 0 and no warnings. It proves automatic holomorphy, exact strict and weak source-margin
criteria, and the unconditional equivalence `riemannHypothesis_iff_xi_newton_nonnegative_margin`.
These are proved reductions, not a proof of the source margin or of RH.

Receiver source read in full and individually audited with exit 0.
Search inventory reports broad Lean coverage but many source-only declarations; candidate
applicability must be checked by direct Lean audit.

### Cycle 4 verification

`XiNewtonCriticalPoleExclusion.lean` passed individual foreground audit:
`lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/XiNewtonCriticalPoleExclusion.olean GaloisForLFunctions/RHTower/XiNewtonCriticalPoleExclusion.lean` (exit 0, no warnings).
Both finished modules are wired into `RHTower.lean`; no umbrella build was run.
The source-margin module's twelve public theorems have also passed a scratch-file
`#print axioms` audit: only `propext`, `Classical.choice`, `Quot.sound`.

### Cycle 5 — curvature defect behind boundary failure

Conjecture: the source margin is superharmonic, so nonnegative boundary values
could force a nonnegative interior. **False: the sign is reversed.**

Dependency-closed paper calculation, for any holomorphic `f` and `w = z-c`:
put `A = w f' - f`. Then `A' = w f''`. Since
`Δ|g|² = 4|g'|²` for holomorphic `g`,

`Δ Q(c,r,z) = 4 (r² - |z-c|²) |f''(z)|²`.

Thus the margin is subharmonic inside its disc. Boundary positivity is an
upper-envelope statement; it leaves a positive interior curvature cost to pay.
This explains the earlier quadratic failure without relying on a numerical
example. The positive survivor is the exact curvature identity and a prospective
Green-function budget: interior margin equals the harmonic extension of boundary
margin minus the nonnegative Green potential of this curvature density.

**Next conjecture:** Xi's boundary margin dominates that curvature potential on
suitable line-centered discs covering its zeros. This must be derived from an
actual Xi source identity; it is not supplied by the maximum principle, the
known exterior log-derivative sign, or the conditional Laguerre window lemmas.
Curvature identity: paper proved, Lean audit pending. Green-budget identity:
proposed next target, not yet proved in Lean. Actual Xi budget: open.
