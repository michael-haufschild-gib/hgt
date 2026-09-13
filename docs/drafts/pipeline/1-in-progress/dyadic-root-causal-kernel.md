# Dyadic roots from the pole-cleared causal kernel

- **Stage:** 1-in-progress
- **Type:** CANDIDATE; cell remainder and initial-region arithmetic transform formalized; critical full-source estimate open
- **Target:** Construct actual global analytic dyadic roots, not a new multiplicity receiver.

## Construction and exact arithmetic source

Write `b(n)=zetaBinomialHalf(n)`, regarded as real. The inspected corpus proves
`0<=b(n)<=1`, `b(1)=1`, and Dirichlet convolution `b*b=1`:
`SquarefreeConvolutionHalfSelbergDelangeFactorization.lean:119–232`.
For positive `u`, put

\[
k(u)=\frac{e^u}{\sqrt{\pi u}},\qquad
r(u)=k(u)-\int_0^u k(v)\,dv,\qquad
g(u)=\sum_{1\le n<e^u}b(n)r(u-\log n).
\]

Extend kernels by zero to negative arguments; endpoint values do not affect integrals.
Every bounded interval has only finitely many arithmetic atoms. The singularities
are of order `u^(-1/2)`, hence locally integrable. On `Re(s)>1`, absolute convergence
justifies every sum/integral interchange and gives

\[
\mathcal Lr(s)=\frac{\sqrt{s-1}}s,\qquad
\mathcal Lg(s)=\frac{\sqrt{s-1}}s\sum_{n\ge1}\frac{b(n)}{n^s},\qquad
(\mathcal Lg(s))^2=\frac{(s-1)\zeta(s)}{s^2}.
\]

Here the square root is the Euler-side branch. This formula is not yet continuation
to `Re(s)>1/2`. The required new estimate is
`integral_0^infinity exp(-sigma*u)*abs(g(u)) du < infinity` for every `sigma>1/2`.
This would construct the first root of the pole unit; higher dyadic levels remain separate work.

## Direct attack: convolution-square growth

The beta integral gives `k*k=e^u`. On each finite triangle all products are absolutely
integrable: the worst endpoint product is `v^(-1/2)*(u-v)^(-1/2)`.
Consequently causal convolution associativity and primitive interchange give

\[
r*r=e^u-2\int_0^u e^v\,dv+\int_0^u(u-v)e^v\,dv=1-u.
\]

Yet
\[
r'(u)=-\frac{e^u}{2\sqrt\pi\,u^{3/2}}.
\]
For `u>=1`, integration and `v^(-3/2)>=u^(-3/2)` on `[1,u]` give

\[
r(u)\le r(1)-\frac{e^u-e}{2\sqrt\pi\,u^{3/2}}.
\]

Thus for every `0<=sigma<1`, `exp(-sigma*u)*r(u)->-infinity`.
In particular weighted absolute integrability fails for the elementary kernel at
these exponents, despite its polynomial convolution square. This falsifies the
unqualified square-growth bootstrap, not the full arithmetic construction.

## Positive survivor: retain the whole arithmetic cancellation

The exact finite convolution identity is

\[
(g*g)(u)=\sum_{1\le n<e^u}(1-u+\log n)
=\lfloor e^u\rfloor-\int_0^u\lfloor e^v\rfloor\,dv
=1-\{e^u\}+\int_0^u\{e^v\}\,dv
\]

away from atom endpoints (and almost everywhere). Each equality follows from the
finite source sum, `b*b=1`, and integrating the indicator `log(n)<v`.
The final expression lies in `[0,1+u]`. Its nonnegativity is additional arithmetic
information absent from the elementary counterexample; it must not be discarded
when judging whether a stronger growth argument can work.

At each positive integer `N`,
`sqrt(u-log(N))*g(u) -> b(N)/sqrt(pi)` from the right. Indeed all older terms remain
continuous, the newly born term has this limit, and the next atom is separated.
Hence global pointwise bounds cannot hold across nonzero atoms. Weighted `L1`, or a
justified smoothing with the same Laplace branch, is the relevant norm.

## Unresolved estimate and scope

### Sharper direct attack: the atomic half-power boundary

The regular part `r(u)-1/sqrt(pi*u)` is strictly decreasing for `u>0`, since its
derivative is `-(exp(u)-1)/(2*sqrt(pi)*u^(3/2))`. Fix an arithmetic cell
`u=log(N)+x`, `0<x<d=log(1+1/N)`. Every older term is decreasing. Consequently
`g(log(N)+x)-b(N)/sqrt(pi*x)` is decreasing on this cell.

For any integrable `f(x)=c/sqrt(x)+h(x)` on `(0,d)` with `c>=0` and decreasing `h`,
reflection about `d/2` gives, for `0<x<d/2`,
`abs(f(x))+abs(f(d-x)) >= f(x)-f(d-x) >= c*(1/sqrt(x)-1/sqrt(d-x))`.
Integration yields the sharp lower bound

\[
\int_0^d |f(x)|\,dx\ge 2(\sqrt2-1)c\sqrt d.
\]

The constant is attained by `h(x)=-c*sqrt(2/d)`, so this is not a sign or size
assumption on the unknown background. In particular each actual arithmetic cell
has absolute mass at least `2*(sqrt(2)-1)*b(N)*sqrt(d/pi)`.
For `N>=1`, `d>=1/(2*N)`. At a prime, `b(N)=1/2`; disjoint prime cells therefore
force `integral exp(-u/2)*abs(g(u)) du = infinity`, by divergence of the prime
harmonic sum. The same holds for smaller nonnegative exponents. This is a
paper-level lower boundary, not the desired upper estimate for exponents above `1/2`.
The finite-cell inequality and arithmetic instantiation are now checked in Lean:
`GaloisForLFunctions.HTGeometry.halfSingular_absolute_mass_lower` and
`RHTower.zetaPoleHalfCausalSource_cell_absolute_mass_lower`.
The concrete prime corollary is `zetaPoleHalfCausalSource_prime_cell_mass_lower`.
Lean's kernel omits `1/sqrt(pi)`: it is `sqrt(pi)*r`, and its full arithmetic source
is `sqrt(pi)*g`. The prime bound is therefore `sqrt(d)/4` before normalization.
The global weighted-divergence deduction above remains paper-level.

The termwise absolute bound cannot cross `Re(s)=1`: even the `n=1` term fails there.
The full sum may still cancel that growth. Neither `b*b=1`, nonnegativity of `g*g`,
nor the displayed small source bound has yet yielded the required weighted `L1`
estimate for `g`. No root on the remaining critical half-plane has been constructed.
No route is retired, and no Route-T producer is assumed or pursued.

## Cell-baseline upper-bound attack

Use the unnormalized Lean kernel `R=sqrt(pi)*r` and write `q(t)=t^(-1/2)`.
For `0<a<=t<=b`, derivative comparison gives
`0<=R(t)-R(b)<=exp(b)*(q(a)-q(b))`: the function `R(t)-exp(b)*q(t)` is
nondecreasing on `(0,b]`. For `0<d<=1`, direct integration gives
`integral_0^d abs(R)<=6*exp(d)*sqrt(d)`.

Set `d_N=log(N+1)-log(N)` and retain the exact old-atom baseline
`C_N=sum_(1<=n<N) b(n)*R(log(N+1)-log(n))`. On the `N`th cell write the full source
as `G(log(N)+x)=C_N+E_N(x)`. The proposed bound, with no sign assumption on `C_N`, is

\[
\int_0^{d_N}|E_N(x)|\,dx\le12b(N)\sqrt{d_N}
+2\sum_{1\le n<N}\frac{b(n)}n
 \left(q(\log(N/n))-q(\log((N+1)/n))\right).
\]

Derivation: separate the newest atom and apply the preceding kernel comparison to
each older atom. Use `exp(d_N)<=2` and `d_N*(N+1)<=2`; all old-atom differences are
nonnegative. For `sigma>1/2`, weight by `N^(-sigma)` and interchange nonnegative
finite sums before passing to the limit. For each fixed `n`, the old differences
telescope from `N=n+1` to infinity, and `N^(-sigma)<=n^(-sigma)`. Their sum is bounded
by `q(log(1+1/n))<=sqrt(n+1)<=sqrt(2*n)`. The newest atom uses
`sqrt(d_N)<=1/sqrt(N)`. Thus the full remainder has weighted absolute mass at most
`(12+2*sqrt(2))*sum b(n)*n^(-sigma-1/2)`, which is finite using `b(n)<=1`.

The complete scratch now verifies the finite-prefix bound
`sum_(1<=N<M) N^(-sigma)*integral_cell abs(G-C_N)
 <=16*sum_(1<=N<M) b(N)*N^(-sigma-1/2)` for every `sigma>=0`.
It also verifies summability for every `sigma>1/2`, with total at most
`16*sum_(N>=1) N^(-sigma-1/2)` (the Lean sequence has zero term at `N=0`). These are unconditional theorems about the literal
source; neither analyticity nor a root family is assumed. The passage from the
weighted cell sums to the single half-line Lebesgue integral remains paper-level.

This is not a bound for `G`. It retains `C_N` exactly. The remaining coarse contribution has weighted mass
comparable to `sum abs(C_N)*N^(-sigma-1)`; that arithmetic bound is unproved.
Replacing `C_N` by the actual cell average changes the remainder bound by at most a
factor two, but does not control the average. The convolution-square identity must
still be applied to the complete source, including both mixed terms and the baseline.

### Convolution-growth bootstrap: complete counterexample

The [full source construction](../5-failed/positive-convolution-square-growth-bootstrap.md)
now passes Lean scratch. There is an explicit real causal `g` with
`g*g=exp(-t)*t*((1-t)^2+t^2/3)` almost everywhere on the positive ray.
The square is strictly positive there, integrable, and tends to zero. Nevertheless,
`exp(-3*t/4)*g` is not integrable, whereas `exp(-2*t)*g` is integrable.
Thus positivity and decay of the full convolution square do not provide the missing
source-growth bound, even when a real source and its square identity are supplied.
The actual arithmetic producer is not retired: its coefficients and cell structure
are additional information absent from this counterexample.

The earlier target-only test `exp(-t)*(1-2*t)^2` also passed Lean scratch, including
its transform, simple zero, and analytic-square-root obstruction. The stronger
source-level result supersedes it; no separate production module was added for it.

### Positive survivor: exact kernel transform connection

`CausalGammaHalfLaplace` proves the normalized positive-rate Gamma integral and the
filter `R_w=B_w-(3-w)*(A*B_w)`, with `A(t)=exp(-3*t)` on the positive ray.
Its Laplace square is `(s+w)/(s+3)^2` for `Re(s)>=0`, `Re(w)>0`.
At `w=2`, a separate scratch proof identifies this exact filter with
`exp(-3*t)*poleClearedHalfKernel(t)/Gamma(1/2)` on the positive ray.
The identification retains the complete primitive subtraction and gives integrability
and the square-transform formula for the already defined kernel.

### Full arithmetic transform and absolute-integration boundary

Write `D(t)=exp(-3*t)*R(t)/Gamma(1/2)` on the positive ray, with zero extension,
and `H(t)=exp(-3*t)*G(t)/Gamma(1/2)`. The production module verifies, for every real `t`,

\[
H(t)=\sum_{n\ge1}\frac{b(n)}{n^3}D(t-\log n).
\]

This is the existing floor-cutoff source, not a replacement. Terms beyond the cutoff
vanish by causality. At `t=log(n)`, the Lean kernel has value `R(0)=0`, so the strict
causal indicator and inclusive floor cutoff agree exactly, not only almost everywhere.
Translation preserves the integral of the norm of each atom. Summability of the
Dirichlet term norms at `3` therefore proves `H` integrable on the whole real line.

For every complex `s` with `Re(s)>=0`, the weighted atom identity retains the coefficient
`LSeries.term b (s+3) n`. Its exact integral-of-norm formula justifies the infinite
sum/integral exchange and gives

\[
\mathcal LH(s)=B(s+3)\mathcal LD(s),\qquad
(\mathcal LH(s))^2=\zeta(s+3)\frac{s+2}{(s+3)^2}.
\]

The complete source's transform is analytic on `Re(s)>0`, proved from its admitted
Bochner integral. Thus this construction is checked at original `Re(z)>=3`, with
analyticity for `Re(z)>3`. It does not extend the previously known root region.

The literal coefficient identity also proves the sharp statement
`LSeriesSummable zetaBinomialHalf z iff 1<Re(z)`: convergence of the half implies
convergence of its Dirichlet convolution square, which is zeta. No assumed zero
location or prime asymptotic enters this implication. For the original atom family,
integrability of every weighted atom **and** summability of their integral norms force
`1<Re(s+3)`. The proof checks that the weighted kernel has strictly positive norm
integral when integrable; it does not mistake the default integral of a nonintegrable
function for zero mass. The closed instance at original `z=2/3` rules out this
termwise absolute-integration package.

The positive survivor is the exact full-source transform and its admitted analytic
initial region. The rejected step is taking absolute values atom by atom to cross
`Re(z)=1`, not the causal-source route. The hard growth target remains
`sum abs(C_N)*N^(-sigma-1)<infinity` for every `sigma>1/2`. Subsequent estimates must
retain cancellation in the summed source. The physical full convolution identity
with the literal floor forcing, and a signed baseline estimate from that arithmetic,
remain to be checked; generic positivity cannot supply the latter.

## Source audit

- Deep/method searches for delayed arithmetic integration, divisor-convolution
  cancellation, weighted finite swaps, and signed baselines used inventories of
  57,458--57,461 files with no pending source inventory. Two requests returned partial
  method results; the final signed-baseline request was complete. Retrieved identities
  did not provide a checked baseline bound. Exact source reads supplied the applicable
  Bochner sum theorem and `ArithmeticFunction.LSeriesSummable_mul`.
- Broad newest-first arXiv search `coercivity`: Xinye Li,
  [Existence and strong-field asymptotics of skyrmions in a fourth-order model of
  frustrated ferromagnets](https://arxiv.org/html/2609.08255v1), 8 September 2026,
  Lemmas 2.4--2.5 and Proposition 3.1 inspected. The residual-energy lower bound uses
  a sphere-valued map and nonzero degree, forcing surjectivity. Neither an arithmetic
  realization of those hypotheses nor a baseline upper bound was obtained.
- Broad newest-first arXiv search `renewal`: Liu--Lu--Shi,
  [Polynomial mixing for the 3D damped cubic nonlinear Schrödinger equation with
  degenerate noise](https://arxiv.org/html/2609.08645v1), 8 September 2026,
  introduction, Assumptions 3.1--3.4 and Theorem 3.6 inspected. Its contraction mechanism
  requires a stable--compact decomposition, Gaussian forcing with dense Malliavin
  range, Lyapunov control and irreducible resets. None of those hypotheses has been
  established for the arithmetic baseline; stochastic mixing is not a deterministic
  bound on this source. Neither paper is used as a Lean premise.

- Deep/method query `arithmetic summatory half convolution cancellation old atom baseline`
  completed at inventory generation `891928`, with compiler coverage incomplete.
  It returned Abel summation and convolution identities, not a baseline estimate.
  The generated Mellin-to-arithmetic group was `not_verified`; its unrelated Hawking
  time identity supplies no arithmetic transfer and is not used.
- Direct inspection of `SquarefreeConvolutionHalfSelbergDelange.lean:312` found that
  `exists_zetaBinomialHalf_summatory_bound` assumes `ZetaBinomialHalfKatoInversion`.
  It is not an unconditional source for the required bound.
- Broad single-word arXiv search `renewal`, sorted by newest announcement, found Ding,
  Tran, Vicente, [Non-monotone direct-search methods for deterministic and stochastic
  derivative-free optimization](https://arxiv.org/html/2609.11567v1), 10 September 2026.
  Section 2 corrects stored values by ordered step-size penalties, but its decrease
  law depends on an algorithmic acceptance inequality. No corresponding inequality
  has been proved for the arithmetic baseline. No paper is used as a Lean premise.

- Local deep/method searches for nonnegative telescoping and triangular sums found
  `sum_Ico_telescope`, `Finset.sum_range_sub`, and `Finset.sum_Ico_Ico_comm'`.
  The hybrid method search completed against inventory generation `891538`; compiler
  coverage remained incomplete. Candidate application is checked in the cell scratch.
- A separate hyperbola/convolution deep search returned von-Mangoldt and generic
  convolution ingredients, not a checked estimate for the retained zeta-half baseline.
- Krstic, *Approximate Feedback Linearization for a Nonlinear Hyperbolic PDE Class —
  Part I: Volterra Truncation*, 5 July 2026, [Assumption 1, Proposition 1, Theorem 1](https://arxiv.org/html/2607.04361v1):
  the stability proof assumes kernel growth and a small ball with contraction constant
  below one. No such contraction has been established for this arithmetic source;
  the paper is not a proof premise.

- Local deep search: `fractional convolution Gamma semigroup causal primitive square Laplace`.
  Found causal Laplace convolution and beta-integral tools, not the missing arithmetic bound.
- Local method/source search: `integral rpow one sub rpow`, hybrid, all retrieval views.
  Located `HTGeometry.TanhSubstitution.integral_rpow_mul_one_sub_rpow:150`.
  An attempted `--retrieval-views method` was rejected; the supported mode is `all`.
  Search results are discovery evidence, not compiler certification.
- `RHTower.ZetaFractLaplace.integral_Ioi_zero_fract_exp:43` is the existing exact
  fractional-part Laplace identity on `Re(s)>0`, away from `s=1`.
- Broad recent searches: renewal, fractional, semigroup, subordination, deconvolution.
  Fricain–Hartmann–Ross–Timotin, [Littlewood subordination for de Branges–Rovnyak
  spaces](https://arxiv.org/html/2609.10115v1), 9 September 2026, Theorems 1.4–1.5,
  transfer already analytic disk functions by composition; they do not construct a
  fractional root of a prescribed function.
- Kovács–Sikolya, [Benjamini–Schramm limit of the heat semigroup on quantum
  graphs](https://arxiv.org/abs/2607.16489), 17 July 2026: abstract checked. Its graph
  semigroup double-limit theorem supplies no identified bound for this arithmetic kernel.
- Barzykin, [Hawkes-Driven OTC Market Making: Volterra–Riccati
  Approximation](https://arxiv.org/html/2608.02002v2), 25 August 2026: introduction and
  stated scope checked. The proposed Riccati hierarchy is approximate; no exact root-growth
  theorem was obtained from it. None of these papers is a Lean proof premise.

## Verification

### Full arithmetic source

- `ZetaPoleHalfArithmeticLaplace.lean`: 18 public theorems; complete scratch passed
  with default heartbeats, including whole-line integrability, exact transform,
  initial-region analyticity, coefficient convergence classification, and the closed
  absolute-interchange obstruction at `2/3`.
- Final scratch profiling reported 1.03 seconds of tactic execution and 1.45 seconds of
  typeclass inference. Cast rewrites and translated integrals use explicit identities;
  no heartbeat limit or proof admission was introduced. Profiling is scratch-only.
- The production leaf is wired into the RH umbrella. Its targeted build passed.
  Replacing the fractional-pole module dependency with the direct Dirichlet convolution
  proof reduced the target's dependency job count from 9,586 to 9,513; the optimized
  leaf built in 110 seconds. Other dependency messages were cached replays, not a
  request to build an umbrella. The production axiom audit checks all 18 public
  theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Scratch checks, targeted builds and the final axiom check ran one owned Lean
  process at a time; every next launch required a terminal previous handle. No
  full build, umbrella build, added axiom, admission, heartbeat increase, `#eval`,
  or numerical experiment was used.
- The lint run reported unrelated unreachable modules
  `RHTower.Sieve.KloostermanGlobalCollisionCoprime`,
  `RHTower.ThetaCuspHawkingBMIngoingFullCurrent`, and
  `RHTower.ThetaCuspHawkingBMLeftHorizonFactor`, plus existing large-file warnings.
  No unrelated module was changed. The formal API, gaps and overview indexes were
  regenerated; source indexing refreshed three changed files.

### Complete convolution-growth test and kernel transform

- Three production leaves: `HTGeometry/CausalGammaHalfLaplace.lean` (16 public
  theorems), `HTGeometry/PositiveConvolutionSquareGrowth.lean` (33), and
  `HTGeometry/GammaHalfPoleClearing.lean` (6). All three targeted builds passed.
- Complete Gamma-source scratch and kernel-identification scratch passed
  `lake env lean`; all three leaves are wired into the HTGeometry umbrella.
- `lake env lean /tmp/dyadic-positive-laplace.JLS3Bp/Axioms.lean` audited every one
  of the 55 public theorems: only `propext`, `Classical.choice`, and `Quot.sound`.
- Default heartbeats throughout; no `native_decide`, `#eval`, or numerical experiments.
  One transient overlap of two owned scratch checks occurred when a running poll was
  misread. Both exited; later launches required a confirmed terminal handle.
- Final owned-process inspection found no live Lean checks, targeted builds, or searches.
  `scripts/formal_tools.py index` completed and regenerated the three formal indexes.
- Final lint still reports unrelated unreachable RH modules
  `RHTower.Sieve.KloostermanGlobalCollisionCoprime` and
  `RHTower.ThetaCuspHawkingBMOriginalHorizonRegularity`, plus existing large-file warnings.
  No unrelated module or umbrella entry was repaired here. No full or umbrella build.
- These results supply no bound for the actual arithmetic baseline and no new global
  root domain. The later full arithmetic identification is recorded above.

### Weighted cell remainder

- New production leaves: `HTGeometry/PoleHalfKernelCellOscillation.lean` (7 public
  theorems) and `RHTower/ZetaPoleHalfCellRemainder.lean` (17 public theorems).
- Complete `/tmp/dyadic-cell-upper.nZymVG/Combined.lean`: `lake env lean` passed.
- Both targeted leaf builds passed, with default heartbeats; both umbrellas are wired.
- `lake env lean /tmp/dyadic-cell-upper.nZymVG/Axioms.lean`: all 24 public theorems
  depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Repository lint still reports the pre-existing unrelated missing umbrella import
  `RHTower.Sieve.KloostermanGlobalCollisionCoprime`, plus large-file warnings.
- The single half-line weighted-integral passage, full baseline estimate, transform
  identities, and global analytic root construction are not certified by these modules.

### Earlier kernel calculus and cell lower bounds

- `/tmp/dyadic-causal-root.MEsXRR/Combined.lean`: complete 19-theorem scratch proof passed.
- `/tmp/dyadic-causal-root.MEsXRR/Generic.lean`: isolated narrow-import kernel proof passed.
- `lake env lean GaloisForLFunctions/RHTower/ZetaPoleHalfCausalSource.lean`: passed.
- Targeted build of `GaloisForLFunctions.HTGeometry.PoleClearedHalfKernel`: passed.
- Targeted build of `GaloisForLFunctions.RHTower.ZetaPoleHalfCausalSource`: passed.
- `lake env lean /tmp/dyadic-causal-root.MEsXRR/Axioms.lean`: all 19 public theorems
  depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- Two new modules are imported by their respective umbrellas; no umbrella build run.
- No added heartbeat/recursion options, computations, axioms, or admitted proofs.
- The Laplace identities, convolution-square identity, near-atom limit, optimality of
  the reflected-cell constant, and global critical-weight divergence remain paper-level.
  The kernel calculus, comparison upper bound, reflected integral inequality, actual
  source/prefix equality, and all-cell/prime-cell lower bounds are the formalized portion.
- Scratch audit directory: `/tmp/dyadic-causal-root.MEsXRR`.
- `scripts/formal_tools.py lint`: exit 1, one unrelated unreachable module:
  `GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime`.
  Existing large-file warnings remain. Both new modules are umbrella-wired.
- All owned search, scratch, build and axiom-audit handles terminated; process inspection
  found no remaining owned Lean process. No full builds or umbrella builds were run.
