# Conjecture: trace-zero completed Suzuki modes are \(H^1_0\) at every finite-recurrence aperture

- **ID:** `suzuki-finite-recurrence-trace-zero-h1-conjecture`
- **Stage:** 1-in-progress
- **Type:** LITERAL COMPLETED-SOURCE CONJECTURE / INVALIDATED PROOF ARCHITECTURE
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Inputs:** `suzuki-completed-eigenmode-atomic-jump-boundedness.md`,
  `suzuki-weak-signed-half-log-trace.md`,
  `suzuki-tempered-orbit-carrier-aperture-recurrence-dichotomy.md`,
  `suzuki-paired-seam-carleman-logistic-normal-form.md`,
  `suzuki-interior-seam-indicial-dipole-exclusion.md`,
  `../3-formalized/new_scientific_knowledge/suzuki/suzuki-flat-flux-charge-automaticity.md`,
  `suzuki-paired-gamma-logistic-flat-sector-conjecture.md`,
  `suzuki-polar-remainder-lipschitz-gamma-subcriticality.md`
- **Current obstruction:** higher-rank source-selected finite-to-flat transfer

## 0. Retraction of premature theorem status

The statement below was prematurely placed in Stage 2. Sections 5--6 treated a coordinatewise
initial cutoff as harmless after differentiating prime transport. The exact cutoff equation
contains

```text
[M_chi,B_(a,w)]F'.
```

The cutoff-covariance classification proves that event-adapted cutoffs cannot commute with
connected valuation shifts when event times are unbounded. If they do not commute, this term has
no zero-order \(L^2\) bound; controlling it assumes derivative regularity being sought.

Therefore Sections 5--9 below remain a conjectural proof program, not a proof. The raw commutator
obstruction has since been resolved at the exact graph level:
`suzuki-coordinate-cutoff-primitive-flux-identity.md` rewrites it as a primitive source, and
`suzuki-primitive-flux-nonnormal-graph-reduction.md` removes the derivative of that primitive from
an augmented flux system. Valid components are now:

```text
weighted paired physical profiles;                       [PROVED]
exact prime intertwining before cutoff;                  [PROVED]
finite-recurrence zero-order event summability;          [PROVED]
paired local Gamma/logistic normal form;                 [PROVED]

differentiated primitive-flux graph after adapted cutoff;[PAPER-PROVED]
weighted uniqueness inside the flux graph;               [PAPER-PROVED]
flat solution has automatic zero charge and enters
  weighted value/flux;                                  [PAPER-PROVED]
complementary flux controls physical root derivative;    [PAPER-PROVED]
finite-recurrence trace-zero H1_0 theorem;               [CONJECTURE].        (0)
```

The live replacement is source-side:
`SUZUKI-LITERAL-PAIRED-ASSEMBLY-EXPANSION-AND-MIDDLE-COVERAGE`. Complementary primitive flux
propagates weighted control through the rough prime cutoff without differentiating it. The
physical one-sided dipole and terminal flat charge are now forced to zero. The literal
completed-source equation is now assembled with corrected rooted signs and a canonical
literal-support cutoff. Formalized dyadic orbit charts already cover compact middle. The
rough-primitive Hardy theorem closes analytic admission in rank zero/one on `2a<log 3`; higher
rank still needs finite-to-flat or source-selected cancellation.

## 1. Conjectured result

Fix an aperture \(a>0\) and its finite visible-prime set \(P_a\).  Let

```text
Gamma_a={sum_(p in P_a)nu_p log p:nu in Z^(P_a)}.
```

Define

```text
R(a)
 =limsup_(|nu|_1->infinity, ell(nu)!=2a)
   [-log|2a-ell(nu)|]_+/|nu|_1.                         (1)
```

Let \(u\) be a completed zero mode of Suzuki's restricted-Weil operator on
\(I=(-a,a)\), in the original eigenfunction variable, extended by zero to \(\mathbb R\).
Suppose

```text
R(a)<infinity,
beta_+(u)=beta_-(u)=0.                                  (2)
```

Conjecturally,

```text
u in H1_0(-a,a).                                        (3)
```

No conormality, finite seam orbit, self-adjoint weighted adjacency, or spatial derivative premise
is assumed.

The attempted proof constructs a paired physical-orbit equation. Every translated center uses
the same unit physical window, so arbitrarily close seam centers require no disjoint
localization.  Near-endpoint recurrences appear only as finite logarithmic-time boundary events.
The exponential valuation weight absorbs the complete family of those events exactly when
\(R(a)<\infty\).

Since \(R(a)=0\) for almost every aperture, a proof would establish `(3)` at almost every aperture.
Dense relative-Liouville apertures would remain outside the statement. The coordinate-cutoff
obstruction is already present at finite recurrence type and is now the first open core.

## 2. Literal orbit centers and paired profiles

Put

```text
G=Z^(P_a),
ell(nu)=sum_p nu_p log p,
w(nu)=exp(-kappa|nu|_1).                                (4)
```

Use the two endpoint cosets

```text
x_(+,nu)=a-ell(nu),
x_(-,nu)=-a+ell(nu).                                    (5)
```

Duplicate labels are retained; at an exact opposite-end resonance they are the two oriented root
ports.  For each label \(v=(\epsilon,\nu)\), write \(x_v=x_{\epsilon,\nu}\), and define for
\(L>0\)

```text
F_(v,+)(L)
 =w(nu)[u(x_v+exp(-L))-u(x_v)],

F_(v,-)(L)
 =w(nu)[u(x_v-exp(-L))-u(x_v)].                         (6)
```

Here the zero extension defines \(u(x_v)\) and both samples even when \(x_v\notin I\).
Boundedness of completed modes gives

```text
sup_L sum_(v,o) ||F_(v,o)(L)||^2
 <=8||u||_infinity^2 sum_nu w(nu)^2<infinity.           (7)
```

Thus \(F\) is a bounded tempered vector in the two-orientation weighted orbit Hilbert space.
The scalar mode is retained at the root labels; no infinite evaluation is used.

The common value at every interior center has already been subtracted in `(6)`.  At a physical
endpoint, the exterior orientation is identically zero on the terminal ray and the interior
orientation has the signed half-log trace from `(2)`.

## 3. Why one fixed window removes dense-seam localization

At each center \(x_v\), split the principal logarithmic jump using the fixed interval

```text
x_v-1<y<x_v+1.                                         (8)
```

After translating \(x_v\) to zero, the exact paired normal form applies to `(6)` for every
\(L>0\).  No neighborhood is required to exclude another seam; the formula uses the complete
physical \(u\) on both punctured sides.

The complement \(|y-x_v|\ge1\) has a kernel smooth in the sample point.  Differentiating
\(x_v\pm e^{-L}\) gives

```text
d/dL [far logarithmic block]=O(e^-L)||u||_2             (9)
```

uniformly in \(v\).  Suzuki's polar convolution has the same rate by its proved local Lipschitz
bound.  The scalar/eigenvalue term differentiates into a bounded diagonal multiple of \(F'\).

This is the point at which the earlier shrinking-cutoff architecture was unnecessarily hard:
dense centers do not require disjoint charts.

## 4. Exact prime intertwining

Let a visible prime-power step be \(s=\pm j e_p\), and identify the right/left root labels with
\(\epsilon=+1/-1\). Translation of the sample in `(6)` gives the root-dependent law

```text
u(x_(epsilon,nu)+/-exp(-L)-ell(s))
 =u(x_(epsilon,nu+epsilon*s)+/-exp(-L)).                (10)
```

The former same-direction formula was false on the left coset:
\(x_{-,\nu}-\ell(s)=x_{-,\nu-s}\). After subtracting center values, the retained descendant
center constants disappear upon differentiation. Therefore the literal differentiated prime
term is the rooted weighted coordinate shift

```text
(S_(epsilon*s,w)Z)_nu
 =[w(nu)/w(nu+epsilon*s)]Z_(nu+epsilon*s).             (11)
```

Because Suzuki's prime block contains both \(s\) and \(-s\) with equal coefficients, reindexing
\(s\mapsto-s\) makes the complete prime coupling the same bounded nonnormal operator on both
rooted cosets:

```text
B_(a,w)=sum_(s in Sigma_a)c_s S_(s,w).                  (12)
```

The norm estimate from the tempered-orbit theorem gives

```text
||B_(a,w)||
 <=sum_s |c_s|exp(kappa|s|_1)<infinity.                 (13)
```

Equations `(10)`--`(13)` are exact on every coordinate for which the sampled point is in \(I\).
When it is outside, \(u=0\); the discrepancy is a boundary-event source, classified next.

The exact marked-descendant decomposition, canonical literal-support cutoff, two-coset
distributional assembly, and finite-recurrence source estimate are now proved in
`../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-literal-paired-source-assembly.md`.

## 5. Boundary events and the zero-order recurrence budget

For a center in either endpoint coset, a sampled ray crosses a physical endpoint only when

```text
exp(-L)=|ell(nu)|
or
exp(-L)=|2a-ell(nu)|.                                   (14)
```

The first family is never worse than exponential in word length.  Indeed, if
\(\ell(\nu)\ne0\), put

```text
q_nu=product_p p^(nu_p)=A/B !=1.
```

Both \(A\) and \(B\) are at most \(p_{\max}^{|\nu|_1}\).  Since \(|A-B|\ge1\),

```text
|ell(nu)|=|log(A/B)|
 >=c_a exp(-C_a|nu|_1).                                (15)
```

Thus

```text
[-log|ell(nu)|]_+<=C_a(1+|nu|_1).                       (16)
```

The second family is controlled by `(1)`.  Given \(\epsilon>0\), every sufficiently large
\(\nu\) has event time

```text
L_nu
 <=[R_*(a)+epsilon]|nu|_1,
R_*(a)=max(C_a,R(a)).                                   (17)
```

The boundary upper estimate for completed modes and the exterior residual estimate show that on
one unit \(L\)-block around an event, every undifferentiated profile and completed source has at
most polynomial size in \(1+L_\nu\).  A source supported before the event has the same block
bound up to that time.  Therefore, for every \(0<\sigma<1\),

```text
sum_nu
 w(nu)^2 exp(2sigma L_nu)(1+L_nu)^N<infinity            (18)
```

for each fixed \(N\), provided

```text
kappa>sigma R_*(a).                                    (19)
```

If the differentiated fixed-window/far-block decomposition costs a fixed additional exponential
power \(mL_\nu\), choose instead

```text
kappa>(sigma+m)R_*(a).                                  (20)
```

There is no upper restriction on \(\kappa\) for the zero-order event sum or boundedness of `(13)`.
There is a sharp upper restriction for the direct Gamma fundamental-matrix method:
\(\kappa<\sigma<1\). Combining this with lattice square summability
\(\kappa>d/2\) leaves a uniform radial polynomial-carrier window only for valuation ranks
\(d\le1\). Higher rank must use source-selected homogeneous cancellation, reciprocal
biweighting, or the primitive-flux finite-to-flat route.

Equations `(18)`--`(20)` put zero-order exterior crossings, support-pruning discrepancies, exact
resonances after their root labels are retained, initial pieces, far-window terms, and polar terms
in the paired Gamma block source space. They do **not** control the first-order prime commutator
created by coordinate-dependent terminal cutoffs. This distinction is load-bearing.

## 6. Attempted differentiated assembly and exact failure

Combining the exact paired normal form, `(9)`, and prime intertwining would give

```text
(2L I+R-B_(a,w))F'
 +F-K JF
 =H_a.                                                   (21)
```

Here:

- \(R\) is the literal componentwise Gamma remainder;
- \(J\) swaps the two punctured orientations at each labeled center;
- \(K\) is the logistic convolution from the exact Carleman cross block;
- \(B_{a,w}\) is the complete weighted prime/scalar derivative coupling;
- \(H_a\) is the sum of the initial, physical-boundary-event, far-window, polar, and low
  counterterm sources.

For every \(\sigma<1\), choose \(\kappa\) as in `(20)`.  Then

```text
H_a belongs to the sigma block source space
and exp(sigma L)H_a belongs to L2.                       (22)
```

But an event-adapted diagonal cutoff \(M_\chi\) changes the prime derivative block by

```text
[M_chi,B_(a,w)]F'.                                      (22a)
```

The cutoff-covariance theorem proves:

```text
[M_chi,B_(a,w)]F'=0 for all F
 -> chi_nu is independent of nu;

unbounded event times
 -> no such common cutoff is event-adapted;

nonzero commutator
 -> no L2 bound from ||F||_2 alone.                      (22b)
```

Thus `(22)` is not established. Simultaneous mollification does not repair the loss: its
derivative norm diverges precisely when the original profile lacks \(H^1\), so Fatou supplies no
majorant for `(22a)`.

The exact replacement is now proved:

```text
G_cut=[R-B,M]F,
Y=(2L+R-B)(MF)-G_cut,

Y'=(2I-Z)(MF)-H_cut.                                    (22c)
```

At finite recurrence type, \(G_{\rm cut}\) and \(H_{\rm cut}\) have the required weighted
zero-order norms. The weighted graph estimate for `(22c)` uses only \(\|B\|\), even when \(B\) is
nonnormal. Volterra Liouville supplies the flat value/flux upgrade, and complementary
\(M\)/\(I-M\) fluxes recover the weighted derivative.  Superpolynomial block flatness forces the
terminal flux charge to zero, so no separate matching premise remains. Literal source assembly
is now proved; remaining work is finite-to-flat expansion.

## 7. Conditional value and dipole matching

At every interior center, `(6)` subtracts the common value.  Hence the symmetric residue charge of
the paired frequency ODE is zero.

The complete undifferentiated right-hand side of Suzuki's interior equation is continuous at the
center:

1. scalar multiplication preserves continuity;
2. every prime translate of the globally continuous zero extension is continuous;
3. the polar convolution is locally Lipschitz;
4. the far fixed-window block is smooth at the center.

Therefore its right and left limits agree.  The interior dipole theorem identifies their
difference with the antisymmetric zero-frequency moment:

```text
P_anti h_a(0)=0.                                        (23)
```

This remains true at a marked descendant.  Its conormal cusp is continuous at the center; only
its punctured derivative is singular.  Exact opposite-orientation collisions remain separate
labels but have the same zero scalar jump.

At the physical roots, one punctured orientation is zero and the other half-log charge is
\(\beta_\pm(u)\).  Assumption `(2)` removes both. The one-sided endpoint indicial coefficient is

```text
[(1-2tau)/(1-tau)]beta,
```

so the half-log channel `tau=1/2` is the unique nonzero subunit root. At `tau=1`, a putative
`beta/L` dipole produces `-beta log L+o(log L)` with no opposite-orientation cancellation; the
literal bounded source forces `beta=0`. On the all-orders-flat residual, the defining flux
equation forces terminal charge zero. These statements are proved in
`suzuki-flat-flux-charge-automaticity.md`.

Thus every regular-singular and flat terminal charge of `(21)` vanishes once the literal flux
solution is admitted to the frequency-zero graph. Volterra Liouville then proves shifted
value/flux \(L^2\), and complementary flux proves the root derivative.

## 8. Conditional Gamma-strip upgrade and dimension split

For a polynomial carrier of degree \(\kappa\), conditional on `(21)` and `(22)`, apply the paired
Gamma--logistic flat-sector theorem only at heights

```text
kappa<sigma<1                                            (24)
```

allowed by the chosen block cutoff,

```text
exp(sigma L)F in H1(dL;ell2).                            (25)
```

The logistic and Gamma multipliers have their common first pole at height one. The nonnormal prime
operator causes no further loss in the weighted derivative estimate after shifted value control,
but its group growth is load-bearing in the direct Hardy step.

Take \(\max(1/2,\kappa)<\sigma<1\). At either physical root, root-coordinate projection and `(25)` give

```text
integral exp(L)|F_root'(L)|^2dL<infinity.                (26)
```

Under \(r=e^{-L}\), `(26)` is exactly the spatial \(H^1\) derivative norm near that endpoint.
This would make \(u\) \(H^1\) in two endpoint collars with zero Sobolev trace. The uniform radial
polynomial route can realize such a \(\kappa\) only in ranks zero and one. In rank one the concrete
window \((\kappa,\sigma)=(2/3,3/4)\) and its three-step rough-primitive transfer are now
paper-proved. Thus `(3)` is closed for `2a<log 3`.

## 9. Conditional interior coverage

If `(25)` applies to every labeled interior center, then around a center \(x_v\), both
orientations cover some physical interval

```text
(x_v-e^-L0,x_v+e^-L0)
```

and `(25)` gives \(u\in H^1\) there.

The prime-log orbit is dense once two prime directions are visible.  For any compact
\(K\Subset I\), choose for each \(x\in K\) one orbit center \(x_v\) within one quarter of
\(\operatorname{dist}(K,\partial I)\).  Its paired chart contains a neighborhood of \(x\).
Compactness gives a finite subcover.  Hence \(u\in H^1(K)\).

The formalized dyadic orbit-chart theorem replaces this former elliptic-system argument. If prime
\(2\) is invisible, \(2a<\log 2<1\), so one physical endpoint chart covers the whole aperture. If
prime \(2\) is visible, centers \(a-k\log2\) have spacing below one and finitely many unit charts
cover \([-a,a]\). Combining those charts with `(25)` gives

```text
u in H1(I).
```

The zero extension and zero endpoint traces would put \(u\) in \(H^1_0(I)\). Coverage is proved;
only analytic admission in Section 8 remains open.

## 10. Corrected frontier

The completed-Evans scale gap is now:

```text
R(a)<infinity
 -> zero-order boundary events are Gamma summable;       [PROVED]

R(a)=infinity
 -> tempered orbit carrier unavailable;                 [CLASSIFIED]

coordinate-adapted differentiated assembly
 -> derivative commutator with no zero-order bound;      [BLOCKED]

primitive global flux / exterior-residual relation
 -> physical dipole and flat charges vanish;             [PROVED]

literal two-coset paired source assembly
 -> exact rooted signs and weighted source class;        [PROVED]

rank zero/one rough primitive transfer
 -> low-rank trace-zero H1_0 via dyadic coverage;        [PAPER-PROVED]

rank at least two source-selected finite-to-flat transfer
 -> higher-rank trace-zero H1_0 via dyadic coverage;     [OPEN]

all apertures
 -> additionally pass recurrence-infinite class.         [OPEN]               (27)
```

The trace-zero theorem remains open even on the full-measure finite-type class.

## 11. Hostile audit after retraction

1. **Raw gap retained, graph repair proved.** Adapted cutoffs do not commute with
   \(B\partial_L\), but the complete defect is now an exact primitive flux.
2. **No mollifier escape.** Uniform derivative control is the desired conclusion.
3. **No recurrence escape.** Linear event-time growth controls location, not derivative order.
4. **Surviving exact pieces retained.** Fixed-window normal form, weighted transport before
   cutoff, and zero-order event sum are unaffected.
5. **Dimension wall retained.** Uniform radial polynomial Hardy transfer survives only in ranks
   zero and one; higher-rank source-selected/primitive transfer is not inferred.
6. **No compact-middle debt.** Formalized dyadic orbit charts give exact finite coverage.
7. **No theorem-statement falsification.** The finite-type implication remains a conjecture.
8. **No all-aperture or RH claim.** Exceptional apertures and Evans positivity remain later gates.

## 12. Conjecture boundary

Weighted orbit lifts, fixed-window localization, regular-singular gluing, and Diophantine event
budgets are classical ingredients. The intended source theorem remains

```text
finite prime-log recurrence
 -> exact weighted paired physical-orbit equation
 -> finite-to-flat expansion
 -> automatic value/dipole/flat-charge matching
 -> Gamma-strip derivative
 -> trace-zero H1_0.                                    (28)
```

The augmented primitive-flux equation, weighted graph estimate, automatic zero-charge flat
value/flux upgrade, physical dipole exclusion, and complementary derivative recovery are proved.
Literal source assembly and compact-middle coverage are proved. Low-rank analytic admission is
paper-proved; higher-rank admission is not.
Therefore theorem `(3)` remains open.

## 13. Lean decision

The dependency-closed cutoff-covariance no-go, primitive identity, exponential flux cancellation,
absorption inequality, complementary flux cancellation, automatic flat-charge squeeze, and
physical indicial coefficients, rooted transport, literal cutoff support, and exact source
algebra are formalized. No wrapper may assume finite-to-flat expansion, `(25)`, or theorem `(3)`.

## Gates

- [x] construct literal weighted paired orbit state from every completed mode
- [x] avoid disjoint localization by one fixed physical window
- [x] prove exact weighted prime intertwining
- [x] control approximation to zero by elementary rational separation
- [x] control opposite-end events by finite recurrence type
- [x] prove zero-order event/far/polar sources enter the Gamma block space
- [x] identify exact first-order cutoff commutator
- [x] prove current differentiated assembly architecture cannot close from zero-order norms
- [x] construct exact primitive global flux relation
- [x] prove arbitrary-nonnormal weighted graph uniqueness for that flux
- [x] prove flat-tempered primitive-flux Volterra Liouville
- [x] prove complementary primitive-flux root derivative recovery
- [x] prove physical-root dipole and terminal flat-flux charge vanish automatically
- [x] derive literal infinite paired-orbit normal equation on the completed source
- [x] correct opposite rooted valuation directions and retain descendant center constants
- [x] construct canonical smooth cutoff supported exactly on literal interior samples
- [x] prove complete primitive/zero-order source signs and finite-recurrence Hilbert bounds
- [x] classify the sharp radial polynomial Gamma dimension wall
- [x] prove rank-zero/one rough primitive transfer without a flatness premise
- [ ] prove higher-rank source-selected finite-to-flat transfer
- [x] obtain spatial endpoint \(H^1\) for `sigma=3/4` in rank zero/one
- [x] cover compact middle by dyadic orbit charts
- [ ] compose analytic admission with coverage and prove global \(H^1_0\)
- [ ] pass recurrence-infinite apertures
- [ ] identify trace-zero square-Evans kernel with raw Evans kernel for every aperture
- [ ] prove nonzero-trace return
- [ ] prove raw Evans Gram positivity
- [ ] RH or whole-Connes no-go
