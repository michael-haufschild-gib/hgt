# Periodic labeled sections with infinitely many critical points

- **ID:** RH-PLBS-20261007
- **Stage:** 1-in-progress
- **Type:** FALSIFIED candidate; main positive survivor verified in Lean
- **Source:** `xi-marked-joint-monodromy.md`, hostile audit of C2
- **Statement:** The three exact labeled lattice fibers do not force a rational Schwarzian or finitely many critical points.

## Exact conjecture and purpose

Let omega=exp(2*pi*i/3). A nonconstant meromorphic V on C obeys
`V(-w)=1/V(w)` and `V(conj w)=1/conj(V(w))` as maps to P1. Suppose
every preimage of omega^j is simple and lies in `j+3Z`, for j=0,1,2.
The stronger candidate C2-S was that its Schwarzian is rational in w.
This would imply differential algebraicity and supply a specific geometric
mechanism for C2. Its first apparent open core was exclusion of infinitely
many critical points away from the distinguished fibers.

**Verdict: FALSE, with a Lean-certified witness.** Exact lattice labeling permits infinitely many
ordinary critical points. The construction below remains differentially
algebraic, so C2 and the actual Xi no-lift problem remain open.
The positive survivor has verdict BRIDGE; significant novelty is unverified.

## Complete paper construction

Put a=sqrt(2/3), t=exp(pi*i*w/12), and

```
N(t)=t*(t-a), D(t)=1-a*t,
R(t)=N(t)/D(t), V(w)=R(t).
```

N and D have no common root: the only roots of N are 0 and a,
where D is respectively 1 and 1-a^2=1/3. The identities
`R(1/t)=1/R(t)` and `R(conj t)=conj(R(t))` give both required
symmetries of V, because `t(-w)=1/t(w)` and
`t(conj w)=1/conj(t(w))`.

The three complete fibers are

```
V=1:       w in 24Z or 12+24Z;
V=omega:   w in 1+24Z or 19+24Z;
V=omega^2: w in -1+24Z or -19+24Z.
```

Indeed N-D=t^2-1. For omega, the polynomial N-omega*D has
roots exp(pi*i/12), exp(19*pi*i/12): their product is -omega
and their sum is `a*(1-omega)`, by the exact half-angle identities
for pi/12. The omega^2 roots are their conjugates. Each quadratic
has two distinct roots, none a pole; the exponential is locally unramified.
The exponential equality criterion gives exactly the lists above.
Their residues are respectively 0,1,2 modulo three. This checks whole
fibers, not only interpolation at selected lattice points.

There is a second certificate of full lattice containment that avoids
choosing quadratic roots. At a distinguished fiber N=cD, c^3=1,
coprimality gives D nonzero. The quotient identity below then forces
`t^8=c`; since `t^8=exp(2*pi*i*w/3)`, its entire preimage is exactly
the required residue class when c=omega^j. Distinguished fibers are
simple because their quadratic `g=t^2+a*(c-1)*t-c` has no multiple
root: a multiple root would imply `c^2+4c+1=0`; together with c^3=1
this implies c=-1/5, contradicting that quadratic. Thus the cancellation
identity alone controls all preimages and their orders, even before the
more detailed mod-24 lists are extracted.

Differentiate the rational map:

```
R'(t)=(-a*t^2+2*t-a)/(1-a*t)^2.
b_plus=(sqrt(3)+1)/sqrt(2),
b_minus=(sqrt(3)-1)/sqrt(2).
```

The numerator has exactly the distinct roots b_plus,b_minus. Neither is
0, 1, or 1/a, by substitution and a^2=2/3. Therefore each is an ordinary
simple critical point, and V has simple critical points at every
`12*log(b_plus)/(pi*i)+24k`, k in Z, and similarly for b_minus.
These are distinct. Here the b's are explicit positive reals, so their
real logarithms are defined; this is an exact exponential identity, not a
growth or sign-based rigidity argument.

At a simple critical point w0, write `V=V0+c*(w-w0)^2+...`, c nonzero.
Then `V''/V'=1/(w-w0)+holomorphic` and V'''/V' has at most a simple
pole. Consequently `S(V)=V'''/V'-(3/2)*(V''/V')^2` has a genuine
double pole with leading coefficient -3/2. Infinitely many such points
exclude rationality of S(V), since a rational function has finitely many
finite poles. No magnitude estimate is used.

For the formal local pole certificate, use the cleared Schwarzian
`(2*V'*V'''-3*(V'')^2)/(2*(V')^2)`. At an order-two branch point,
V' has exact order one and V'' is nonzero. Thus the numerator is a
holomorphic unit and the denominator has exact order two. The quotient
has meromorphic order -2. This is an exact valuation identity; it does
not estimate either summand of the Schwarzian or any growth quantity.

The branch multiplicity has a useful exact certificate avoiding derivative
estimates or a series truncation. For either critical t-value b,
`R(t)-R(b)=(t-b)^2/D(t)`. Clearing denominators leaves exactly
`(t-b)*(-a*b^2+2*b-a)`, which is zero. The exponential coordinate is
unramified at b, and D(b) is nonzero, so this is an exact local order-two
factorization at every point of the corresponding progression.

## Entire-section survivor

Set r=exp(-2*pi*i*w/3)=t^(-8). Define

```
B(t)=t^4-3*a*t^3+3*t^2-3*a*t+1,
C(t)=a*t^2+t+a.
N^3-D^3=(t^2-1)*B(t),
t^8*D-N=-t*(t^2-1)*B(t)*C(t).
Q(t)=-C(t)/t^7,
h(w)=2+3*D(t)^2*Q(t).
```

Both polynomial identities follow by expansion using a^2=2/3. They give
`(N^3-D^3)*Q=D-r*N` and hence the full normalized lift equation
`(N^3-D^3)*h=2*N^3-3*r*N*D^2+D^3`.
Since t never vanishes, h is entire. This handles every exceptional fiber
and every pole directly, with no removable-point limit argument.

For every real L nonzero, put w=L*(s-1/2)/(pi*i) and
`F(s)=exp(L*s)*P(h(w))`, where P(x)=(x-2)*(x+1)^2/4.
The rational identity and reciprocal symmetry give
`r^3*P(h(-w))=P(h(w))`; hence F(1-s)=F(s).
Real coefficients and `t(-conj w)=conj(t(w))` give real structure.
Taking L=log 2 gives an entire cubic lift for integer mark two.

For a direct Laurent-polynomial verification of reflection, put
`H=t^6+a*t^5+(2/3)*t^4+(2/3)*t^2+a*t+1` and `J=D*(t-a)*H`.
Expansion gives `t^7-D^2*C=(t-a)*H`, hence
`h+1=3*(t-a)*H/t^7` and `P(h)=-(27/4)*J^2*C/t^21`.
The exact reciprocal identities `H(1/t)=H(t)/t^6`,
`J(1/t)=J(t)/t^8`, `C(1/t)=C(t)/t^2` prove
`P(h(1/t))=t^24*P(h(t))`. Thus the reflection argument does not
divide by a function vanishing on an exceptional fiber.

At t=1/a, D vanishes simply and `C(1/a)=2/a+a` is nonzero
(multiply by a to obtain 2+a^2=8/3). Thus h-2 has exact order two,
while h+1=3. These give an infinite arithmetic progression of off-line
zeros of F of exact order two and its reflected progression. The real
part is off the critical line because 1/a is a positive real unequal to 1,
so `Re(s)-1/2=12*log(1/a)/L` is nonzero. Entireness and these exact orders
are the strongest survivor to formalize along with the whole-fiber and
infinite-critical-point certificate.

## Audit and relevance

- Internal deep Schwarzian/labeled-lattice search returned partial results
  (reranking deadline). Inspected all 20 candidate statements and all 20
  source-argument statements. Useful parents include rational Schwarzian
  substitution, meromorphic-field embeddings, and a doubly periodic
  differential-algebraicity theorem. None inspected supplies the stated
  labeled-fiber rigidity. The suggested ingredient set, Schwarzian escape
  in rational fields, has unverified applicability and does not prove it.
  Inventory is complete at its snapshot; compiler freshness is not global.
  No corpus-wide absence claim follows.
- The corpus already has the differential-field Schwarzian invariant and
  projective-coordinate machinery in `H:SchwarzianProjectiveInvariant` and
  the `ProjectiveHorizonSchwarzian*` modules. Those algebraic identities do
  not classify this analytic lattice geometry.
- Bergweiler--Eremenko, [Meromorphic functions with three radially distributed
  values](https://www.math.purdue.edu/~eremenko/dvi/radial_mero_revision2.pdf),
  Theorem 1.3, gives a rational-Schwarzian characterization when three value
  fibers lie on three distinct equally spaced rays. The present fibers lie
  on residue classes of one line, so that theorem does not apply. Its proof
  also uses characteristic/harmonic-measure estimates, excluded here.
- Their [linearly distributed values paper](https://www.math.purdue.edu/~eremenko/dvi/real.pdf)
  retains a real-map alternative and does not force rational Schwarzian for
  this case. These are parent theories, not novelty certification.
- R is a quadratic finite Blaschke product; that rational-map family and
  its critical-point geometry are classical. The primary paper
  [Semmler--Wegert](https://arxiv.org/abs/1703.01126) describes the established
  prescribed-critical-point problem. Its moment/energy methods are not used
  here. The present task is the exact labeled cancellation application;
  the underlying function class and Schwarzian pole law are not new science.

## No-go closure

- **Exact failure:** rational-Schwarzian/finite-critical-point rigidity fails
  despite every distinguished fiber being simple and correctly labeled.
- **Strongest positive survivor:** an explicit periodic meromorphic parameter
  with complete lattice fibers, infinitely many simple critical points, and
  an entire reflected cubic lift with an infinite progression of off-line
  zeros of exact order two.
- **New insight:** finite ramification is unavailable as the missing global
  premise. C2 must allow periodic infinite ramification while controlling
  differential algebraicity. Infinite branching alone is not its obstruction.
- **Status:** the main positive theorem passes Lean in four leaves:
  `H:PeriodicLatticeSections`, `H:PeriodicLatticeBranching`,
  `H:PeriodicLatticeFibers`, `H:PeriodicLatticeSchwarzian`. The final theorem
  `labeled_fibers_infinite_double_poles` combines whole-fiber containment
  and exact simplicity with infinitely many Schwarzian poles of order -2
  for the same map. Its global meromorphy is also verified. Finer mod-24
  lists remain a paper refinement. No actual Xi premise has been discharged,
  and no significant novelty is certified. C2 remains active on the parent.

## Checklist

- [x] Exact conjecture, hostile counterexample and dependency-closed paper proof.
- [x] Preliminary internal/external audit; BRIDGE, significant novelty unverified.
- [x] Verify algebraic identities and the entire-source theorem in Lean.
- [ ] Optional refinement: verify the finer explicit mod-24 lists in Lean.
- [x] Verify whole-fiber lattice containment, simplicity and the infinite critical set in Lean.
- [x] Verify Schwarzian nonrationality or exact local double poles in Lean.
- [x] Run axiom audit, direct leaf audits, targeted builds, umbrella check and lint; global lint limitations below.
- [ ] Return to C2's actual differential-algebraic obstruction.

## Log

- 2026-10-07 — derived symbolically after closing the finite cubic family's
  analytic survivor. No numerical experiment or bounds were used.
- `H:PeriodicLatticeSections` passes direct `lake env lean` without warnings.
  Its unconditional `reflected_integer_marked_periodic_source` provides the
  entire real reflected source, cubic lift for integer mark two, and an
  injective integer-indexed family of off-line zeros of exact order two.
  Off-line location is proved from conjugation and a^2=2/3, not a logarithm
  estimate. The full labeled-fiber and infinite-critical-point geometry is
  not yet certified in Lean. Targeted build and companion work are underway.
- Targeted `lake build --old +...PeriodicLatticeSections` passes (2,722
  jobs, leaf 3.2 seconds). Umbrella import added once. The branching
  companion uses the exact quadratic difference factorization above;
  its direct audit is next, before claiming the geometric obstruction in Lean.
- `H:PeriodicLatticeBranching` passes its first direct leaf audit without
  warnings. `infinitely_many_simple_branch_points` gives an injective
  integer-indexed family on which the meromorphic parameter is analytic
  and its local value difference has exact order two. The proof uses the
  quadratic difference identity and analytic orders. Full lattice-fiber
  containment/simplicity and the Schwarzian pole theorem remain to formalize.
- `H:PeriodicLatticeFibers` now passes direct audit without warnings.
  `every_fiber_labeled` treats every zero of the cleared fiber equation,
  forcing it onto its prescribed class modulo three. `every_fiber_simple`
  gives exact order one. Denominator nonvanishing follows from the verified
  coprimality lemma, so these are actual fibers, not artifacts of a quotient
  evaluated at a pole. The explicit finer mod-24 lists remain paper-only;
  the universal containment and simplicity needed for the failed rigidity
  conjecture are verified. Branching targeted build passed (2,723 jobs).
- The same-coordinate combined fiber/branch certificate passes direct audit
  without warnings, as does the Schwarzian leaf. The latter proves exact
  meromorphic order -2 at every point of an injective integer-indexed family.
  Fiber targeted build passes (2,724 jobs); Schwarzian targeted build passes
  (2,728 jobs). All four leaves are wired once into HTGeometry. Expanded
  axiom audit and final lint follow.
- All eleven expanded axiom checks pass with exactly `propext`,
  `Classical.choice`, and `Quot.sound`. Generated indexes refreshed.
  Final `scripts/formal_tools.py lint --check-generated` reports six
  unrelated unreachable modules: `R:ZetaLineTwistedSeriesMoment`,
  `H:ApertureConeCalculus`, `H:ApertureConeWinding`,
  `H:ApertureLogTranslation`, `H:ApertureOpenHistoryIdeal`, and
  `H:BoundaryCoronaCStarAlgebra`. No stale generated report or error in
  the four new leaves is reported. The global gate is not clean.

## Assessment and next core

The exact finite-branching shortcut is eliminated, including its nontrivial
positive survivor. This is a verified route restriction, not a certified
new branch of mathematics or a source-specific Xi theorem. The construction
uses a classical quadratic rational map and local valuation laws; those
ingredients cannot be counted as scientific novelty. The arithmetic fiber
application has verdict BRIDGE and has not passed a significant-novelty gate.

C2 remains the active mathematical target. The next mechanism must permit
infinitely many critical points and Schwarzian poles. A sharper candidate
to audit is that every nonrational admissible parameter has a nonzero
translation period; its competing possibility is an admissible nonperiodic
parameter, potentially hypertranscendental. Neither assertion is assumed.
The first open core is to derive such a period from the full labeled-fiber
condition or construct a counterexample. Even a periodicity proof would
still require a justified passage to differential algebraicity; do not
silently import a growth, normal-family or Picard argument as an allowed
mechanism. No additional finite example alone resolves this core.
