# BAG complete three-frequency Ramanujan source

- **ID:** BAG-C28.56ag, continuation01a5.
- **Stage:** 1-in-progress.
- **Type:** ag.1/ag.2 sources and ag.3 complete finite physical identity formalized; signed growing action open.
- **Target:** full physical cubic, retaining all three rational frequencies,
  including the finite-height neighborhood of c=a*b.
- **Corpus basis:** PMPowerDampedMobiusDivisorHaar;
  PMPowerDampedMobiusRamanujanExpansion/Weights;
  ChiRamanujanDampedSquareRightLine; ChiPrimeGaussianCubicMain;
  complete weighted rational trace and its Schwartz boundary.

## Hard problem and intended advance

The existing six-zeta arithmetic source evaluates the exact resonance c=a*b.
It does not estimate the complete finite-height neighborhood. A literal
three-frequency construction must first make sense of the ungrouped rational
mode limit without assuming absolute summability of its signed residue atoms.
The proposed construction uses uniform bounds on the actual Fourier
coefficients of finite-prime signed measures. It does NOT infer a cubic bound
from a generic quadratic bound. Its success would supply a full-frequency
source and justified interchange, not yet the required signed cubic estimate.

## Concrete source-based conjecture

For a finite prime set P, let h_p be the uniform measure on the p-torsion
points of the circle. Define the finite signed convolution

    nu_(e,P) = convolution_(p in P) (delta_0 - p^(-e) h_p).

The Fourier coefficient at integer n is exactly

    d_(e,P)(n) = product_(p in P, p divides n) (1-p^(-e)).

The normalized local nonzero residue weight is the literal Ramanujan weight:
after dividing by product_(p in P)(1-p^(-1-e)), it is
-1/(p^(1+e)-1), with the zero residue retaining weight one. Thus this is a
finite-prime version of the actual source, not a replacement random measure.

For n!=0, once P contains every prime factor of |n|, the Fourier coefficient
is exactly pmPowerDampedDivisorCoeff e |n|. For e>=0 every coefficient is in
[0,1]. The signed atomic total variation need not remain bounded; the Fourier
bound is the proposed route to a distributional limit.

Crucial critical-limit subtraction: use

    (nu_(e,P)-nu_(0,P))/e,

before sending e to zero and P through all primes. Subtracting only the
infinite-prime zero-damping limit leaves spurious 1/e coefficients at integers
whose prime factors have not entered P. For n!=0, the proposed bound for the
correct subtraction is log|n|, uniformly in e>0 and P. If P contains 2 and 3,
the zero Fourier coefficient divided by e is bounded by e*log2*log3 and
therefore vanishes as e->0, independently of the remaining primes.

Conjecture: this compensated finite-prime source converges jointly, against
every Schwartz test, to the distribution with Fourier coefficients
vonMangoldt |n| for |n|>1 and zero at 0,+1,-1. The tensor product in three
variables should have a uniform finite-seminorm bound and the corresponding
joint limit, retaining all three independent frequency variables. Squarefree
Fourier restriction then removes proper prime powers exactly.

For the literal finite physical band, taking P to contain all prime factors
of integers up to floor(2N) makes the zero-damping subtraction vanish on
every active coefficient. No source integer is then omitted. This is the
proposed link back to the actual cubic; it still requires the full physical
kernel identification and an estimate of its signed near-resonant action.

## Proof obligations and limits

Prove the finite Fourier identity, uniform compensated coefficient bound,
joint coefficient limits (including n=0), and full three-variable tested
convergence from actual Schwartz lattice summability. Verify the exact
Ramanujan normalization and actual prime-only physical-band identification.
Do not declare the growing oscillatory test controlled merely because every
fixed Schwartz test converges. The final cubic estimate, growing moments,
moving cofactors, positive common-height self-return and RH remain open.

Direct-contour attempt preceding this construction did not supply a saving:
the literal chi/three-Dirichlet-polynomial shift retains the saddle scale,
and the physical compact smooth window is not an analytic contour weight.
No contour identity or bound was assumed or formalized from that attempt.

## Log

- 2026-10-05 — Created before source formalization. Corpus searches for the
  direct contour, prime reciprocal source, and finite-prime Fourier mechanism
  are being inspected. No theorem in this card is yet claimed Lean-audited.

- continuation01a5 development checkpoint: the actual finite-P compensation,
  uniform log bound for n>0, zero-frequency bound using 2 and 3, exact divisor
  coefficient identification, and JOINT (P,e)->(all primes,0+) coefficient
  limit have compiled in scratch. Production leaf
  `ChiRamanujanFinitePrimeCompensation.lean` passed its foreground leaf audit.
  `ChiRamanujanThreeFrequencyLattice.lean` also passed: every three-variable
  Schwartz test has an explicit finite-seminorm summable lattice envelope.
  Both are wired once; their axiom/index/lint audit is still pending. These
  facts do not yet prove the complete finite rational atom action or the
  physical cubic estimate. The atom identity and tested-limit capstone remain
  under development. No claim of cubic cancellation or RH closure.

- Source construction simplification: use the literal finite divisor atoms
  `sum_(d|rad(P)) mu(d)d^(-e)/d * sum_(a mod d) delta_(a/d)`.
  Their integer Fourier coefficient is D_e(gcd(rad(P),|n|)), including n=0.
  This equals the proposed finite prime product, and retains every rational
  frequency. Repeated rational points are allowed in the finite atom index;
  no atomwise absolute convergence over all primes is assumed.

## Next conjecture: prime-only source without an arithmetic test mask

The corpus theorem `vaughanSquarefreePart_vonMangoldt` removes proper prime
powers exactly. Applying a squarefree mask to the *test* destroys its smooth
continuum profile and cannot be ignored in a stationary-phase bridge. Put
this mask in the finite source instead. For each retained prime p, convolve
with `delta_0-h_(p^2)`. Its integer Fourier multiplier is
`1-1_(p^2 divides n)`. Their finite convolution has multiplier A_P(n) in
{0,1}, and eventually A_P(n)=1_(Squarefree |n|) for every n!=0. At n=0 any
retained prime already gives A_P(0)=0. Thus the compensated source convolved
with this squarefree sieve should converge jointly to the exact prime-only
logarithmic Fourier distribution. The existing uniform envelope survives
because |A_P|<=1. All atoms remain finite rational torsion points; their
nodes add under convolution. No arithmetic discontinuity need be moved into
the smooth physical test. This is a source-derived CONJECTURE, not yet proved
or formalized here; the exact finite atom identity must be supplied.

Stationary bridge to the existing multiplicative modes (PAPER mechanism,
not a theorem): the full continuum physical phase pq/r paired with additive
Fourier coordinates x,y,z has stationary equations q/r+x=0, p/r+y=0,
-pq/r^2+z=0, hence z=x*y. Integer lifts of the periodic rational coordinates
produce the positive-rational multiplicative modes. This explains the
relationship to c=a*b, but does not justify discarding its finite-height
neighborhood or establish a uniform signed estimate. Complete Poisson
summation, squarefree source, actual contractions, and growing-test errors
remain obligations.

- Squarefree source search `/tmp/bag-squarefree-atom-source-search-01a5.json`
  finished partial (65649/65649 indexed; reranking local runtime deadline;
  refresh incomplete). All20 candidate and20 source statements/methods plus
  the proposed ingredient pair were inspected. Prime-square fixed vectors
  and squarefree shear diagonals do not establish the desired torsion
  annihilator identity. The applicable exact prime-only coefficient source
  remains `vaughanSquarefreePart_vonMangoldt`; no search hit is treated as an
  unproved interchange or cancellation estimate. Rephrasing lexically next.

- Lexical rephrase `/tmp/bag-squarefree-mangoldt-search-01a5.json` completed
  with two hits, both inspected. The Vaughan squarefree-Mangoldt identity
  applies; SquarefreeCoronaCodiagonal's alternating prime-power Laplace
  channel does not implement this additive torsion projector.
- Further PAPER simplification of the conjectured prime-only source:
  h_p*h_(p^2)=h_(p^2), so its local finite signed factor is
  `delta_0-p^(-e)h_p-(1-p^(-e))h_(p^2)`. At e=0 this is the same
  `delta_0-h_p` as the unfiltered source. At integers divisible by p^2,
  its Fourier coefficient is exactly zero at EVERY damping value. Thus
  prime-power removal belongs inside the source before the growing smooth
  test is introduced. The finite convolution identity and full prime-only
  joint limit are not yet claimed Lean-proved.

## ag.1 completed audit checkpoint

The additive source theorem and exact finite atom/Fourier interchange are
now formalized in all five production leaves. Final capstone is
`tendsto_ramanujanTripleFiniteAtomAction`; its fixed Schwartz profile gives
a periodic Fourier test, with no relation among the three coordinates.
All five foreground leaf audits passed, all41 declarations have only standard
axioms, index refreshed, all five umbrella imports occur once. Lint reports
27 unrelated unreachable modules and no finding for these leaves. P2/P3
`bag-additive-rational-three-frequency-source` and frontier C28.56ag.1 record
this exact closure. The source-level prime-square filter, normalization and
physical stationary bridge remain open in this parent card. No complete
physical cubic, multiplicative finite-height transfer, or RH proof claimed.

## continuation01a6 — exact prime-only atom tensor

Prior turn classified PROGRESS: ag.1 changed the authoritative Lean corpus
and closed fixed-test additive source/interchange, with the full physical
cubic still open. Current target is ag.2, source-level prime-square deletion,
followed by the actual growing physical test. No repeat of the ag.1 audit.

Finite construction chosen for direct verification: for each p in P, use the
three literal atom families delta_0, -p^-e h_p and -(1-p^-e)h_(p^2). Form the
finite product of their atom choices, adding rational nodes and multiplying
weights; compensate the WHOLE product between e and zero. Finite Fourier
orthogonality should identify this exactly with the old compensated Fourier
coefficient times the finite predicate that no retained p^2 divides n.
This avoids assuming any all-prime atomic total variation. The finite square
predicate eventually equals Squarefree n, so the corpus squarefree-Mangoldt
identity gives the exact prime logarithm. The same Schwartz envelope should
then prove the full triple limit, retaining a smooth physical test.

- Corpus search01a6 returned the exact `sum_moebius_sq_dvd` theorem in
  HTGeometry/SquarefreeClockLaw and the sieve squarefree indicator identity.
  This permits a simpler literal finite filter: sum_(d|rad(P)) mu(d)h_(d^2).
  Its coefficient at n is mu(gcd(rad(P)^2,|n|))^2. Convolve this finite filter
  with the already constructed compensated divisor atoms by adding their
  rational nodes. The newly discovered exact square-divisor identity replaces
  the longer product-of-local-options implementation; no estimate is assumed.
  The prior source leaf gains a public finite-torsion orthogonality helper;
  Serena symbol lookup rejected its ignored Lean path, so a targeted patch
  is used. The existing public theorems remain unchanged.

- Square-sieve coefficient scratch45733, production3905: exit0 with no
  diagnostics. Literal rational convolution scratch95456, production55141:
  exit0 with no diagnostics. The torsion API audit81094 and exposed periodic
  summability helper audit69251 also exited0. Full prime-only tensor/action
  capstone is still in development; no full cubic cancellation is claimed.
  Development failures were dependent `if` rewriting, an underdetermined
  prime-factor subset binder, and finite-sum rewrite order; all were fixed
  without changing mathematical statements, axioms or resource limits.

## Next hard conjecture: complete signed transverse action

The source is now arithmetic at the atom level. The next task is not another
fixed-test topology or a seminorm constant. Keep the actual all-band W/V
amplitudes and both physical contractions. For the smooth full physical
amplitude f_N(p,q,r), including reciprocal logarithms to undo the source's
prime logarithms, its additive Fourier test has phase

    pq/r + x*p + y*q + z*r
      = (p+y*r)*(q+x*r)/r + (z-x*y)*r.                 (r != 0)

Thus translating u=p+y*r, v=q+x*r gives an EXACT candidate kernel

    K_N(x,y,z) = integral_r exp(2*pi*i*(z-x*y)*r) B_N(r;x,y) dr,
    B_N(r;x,y) = integral_(u,v)
      f_N(u-y*r,v-x*r,r) exp(2*pi*i*u*v/r) du dv.

Every integer lift of the rational atom coordinates must remain. The
stationary point is p=-y*r, q=-x*r; physical p=r and q=r correspond to
y=-1 and x=-1 in these lifts. This locates the contraction axes in the
new representation but does not yet justify restricting the source there.

Conjecture to attack: the COMPLETE finite signed atom tensor applied to
this exact kernel, with the literal two physical contraction actions
subtracted and their intersection restored, is o(N/log(N)^2) under a
source-derived prime/damping exhaustion recovering the physical band.
The full transverse neighborhood |z-x*y| of size 1/N, all larger tails,
all lifts and the scale-dependent edge cutoffs are obligations. Replacing
B_N by its stationary value, replacing the neighborhood by z=x*y, or
using pointwise fixed-P damping convergence is not a proof.

In particular, at positive damping the new source still includes squarefree
composites: its covered-band coefficient is 1_(Squarefree n)*D_e(n)/e.
The physical prime limit and the transverse estimate must therefore be
controlled together. No such growing-test estimate is claimed here.

Searches `bag-growing-physical-source-search-01a6.json` and
`bag-cubic-dual-phase-search-01a6.json` completed nonpartial, covering
65656/65656 and 65659/65659 indexed files respectively; refresh remained
incomplete under the background indexer, with source-only/pending compiler
metadata. All20 candidates and20 source statements/methods in each were
inspected, plus empty proof-idea arrays and proposed ingredient sets. The
first proposed Lag/cubic pairing is inapplicable; the second chi stationary
pairing controls the original height transform, not the new full dual cone
action. Relevant existing physical sources were read directly. No search
ranking or absence of a hit is used as a mathematical assertion.

## Stronger finite-band bridge discovered during ag.2

The positive-damping composite issue need not be accepted as an obligatory
physical source limit. The finite source can first be differentiated at zero.
Its literal divisor atom weight becomes

    -mu(d)*log(d)/d,  at every a/d, d|Q(P).

Convolve with the same square-divisor sieve. Finite torsion orthogonality and
the exact corpus theorem `ArithmeticFunction.sum_moebius_mul_log_eq` give
Fourier multiplier

    mu(gcd(Q(P)^2,|n|))^2 * Lambda(gcd(Q(P),|n|)).

If P covers every prime factor of 1<n<=M, the prime-factor sets of the
second gcd and n agree; their von Mangoldt values agree. The first factor
is the exact squarefree indicator. Thus this CRITICAL finite atom source
should equal the prime logarithm EXACTLY on the whole covered band, not
only in a damping limit. Tensoring and finite Fourier interchange would
give an exact all-band physical cubic representation with no damping
approximation. The complete signed growing rational atom action remains
the hard problem; nothing here bounds its near-cone neighborhood.

This is the next concrete source-derived conjecture, with paper mechanism
specified but not yet formalized. Search76197, retained in
`/tmp/bag-finite-critical-prime-search-01a6.json`, completed nonpartial with
65661/65661 indexed files, incomplete background refresh and source-only
compiler metadata. All20 candidate and20 source statements/methods, the
empty proof-idea list and proposed ingredient set were inspected. The exact
mathlib Möbius-log identity was read in this toolchain. A finite atom Fourier
proof and the full covered-band equality still require their Lean audit.

### Exact physical contractions in the additive representation

Use the already audited finite torsion orthogonality, rather than assuming
that a multiplicative trace axis is the physical contraction. For a periodic
Fourier test F define, with an integer D larger than every active frequency
difference in the finite physical band,

    E13 F(x,y,z) = (1/D) sum_(a mod D) F(x+a/D,y,z-a/D),
    E23 F(x,y,z) = (1/D) sum_(b mod D) F(x,y+b/D,z-b/D).

The multipliers are 1_(D divides n1-n3) and 1_(D divides n2-n3).
On the covered finite band these are exactly n1=n3 and n2=n3. Therefore
(1-E13)(1-E23) retains precisely the original two contraction exclusions,
with the intersection restored. All averaging points are finite rational
translations and the periodic test stays smooth. This is a concrete next
formalization target, not a claimed completed identity or cancellation bound.

The completed phase exposes a term that must survive any later comparison
with the multiplicative trace. Writing delta=z-x*y, the simultaneous shift
by a/D and b/D changes it to

    delta-(1+y)*a/D-(1+x)*b/D-a*b/D^2.

The mixed term and the translated amplitudes cannot be suppressed. The
single averages identify y=-1 and x=-1 as the tangent cases, but those axes
alone do not describe the finite-height double average. This directs the
next proof toward the literal full physical source and its mixed transverse
action, rather than another fixed-test limit.

Projector search68330 nonpartial65664/65664, refresh incomplete, all20+20
statements/methods and proposed ingredients inspected. Circle Fourier
projection methods are relevant; the proposed Connes diagonal/finite deck
projection pairing does not itself prove the physical identity. The finite
torsion theorem already audited in ag.2 is sufficient for the finite-band
projection approach above. No new numerical experiment or selected packet.

## ag.2 completed audit checkpoint

The three new leaves ChiRamanujanPrimeOnlySieve (10 public declarations),
ChiRamanujanPrimeOnlyAtoms (8), and ChiRamanujanPrimeOnlyThreeFrequency (14)
passed final foreground leaf audits3905/55141/68933. Existing-source helper
audits81094/69251 passed. All34 new/exposed declarations passed axiom
probe44712: standard axioms only, no diagnostics. Index46234 exit0 and every
public name present; all three imports wired once. Lint52691 exit1 only29
unrelated unreachable modules; no proof-debt/new-leaf finding. P2/P3
bag-prime-only-rational-three-frequency-source and frontier C28.56ag.2 now
record the exact closure. No owned job remains; completed scratch sources
removed, logs/JSON retained. RH goal ACTIVE.

Evaluation: prime-power removal and full fixed-test source/interchange are
now proved. The central cubic cancellation has NOT advanced to a signed
estimate. Next work must target the critical finite-band physical source,
its literal contraction projectors and the COMPLETE transverse action;
another fixed-test convergence theorem would not address that gap.

## continuation01a7 — exact finite critical physical source

Prior turn PROGRESS: ag.2 closed source-level prime-power removal, but no
signed cubic saving. Current proof target is the literal critical finite
atom source and its exact whole-band physical action with both contractions.
Use the existing finite atom identity and the derivative of EACH finite
weight at zero: -mu(d)*log(d)/d. Finite-sum limits identify the critical atom
Fourier value on the covered band from the already proved Wold derivative
and exact squarefree source identity. This avoids assuming a growing-test
limit or adding a von Mangoldt/gcd classification premise. The rational
translation projectors will impose the actual p=r and q=r exclusions.
Hard remaining target is still the COMPLETE signed transverse action at
o(N/log(N)^2), followed by growing moments and common-height self-return.

Critical finite source scratch62391 and production23109 passed with no
diagnostics. The six public declarations in ChiRamanujanCriticalFiniteAtoms
include the actual atom-weight derivative and exact prime-log Fourier value
on the entire covered band. New module wired once; final axiom/index/lint
audit pending. No signed cancellation estimate claimed.

Deep search64072 nonpartial65666/65666 had source-only/pending compiler data
and incomplete background refresh. All20 candidates/20 source statements,
its spectral-finiteness transfer idea and torsion-descent ingredients were
inspected; the transfer/ingredient proposals are inapplicable. Lexical
rephrase95006 recovered the current finite source and Wold derivative APIs,
whose actual sources were read. No numerical evidence or recalled theorem
substitutes for these sources. Development problems were a deprecated
finite-sum limit alias, universe inference in probes, and definitional
composition matching; all resolved without weakening the statement.

## ag.3 completed audit checkpoint — continuation01a7

The COMPLETE original physical cubic identity is now formalized, including
both literal contractions and their intersection. All real N>=1 are covered;
there is no damping approximation, prime mask in the test, selected packet,
or missing physical factor. CriticalFiniteAtoms (6 declarations),
FiniteContractionProjectors (11), and PrimeGaussianCubicCriticalAtoms (7)
passed final leaf audits23109/69239/21647 without diagnostics. All24 public
declarations passed axiom audit90494 with standard axioms only. Index19426
passed with all names present and all three imports wired once. Lint43522
reports33 unrelated unreachable modules only; global lint is not clean.
Completed scratch sources removed; all owned jobs terminal. P2/P3
bag-critical-physical-cubic-atom-identity and frontier C28.56ag.3 record closure.

Evaluation: the exact additive physical bridge and contraction matching are
closed; the hard signed growing-action estimate remains entirely open.
Next conjectures must address that complete action, not another fixed-test
limit or generic quadratic-to-cubic promotion. All integer lifts, near-cone
width, tails and actual growing smooth-edge costs must be retained. No
multiplicative six-zeta axis matching follows from this additive identity.
RH and the downstream growing moments, moving cofactors and common-height
self-return remain open. Goal ACTIVE.

## continuation01a8 — full transition, no signed saving yet

Follow-on paper attempt is recorded in bag-complete-hyperbolic-transition-action.md.
The current edge comparison and a simple stationary Taylor expansion demand
incompatible sufficient edge-width regimes. This invalidates that proposed
proof, not BAG or all stationary methods. The candidate replacement retains
the exact Fourier multiplier exp(-2*pi*i*r*xi*eta), the full physical edge
transition, every Poisson lift and both literal contractions. The hard goal
is its complete source-specific signed aggregate; operator unitarity alone
or another exact representation will not be counted as a cubic saving.
Four corpus searches completed and were inspected, actual sources read;
no new Lean declaration or cancellation theorem in this follow-on attack.
See the new card for exact formula, proof mechanism and remaining obligations.

## continuation01a9 — exact full-window continuum transition

C28.56ag.4 is formalized in two leaves with19 public declarations. The full
hyperbolic Fourier multiplier retains the actual Gaussian/logarithmic
slices, physical-window Mellin line and edge transitions, with absolute
convergence proved. The unconditional family retains the existing
negligible sharp/smooth error. Production59166/41307, axiom56220 and
index35593 passed; lint11175 has26 unrelated unreachable modules. See
P3:bag-full-window-hyperbolic-transition for exact audits and scope.
This closes a continuum construction, not full lattice transfer or signed
cubic cancellation. Every lift, r-variable and literal contraction remains
in the next complete assembly. Overall RH goal ACTIVE.

## continuation01aa — full three-coordinate Fourier family

C28.56ag.5 constructs the actual compact physical amplitude, proves exact
integer coefficient matching and all-shift absolute Fourier lattice
summability. One leaf,12 declarations, production19066/axiom14865/index92591
passed; lint13216 has28 unrelated unreachable modules. P3:
bag-full-physical-fourier-lattice-summability gives the precise scope.
P1:bag-complete-lattice-fourier-transfer tracks complete Poisson matching
and full finite critical atom/projector assembly. Fixed-scale convergence
does not imply the signed growing-action estimate. RH goal remains ACTIVE.
