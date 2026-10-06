# BAG: complete signed source outside the shrinking cone

- **ID:** bag-global-conormal-localization-26az
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** bag-covered-global-defect-cancellation.md; ChiPrimeGaussianCubicDefectAction; ChiCubicPhysicalAmplitudeBudgets.
- **Statement:** The complete critical source, with both noncontraction projectors and every Fourier lift, has negligible action on the part of the actual moving Fourier amplitude outside a shrinking neighborhood of its stationary cone.

## Hard target and scope

BAG remains the route. Full original cubic cancellation is open; this
attempt must produce a uniform signed estimate for an entire global sector,
not another pointwise kernel identity. Near-cone arithmetic cancellation,
growing moments/cofactors and deterministic common-height return remain
separate hard obligations. The COMPLETE exterior-sector capstone is now formalized in
ChiCubicExteriorSource. The original sharp reduction to the entire
retained near-cone action is checked in ChiCubicNearConeReduction. The
remaining arithmetic target is tracked in bag-entire-near-cone-arithmetic.md.

Let A_N be the literal controlled-edge physical Schwartz amplitude, with
edge width N^(1/4), as in the existing sharp/smooth transfer. Let
D(xi)=xi_2+xi_0*xi_1. Choose a fixed smooth scalar cutoff chi, equal to one
on [-1,1] and zero outside [-2,2]. The proposed exterior test has Fourier
transform (1-chi(N^(1/8)*D(xi)))*Fourier(A_N)(xi).
The target is o(N/log^2 N) for the ENTIRE critical atom action of both
original projectors applied to its complete lifted Fourier test. No lower
bound on a nonzero rational defect is available or assumed. Every growing
modulus and every source coefficient remains in this target.

## Corpus basis and proof obligations

The all-integer critical source Fourier law is the distinguished-prime
multiplier (ChiRamanujanCriticalDistinguishedPrime). Its damped precursor
has a source-uniform polynomial coefficient bound
(ChiRamanujanPrimeOnlyThreeFrequency), and weighted Schwartz lattice
summability is proved in ChiRamanujanThreeFrequencyLattice. These suggest
bounding the aggregate action by Fourier coefficients, avoiding the huge
sum of absolute atom weights. This bound alone does not pay the actual
moving test.

The actual normalized slice has every L1 derivative budget, including the
selected edge cost, in ChiCubicPhysicalAmplitudeBudgets. Its two-dimensional
reciprocal kernel has all-order tangential decay, but this is not yet the
required three-dimensional normal estimate.

For r!=0 write K(p,q,r)=exp(2*pi*i*p*q/r)/r. Direct differentiation gives

    L K=0,             L=partial_r-i/(2*pi)*partial_p partial_q,
    Fourier(L f)=2*pi*i*D*Fourier(f),
    L(w K)=K*(partial_r w+(p/r)*partial_p w+(q/r)*partial_q w
                           -i/(2*pi)*partial_p partial_q w).

These calculus steps belong to the pending moving-test proof, not the
checked source estimate. Repeated
transport must retain all derivatives of the actual W, V, logarithms,
reciprocal and selected edges. The physical edge derivative costs
N^(-1/4) per first derivative; a mixed derivative costs N^(-1/2).
Polynomial losses from Fourier derivatives and the shrinking cone cutoff
must be paid by sufficiently many normal iterations, with constants
independent of N and the complete source modulus. Frequency infinity
also needs a weighted estimate; a compact-frequency argument alone is
insufficient.

Both projectors act AFTER forming the exterior test. Their shifts do not
preserve D. Thus a bound for one unshifted grid or one cone sheet cannot
be substituted for the full projected action. On integer Fourier
coefficients the masks have norm at most one, offering a way to retain
all shifts without estimating atom total variation.

The near-cone remainder is deliberately not assumed negligible. Inverting
D there merely asks for a singular arithmetic source estimate; no such
inverse-norm or restriction premise may be introduced.

## Plan and gates

1. Establish the exact normal transport for the literal amplitude and
   source-uniform complete Fourier-coefficient control.
2. Prove all-order weighted exterior estimates with the actual moving
   edges; sum the COMPLETE signed source and both projectors.
3. Audit the resulting unconditional sector theorem in Lean, then attack
   the retained near-cone arithmetic action. Do not count step1 alone as
   closure of a hard analytic sector.

- [x] 0 -> 1: actual source and unconditional sector target specified.
- [x] 1 -> 2: full weighted estimate and all source exchanges proved.
- [x] 2 -> 3: direct leaf/axiom audits, unique umbrella wiring, own lint findings zero; unrelated repository lint failures recorded below.

## Log

- 2026-10-06,26az: active conjecture. Fourier-coefficient boundedness by
  itself loses powers at the moving cone. The new source-control leaf
  proves the cutoff-independent bound with both projectors. The full
  exterior estimate remains under formal audit; no hard-sector closure
  or RH proof is claimed.

## Full exterior estimate: paper derivation under formal audit

This calculation uses the L1 derivative budgets of the ACTUAL normalized
slice, not a new regularity hypothesis. Write epsilon=N^(-1/8),
H=N^(1/4), delta=H/N=N^(-3/4), and L_N=log N. All assertions below are
for sufficiently large real N. Constants may depend on fixed derivative
orders, never on N, the source prime set P or projector level D0.

1. For every j, the existing normalized-slice L1 bound at order j+1
   gives sup_x |F_delta,h^(j)(x)| <= C_j delta^(-j). Indeed integrate
   F^(j+1) from a point below its support, where every derivative is
   zero, and bound by its full L1 norm. Taking h=1/log N and using the
   exact physical-slice identity yields

       |partial_x^j slice_N(x)| <= C_j L_N^(-1) N^(-j/4).

   This includes the sharp-edge transition cost. It is not a uniform
   bound in the normalized edge width without that cost.

2. Factor A_N=w_N K, where K=r^(-1)e(pq/r) and w_N contains 2*pi,
   all THREE actual slices (with the third conjugated), and
   W(pq/(r*N)). On the physical box [N,2N]^3, every jth derivative
   of W(pq/(r*N)) is O_j(N^(-j)); its argument stays in a fixed
   compact interval. Product and chain rules therefore give

       |partial^alpha w_N| <= C_alpha L_N^(-3) N^(-|alpha|/4).

   The cutoff factors give smooth zero extension across the box.
   Reciprocals are differentiated only where r>=N; outside a fixed
   neighborhood of this box the entire amplitude and all jets vanish.

3. With L and T from the transport identity above, induction gives
   L^k A_N=K T^k w_N. Coefficients p/r,q/r and all their derivatives
   are O_alpha(N^(-|alpha|)). Each first derivative in T gains
   N^(-1/4), and its mixed derivative gains N^(-1/2). Leibniz induction
   on k, simultaneously for every multiindex alpha, proves

       |partial^alpha T^k w_N|
           <= C_(k,alpha) L_N^(-3) N^(-(k+|alpha|)/4).

   Derivatives of K on this box are O_alpha(N^(-1)); its phase has
   bounded first derivatives and higher derivatives cost powers of
   N^(-1). Hence f_(N,k)=L^k A_N has the same compact support and

       |partial^alpha f_(N,k)| <= C_(k,alpha) L_N^(-3) N^(-1-k/4).

4. Differentiating the Fourier transform j times inserts coordinate
   moments of degree j. Integrating by parts in physical coordinates
   then gives, for EVERY fixed nonnegative m,j,

       sup_xi (1+|xi|)^m |partial_xi^j Fourier(f_(N,k))(xi)|
           <= C_(k,m,j) L_N^(-3) N^(j+2-k/4).

   For a radial polynomial weight use a finite sum of coordinate
   monomials; derivatives of the moments only reduce their N-power.
   The volume N^3 and amplitude N^(-1-k/4) are both included here.

5. Set g_k(t)=(1-chi(t))/t^k, smoothly extended by zero near t=0.
   For k>=1, every derivative of g_k is bounded. The exterior Fourier
   test equals

       epsilon^(-k) (2*pi*i)^(-k)
           g_k(D(xi)/epsilon) Fourier(f_(N,k))(xi).

   Chain rule for the quadratic D gives, for every multiindex beta,

       |partial^beta g_k(D(xi)/epsilon)|
           <= C_(k,beta) epsilon^(-|beta|) (1+|xi|)^|beta|.

   Thus the exterior test is Schwartz, including frequency infinity.
   Applying item4 with j<=9 and weight m<=13 controls all Fourier
   derivatives needed for the physical seminorms of orders (a,0),
   a<=9. Weight4 is integrable in dimension3. Fourier inversion and
   integration by parts give for its inverse transform B_N

       sup_x (1+|x|)^9 |B_N(x)|
           <= C_k L_N^(-3) epsilon^(-(k+9)) N^(11-k/4)
            = C_k L_N^(-3) N^((97-k)/8).

   No exchange of an N-limit with the source or lattice sum occurs.

6. At the integer lattice, the product weight
   w(n)=(1+|n_1|)(1+|n_2|)(1+|n_3|) satisfies w(n)<=C(1+|n|)^3.
   Therefore |B_N(n)|w(n) is bounded by the item5 constant times
   w(n)^(-2), up to a fixed norm-comparison factor. The latter sum
   converges as a product of three one-dimensional square tails.
   The complete critical-source bound proved in the new Lean leaf
   applies to the resulting Schwartz function in product coordinates,
   retaining BOTH projectors and every integer frequency.

7. Choosing a fixed k=100 gives a bound

       |complete projected source on B_N|
           <= C N^(-3/8)/log^3 N,

   uniformly in P and D0. This is stronger than the required cubic
   normalization. The choice100 is only a convenient finite order;
   no claim about optimal exponents is relevant to this argument.
   Full Schwartz Poisson identifies the periodic Fourier test of B_N
   with its complete lifted Fourier test. Its justification is absolute
   Schwartz periodization plus Fourier coefficient inversion; the
   current local full_poisson theorem only exposes compact physical
   inputs, so its Schwartz extension must still be built in Lean.

The calculation leaves the ENTIRE shrinking near-cone test
chi(D/epsilon)*Fourier(A_N) in place. Projector translations are applied
only after this split, so no false claim of cone invariance is used.
This does not identify that remaining tube with the already closed exact
positive cone. Such an identification would require a new arithmetic
estimate for all near-cone defects, including zero/negative sectors.

Formal status at30az: source-uniform control, all-order normalized
transport/phase jets, exact physical conjugation, global physical jets,
weighted Fourier control, the WHOLE shrinking multiplier, arbitrary
polynomial decay of EVERY physical exterior Schwartz seminorm, full
Schwartz Poisson and COMPLETE projected-source attachment are checked.
The same selected cutoff's sharp/smooth transfer was already checked.
The original sharp reduction to the ENTIRE near-cone action is checked.
ENTIRE near-cone arithmetic cancellation remains open and is now tracked
in bag-entire-near-cone-arithmetic.md.

## Checked source-control component

ChiRamanujanCriticalSourceControl proves, without analytic premises:

- ramanujanDistinguishedPrimeMultiplier_uniform_bound: for EVERY finite
  prime-source set P and EVERY natural n, its literal coefficient lies
  between zero and log(n+1), including n=0 and uncovered n. If P has no
  prime dividing n all entries vanish. If p in P divides n, every other
  distinguished entry vanishes because its product contains 1-U_p(n).
  The remaining entry is bounded using p<=n unless p^2 divides n, in
  which case it vanishes too.
- ramanujanCriticalTripleAtomAction_projected_periodic_bound: for EVERY
  P,D and Schwartz Phi, the norm of the COMPLETE signed rational source
  after BOTH original projectors is at most sum_n |Phi(n)|w(n). The
  bound has no cutoff/modulus constant and no norm of the atom weights.
  The exact all-integer projector either kills or retains a phase;
  D=0 is handled separately. Continuity of the finite source/projector
  functional on the product space justifies mapping the full summable
  Fourier series. No analytic summability premise is accepted.

Scratch proof passed; final direct leaf command passed with empty output:

    lake --old env lean GaloisForLFunctions/RHTower/ChiRamanujanCriticalSourceControl.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ChiRamanujanCriticalSourceControl.olean

Both public declarations have only propext, Classical.choice and Quot.sound
in the separate /tmp axiom audit. The leaf is wired once into RHTower.lean;
no umbrella build was run. This is an actual full-source analytic bound,
but its right side must still be paid for the moving exterior test.


## 27az — formal normal transport, same active conjecture

Previous26az was verified progress on full source control, not hard-sector
closure. This continuation stays on the actual exterior proof. Corpus
search normal-transport27az is nonpartial67714 indexed, index1264670,
coverage/current1264676, compiler pending51364/stale2660/error2, no inventory
errors. All20 candidate statements,20 source arguments and the ingredient
proposal were inspected. Generic compact-support bounds do not give the
required moving-width constant; unrelated sphere-packing decay was not
substituted for it.

A useful strengthening of the paper induction is to keep physical H free:
for N>=exp1 and 1<=H<N/2, the literal slice has EVERY pointwise derivative
bounded by C_j/(log N*H^j). The first direct scratch proof of this exact
statement passed. It follows from the actual L1 budget at order j+1,
zero jets below support, interval FTC, and exact positive dilation. Both
cutoff-width and logarithmic parameters remain uniform; no new bound is
assumed. This avoids mixing fractional N-powers into the transport step.

For the transport induction, retain the stronger target

    |partial^alpha T^k w_(N,H)|
       <= C_(k,alpha)/(log^3 N*H^(k+|alpha|)).

Coefficient p/r,q/r jets cost N^(-j)<=H^(-j), and the mixed derivative
costs H^(-2)<=H^(-1). Thus the same fixed-order induction should work for
ALL admissible H>=1; only the final exterior application selects H=N^1/4.
The actual all-order transport bound remains to be formalized. Scratch
normal-operator work checks the full Fourier symbol and reciprocal kernel
annihilation; neither identity is counted as sector cancellation.

27az checked transport producer: ChiCubicPhysicalSliceJets proves BOTH
all-order normalized slice bounds C_j/delta^j and the literal physical
bounds C_j/(log N*H^j), uniformly in the actual admissible parameters.
ChiCubicNormalSymbol proves the exact all-iterate Fourier symbol, exact
reciprocal-phase annihilation and complete actual amplitude factorization.
ChiCubicNormalTransportJets proves, for EVERY k,n, a constant C_(k,n)>0
such that the literal normalized coupled weight w_(delta,h) satisfies

    ||D^n (T_t^k w_(delta,h))(v)|| <= C_(k,n)/delta^(n+k)

on the full cube [1,2]^3, uniformly for 0<delta<1/2, 0<=h<=1 and
|t|<=delta. Here T_t=partial_2+(v0/v2)partial_0+(v1/v2)partial_1
-i*t/(2*pi)partial_0 partial_1. Smoothness of every actual iterate on
v2>0 is also produced. The finite-order product induction retains all
three actual Gaussian/logarithmic slices and the coupled height window;
its mixed term consumes TWO derivatives but its actual coefficient
|t|<=delta restores one power. No generic jet/cancellation premise.
All three production leaves passed direct lake --old env lean audits,
with own oleans only and empty logs, and are wired once into the umbrella.
This is formal progress on the moving transport input; exterior Fourier
control, complete Schwartz Poisson attachment and near-cone arithmetic
are still unpaid. Do not label the exterior or original cubic closed.

The next source search /tmp/bag-physical-transport-search-27az.json is
partial (semantic_retrieval unfinished): 67812 indexed, index1265036,
coverage1265039/current1265046, compiler pending51461/stale2660/error2,
no inventory errors. All20 candidate statements and20 source arguments
plus the ingredient proposal were inspected. Directional product/local
congruence arguments apply; Suzuki phase transport and unrelated dilations
do not supply this amplitude's moving estimate. Work continues on exact
conjugation for the literal normalized phase and then physical dilation.

27az exact attachment checked: ChiCubicNormalConjugation proves EVERY
normalized normal-operator iterate on K_N*w_(delta,h) equals
K_N*T_(1/N)^k w_(delta,h) on positive height, using produced regularity.
It also proves the literal physical amplitude at N*v is exactly
2*pi/(N*log^3 N)*K_N(v)*w_(H/N,1/log N)(v). Scratch57376 and final direct
leaf39411 passed with empty logs. No quotient-rule axiom was introduced:
the real-domain/complex-target Fréchet derivative uses multiplication by
the inverse and the scalar inverse chain rule. The exact product-rule
terms cancel, including the derivative of the reciprocal prefactor.

Next hard continuation: intertwine the physical Schwartz normal operator
with positive dilation; prove EVERY ordinary physical jet of its k-th
iterate is bounded by C_(k,n)/(N*log^3 N*H^k) for 1<=H<N/2. This follows
on paper from the now-checked transport jets and all-order phase jets:
normalized phase order j costs N^j, transport order n-j costs
(H/N)^(-(k+n-j)), and the physical n-th derivative contributes N^(-n).
The surviving H^(-(n-j)) is <=1. Support stays in the full physical cube.
Weighted Fourier estimates, the complete shrinking multiplier and full
Schwartz Poisson/source attachment then remain; no near-cone restriction
norm or arithmetic cancellation is supplied as a premise. Keep the
ENTIRE retained near-cone test and both projectors. Do not revisit already
closed fixed-radius packets or count these attachment identities alone
as new cubic cancellation.

Final27az audit: ALL10 public theorems across the four leaves have only
propext, Classical.choice and Quot.sound (separate scratch47708).
Index44681 passed. Authoritative lint13206 reports367 large-file warnings
and17 unreachable modules outside this work; no finding names any new
leaf. All four imports occur exactly once. All owned27az processes are
terminal. Six scratch Lean sources and one assembly text fragment were
removed; diagnostic logs and search JSON retained. No numerical experiment,
subagent, admission/new axiom, heartbeat override, full/umbrella build,
commit or push. Frontier records the exact new producer; RH goal active.

## 28az — physical all-jet producer, same exterior conjecture

Previous27az is verified progress: actual normalized transport jets and
exact iterated phase attachment. Complete exterior and near-cone estimates
remain open. Current plan: (1) pay all ordinary reciprocal-phase jets,
(2) intertwine physical normal differentiation and exact dilation and
combine with the actual transport bound, (3) pay weighted Fourier jets
and the full exterior source. No numerical experiment or route switch.

Phase-jet conjecture: ||D^n K_N(v)||<=C_n N^n on [1,2]^3 for N>=1.
A useful exact renormalization comes directly from the literal phase:
put tau=1/N and write K_N(v+tau*w)=exp(2*pi*i*N*v0*v1/v2)*F(tau,v,w),
where

 F = exp(2*pi*i*(v0*w1+v1*w0+tau*w0*w1-(v0*v1/v2)*w2)
                    /(v2+tau*w2))/(v2+tau*w2).

Unlike the original N-family, this is smooth through tau=0 on a fixed
neighborhood of [0,1]x[1,2]^3x{0}. Its full jets there are compactly
bounded; exact affine composition transfers the bound to N^-n D^n K_N.
This supplies an actual compact parameter family, rather than assuming a
uniform bound on an unbounded oscillatory parameter. Audit against corpus
composition APIs before choosing the shortest formal induction.

28az phase producer checked: actual normalized K_N has ALL Frechet jets
<=C_n N^n on the whole cube, N>=1. Scratch39468 and final leaf58341 passed
with empty output. ChiCubicReciprocalPhaseJets is wired once. The proof
uses the corpus norm_iteratedFDerivWithin_comp_le directly: real osc(x)
=exp(i*x) has norm1 at EVERY derivative; the actual geometric phase
2*pi*v0*v1/v2 has compactly bounded jets; scaling by N and the composition
bound yield C_n N^n, and a full Leibniz sum retains 1/v2. The translated
compact-parameter identity above remains an alternative paper derivation;
it was not needed for this checked producer.

Initial deep phase search was partial(decomposition), indexed67864,
index1265351,coverage/current1265353,compiler pending51512/stale2660/error2;
all candidate/source statements inspected but its polynomial/all-order
hits did not provide the estimate. Exact lexical followup returned zero
hits. Rephrased hybrid actual composition-symbol search was nonpartial,
indexed67865,index1265396,coverage/current1265397,compiler pending51513,
stale2660/error2; all20 candidates and20 source arguments inspected.
It returned the exact composition estimate now verified in Lean. No
inventory errors. Physical normal-operator dilation is being attached.

28az physical producer checked: ChiCubicPhysicalNormalJets proves EXACT
physical normal-iterate conjugation and, for EVERY k,n, a constant C_(k,n)
with ||D^n L^k A_(N,H)(x)||<=C_(k,n)/(N*log^3 N*H^k), for EVERY x in
physical space, N>=exp1, 1<=H<N/2. No support or analytic premise: all
jets outside the literal closed cube [N,2N]^3 are proved zero. Scratch37111
and final leaf76023 passed with empty output; own olean, wired once.
Ordinary derivatives of the complete oscillation are paid, not discarded.

The weighted-Fourier continuation uses a stronger quantifier requirement:
for each recipient Schwartz weight/order (p,n), choose a finite polynomial
degree M BEFORE choosing normal order k; then for EVERY k the actual
Fourier seminorm is <=C_(p,n,k)*N^M/(N*log^3 N*H^k). Corpus continuity
of Fourier gives finitely many physical seminorms independent of k;
the new global physical jet bound plus exact cube support pays them all.
The degree need not be numerically optimized. The shrinking multiplier
has a fixed finite derivative cost in epsilon^-1 independent of k,
so a sufficiently large fixed k can pay the whole exterior after this
finite family is selected. This formal route does not assume the sharper
N^(j+2) Fourier bound or the convenient paper choice k=100.

Weighted-Fourier corpus search is nonpartial:67868 indexed,index1265505,
coverage1265515/current1265516,compiler pending51515/stale2660/error2,
no inventory errors. All20 candidate/source statements and ingredients
inspected. Seminorm.bound_of_continuous and the corpus's finite-seminorm
Fourier mechanism apply; one-dimensional Deninger cap assumptions do not.
The corresponding three-dimensional actual producer is now in audit.

28az weighted-Fourier scratch29814 passed with empty output. New
ChiCubicNormalFourierBudgets proves EVERY physical seminorm of L^k A
<=C_(k,p,n) N^p/(N log^3 N H^k), and EVERY Fourier seminorm has the
quantifiers forall(p,n), existsM, forallk, existsC_(p,n,k)>0, uniformly
in N,H. Its bound is C N^M/(N log^3 N H^k). This quantifier order is
essential: M is fixed by the Fourier continuous map BEFORE k, so it
cannot cancel the gain from more normal differentiation. No source-norm,
uniform jet or Fourier-budget premise. Final direct leaf78072 passed with
empty output, own olean only; wired once.

Exact next multiplier obligation (same full exterior conjecture): choose
one actual smooth chi with chi=1 on [-1,1] and support in [-2,2]. For
k>=1 prove g_k(t)=(1-chi(t))/t^k has bounded derivatives of EVERY order,
including across zero. Outside [-2,2] it is the literal inverse power;
inside compact transition its smooth jet bound is paid. On the zero
neighborhood it is identically zero. With D=xi2+xi0*xi1, composition gives

 ||D^m[g_k(D/epsilon)](xi)||
     <=C_(k,m) epsilon^(-m) (1+||xi||)^m, 0<epsilon<=1.

A finite Leibniz sum therefore controls EVERY Schwartz recipient seminorm
of g_k(D/epsilon)*Fourier(L^k A) by epsilon^(-n) times finitely many
Fourier seminorms, whose indices are independent of k. Exact normal
symbol gives the entire exterior transform by multiplying also
(2*pi*i)^(-k) epsilon^(-k). Continuity of inverse Fourier then selects
finitely many such recipients, still independent of k. Their maximum
polynomial degree M and maximum derivative cost R give

 seminorm(exterior) <= C_k N^(M-1) H^(-k) epsilon^(-(k+R))/log^3 N.

For H=N^(1/4), epsilon=N^(-1/8), this is
C_k N^(M-1+(R-k)/8)/log^3 N. Choose a sufficiently large fixed k only
after M,R are fixed; any prescribed polynomial decay follows. No numeric
optimization, finite frequency truncation, rational separation, source
absolute mass or exchange of limits is needed. Still required: complete
Schwartz Poisson/source attachment and the original admissible-cutoff
edge transfer. ENTIRE shrinking near-cone arithmetic remains unpaid.

28az final audit: all three direct leaf audits passed. Axiom audit32030
passed for all seven public theorems: only propext, Classical.choice,
Quot.sound. Index20420 passed. Authoritative lint17292 reported16
unreachable modules outside this work and367 size warnings; no findings
in these three leaves. Owned scratch sources removed after all owned
processes terminated. No full/umbrella build, numerical experiment,
heartbeat override, new axiom, commit or push.

## Continuation 29az: the whole shrinking multiplier

Route BAG. Last continuation paid all physical normal jets and all
weighted Fourier seminorms, with polynomial degree fixed before normal
order. This contributes directly to the hard complete exterior estimate.
Plan: prove global bounded jets for an actual smooth inverse-power cutoff;
compose with the full signed quadratic defect, retaining the whole
frequency space; use the paid Fourier budgets to obtain the complete
exterior Schwartz estimate. Then attach the full arithmetic source.
The entire near-cone arithmetic, growing moments/cofactors and common
height return remain open. Research search is running before new code.

29az search98820 terminal0: deep search of smooth shrinking-defect
inverse-power multiplier, nonpartial67872 indexed;index1265670,
coverage1265672/current1265679; compiler pending51519/stale2660/error2,
no inventory errors, semantic coverage not measured. All20 candidate
statements,20 source arguments and proposed ingredients inspected.
Ranked L2/scattering multipliers do not pay the actual Schwartz estimate;
no assumptions transferred. Exact source inspection found ContDiffBump,
iter_deriv_zpow, bounded composition and Schwartz product seminorm APIs.

29az inverse-power scalar scratch37184 passed with empty output: actual
chi=ContDiffBump(0),inner1/outer2; g_k=(1-chi)/t^k is globally smooth and
EVERY jet is bounded on the entire real line, all k including0. Zero
is handled by an exact zero germ. On the compact transition use smooth
compactness; outside[-3,3] use exact zpow derivative and |t|>=1. No
inverse-defect or frequency cutoff premise. Next composition proof uses
the actual polynomial defect's temperate growth to select a finite degree
BEFORE k; no sharp degree optimization is needed. Full product bound
selects a finite Schwartz-seminorm rectangle independently of k.

29az complete multiplier and parameter estimate: final direct leaf55171
ChiCubicExteriorMultiplier passed with empty output, own olean and unique
umbrella import. The full inverse-power cutoff has bounded jets on the
whole line. For every maximal jet order n, the actual composed multiplier
has <=C_(n,k) epsilon^-n (1+norm xi)^L_n bounds for ALL jets i<=n, with
L_n selected BEFORE k. Its multiplication on Schwartz space costs one
finite input rectangle independent of k. This avoids numerical exponent
optimization while preserving the decisive normal-order gain.

Final direct leaf28138 ChiCubicExteriorEstimate passed with empty output,
own olean and unique umbrella import. Exact FULL Fourier factorization,
including D=0, yields EVERY physical exterior seminorm <=
C_k N^M/(N log^3 N H^k epsilon^(k+R)), with M,R BEFORE k. No truncation,
excluded transition band, positive-sheet restriction or source norm.
The specialization H=N^(1/4),epsilon=N^(-1/8) is being audited: choose
k=8*(M+a)+R after recipient and desired decay order a. Their combined
power H^k epsilon^(k+R)=N^(M+a); N log^3 N>=1 gives <=C/N^a.
Admissible scales include EVERY sufficiently large original natural N.

Source recheck: primeGaussianCubic_controlled_cutoff_negligible_error
in ChiPrimeGaussianCubicSharpEdges already proves the sharp/smooth
transfer for the SAME literal controlled cutoff H=N^(1/4). That obligation
was overlisted in28az; no rebuilding or new premise is needed. The
full-Schwartz lifted source identification still needs attachment.

Poisson search27880 partial(decomposition worker disconnected),67965
indexed,index1265922,coverage1265916/current1265923;compiler pending51611,
stale2660/error2,noinventoryerrors. All20candidate/source statements and
ingredients inspected. Focused Poisson search24186 nonpartial67967,
index/coverage1265955,current1265956;compiler pending51613/stale2660/error2,
noinventoryerrors. All20candidate/source statements inspected. Mathlib
supplies one-dimensional Schwartz Poisson; local3D theorem requires
compact physical support, which the canonical exterior does not have.
No unwarranted transfer of that premise. Weighted triple domination
ramanujanTripleSchwartz_weighted_le gives a fixed finite seminorm, and
ChiRamanujanCriticalSourceControl retains BOTH original projectors.

29az density search74472 terminal0 with partial semantic coverage:
67969 indexed,index1265972,coverage/current1265977;compiler pending51615,
stale2660/error2,noinventoryerrors; semantic Qdrant deadline. All20
candidate/source statements and ingredients inspected. The corpus has
one-dimensional compactSupportApproximation_sub_seminorm_le; its type
does not cover BAGPhysicalSpace. This is a useful proof mechanism, not
an applicable three-dimensional density theorem.

Next source-attachment proof path, without changing the sector target:
For a fixed physical Schwartz f, construct f_R=chi_3(x/R)f using an actual
smooth compact bump equal1 near0. For every recipient seminorm, the j=0
Leibniz term is zero for normx<=R and is bounded using one additional
Schwartz weight outside; j>0 cutoff jets carry R^-j<=R^-1. This produces
Schwartz convergence f_R->f with a fixed finite seminorm bound, rather
than assuming density. Fourier continuity transfers convergence. Weighted
lattice sampling of f_R and Fourier(f_R) is continuous by an explicit
summable polynomial lattice majorant (the existing 3D proof uses products
of (1+n_i^2)^-1). Passing through the already proved compact twisted
Poisson identity gives full Schwartz twisted Poisson, every real shift.
Then identify ramanujanTriplePeriodicTest in product coordinates with
the complete bagLiftedFourierTest. Existing source control and the fixed
ramanujanTripleSeminorm rectangle(9,0) pay the entire P,D-uniform action.
No source limit is exchanged with N; both projectors remain after split.
This remains a pending Lean proof, not a claimed Poisson closure.

29az actual rapid decay CLOSED: final direct leaf40677
ChiCubicExteriorRapidDecay passed with empty output. For EVERY p,n,a,
existsC>0,forall admissible N, seminorm_(p,n)(B_N)<=C/N^a. The actual
admissible scale domain contains EVERY sufficiently large original
natural N. The bound chooses k after the recipient and requested decay;
there is no extra analytic premise or assumed source norm. Both the
complete shrinking multiplier and the full physical-space exterior
estimate are now formalized. All three final commands used
lake --old env lean <leaf> -o <own olean>; all three imports unique.
Axiom audit70209 passed for all12 public theorems, only propext,
Classical.choice,Quot.sound. Index36171 passed(6changed,0removed).
Authoritative lint86066 exited1 with20 unrelated unreachable modules;
zero findings in the three new leaves. All owned builds/searches/audits
are terminal, and all eight owned scratch/assembly sources were removed;
diagnostic logs and search JSON are retained. The full projected-source
sector capstone and ENTIRE near-cone arithmetic are still open.

## Continuation30az — full projected-source attachment

Route BAG. Previous29az is verified progress: the complete actual moving
exterior is rapidly decreasing in EVERY physical Schwartz seminorm.
Current hard target is still the original full projected arithmetic
exterior, then ENTIRE near-cone arithmetic cancellation. Source projection
norm is already paid; full3D Schwartz Poisson remains the immediate gap.
Plan: inspect actual normal-convergence/fundamental-domain APIs, prove
Poisson for all physical Schwartz functions, attach the uniform weighted
source bound and the actual rapid-decay family; final direct audits,
axioms, umbrella wiring,index/lint and frontier update. No new premise,
finite-frequency approximation, full build or numerical experiment.
The pending compact-cutoff approximation proof from29az is one viable
paper mechanism. Direct absolute periodization plus fundamental-domain
integration may supply the SAME full Schwartz identity with fewer new
intermediate theorems; this will be decided from current source evidence.

30az corpus search87717 nonpartial67971 indexed,index1266057,
coverage1266064/current1266065;compiler pending51616/stale2660/error2,
noinventoryerrors. All20candidate/source statements and ingredients
inspected. Search returned SpherePacking's PoissonSummation_Lattices;
its actual body is `sorry`, so it is inadmissible and is NOT imported.
Current verified source APIs support direct normal periodization.

The direct proof of the SAME full3D Poisson identity succeeds at its
analytic integration stage: bounded-translation summable majorants give
continuous periodization; integral_tsum with the finite-volume fundamental
cube pays the full integration exchange. Character multiplication retains
the same majorant. Torus coefficient inversion then proves the identity.
Scratch10950 and final direct existing leaf66849
ChiCompactLatticePoisson passed with empty output, including unchanged
compact theorem and new poisson_of_summable_translates. No heartbeat
increase: one earlier metavariable inference timeout was fixed by correctly
specifying majorant/minorant arguments. This generic helper is not yet an
unconditional Schwartz closure: actual Schwartz majorants/integrability
are now being audited in the consuming leaf. Compact approximation from29az
remains a valid alternative paper proof, not a failed mathematical route.

30az full Schwartz Poisson CLOSED: ChiCubicSchwartzPoisson final direct
leaf51816 passed with empty output and own olean; unique umbrella import.
For EVERY physical Schwartz f and EVERY real shift a, the complete
shifted Fourier triple sum equals the complete twisted physical lattice
sum. No compact support or summability premise. Actual uniform translate
majorants are proved from the fixed Schwartz weight6 rectangle and
products of (1+abs(n_i))^-2; both integration and Fourier coefficient
inversion include all translates. The inadmissible SpherePacking result
was not used. Remaining source attachment now has no Poisson gap.

30az complete arithmetic exterior scratch29711 PASSED. Full Poisson plus
continuous product coordinates and the fixed weighted lattice seminorm
prove a single P,D-uniform physical Schwartz source bound. Consequently
EVERY natural a has C_a with the COMPLETE exterior source norm<=C_a/N^a.
Final production audit10040 is running. The next exact reduction is on
the ORIGINAL natural scale: linearity gives smooth cubic = near action +
exterior action; existing same-cutoff sharp/smooth error and the exterior
bound make sharp minus the ENTIRE near action negligible at log²N/N.
Near physical test has exact Fourier value chi(D/epsilon)*Fourier(A_N).
No positive exact-cone replacement or missing-sheet deletion is permitted.

Search84883 nonpartial67975 indexed,index/coverage1266241,current1266248;
compiler pending51619,stale2660,error2,noinventoryerrors,semantic coverage
unmeasured. All20 candidate and20 source argument statements inspected;
proof_ideas/ingredient_sets empty. Hits confirm literal selected family,
actual cutoff, rapid exterior, and positive exact-cone theorem; the latter
is not an entire-tube cancellation theorem.

Integration audit found a source-name collision: the earlier reciprocal
Fourier branch already defines bagCubicControlledPhysicalSchwartz for
N>1; physical normal jets independently used that name for N>=exp1.
Rename ONLY the new exp1-domain definition and its four-module consuming
chain to bagCubicExpControlledPhysicalSchwartz; keep existing public bound
names. Reaudit this exact chain and both branches in one scratch import.
This is necessary for the new mathematical closure to compose in the
umbrella, not a new research direction.

30az final arithmetic exterior source10040 PASSED. Collision fix is now
also fully checked: chain12356 audited physical normal jets, Fourier
budgets, exterior estimate, rapid decay and complete source in dependency
order, each via lake --old env lean <leaf> -o <own olean>; all five empty
logs. Only the new exp1-domain constructor name changed. Existing N>1
constructor and its cone consumers remain untouched. Scratch46834 now
imports BOTH branches and audits the original sharp near-cone reduction.

Near-cone search3709 returned nonpartial but largely irrelevant confocal/
torsion candidates; proposed ingredient set rejected as inapplicable.
Focused search37777 was nonpartial67977,index/coverage1266330,current1266331,
compiler pending51621/stale2660/error2,no inventory errors; all20 candidates
and20 source arguments inspected, no proof ideas/ingredient sets. Actual
useful next ingredients: bagDefectEquiv, bagDefectNode_physical (whole
normal phase exp(-2*pi*i*r*d/Q²)), criticalProfileFibre_eq (zero axes and
nonzero inverse curves), and criticalProfileInverse_kloosterman. Local
prime-height fibres still do not identify the entire global shrinking
tube. No such identification is claimed.

30az original sharp reduction CLOSED: final direct5368
ChiCubicNearConeReduction passed (one abel_nf tactic suggestion, no errors
or warnings). The full original-natural exterior has every power saving;
its normalized norm tends to zero. Exact source linearity proves the
literal smoothed split. Existing same-cutoff error gives
log²N/N*norm(original sharp cubic - ENTIRE near-cone action)->0.
The retained physical test has exact Fourier value chi(D/epsilon)*F(A_N).
No source, lift, congruence alias or projector term is dropped.
Axiom audit85038 is running; index87063 PASS(5changed,0removed).
Lint72188 exit1:367sizewarnings,24 unrelated unreachable modules; ZERO
findings in all nine touched leaves. Three new imports unique; no full
or umbrella build. Next hard research card: bag-entire-near-cone-arithmetic.

30az final certificate: axiom85038 PASS, all25 public theorem endpoints
use only propext,Classical.choice,Quot.sound. The same scratch imports
both BAG branches and proves equality of old/new actual constructors
on the overlapping scale domain. All owned processes are terminal.
P3:bag-complete-arithmetic-exterior records the complete theorem, paper
proof and audits. RH goal remains active; entire near-cone arithmetic
continues in P1:bag-entire-near-cone-arithmetic.
