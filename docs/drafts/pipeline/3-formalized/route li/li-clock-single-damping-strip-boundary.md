# Actual reciprocal-Xi logarithm: exact single-damping strip boundary

- **ID:** LI-CLOCK-SINGLE-DAMPING-STRIP-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [actual all-order source sign](../1-in-progress/li-clock-single-damping-strip-sign.md)
- **Statement:** At each p>0 all alternating derivative signs of log Phi(1/p) are nonnegative exactly when every actual zero has |Im alpha|<=1/(2p). The signs are strict under this closed strip; the Taylor radius is p. A strip violation forces infinitely many negative orders.

## Gates

- [x] Complete346-line independent source/branch/radius audit.
- [x] Root ALL346 review, exact source spot-checks and primary generalized-Li parameter verification.
- [x] Exact Lean formalization and full compiler/source/integration gates (see Lean certificate).

RH remains OPEN. The unconditional interval0<p<=1 is bounded. Source signs at an unbounded set of p are still missing. Genuine signed Laplace admission remains p>1/300; smaller p statements use analytic source continuation. This is an exact application of known generalized Li mathematics, not a new RH proof.

Complete certificate follows verbatim: `/tmp/li_current_single_damping_strip_audit.md`, SHA256 `38c77b7c05603a1188bdf614aa63eb8bf3b35a6e4cbe5986d2bf7568f2a6e39b`. Root review: `/tmp/li_root_single_damping_strip_review.md`.

# Single damping: exact all-order strip classification

Status: **PAPER PASS**, with explicit domain correction below. This closes the card's
identity, forward range, and converse. It does not produce source signs at unbounded
positive dampings. No Lean/compiler run, numerical experiment, tree/card edit, or
new agent occurred. The only written artifact is this report.

## 1. Literal objects and exact conclusion

Keep every `q : XiZeroCopy`, with its original divisor multiplicity. Put

    alpha_q = xiSpectralPoint q, w_q = alpha_q^(-1), lambda_q = w_q^2,
    Phi(z) = XiC(-I*z)/XiC(0) = xi(1/2+z)/xi(1/2),
    H(p) = log(Phi(1/p)), p>0.

On the real axis Phi is strictly positive. Here log means the ordinary real
logarithm of that positive value. Near any positive p its derivatives are those
of a coherent local holomorphic logarithm; no globally chosen principal log is
required. All quantities below use SINGLE Xi normalization.

For every real p>0 and integer n>=1 the COMPLETE cancelled family is absolutely
summable and

    T_n(p) := (-1)^n H^(n)(p)/(n-1)!
      = (1/2) sum_q Re[2/p^n - (p-I*w_q)^(-n) - (p+I*w_q)^(-n)].       (S1)

Moreover, at each fixed p>0,

    (forall n>=1, T_n(p)>=0)
       iff (forall q, |Im alpha_q|<=1/(2p)).                         (S2)

The forward implication in fact yields **T_n(p)>0 for every n>=1**, including
when some source zeros lie on the closed strip boundary. Consequently

    0<p<=1 => forall n>=1, T_n(p)>0                                 (S3)

unconditionally, using the actual strict strip |Im alpha_q|<1/2. Also H(p)>0
for every p>0, but n=0 is separate and is not covered by the factorial formula.

The signed Laplace integral defining H in the parent paper is genuinely
admitted only for p>1/300. For 0<p<=1/300, S1 concerns the source function
log Phi(1/p), analytically continued along the positive axis. This report does
NOT identify it with an unadmitted integral there, including at p=1/300.
p=0 is excluded throughout.

## 2. Source ledger, read from actual declarations

Paths in this section are relative to `formal/GaloisForLFunctions/`.

| Source | Exact admitted content used |
|---|---|
| RHTower/RiemannTower.lean:28–55 | Literal entire xi; `xi_eq_half_mul` away from 0,1; functional equation; xi(0)=xi(1)=1/2. |
| RHTower/XiEntireReal.lean:23–61 | Literal XiC rotation, entire differentiability, Schwarz reality, evenness. |
| RHTower/XiCanonicalProduct.lean:24–79 | Countable multiplicity-copy type; alpha nonzero; complete square-reciprocal summability. |
| Same:82–98,141–159 | Every copy is an actual XiC zero, and EVERY XiC zero has an actual copy. No divisor truncation. |
| RHTower/XiGuinandWeilRectangleExhaustion.lean:25–44 | `xiSpectralPoint_im_eq`; `xiSpectralPoint_im_mem_openHalf`, and its all-XiC-zero corollary. The task's “32” is a line anchor, not a filename suffix. |
| RHTower/PrimeArchValuationSectorCones.lean:34–67 | Complete mass summability and strict positive mass; `nonempty_xiZeroCopy`; Re(lambda)>0 via `xiThermalNode_pos`; stronger sector lower bound. |
| RHTower/XiReciprocalSquareSecondMomentRadius.lean:31–66 | Exact |lambda|<1/150 and |alpha|^2>150. Only boundedness is needed for S1; no RH premise. |
| RHTower/LiEvenCrossActualClockDampedResolvent.lean:99–122,183,220–320 | Literal complete resolvent D(p), denominator >=p^2 and absolute sum for EVERY p>0; genuine F Laplace identity only p>1/300. |
| RHTower/PrimeArchThetaCumulantMinor.lean:439–446 | All even XiC jets equal (-1)^j times literal raw theta moments. |
| RHTower/XiCTaylorThetaTailMomentLogConvex.lean:16–40 | Every actual raw even theta moment is strictly positive, with genuine source L1. |
| RHTower/LiEvenCrossActualClockBorelSource.lean:37–49 | nu_j>0 for all j and nu_0=1. |
| RHTower/ThetaCuspTiltFluxSourceWeld.lean:86–122 | Literal positive full theta source, faster-than-every-exponential envelope, full-complex bilateral-Laplace/Xi weld. |
| RHTower/ThetaSourceGlobalStrictLogConvexity.lean:31–125 | Full-complex moment differentiation, every real tilt's genuine polynomial L1, positive real partition function. |
| HTGeometry/VivantiPringsheim.lean:32–36,294–324 | Precisely defined coherent `ContinuesAcross`; realSeriesSum analytic on its convergence disk; nonnegative series cannot continue at its finite positive radius. |
| RHTower/PrimeArchBernsteinPringsheimCollar.lean:125–166 | Source-read pattern for segment germ propagation and convex disk-overlap identity. Its source-specific RH theorem is NOT imported as a proof of S2. |
| RHTower/LiCriterion.lean:82–165 and LiCoefficientXi.lean:27–74 | Installed ordinary paired Li receiver, multiplicity and FE inverse pairing; exact overlap limitations recorded in section 8. |

The whole 217-line `/tmp/li_root_integrated_clock_source_boundary.md` and
349-line `/tmp/li_producer_integrated_clock_cumulant_attack.md` were read.
Their P9/P10 and C2 supply the initial logarithmic identity below, with genuine
Laplace admission. These are independently audited PAPER dependencies, not
claimed already-exported Lean H theorems.

The actual full theta weld and moment ladder give the entire expansion

    Phi(z)=sum_(j>=0) nu_j*z^(2j)/(2j)!, nu_0=1, nu_j>0.

Entire Taylor convergence follows from XiC entire; the moment identification
fixes every coefficient. For real z, the even expansion gives Phi(z)>=1,
and for z!=0, Phi(z)>=1+nu_1*z^2/2>1. This also proves the positive-axis
nonzero property needed for local logs without ANY assumed nonreal zero-free
region. `XiCanonicalProduct` alone gives a genus-one product and zero-set
completeness; it is not silently treated as a proved half-log quadratic product.

## 3. Initial admitted identity and complete continuation

Let A=sum_q |w_q|^2<infinity and gamma=1/300. Parent P2 admits P(t)=integral_0^t F
and all polynomially weighted signed P Laplace integrals for p>gamma. Its exact
source identity P+P*K=t*K, K=B', gives by genuine Fubini and positive-source Tonelli

    P_hat(p)=Phi'(1/p)/(p^2 Phi(1/p)).

The full sine/resolvent source gives F_hat(p)=D(p) and P_hat(p)=D(p)/p. Therefore

    -H'(p)=sum_q Re[lambda_q/(p*(p^2+lambda_q))], p>gamma.           (S4)

This is factor ONE at n=1, over ALL copies. Parent P10 fixes the additive
constant by both sides tending to zero as p tends to infinity, so H really is
log Phi(1/p), not an arbitrary antiderivative.

Now show both sides of S4 are real analytic on the entire connected interval
(0,infinity). H is real analytic because Phi(1/p)>0. The sum has genuine local
holomorphic normal convergence as follows. Fix p0>0 and W bounding all |w_q|.
Choose delta>0 so delta<p0/2 and delta*(2p0+delta)<p0^2/2. For |z-p0|<delta,

    |z|>=p0/2,
    |z^2+lambda_q| >= |p0^2+lambda_q|-|z^2-p0^2| >= p0^2/2,

since Re(lambda_q)>0. Thus each rational summand is holomorphic there and is
bounded by a fixed constant times |lambda_q|. The COMPLETE mass is summable.
The same holds on smaller compact disks and licenses the analytic sum. Real
analytic identity on a connected interval extends S4 from (gamma,infinity)
to EVERY positive p. Equivalently use overlapping local complex disks along
that real interval. No analytic continuation through a zero or p=0 is used.
This continuation is of source derivatives, not of a signed integral admission.

## 4. All orders, exact cancellation, and factor 1/2

Define C_n(z,w)=2*z^(-n)-(z-I*w)^(-n)-(z+I*w)^(-n), n>=1.
Its exact common-denominator numerator is

    C_n(z,w) = N_n(z,w)/[z^n*(z^2+w^2)^n],
    N_n(z,w) = 2 sum_(k=1..n)
      [choose(n,k)-(-1)^k choose(n,2k)] z^(2n-2k) w^(2k).          (S5)

Choose(n,2k)=0 when 2k>n. Expanding both powers proves S5; the constant and
all odd w powers cancel. On the disk in section 3, every numerator term is
bounded by a fixed constant times |w|^2, using |z|<=p0+delta and |w|<=W.
The denominators have a fixed positive lower bound. Thus for every FIXED n

    |C_n(z,w_q)| <= K(p0,delta,W,n)*|w_q|^2.

This proves full absolute/local uniform summability at every positive p, with
no splitting into constant or first-power reciprocal sums. Individual
(p+-I*w_q)^(-n) tend to p^(-n) as w_q tends to zero and are not the summable
families being asserted. The estimate is not uniform as n tends to infinity.

Direct algebra gives C_1(p,w)=2*w^2/[p*(p^2+w^2)]. Hence S4 is
H'(p)=-(1/2) sum_q Re C_1(p,w_q). Normal convergence allows every fixed-order
complex derivative, and

    derivative^(n-1) C_1 = (-1)^(n-1)*(n-1)!*C_n.

Differentiating the ACTUAL source derivative proves S1, including n=1.
The factor 1/2 is mandatory; at n=1 it cancels C_1's factor2 and recovers
D(p)/p exactly. No copy deletion or parity restriction is present.

## 5. Closed-strip forward implication and strict boundary handling

Write alpha=A0+i*B0. Since alpha!=0, w=(A0-i*B0)/|alpha|^2. Exact algebra gives

    |p+I*w|^2=p^2+(1+2p*B0)/|alpha|^2,
    |p-I*w|^2=p^2+(1-2p*B0)/|alpha|^2.                           (S6)

Thus BOTH denominator norms are >=p exactly when |B0|<=1/(2p).
Under this closed strip, for every n>=1,

    Re[(p+-I*w)^(-n)] <= |p+-I*w|^(-n) <= p^(-n).

Moreover at least ONE denominator norm is STRICTLY greater than p, since
the sum of their squared norms is 2p^2+2/|alpha|^2>2p^2. Consequently Re C_n
is strictly positive for EACH actual copy, even if the other norm equals p
at a boundary zero. Complete summability and the nonempty actual copy type
then give T_n(p)>0. There is no cancellation among positive terms and no
finite-packet approximation.

Actual |B0|<1/2 implies |B0|<1/(2p) whenever 0<p<=1. This proves S3 including
p=1. The classification uses a CLOSED strip; replacing its boundary by a
strict strip would lose the correct converse.

## 6. Converse: coherent logarithms and Pringsheim radius

Fix p>0 and assume T_n(p)>=0 for every n>=1. Put

    G_p(u)=Phi(1/(p-u))/Phi(1/p), |u|<p.

This is holomorphic on the entire disk |u|<p, G_p(0)=1, and is positive on the
real segment 0<=u<p. It is not assumed nonzero at other complex points.
Continuity supplies a local nonzero disk at0 and a local analytic logarithm
L_p with L_p(0)=0. Its real Taylor coefficients are

    a_0=0, a_n=(-1)^n H^(n)(p)/n!=T_n(p)/n, n>=1.

All are nonnegative. Let R be the true Taylor convergence radius; R>0.
If R<p, then R is finite. The summed series L is analytic on |u|<R and
exp L=G_p there by the analytic identity theorem, starting at0. In particular
for every real 0<=u<R, L(u) is real and L(u)=log G_p(u).

At the positive real boundary u=R, G_p(R)>0. Choose epsilon>0 so G_p is
holomorphic and nonzero throughout the epsilon disk about R, still inside
|u|<p. A coherent local logarithm l exists with l(R)=log G_p(R). On a small
real interval just left of R it is real log G_p and agrees with L. Both are
analytic on the convex overlap of the two disks. Identity from that interval
therefore proves equality on the FULL overlap and supplies `ContinuesAcross`
of the Taylor sum at R. This is exactly the coherence required by the
installed Vivanti--Pringsheim contract, not merely positivity of G_p(R).

By definition of the finite radius, the nonnegative series converges for
every 0<=s<R and does not converge for every s>R. These are its hconv/hdiv
premises. `not_continuesAcross_of_nonneg` contradicts the continuation just
constructed. Therefore R>=p (including R=infinity).

The Taylor sum is consequently analytic on |u|<p. Its exponential agrees with
G_p near0 and hence on the WHOLE connected disk. Thus G_p has NO zero there.
If any actual alpha_q has |Im alpha_q|>1/(2p), S6 says one point

    u_q=p+I*w_q  or  p-I*w_q

has |u_q|<p. At it, 1/(p-u_q)=+I*alpha_q or -I*alpha_q. Therefore
Phi(1/(p-u_q))=XiC(+alpha_q)/XiC0 or XiC(-alpha_q)/XiC0=0, by the actual
zero identity and XiC evenness. This contradicts exp L=G_p. Hence every
actual copy lies in the claimed closed strip, proving S2.

Multiplicity matters only positively here: each support zero has at least
one copy, and all finite positive divisor orders are retained. A multiple
zero still cannot equal an exponential of a holomorphic function. No
assumed nonvanishing of eta, Xi, or a globally totalized log enters the proof.

## 7. Accumulation, sharp radius, and strongest direct survivor

Square summability implies that for every epsilon>0, only finitely many
copies have |w_q|>=epsilon. This is the elementary finite-level-set consequence
of summability of nonnegative |w_q|^2. Finite multiplicity is already built
into XiZeroCopy. Thus reciprocal singularities p=+-I*w_q can accumulate only
at0 in the complex DAMPING plane; the corresponding u=p+-I*w_q points can
accumulate only at u=p in the fixed-damping Taylor plane. Neither 0 nor p is
crossed by the converse continuation. Away from0, the rational series has
only a finite local head of poles and a normally convergent cancelled tail.
A genuine interior Xi zero cannot be cancelled in the exponential/log proof.

Under S2, the logarithm's radius is EXACTLY p, not just at least p. As real
u increases to p,

    G_p(u)>=nu_1/[2*Phi(1/p)*(p-u)^2] => L_p(u) tends to infinity.

An analytic extension of the Taylor sum across p would be locally bounded,
a contradiction. Thus R<=p; combine with section 6. The singularity at the
positive boundary is present independently of nonreal zero information.

A further direct paper corollary is worth retaining for independent audit:
if an actual zero violates the strip at this FIXED p, the coefficient sequence
T_n(p) has infinitely many negative terms. Indeed that interior zero forces
R<=|u_q|<p. If only finitely many coefficients were negative, subtract their
finite Taylor polynomial; the remaining nonnegative series has the SAME
finite radius R, while the coherent positive-axis source logarithm minus
that polynomial continues across R. Pringsheim again contradicts it.
Equivalently, eventual all-order nonnegativity at a fixed p has the SAME strip
content as all-order nonnegativity. This uses no order/damping interchange.
It is a strengthened receiver/boundary classification, not an arithmetic
producer of the signs.

## 8. Exact prior overlap and coverage limits

Root direct deep query10145 completed exit0: report
`/tmp/li_root_single_damping_strip_research.json`. Query:
“reciprocal Xi logarithm complete monotonicity all derivative orders single
damping Pringsheim critical strip disk coefficient positivity”. Its output
was fully inspected by section:20 candidate lemmas,20 source arguments,
0 declarations,0 proof ideas,1 unverified ingredient set. Most candidates are
unrelated damping scalars or reciprocal-operator actions. Candidate11
`I_mul_xiSpectralPoint` is a coordinate algebra anchor; source argument4 is a
common reciprocal-square bound. FE quartet multiplicity and open-unit-strip
arguments are structural anchors, not all-order sign producers. The sole
operator-action ingredient set does not address this logarithmic observable.

Coverage is explicitly PARTIAL: malformed judge JSON and a Qdrant timeout;
unfinished filter_and_judge and semantic_retrieval. Inventory63621/63621,
index generation1166678, coverage1166689 vs current1166690; semantic coverage
not measured. Compiler coverage:43 compiled_snapshot,2 error,47974 pending,
2660 stale,38 stale_snapshot,2654 unavailable,10249 not_applicable,
1 umbrella_source_only. All40 candidate/argument entries are source_only.
Elapsed116.534171916s. This is neither exhaustive semantic retrieval nor a
compiler verification of this paper. Runtime model metadata adds no theorem.

A direct lexical rephrase used the documented command, without help/source:

    python3 scripts/formal_tools.py research '"LiCriterion" "VivantiPringsheim" "PringsheimCollar"' --mode lexical --any --no-refresh --json

Then --per-module0 --explore0 with offsets0 and20 exhausted the23 reported
eligible declarations across the two returned modules. All23 names/locations
were inspected; applicable Li and Pringsheim bodies were read directly.
The initial cap returned4 entries. Lexical JSON reports no compiler freshness,
semantic coverage, elapsed budget, or generation fields; those are UNREPORTED,
not inferred from exit0. Absence of a collar hit does not refute its actual
source, which was independently read. No worldwide novelty-absence claim.

Installed `LiCriterion` proves the ordinary paired transform using a finite
phase/maximal-packet argument, not Pringsheim. Its Cayley images
1-1/rho and their inverses differ from the present fixed-centered reciprocal
transform. Thus its public theorem is not a drop-in proof of S2. The installed
Pringsheim theorem is applicable once the local-log radius and coherent
continuation in section 6 are constructed; the collar module supplies the
exact germ-matching pattern, not an additional sign hypothesis.

Primary literature verification materially narrows novelty. Sekatskii's
[Generating functions for the generalized Li's sums, arXiv:1411.6209](https://arxiv.org/pdf/1411.6209)
was opened; Theorems2–3, pp.2–4, give the relevant half-plane criterion and
Möbius generating function. Set its b=-1/2 and sigma=1/2+1/(2p), and v=u/p.
Then its generating-function argument is exactly 1/2+1/[p(1-v)], so

    lambda_(n,b,sigma)=p^n*T_n(p).

This is an exact change of variables, not an analogy. Pairing rho with1-rho
turns its single-branch zero sum into the full absolutely cancelled bracket
of S1; divisor orders are unchanged. The right half-plane threshold sigma,
together with FE reflection, is exactly |Im alpha|<=1/(2p). The original
[generalized Bombieri–Lagarias paper, arXiv:1304.7895](https://arxiv.org/pdf/1304.7895)
was also opened and its underlying generalized criterion checked.

[Bombieri–Lagarias, 1999, publisher primary record](https://www.sciencedirect.com/science/article/pii/S0022314X99923922)
explicitly treats Li positivity as a general multiset criterion. Its author
PDF was opened but text extraction is corrupted; no precise theorem wording
is certified from that corrupted text. [Freitas, 2006, primary journal record](https://www.cambridge.org/core/journals/journal-of-the-london-mathematical-society/article/litype-criterion-for-zerofree-halfplanes-of-riemanns-zeta-function/BA2F80D2F63AD291035C3426548E3628)
and [author preprint](https://arxiv.org/pdf/math/0507368) were opened; the
abstract independently records zero-free-strip Li criteria. No unverified
identity with its particular parameter normalization is needed: Sekatskii's
explicit Theorems2–3 already give the exact overlap above.

Hence this classification is a source-normalization/application/formalization
survivor of known generalized Li mathematics. Its new utility here is the
checked single-Xi/full-copy factor, exact all-positive-p source continuation,
strict closed-boundary result, and explicit ledger separating integral
admission from source derivatives. It is NOT a new RH proof mechanism.

## 9. Target disposition and remaining obstruction

| Card obligation | Disposition |
|---|---|
| Exact factor1/2, every n>=1,p>0, full cancellation | PASS sections3–4; formal implementation remains open. |
| Genuine derivative and same logarithmic normalization | PASS; initial genuine p>1/300 identity, then local analytic continuation only. |
| Actual all-order strict0<p<=1 | PASS section5, including p=1. |
| Converse iff closed strip at one p | PASS section6; local coherent branches, complete divisor, actual zero contradiction. |
| Boundary and reciprocal accumulation | PASS sections5–7; damping0/Taylorp excluded, no uniform order limit assumed. |
| Exact known overlap | PASS section8; explicit generalized Li parameter identification. |
| Independent literal arithmetic signs at unbounded p | OPEN. Nothing here supplies them. |
| Lean closure | OPEN: this task ran no compiler and wrote no Lean. |

For completeness, S2 implies that signs at an UNBOUNDED set of positive p
force every Im alpha=0: a fixed nonzero transverse displacement would violate
the strip at sufficiently large p. RH implies the strip signs for EVERY p.
This is only the receiver equivalence, with unbounded damping explicitly
quantified. Signs at one finite damping certify a strip of positive width,
not RH. The unconditional interval0<p<=1 is bounded and cannot be promoted
by an order/damping limit interchange. The original integrated-clock/source
positivity problem remains OPEN.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.LiClockThetaSingleDampingSource`, `GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (both `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the umbrella):
`GaloisForLFunctions.RHTower.LiClockThetaSingleDampingSource` (atoms, S4–S6, holomorphic extension, S1) and `GaloisForLFunctions.RHTower.LiClockThetaSingleDampingStrip` (S2, S3, strengthened converse, radius, receiver).

| Claim | Declaration |
|-|-|
| (S1) for every `p > 0`, `n ≥ 1`: `T_n(p) = (-1)^n H^{(n)}(p)/(n-1)! = (1/2) Σ_q Re C_n(p, w_q)`, absolutely summable | `liClockStripCoefficient`, `liClockStripAtom`, `hasSum_liClockStripCoefficient`, `summable_norm_liClockStripAtom` |
| (S4) `-H'(p) = Σ_q Re[λ_q/(p(p²+λ_q))]` for every `p > 0` (all copies, factor one) | `hasDerivAt_log_liClockThetaGeneratorReal_inv_resolvent`, `hasDerivAt_log_liClockThetaGeneratorReal_inv_eq_tsum`, `liClockStripAtom_one_eq` |
| Section 3–4 continuation: local holomorphic normal convergence and every-order termwise differentiation on all of `(0, ∞)` | `liClockStripHolomorphic`, `liClockStripHolomorphic_local`, `iteratedDeriv_re_liClockStripHolomorphic`, `hasDerivAt_liClockStripAtom`, `hasDerivAt_liClockStripDerivAtom` |
| (S5) numerator identity `z^n(z²+w²)^n C_n = 2Σ_{k=1}^n[C(n,k) - (-1)^k C(n,2k)] z^{2n-2k}w^{2k}` and the `|w|²` bound | `liClockStripAtom_numerator`, `liClockStripAtom_eq_double_sum`, `norm_liClockStripAtom_le` |
| (S6) `|p ± iw|² = p² + (1 ± 2p Im α)/|α|²`; `p ± iw_q ≠ 0`; uniform gap; finite level sets of `|w_q|` (accumulation only at `0`) | `normSq_ofReal_add_I_mul_inv`, `ofReal_add_I_mul_inv_xiSpectralPoint_ne_zero`, `exists_liClockStrip_gap`, `tendsto_inv_xiSpectralPoint_cofinite` |
| (forward, strict) closed strip ⇒ `Re C_n(p,w_q) > 0` for every copy and `T_n(p) > 0` | `norm_shift_of_strip`, `re_liClockStripAtom_pos_of_strip`, `liClockStripCoefficient_pos_of_strip` |
| (S3) `0 < p ≤ 1` ⇒ `T_n(p) > 0` for every `n ≥ 1` | `liClockStripCoefficient_pos_of_le_one` |
| (S2) all signs ⟺ closed strip ⟺ eventual signs | `liClockStripCoefficient_nonneg_iff` |
| Section 7: a strip violation forces infinitely many negative `T_n(p)` | `frequently_liClockStripCoefficient_neg`, `norm_shift_lt_of_not_strip`, `exists_simultaneous_pow_recurrence` |
| Section 7: under (S2) the Taylor radius of `H` at `p` is exactly `p` | `liClockStrip_taylor_radius` |
| Section 9: RH ⟺ all signs at every `p > 0` ⟺ all signs on an unbounded set of dampings | `rh_iff_liClockStripCoefficient_nonneg`, `riemannHypothesis_iff_forall_xiSpectralPoint_im_eq_zero` |
| `H(p) > 0` for `p > 0` | `log_liClockThetaGeneratorReal_inv_pos` |

Proof-route notes: (S1) is proved for all `p > 0` directly from the partial-fraction expansion of `ξ'/ξ` (paired with the reflection `α ↦ -α` of the copies) and Weierstrass differentiation of the locally uniformly convergent holomorphic extension, rather than by real-analytic continuation from the Laplace range `p > 1/300`; the converse of (S2) and its eventual strengthening are proved by the dominant-packet asymptotic `2ρ^n T_n(p) = -Σ_S Re u_i^n + o(1)` with simultaneous recurrence, in place of the Vivanti–Pringsheim argument; the radius `≥ p` uses the `|w|²` bound, the radius `≤ p` a harmonic lower bound. The Sekatskii parameter identification (section 8) is literature overlap, not a formal claim.

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
