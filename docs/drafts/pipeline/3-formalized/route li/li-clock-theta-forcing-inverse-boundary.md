# Actual theta forcing and inverse comparison boundary

- **ID:** LI-CLOCK-THETA-FORCING-INVERSE-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [completed-clock sign attempt](../1-in-progress/li-clock-completed-forcing-direct-sign.md)
- **Statement:** The literal massive theta forcing is strictly negative at every positive clock, with an all-order coefficient margin; the same actual causal kernel nevertheless has a positive odd input with every odd coefficient positive whose entire inverse response changes sign within the actual clock growth class.

## Gates

- [x] Actual source, prior research, complete paper proof and every analytic admission.
- [x] Complete author/root audit of final291; independent audit of root121 resolvent proof.
- [x] Formalize the exact forcing, inverse, contour growth and resolvent survivors.
- [x] Named/direct builds, all-public axioms, complete source review and integration.

## No-go closure

- **Exact killing mechanism:** For the actual K=B_theta', the genuine r=-u'' solves r+r*K=K and has a negative positive-clock value, although K is odd entire with every odd coefficient strictly positive. Every fixed derivative of r has growth exp(delta*abs(t)) for one delta<1/300.
- **Strongest positive survivor:** All-clock forcing and every fixed derivative have explicit signed coefficient bounds; the actual reciprocal-Xi germ defines an entire causal inverse with a complete finite-contour growth certificate; the literal massive response has the exact decomposition -S=g-r*g.
- **New insight:** The needed inequality is the particular source correlation r*g<=g. Positive forcing, positive coefficients and the required response growth do not supply it.
- **Status:** PAPER PASS; Lean CLOSED (see Lean certificate). This no-go remains unretired. No negative actual S/F witness or RH conclusion.

## Audited paper proof [PROVED HERE]

Final291 certificate below is preserved verbatim. Root read all289 original lines and both final wording/dependency changes; all mathematical bodies passed. Frozen certificate `/tmp/li_producer_massive_theta_forcing_attack.md`, SHA256 `f7f219376559c6411960d839726a9c6ade09bbab81b1cb83426065f077f05cc2`. Independent root121 proof `/tmp/li_root_theta_resolvent_coefficient_boundary.md`, SHA256 `420b525658dbe7c6f5fd0253e2c4efaeb0eb90049bd3e6a4409bb7500d923f19`, was read completely and passed by Producer. Its exact inverse-sign argument is included in the certificate below.

The omega bound depends on the fully audited [massive completion comparison](li-clock-massive-completion-comparison.md); smooth clock and massive source admissions are recorded in the [derivative sign boundary](li-clock-derivative-cofinal-sign-boundary.md) and parent sign card. These new claims are paper theorems, not installed Lean APIs.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.BorelSeriesConvolution`, `GaloisForLFunctions.HTGeometry.BorelSeriesParityLaplace`, `GaloisForLFunctions.HTGeometry.RectangleBorelLaplaceInversion`, `GaloisForLFunctions.RHTower.LiClockThetaReciprocalSource`, `GaloisForLFunctions.RHTower.LiClockThetaInverseContourGrowth`, `GaloisForLFunctions.RHTower.LiClockThetaMassiveForcing`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange`, `GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra`, `GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence`, `GaloisForLFunctions.RHTower.LiClockMassiveCompletionComparison`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the umbrellas):
`GaloisForLFunctions.HTGeometry.BorelSeriesConvolution`, `GaloisForLFunctions.HTGeometry.BorelSeriesParityLaplace`, `GaloisForLFunctions.HTGeometry.RectangleBorelLaplaceInversion`,
`GaloisForLFunctions.RHTower.LiClockThetaReciprocalSource`, `GaloisForLFunctions.RHTower.LiClockThetaInverseContourGrowth`, `GaloisForLFunctions.RHTower.LiClockThetaMassiveForcing`, `GaloisForLFunctions.RHTower.LiClockThetaResolventSignChange` (all new);
installed inputs `GaloisForLFunctions.RHTower.LiEvenCrossActualClockVolterra` (`F⋆B=tB'`), `GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence` (score recurrence), `GaloisForLFunctions.RHTower.LiClockMassiveCompletionComparison` (`ω²>6429/40000`).

| Claim | Declaration |
|-|-|
| §1–2 `c_j=ν_j/(2j)!`, `c_0=1`, `0<c_j≤(32/303)^j/j!`; `B=Σc_jt^{2j}/(2j)!`, `K=B'=Σc_{m+1}t^{2m+1}/(2m+1)!`, odd coefficients all `>0` | `liClockThetaGeneratorCoeff_zero`, `_pos`, `_le`, `liEvenCrossActualClockBorelKernel_eq_evenFactorialSeries`, `hasDerivAt_liEvenCrossActualClockBorelKernel_eq`, `liClockThetaKernel_pos` |
| `B>1` off the origin | `one_lt_liEvenCrossActualClockBorelKernel` |
| (3) `F⋆B=tB'` at every real clock (odd/even reflection of the installed `t≥0` law) | `volterraConv_liEvenCrossActualClockResponse_borelKernel` |
| (4) `J_S=S⋆B=tB'''+2B''−ω²tB'−M₀B` (endpoint-exact, `F(0)=0`, `F'(0)=M₀`) | `liClockThetaMassiveForcing_eq`, `liEvenCrossActualClockResponse_eq_oddFactorialSeries`, `liEvenCrossActualClockMassiveSource_eq_oddFactorialSeries` |
| (5) `J_S=Σq_jt^{2j}/((2j)!)²`, `q_j=ν_{j+1}/(2j+1)−(2jω²+M₀)ν_j`, `q_0=0` | `hasSum_liClockThetaMassiveForcing`, `liClockThetaForcingCoeff_zero` |
| (6) `q_j≤−ην_j` (`j≥1`), `η=2ω²+M₀−49/909>6047/22725>1/4` | `liClockThetaForcingCoeff_le`, `liClockThetaForcingMargin_gt`, `one_quarter_lt_liClockThetaForcingMargin` |
| (7) `J_S≤−η(B−1)<−(B−1)/4<0`; `J_S'≤−ηK<−K/4<0`; `J_S^{(m)}≤−ηB^{(m)}<0` (`m≥1`, `t>0`) | `liClockThetaMassiveForcing_le`, `liClockThetaMassiveForcing_lt`, `deriv_liClockThetaMassiveForcing_lt`, `iteratedDeriv_liClockThetaMassiveForcing_le` |
| (8) `g=−J_S'≥ηK>K/4`, coefficient floor and exact ratio `2jω²+M₀−ν_{j+1}/((2j+1)ν_j)` | `hasDerivAt_liClockThetaMassiveForcing`, `liClockThetaForcingInput_ge`, `liClockThetaForcingInput_gt`, `liClockThetaForcingInput_coeff_ge`, `liClockThetaForcingInput_coeff_ratio` |
| (9) `S+S⋆K=J_S'=−g`, `S(0)=0` | `liEvenCrossActualClockMassiveSource_volterra`, `liEvenCrossActualClockMassiveSource_zero` |
| §4 `Φ(z)=XiC(−Iz)/XiC0=Σν_jz^{2j}/(2j)!`, `Φ(0)=1`, entire; zeros of `Φ` are `z=iα_q` | `liClockThetaGenerator_eq_XiC`, `liClockThetaGenerator_zero`, `differentiable_liClockThetaGenerator`, `liClockThetaGenerator_eq_zero_iff` |
| (10) reciprocal germ `1/Φ=Σa_jz^{2j}` on `|z|²<2`, `|a_j|≤2^{−j}` | `liClockThetaGenerator_mul_reciprocalGerm`, `liClockThetaReciprocalCoeff_convolution`, `abs_liClockThetaReciprocalCoeff_le` |
| (11) `u=Σa_jt^{2j+1}/(2j+1)!`, `u+u⋆K=t`, `u0=0,u'0=1,u''0=0,u'''0=−ν₁/2`; unique continuous solution | `liClockThetaCausalInverse_volterra`, `liClockThetaCausalInverse_initial_jets`, `eq_liClockThetaCausalInverse_of_volterra`, `volterraConv_oddFactorialSeries` |
| Poles of `G(p)=1/(p²Φ(1/p))` at `p=−iw_q`; one `d<1/300` bounds all `|Im w_q|` | `liClockThetaGenerator_inv_ne_zero`, `exists_abs_im_inv_xiSpectralPoint_le`, `norm_inv_xiSpectralPoint_lt_half` |
| Coefficient extraction on the big square and Cauchy deformation onto `[−δ,δ]×[−1/2,1/2]` | `rectangleIntegral_borelLaplaceInversion`, `rectangleIntegral_eq_of_differentiableOn_frame`, `liClockThetaInverseSymbol_eq_tsum`, `two_pi_I_mul_iteratedDeriv_liClockThetaCausalInverse` |
| (12) `|u^{(m)}(t)|≤C_m e^{δ|t|}`, one `δ<1/300`, every real `t` | `exists_liClockThetaCausalInverse_iteratedDeriv_growth` |
| (13) `r=−u''`, `r+r⋆K=K`, `r(0)=0`, `r'(0)=ν₁/2>0`; unique; every derivative obeys (12) | `iteratedDeriv_two_liClockThetaCausalInverse`, `liClockThetaResolvent_volterra`, `liClockThetaResolvent_zero`, `hasDerivAt_liClockThetaResolvent_zero`, `eq_liClockThetaResolvent_of_volterra`, `exists_liClockThetaResolvent_iteratedDeriv_growth` |
| Every positive exponential type for `B^{(m)}`, `K^{(m)}` (real clocks) | `abs_iteratedDeriv_liEvenCrossActualClockBorelKernel_le`, `abs_iteratedDeriv_liClockThetaKernel_le` |
| `K̂(p)=Φ(1/p)−1` for every `p>0` | `integral_Ioi_liClockThetaKernel_mul_exp_neg_eq`, `hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg` |
| §5 `r>0` near `0` and `r(t)<0` at some `t>0` (inverse-positivity fails for the same positive odd kernel) | `exists_liClockThetaResolvent_pos`, `exists_liClockThetaResolvent_neg` |
| Cubic floor `K(v)≥ν₂v³/144`; `u(t)<0` at some `t>0` | `liClockThetaKernel_ge_cubic`, `liClockThetaGeneratorCoeff_two`, `exists_liClockThetaCausalInverse_neg` |
| (14) `−S=g−r⋆g`; `S≤0 ⇔ r⋆g≤g` | `neg_liEvenCrossActualClockMassiveSource_eq`, `liEvenCrossActualClockMassiveSource_nonpos_iff` |

Proof-route note: the sign change of `r` is proved from `r̂=K̂/(1+K̂)` (valid under the assumed `r≥0`) by comparing `r̂(q/2)−r̂(q)≤q²/c₁` with `r̂(q/2)−r̂(q)≥(q/2)e^{−qε}∫_0^εtr` instead of the two monotone-convergence limits; the conclusion is the card's. Exponential-type bounds are stated on real clocks, where `B`, `K` are defined.

## Log

- 2026-10-01 — Complete paper and independent source audits pass. Actual all-clock forcing sign and growth-qualified coefficient obstruction recorded. Exact particular-g comparison and RH remain OPEN; formalization remains required.

# Actual massive theta forcing and growth-qualified inverse obstruction

Verdict: dependency-closed PAPER PASS on the complete actual forcing inequality,
genuine reciprocal-plane admission and actual-kernel inverse counterexample.
The particular massive response S<=0 remains OPEN. No Lean/compiler, numerical
experiment, tree/card edit or new agent; new statements are not installed APIs.

## 1. Literal source and normalization

Let R_j=thetaCuspRawEvenMoment j=2 integral_(x>0) x^(2j)k(x)dx, where
k=thetaCuspFullSource is the FULL all-integer theta cusp sum. Its atom is
exp(x/2)*thetaCuspSeed(n exp x), with seed
2pi(2pi y^4-3y^2)exp(-pi y^2). The n=0 term is zero; every positive atom
and every source moment is retained. Put nu_j=R_j/R_0, R_0>0. Exact source
gives nu_0=1, nu_j>0 ALL j, and nu_1=M0=normalizedPrimeArchMoment0.
This is the SINGLE-Xi normalization; no mixed four-variable ZA²/ZU² is
silently substituted into it.

The installed literal kernel is

    B(t)=liEvenCrossActualClockBorelKernel t
        =sum_j nu_j t^(2j)/((2j)!)²,
    K(t)=B'(t), B0=1, K0=0.                           (1)

B is even, K odd. The installed all-order source-score recurrence is

    303nu_(j+1)<=(32j+17)nu_j, ALL j>=0.              (2)

This is an ACTUAL arithmetic theta-source inequality. The source proof
starts with 303x²<=1+32xW_n(x), x>=0,n>0, from the exact first-atom
superpotential lower bound and integer-atom score order. It integrates
against x^(2j) times the actual Born amplitude square. Genuine position/
score integrability precedes integration. The Ward identity gives the
score moment=(2j+1)/2 times the same position moment. Finally the source
sum and division by the actual positive R0 preserve32j+17 and303. There
is no extra positivity/Hankel/RH premise.

Source definitions/proofs read: ThetaCuspFinitePrimeSource:26-28,183-185,
316-317; PrimeArchThetaCumulantMinor:151-162,267-268,439-460;
XiCTaylorThetaTailMomentLogConvex:16-38 (actual all-j strict positivity);
PrimeArchThetaScoreMomentRecurrence ALL154 lines, including EVERY source
admission and normalized conclusion141-148. Ward primary204-208 and
CurvatureGap160-185 were additionally checked. These are existing actual
contracts, not recalled or invented APIs.

## 2. Complete series, every derivative and convolution admission

From (2), nu_j<=(32/303)^j j!. Thus the kernel coefficients obey
nu_j/((2j)!)²<=(32/303)^j/j!. On ANY complex disk |z|<=T with T>=1,
the m-th termwise derivative is bounded by

    (2j)^m ((32/303)T²)^j/j!,

for each fixed m, ignoring finitely many derivative-zero terms. Its full
sum converges by the ratio test. Every fixed derivative is therefore
absolutely/compact uniformly admitted; B extends entire with its literal
real values. The same M-test applies to every polynomial-degree-weighted
forcing below. The source response F and its fixed derivatives have the
separate genuine full-copy cosine/sine admissions and gamma-rate bound
from the frozen massive Dirichlet report. All finite-interval convolutions
and their differentiated integrands are continuous on compact triangles,
so genuine L1 and Leibniz/Fubini precede every manipulation.

Exact installed admissions: BorelSource:19-42 definitions, positivity and
nu0; :43-98 score/factorial bound; :100-125 complete compact summability;
:230-254 genuine first derivative. Higher fixed derivatives here are PAPER
consequences of the explicit majorant, not claimed public Lean symbols.

The literal banked law is

    F*B=tB', t>=0, (f*g)(t)=integral_0^t f(s)g(t-s)ds. (3)

This is LiEvenCrossActualClockVolterra:241-246, factor ONE for single Xi.
Its full term/sum admission is installed; it is not newly discovered as a
producer. B(t)>1 for t>0 follows from positivity of EVERY kernel term and
its j=1 termnu1 t²/4>0. The installed statement B>=1 alone is strengthened
only by this explicit admitted positive term.

## 3. Exact actual negative forcing for EVERY positive clock

Let S=F''-omega²F, omega²=c0-M0>4/25, using the independently audited full
completion bound in /tmp/li_root_massive_completion_comparison_attack.md
and the frozen massive source report. Retain all endpoints:

    (F''*B)=(F*B)''-F'(0)B-F(0)B'
           =(tB')''-M0B,

because F0=0,F'0=M0. Hence the literal transformed forcing is

    J_S:=S*B=tB'''+2B''-omega²tB'-M0B.                (4)

There is no doubled symmetric-square factor here. Substituting the full
series and shifting its degree, the exact coefficient is

    J_S(t)=sum_j q_j t^(2j)/((2j)!)²,
    q_j=nu_(j+1)/(2j+1)-(2j omega²+M0)nu_j.          (5)

The first numerator comes from (2j+2)²(2j+1) times the (j+1)-coefficient:
its SQUARED factorial cancels to1/(2j+1) on denominator((2j)!)².
At j0, q0=nu1-M0nu0=0 EXACTLY.

For j>=1, (2) gives

    q_j/nu_j<=(32j+17)/(303(2j+1))-2j omega²-M0
              <=49/909-2omega²-M0=-eta,
    eta:=2omega²+M0-49/909>6047/22725>1/4.            (6)

The first rational ratio equals16/303+1/[303(2j+1)], so its maximum on
j>=1 is49/909. Positivity of nu_j licenses division. No sign of higher
logarithmic cumulants is assumed. The COMPLETE admitted sums therefore give

    J_S(t)<=-eta(B(t)-1)<-(B(t)-1)/4<0, t>0,
    J_S'(t)<=-eta K(t)<-K(t)/4<0, t>0.               (7)

At0 all these odd/constant-zero terms have their exact filled value0.
Every further fixed derivative of J_S is strictly negative for t>0,
by the same full coefficient comparison after differentiation. For m>=1,
J_S^(m)<=-eta B^(m); for m0 use B-1. These are actual all-t SOURCE laws,
not an inferred sign of S. Define g=-J_S'>0; coefficient by coefficient

    g>=eta K>K/4,
    [t^(2j-1)]g/[t^(2j-1)]K
       =2j omega²+M0-nu_(j+1)/[(2j+1)nu_j], j>=1.   (8)

Differentiating (4) once using B0=1 gives the genuine causal equation

    S+S*K=J_S'=-g, S0=0.                            (9)

The attempted inference from positive B/K or negative forcing to S<=0 is
not valid without a signed inverse/comparison theorem. The next sections
test that exact proposed inference with this SAME actual K.

## 4. Entire inverse germ, every coefficient and gamma-class admission

Define the actual normalized ordinary source

    Phi(z)=XiC(-I z)/XiC0=sum_j nu_j z^(2j)/(2j)!.

XiC0=R0>0, Phi0=1, Phi entire/even and real on real z. AllOrderCumulant:
39-47 gives every odd/even Xi jet; CumulantMinor:439-447 gives the even
raw jets. Multiplication by(-I)^(2j) cancels their(-1)^j sign exactly.
Thus this is the actual WHOLE source Taylor identity, not finite interpolation.

Use the genuinely analytic central reciprocal germ only:

    1/Phi(z)=sum_j a_j z^(2j),
    u(t)=sum_j a_j t^(2j+1)/(2j+1)!.                 (10)

Cauchy on one small zero-free circle admits every compact derivative of u
and makes u entire odd/real. Complete beta coefficient multiplication with
K(t)=sum_(j>=1)[nu_j/(2j)!]t^(2j-1)/(2j-1)! gives

    u+u*K=t, u0=0,u'0=1,u''0=0,u'''0=-nu1/2.        (11)

The two power series and the finite triangle are absolutely admitted BEFORE
interchange. Multiplication is the central identity Phi*(1/Phi)=1. Standard
compact Volterra uniqueness alternatively follows by iterating the bounded
kernel estimate, whose n-th compact iterate is bounded by T(M_T T)^n/n!.
No positive inverse assumption occurs in construction or uniqueness.

The coarse central-circle bound is improved to the actual gamma class
without assuming RH or global reciprocal holomorphy. From exact installed
XiCanonicalProduct:141-159, ALL zeros of Phi(1/p), p!=0, have

    p=-I w_q, Re p=Im w_q, |p|=|w_q|<1/sqrt150.

TopFrequency:106-119 gives square summability and finite upper levels of
|Im w_q|. Together with each strict |Im w_q|<gamma (DampedResolvent:27-36),
the finite set at levelgamma/2 supplies d<gamma bounding ALL |Re p|;
if that set is empty use gamma/2, otherwise take its finite maximum and a
strictly larger d below gamma. Choose d<delta<gamma and H>1/sqrt150.
EVERY reciprocal pole and the accumulation/essential point0 lies STRICTLY
inside the rectangle |Re p|<delta,|Im p|<H.

Let G(p)=1/[p²Phi(1/p)]. Choose a sufficiently large circle, containing the
rectangle, with1/R in the genuine central reciprocal disk. Both series
converge absolutely/uniformly on this compact circle. Coefficient extraction
in (2pi I)^(-1) integral exp(tp)G(p)dp yields exactly(10), since the residue
condition is degree2j+1. G is holomorphic between this circle and the rectangle:
p0 remains inside, and the actual zero-copy theorem rules out every other
singularity in the intervening region. Cauchy deformation is therefore
legitimate even though infinitely many poles accumulate INSIDE the rectangle.
No infinite residue sum, filled reciprocal at0 or global zero-free Xi is used.
The RECTANGLE representation gives for every fixed m and every REAL t

    |u^(m)(t)|<=C_(delta,m)exp(delta|t|), delta<gamma. (12)

Its derivatives insert bounded p^m on one fixed contour. This is a genuine
strict sub-gamma bound; for complex t only the compact-entire admission is
asserted, not the stronger false rectangle-width complex bound. Every
multiplicity is retained in the original Phi; no principal-pole replacement.

## 5. Actual inverse fails even for the SAME positive odd kernel input

Set r=-u''. Differentiating (11) twice by the first factor, including u'0=1
and u0=0, gives

    r+r*K=K, r0=0,r'0=nu1/2>0.                     (13)

r is odd entire, real on real clocks, and all its fixed derivatives obey
(12). Thus it is a genuine response in the actual selected growth class.
The input K has STRICTLY positive coefficients at EVERY odd degree.

Suppose r>=0 on all nonnegative clocks. Then (13), with K>=0, implies
0<=r<=K. Entire Phi Cauchy bounds provide EVERY positive exponential type
for B and K: |B^(m)(z)|<=M_epsilon epsilon^m exp(epsilon|z|). Therefore,
UNDER THIS ASSUMED SIGN, r and K are genuinely weighted L1 for every p>0.
Tonelli and the full source factorials yield

    Khat(p)=Phi(1/p)-1,
    R(p)=integral_0^infinity exp(-pt)r(t)dt
        =1-1/Phi(1/p).

Since Phi(1/p)>=nu1/(2p²), as p decreases to0,

    R(p)->1, (1-R(p))/p=1/[pPhi(1/p)]<=2p/nu1->0.

Monotone convergence first proves integral r=1. Then the same theorem on
((1-exp(-pt))/p)r(t), increasing to t r(t), proves integral t r=0, allowing
infinity before taking the limit. This is impossible because r'0>0 makes
r strictly positive on a nonempty positive interval. Thus r(t)<0 for some
t>0, while r is positive near0. No Landau theorem or unjustified signed
ALL-p Laplace continuation has entered this contradiction.

This audit read ALL121 lines /tmp/li_root_theta_resolvent_coefficient_boundary.md,
SHA420b525658dbe7c6f5fd0253e2c4efaeb0eb90049bd3e6a4409bb7500d923f19,
and independently checked every endpoint, Cauchy/Tonelli/MCT admission,
normalization and derivative. The sign argument uses the assumed r<=K for
small-p admission; (12) alone would not supply ALL p>0.

Consequently even positive odd entire input K, every strictly positive odd
coefficient, forcing>=K/4 and the actual strict sub-gamma response class
DO NOT ensure a nonnegative inverse response. This is an ACTUAL-KERNEL
obstruction, not an actual negative F/S witness or an RH counterexample.
For input t the simpler cubic K lower bound also disproves nonnegative u:
if u>=0, its positive initial interval mass times K(v)>=nu2 v³/144 forces
u+u*K to outgrow t. The full K-input r test is stronger for the proposed
coefficientwise forcing argument, and preserves the exact squared factorial.

## 6. Particular actual input: exact remaining signed comparison

The complete causal resolvent identity on each compact interval is

    (I+K*)^(-1)g=g-r*g.

Expand (I+K*) applied to g-r*g; compact associative/commutative convolution
and (13) cancel all mixed terms. Thus the PARTICULAR actual source obeys

    -S=g-r*g,
    S<=0 iff r*g<=g, with literal g=-J_S'.           (14)

The nonnegative kernel/forcing or coefficient cones have failed as proofs
of this comparison. Nothing in the r counterexample proves that this
particular correlation fails. The exact ratios in(8), their actual moment
normalization and the full reciprocal-plane phase must be retained.
A new independently proved inequality for r*g is still missing; stating
(14)'s right side alone is another receiver in changed coordinates.

A scalar comparison using r>=0 is false by(13). No successful norm-history
majorant is supplied here; replacing r by |r| discards its negative portions
and does not by itself establish the required particular-g comparison.
The score bound(2)
proves g's signs and its coefficient floor but supplies no upper bound on
the signed r*g. Positive odd input K already satisfies that floor and
produces a negative output. Restricted correlation with THIS actual g,
not generic inverse positivity, remains the genuinely open target.

## 7. Overlap/coverage and status

No duplicate prior query. Existing massive/double-pole queries and their
reported PARTIAL/source-only coverage were fully recorded in frozen255
/tmp/li_producer_massive_dirichlet_source_sign_attack.md. Root's focused
reciprocal contour query32335 additionally exited0: path
/tmp/li_root_inverse_theta_reciprocal_contour_research.json, partial=true,
139.873987417s; owner inspected20candidate/20source statements,20names,
10prosepaths and sole ingredient set, no passages/proofideas. Inventory63551,
retrieval1164889, coverage1164934/current1164940, semantic unmeasured;
interrupted text/source and reranking deadline. Compiler43snapshot/2error/
47922pending/2660stale/38stalesnapshot/1umbrellasourceonly/2654unavailable.
Those are OWNER prior-hit dispositions, not a claim this audit reread all
unrelated excerpts. Actual zero/finite-level sources cited above were
independently read here. No corpus absence, world novelty or current compiler
claim is made.

Author PAPER PASS: all actual normalization/score/series/source derivatives;
negative ALL-t forcing and coefficient floor(7)-(8); actual central inverse,
all-p SIGN-CONDITIONED Laplace admission, strict sub-gamma rectangle admission;
actual same-kernel odd/coefficient inverse obstruction; exact literal signed
comparison(14). New survivors remain Lean-open and require root/independent
whole-proof/card gates. Actual S<=0, finite growing-window orientation and
RH remain OPEN. No route retirement or stronger inverse theorem claimed.
- 2026-10-04 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
