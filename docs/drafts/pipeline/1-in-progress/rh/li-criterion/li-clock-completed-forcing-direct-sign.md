# Direct completed-clock compensation through the literal forcing

- **ID:** LI-CLOCK-COMPLETED-FORCING-DIRECT-SIGN
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; direct source-sign attack
- **Source:** [original finite-window target](../../li-clock-finite-eta-orientation-window.md), [exact relative law](../../../3-formalized/li-clock-partition-relative-volterra-forcing.md)
- **Statement:** Prove the literal `Re F_N=C-K_N+Re H_N>=0` for every sufficiently large N throughout one fixed admissible `0<t<=c log(2N+1)` window.

## Goal

This is the existing RH-bearing source inequality, not a replacement receiver.
The proved relative identity is an input. Kernel positivity, full source
identities, aggregate positive area and normalized cancellation limits do not
settle its inverse pointwise sign. The RH-bearing sign claim remains
paper-open. Dependency-closed auxiliary survivors have separate Stage2
cards and the explicit formalization releases recorded below.

## Gates

- [x] Literal source and receiver fixed; direct prior-corpus search initiated.
- [ ] Complete arithmetic sign proof or actual-source refutation of the proposed window.
- [ ] Independent whole-proof and novelty/dependency audit.
- [ ] Formalize only a dependency-closed proof; retain every literal source and guard.

## Exact proposed attack

Write B_N for the proved full mixed kernel, D_N for its exact signed forcing,
and V_N=C-K_N. All clocks below are real restrictions of their literal contours.
For one common regular disk and t>=0, define the completed forcing on paper by

`J_N(t)=D_N(t)+2*integral_0^t V_N(s) B_N(t-s) ds`.

The established relative law and exact completed split give

`2*integral_0^t F_N(s) B_N(t-s) ds=J_N(t)`.

This is an exact identity, not a positivity conclusion. The hard task is to
obtain a source-pure sign estimate strong enough to orient its solution.
Current investigates the complete signed arithmetic forcing; Pole investigates
the residual after literal completion cancellation. Their scratch reports are
read-only mathematical attempts, not certified new theorems.

## Root attempt: normalized forcing and first-zero comparison

Because B_N(0)=1 and B_N>0, put `q_N=B_N'/B_N` and `R_N=J_N/B_N`.
Once the required continuous derivative is admitted, differentiated convolution
gives the exact candidate comparison equation

`F_N(t) = (B_N(t)/2) R_N'(t)`
`         + integral_0^t F_N(s) B_N(t-s) [q_N(t)-q_N(t-s)] ds`.

Thus monotonicity of q_N on the whole window, together with `R_N'>=0`,
would give a positive Volterra comparison kernel and force F_N>=0. This
requires an actual proof for both source conditions; neither is assumed.
For non-strict inequalities, positivity needs the full Volterra iteration or
negative-part Gronwall argument, not an invalid first-touch shortcut.

This monotonicity condition is FALSE on paper for the actual source. Root
and Producer checked the complete177-line derivation and the installed
source contracts: `/tmp/li_producer_completed_forcing_barrier_audit.md`,
SHA256 `8f466058f9c85bffbca125346220ff159d2d2ca0305546a052dbf229be85d82e`.
The [complete mixed-profile survivor](../../../2-fully-proven/li-clock-mixed-kernel-sign-boundary.md)
is Stage2; its two-leaf formalization was released after full typed-plan review.
No new compiled theorem is claimed yet.

With actual infinite moments d_j and reference moments
`u_j=4^j*(2j)!`, put `r_j=d_j/u_j` and `S_j=sum_(a<=j) r_a`.
The exact four-coordinate binomial expansion gives
`M_j=(2j)!*4^j*S_j`; hence
`B_infinity(z)=sum_j S_j*(2z)^(2j)/(2j)!`.
Each finite marginal moment is at most `K*u_j`,
`K=4/(2-sqrt2)^2`, with its OWN squared normalizer. Thus the whole finite
mixed series on |z|<=T is dominated by
`K^2*sum_j(j+1)*(2T)^(2j)/(2j)!`.
Fixed-order source limits and summable tails give locally uniform convergence
of the complete kernels and every fixed derivative; derivative majorants
replace (2j)! by (2j-m)! and remain summable. This is not a growing-order
interchange or an assumed derivative limit.

The existing `r_j->lambda>0` and positive-series ratio theorem yield
`B_infinity(t)/(t*exp(2t))->lambda/2`. If the finite q_N were nondecreasing
through their eventually growing windows, the log-convex chord inequality
would pass at every fixed0<t<T to
`log B_infinity(t)<=(t/T)*log B_infinity(T)`.
Letting T grow forces `B_infinity(t)<=exp(2t)`, contradicting the extra
positive factor t. The geometric moment error gives the stronger exact
profile recorded below and `t^2*q_infinity'(t)->-1`. Consequently there
are fixed0<a<b with `q_N(a)>q_N(b)` for EVERY sufficiently large N. Those
same clocks lie inside every positive logarithmic window eventually.
The history kernel at t=b,s=b-a is therefore strictly negative for all
such N. No numerical experiment, generic countermodel or RH assumption
is used.

This sufficient-condition attempt fails; it does not refute the original
compensation conjecture. Any replacement must keep the signed history term
above and prove a genuine arithmetic bound for it. The strongest paper
survivor is the exact complete profile, logarithmic-curvature limit and
stable source witness; its Lean status remains OPEN. The main card is
not retired or promoted on the strength of that auxiliary result.

## Prior research and coverage

First direct deep search: `/tmp/hgt-li-compensation-next-research.json`,
terminal95988 exit0,85.636s,partial=false. All20 candidate headers inspected;
only the already proved positive-area estimate directly concerns the clock.
All20 source-argument identities are inventoried; some long proof excerpts
are not relied on. The proposed Suzuki midpoint ingredient set concerns
different resolvents and supplies no actual finite-clock sign. Actual relative
law and generic transfer are already proved inputs, not new producers.
Coverage snapshot63509/63509 files, generation1163886 versus query1163877;
semantic coverage unmeasured, most compiler statuses pending/source-only.
No corpus absence or external novelty claim.

Focused literal-clock search8913 finished exit0,44.302s,partial=false;
`/tmp/hgt-li-compensation-source-research.json`. All20 candidate contracts,
all20 source-argument headers and11 lexical names inspected. The proposed
ingredient chain uses the existing margin only for t<=20; it supplies no
growing-window sign. Remaining relevant hits are exact completed splits,
N=1 negativity, positive aggregate area and already proved relative laws.
Coverage63509 indexed files, query/coverage generation1163896; semantic
coverage unmeasured and compiler freshness mixed. No new source-sign producer
was identified among these results; no corpus-wide absence claim. No new
Lean implementation or compilation has started.

## Root follow-up: positive forcing versus exact signed history

The existing full actual clock satisfies `|F(t)|<=A*t*exp(t/300)` and
`M0=integral_0^infinity exp(-2s) F(s) ds=D_actual(2)>0`, with the exact
endpoint value `D_actual(2)=xiEndpointCompletedCurvature/4`. These are
unconditional source theorems, not positivity of F.

The established ratio error `|r_j-lambda|<=C*9^(-j)` gives a sharper candidate
decomposition than the leading mixed-kernel limit. Put
`sigma=sum_j(r_j-lambda)` and `T_n=sum_(j>n)(r_j-lambda)`. Absolute convergence
gives `|T_n|<=(C/8)*9^(-n)` and

`B_infinity(t)=lambda*t*sinh(2t)+(lambda+sigma)*cosh(2t)-E(t)`,
`|E(t)|<=(C/8)*cosh(2t/3)`.

Root and Producer checked this exact factor and remainder. For
`J_infinity=2*(F*B_infinity)`, the complete domination argument proves on paper
`J_infinity(t)/(t*exp(2t))->lambda*M0>0`. Indeed, after multiplication by
`exp(-2t)/t`, the integrand is dominated for t>=1 by a constant times
`exp(-2s)*|F(s)|`, and its pointwise limit is
`lambda*exp(-2s)*F(s)`. Thus eventual positive forcing is compatible with the
already proved implication `not RH -> cofinal F -> -infinity`.

This is an attempted source-sign argument that fails at inverse orientation:
even actual eventual J positivity does not exclude the hypothetical bad
clock. A successful estimate must control the signed-history cancellation
at the scale of F, not merely the positive leading forcing. Producer's complete
120-line independent certificate is
`/tmp/li_producer_completed_forcing_asymptotic_audit.md`,
SHA256 `d841e3434ad85f02465fcf309b118e5b48d7fdf873baf9d2f9582f7a4fa6b503`;
root read it completely and checked the literal damped-source contracts.
It also proves J_N->J_infinity uniformly on every fixed compact from full
clock/kernel convergence at ONE fixed admissible radius. This supplies no
uniform sign on growing windows. Under hypothetical not-RH, J_infinity is
eventually positive while F is negative cofinally; no actual negative clock
or consistency of not-RH has been proved. New forcing limit remains Lean-open.

## Direct coefficient attempt: complete source before inversion

Current's complete337-line proof in `/tmp/li_current_completed_forcing_direct_attack.md`,
SHA256 `50cf49431059768815cbd798617d761dc5bdc40587ee9ae1a35a9962fa2f3068`,
was read and algebra/source-checked by root. Its corrected generator is used
here; an earlier informal skew display omitted a canceling derivative term.
Let A(u),U(u) be the literal separately normalized symmetric ordinary MGFs,
W=A*U (ordinary multiplication), and q_C the completion logarithmic derivative.
If `J_N(t)=sum_n R_(N,n)t^(2n)/[(2n)!]^2`, its ordinary generator is

`Rcal_N(u)=sum_n R_(N,n)u^(2n)/(2n)!`
` =u U(u) A'(u)+u W(u)[q_C(1/2+u)-q_C(1/2-u)-8u/(1-4u^2)]`.

The relative skew's -uAU' cancels the +uAU' from the literal contiguous
clock. The rational term retains eta_N(s)=s L_A,N(s) at its zero s=0.
All logarithmic identities are initially regular central germs; multiplying
out removes finite-MGF logarithmic denominators without assuming they have
no further zeros.

The complete Gamma/dyadic moments satisfy
`0<c_h<=(651/1600)(4/25)^h`. Finite compact support makes uUA' entire.
Writing `w_j=[u^(2j)]W`, the exact signed coefficient is
`R_(N,n)/(2n)!=[u^(2n)]uUA' +2 sum_(j<n)c_(n-j-1)w_j
 -2 sum_(j<n)4^(n-j)w_j`.
The summable sequence w_j/4^j has sum W(1/2)>0 for each FIXED finite N.
The first term divided by4^n vanishes; the completion term is an l1
convolution with a bounded sequence tending to zero. Thus
`R_(N,n)/[4^n(2n)!]->-2 W(1/2)<0`.
Every fixed finite N has negative high-order completed-forcing coefficients.
Full positive-weight head/tail comparison then gives
`exp(-2t)J_N(t)->-W(1/2)` and
`exp(-2t)J_N'(t)->-2W(1/2)` with N FIXED. None is a joint N,t statement.

This also proves on paper that EVERY fixed N>0/admissible r has F_N unbounded
below cofinally. If F_N>=m after T, continuity gives
`J_N(t)>=-2[I+max(-m,0)*t]B_N(t)`, `I=integral_0^T |F_N(s)| ds`.
The complete mixed series gives `B_N(t)<=exp(2sqrt(2Lt))<=exp(t+2L)`.
Multiplication by exp(-2t) contradicts the strict negative J_N limit.
Thus for every m,T0 there is t>T0 with F_N(t)<m. This closes the previously
unclaimed fixed-prefix question on PAPER, without putting any such t inside
the required growing window. No uniform-N or varying-radius conclusion.

The infinite source has the opposite full coefficient sign. With V(s)=s C(s)
and `P(u)=V(1/2+u)V(1/2-u)/V(1/2)^2`, literal completed eta gives
`A_infinity=Xisym/P`, where
`Xisym=xi(1/2+u)xi(1/2-u)/xi(1/2)^2`.
The project's riemannXi=-2xi factor cancels exactly. Raw completed theta
moments give positive even Taylor coefficients of Xisym. For
`T=U_infinity/P`, `U_infinity=1/(1-4u^2)`, one obtains
`Rcal_infinity=u T Xisym'` and
`log T=sum_h [2*4^(h+1)-c_h]u^(2h+2)/(h+1)`.
All coefficients of this logarithm are positive. The full factorial lift
therefore has J_infinity(t)>0 AND J_infinity'(t)>0 for every t>0.
Compact MGF bounds, Cauchy bounds and full clock/kernel convergence identify
this lift with the SAME literal convolution above. This is a paper survivor,
not a supplied assumption or a new installed Lean result.

The original sign proof still FAILS: at a first zero after a positive prefix,
`J_N'(t)=2 integral_0^t F_N(s) B_N'(t-s) ds>0` and J_N(t)>0.
Both strict forcing signs can hold at the very crossing they were intended
to exclude. A successful argument must bound this signed history from the
actual source. Fixed-N negative asymptotics and infinite positive forcing
must not be interchanged or promoted to a growing-window conclusion.

## Direct residual attempt: complete arithmetic cycles

Pole's237-line source derivation is `/tmp/li_pole_completed_residual_direct_attack.md`,
SHA256 `b92a6c159d92af0696c6d8fdd6cf5c50dce593f54ba701f7634dbb5ddb3c5c37`.
Root read the complete proof, checked the literal source trace/contour sign,
both factorials, arithmetic primitive bound/derivative, and source normalization.
The sign attempt FAILED; auxiliary paper deductions below have no new Lean
implementation. No retirement or RH claim.

For the actual one-coordinate probability `dmu_N=exp(-u/2)1_(S_N)du/Z_N`,
write `Phi_N(z)=E exp(-izu)`. The first retained interval gives Z_N>1/2;
halfline domination gives `E[u exp(r u)]<9` for0<r<=1/128. Thus throughout
the full disk, `|1-Phi_N|<=q=9r<1` and `|Phi_N'|<=9`.
The complete geometric quotient expansion has source remainder
`9*q^M/(1-q)`. Its literal trace contour gives

`P_N(t)=sum_(m>=0)(-1)^m B_(N,m)(t)`,
`|P_N-sum_(m<M)(-1)^m B_(N,m)|<=9*q^M/(1-q)*sinh(|t|/r)`.

Here, with m+1 independent coordinates from that SAME law,
`B_(N,m)(t)=E[U_0 Delta_(U_1)...Delta_(U_m) Psi(t U_0)]>=0` for t>=0,
`Psi(v)=sum_(j>=0) v^(2j+1)/[(2j+1)!]^2`.
Each increment acts on the argument u of Psi(tu). Finite product support
admits all contour/series exchanges; the geometric bound supplies genuine
absolute convergence of the complete outer sum.

The attempted decreasing-alternating-term bound is FALSE even inside every
eventual logarithmic window. For the infinite literal law, the installed
bounded arithmetic primitive B satisfies B'=alpha-1/2 off integer corners.
Cellwise integration by parts, with every internal boundary canceled, gives
for p>=1
`m_p=(2^p*p!/Z)*(1+epsilon_p)`, `|epsilon_p|<=3^(-p)/2`.
The origin term vanishes only for p>=1; m_0 remains exactly1.
The complete two-coordinate binomial expansion then gives, for p>=2,
`[(E(U+V)^p)/2-m_p]/m_p >= 25*(p-1)/(84Z)-1`.
Positive full-series prefix negligibility implies
`B_(infinity,1)(t)/B_(infinity,0)(t)->infinity`.
The bound `Psi(tS)<=exp(2sqrt(tS))<=exp(S/4+4t)` admits fixed-clock product
dominated convergence with both own normalizers. One fixed positive clock
therefore has `B_(N,1)>B_(N,0)` for every sufficiently large N, inside
every eventual c log(2N+1) window. Later signed terms remain essential.

The direct next conjecture retains the whole signed sum: choose
`M_N=ceil(d log(2N+1))`, `d>c/[r log(1/q)]`, and prove throughout the
original window
`sum_(m<M_N)(-1)^m B_(N,m)(t) >= 2sinh(2t)-C(t)
 +9*q^M_N/(1-q)*sinh(t/r)`.
The rightmost error tends to zero uniformly, but cannot be dropped when
proving exact nonnegativity. This inequality is UNPROVED and is the actual
remaining arithmetic burden of this attempt.

## Root failed direct estimate: bound the negative history

Next attempted sufficient condition uses the actual unconditional envelope
`E0(s)=A*s*exp(s/300)`. Before a first negative crossing, F>=0 and F<=E0,
so the exact normalized-forcing equation would imply
`F(t)>=L(t):=(B(t)/2)*R'(t)-integral_0^t E0(s)*K_-(t,s) ds`,
where `K(t,s)=B(t-s)[q(t)-q(t-s)]` and `K_-=max(-K,0)`.
Proving L>=0 was a concrete attempt to control the required signed history.

The infinite actual-source profile proves on paper that this estimate fails. Put
`a=lambda/2`, `b=(lambda+sigma)/2`, `p(t)=exp(-2t)B(t)` and
`M1=integral_0^infinity s*exp(-2s)F(s) ds`.
The exact profile gives p(t)=at+b plus an exponentially small remainder,
including its first two derivatives. Direct convolution differentiation gives
`t^2 R'(t)->2M1` and
`t*exp(-2t)*(B(t)/2)*R'(t)->a*M1`.
For every fixed s>0, the same profile gives
`t*exp(-2t)*K_-(t,s)->a*s*exp(-2s)`.
To pass its integral, split at s=t/2. Writing u=t-s, the first part has
`|q(t)-q(u)|<=C*s/(ut)` and `exp(-2u)B(u)<=C'*u`.
After normalization this gives the COMMON integrable majorant
`C*C'*A*s^2*exp(-(2-1/300)s)`.
The second part is bounded by a fixed constant times
`t*(1+t)*exp(-(2-1/300)*t/2)*(t/[2*(2-1/300)]+(2-1/300)^(-2))`,
which tends to zero. Both regions, including t-s near zero, are covered.

Consequently
`t*exp(-2t)L(t)->a*integral_0^infinity s*exp(-2s)[F(s)-E0(s)] ds<0`.
Strictness follows directly from the admitted sine-atom derivative:
`|F(s)|<=300*A*(exp(s/300)-1)<E0(s)` for s>0, using A>0.
With beta=2-1/300 the exact limit ell satisfies
`ell<=-a*A*(2-beta)*(beta+4)/(4*beta^3)<0`.
Thus this actual-source upper-envelope history bound is eventually negative;
it does not prove the clock itself negative. For finite prefixes the correct
upper bound is `E_(N,r)=E0+delta_N*sinh(s/r)`, never E0 alone. Complete
fixed-compact F_N,B_N,B_N' convergence transfers a fixed negative L witness
to these corrected finite lower bounds on every eventual logarithmic window.

Root read and checked Pole's complete291-line certificate
`/tmp/li_pole_completed_history_envelope_audit.md`,
SHA256 `e1bfcda52ef5d4753e233e4fb87dde5828987b8862eaf59fed1fc5e3d749d967`.
All endpoint factors, both genuinely dominated history regions and the strict
source margin pass paper review. Exact lower-bound failure and its positive
two-moment/profile survivor remain Lean-open; no formal no-go closure claimed.

## Next direct attempt: remove the mixed double exponential mode

The new differential attempt has a source-checkable coefficient, rather than
an arbitrary damping parameter. The full clock series gives
`F'(0)=normalizedPrimeArchMoment 0=:m0`; comparison of the same literal
partition/completion jets gives `B''(0)-8=m0-c0`.
Installed bounds are `m0<29/625` (XiOrderFourteenCornerSourceExclusion:179)
and `c0>=181/1600` (PositiveCompletion:311). Hence
`omega^2=c0-m0>2669/40000>1/16`.
The full completion upper bound c0<=651/1600 and m0>0 also give
`1/4<omega<2/3`.
Thus the proposed differential equation has homogeneous part
`F'''-omega^2 F'`, while the actual clock grows at most `A t exp(t/300)`.
Growth excludes its unstable homogeneous exponential, but does not yet sign
its forced solution. In particular the existing remainder bound exp(2t/3)
does NOT justify integrating that remainder against exp(-omega t).
Any larger analytic disk or improved decay needed for an infinity-boundary
Green representation must be proved from the actual source; no zero-free
continuation, Green-kernel sign or forcing sign is assumed.

Current's full305-line source admission has passed root's complete paper
audit, including a fresh installed reciprocal-Gamma source check:
`/tmp/li_current_pole_removed_source_continuation_audit.md`, SHA256
`2a1ec664cbaadc0bc3231a4db1b571ef06971bd2016dac493569cde0bd276dc4`.
The exact entire continuation uses only installed source factors:
`eta_ext(s)=h(s)*riemannXi(s)`,
`h(s)=-L_1(s-1)*(GammaR(s+2))^(-1)/(2*pi)`.
It matches the literal eta germ on its admitted strip; no outside-strip
totalized eta value or zero-free Xi premise is allowed. With s±=1/2±u,
`E(u)=4 eta_ext(s+)eta_ext(s-)/Z^2` continues `(1-4u^2)A(u)`.
The completed generator has the exact entire numerator
`EJ(u)=4u h(s+)h(s-)[X'(s+)X(s-)-X(s+)X'(s-)]/Z^2`, X=riemannXi,
continuing `(1-4u^2)^2 Rcal_infinity(u)`.

Their exact initial coefficients are E0=1,E1=-omega^2,EJ0=0,EJ1=2m0.
Entire-series absolute integration gives for EVERY p>0
`Laplace(R)(p)=p^3 E(1/p)-p^3+omega^2 p`,
`Laplace(Q)(p)=p^3 EJ(1/p)-2p m0`,
R=(d^2-4)^2B and Q=(d^2-4)^2J.
This uses no Laplace integral of F below the proved threshold1/300.
At u_m=2m+1/2,m>=1, the reciprocal Gamma factor makes both E and EJ zero.
Consequently p_m=1/u_m decreases to zero with
`Laplace(R)(p_m)=p_m*(omega^2-p_m^2)` and
`Laplace(Q)(p_m)=-2p_m*m0`.

These audited formulas refute BOTH global sign directions for
each transformed source: R's samples are positive eventually but tend to0,
which is impossible for the Laplace transform of a globally nonnegative
nonzero R as p decreases; a positive sample excludes R<=0. Q's negative
samples exclude Q>=0, and applying the same monotonicity to -Q excludes
Q<=0. This is a direct test of the proposed R>=0,Q<=0 Green argument,
not a sign assertion about F. Continuity supplies both pointwise signs for
each actual infinite R and Q. No cofinal sign-change or finite-window
transfer is claimed. Entire Cauchy bounds also improve both transformed
sources and both fully pole-subtracted remainders to every positive
exponential type. These exact positive survivors remain Lean-open.

## Direct derivative test and next signed source

The actual Green equation has G=F'''-omega^2 F' and the growth-selected
Neumann formula
`F'(t)=-(2omega)^(-1) integral_R exp(-omega|t-s|)G(s)ds`.
Root's new full paper proof is
`/tmp/li_root_clock_derivative_sign_boundary.md`; independent full192-line
audit passed, SHA256
`fca5d719a4ef8b735a18c00c38b0b5332ebb46cd51f86251a8c45f4e74ba3d1c`.
The [full derivative/forcing survivor](../../../2-fully-proven/li-clock-derivative-cofinal-sign-boundary.md)
is Stage2 and includes the separately root-re-audited stronger cofinal G signs.
Compact summable derivative bounds give the literal full-copy cosine trace
`F'(t)=Re sum_q w_q^2 cos(t w_q)` with no first-power mass assumption.
If F'>=0 eventually, F is eventually bounded below, forcing RH by the
installed not-RH cofinal negative response. Under RH the frequency test at
any actual b=w_q0!=0 has exact Cesaro limit
`average(F'(s)cos(bs)) -> (1/2)sum_{w_q=+-b}w_q^2 >0`.
But eventual F'>=0 and the installed F(t)/t->0 force average|F'|->0,
a contradiction. Eventual F'<=0 contradicts unconditional cofinal
unboundedness above. Thus the paper proof gives BOTH derivative signs
cofinally. If G has either eventual sign, the fixed-prefix Green contribution
bounds the relevant side of F by an integrable exp(-omega*t) correction;
upper escape or the resulting RH resonance contradiction excludes it.
Therefore G also has BOTH signs cofinally. This excludes the blanket G<=0
sufficient condition. It does not
give a negative F. The positive resonant-mass and RH signed-variation laws
are retained in the report; no new formal result or no-go retirement yet.

The integrated Green weight is exactly
`K(t,s)=2/omega*(1-exp(-omega*t)cosh(omega*s))` for 0<=s<=t and
`K(t,s)=2/omega*exp(-omega*s)sinh(omega*t)` for s>=t.
Its strict concavity on (0,t) excludes a positive mixture of decaying
exponentials. Hence the new source-sector proof that every admitted
Laplace average of G is negative does not orient this weight by such a
positive-mixture argument.

The next actual sign attempt instead integrates G once:
`S(t)=integral_0^t G=F''(t)-omega^2 F(t)`.
The odd growth-selected Dirichlet kernel gives
`F(t)=-(2omega)^(-1) integral_0^infinity
 [exp(-omega|t-s|)-exp(-omega(t+s))] S(s) ds`.
Its bracket is positive for t,s>0. An independently proved actual S<=0
would therefore orient F while allowing its necessary derivative
oscillations. Producer attempts that signed full source; root checks the
exact completion/arithmetic cancellation. No sign of S is assumed or
claimed, and the finite-N growing-window target remains OPEN.

Producer's full255-line massive-source proof has passed root's complete
paper/source audit: `/tmp/li_producer_massive_dirichlet_source_sign_attack.md`,
SHA256 `e1683e86b989383fb9c403e623803f2d904a3dffb162d4b0f89b996869c4d2e6`.
The actual all-order factorial series gives the strict fixed-window estimate
`S(t)<-(9/56)omega^2 A t` for EVERY 0<t<=20, with zero included non-strictly.
It uses only M0>=167A/168, M1>0 and the complete all-order bound
|M_j|<=A/150^j. The entire tail is bounded by its geometric majorant;
no higher moment sign or finite truncation is assumed.

The full Dirichlet kernel mass is exactly `2(1-exp(-omega*t))/omega`.
An eventual lower bound on S would bound F above, contradicting actual
unconditional upper escape. Hence S is unbounded BELOW cofinally.
Under the explicit not-RH hypothesis, any eventual upper bound on S would
bound F below and contradict its cofinal negative escape; S is then also
unbounded ABOVE cofinally. Thus even an eventual constant upper bound on
the actual S would imply RH. No such upper bound, RH converse or
unconditional positive S witness has been proved. All new survivors are
paper-only; the fixed-20 result does not settle the unbounded clock range.

Root's concrete arithmetic test now has a complete root144/independent210
paper audit: [massive completion comparison](../../../2-fully-proven/li-clock-massive-completion-comparison.md),
with full source proof `/tmp/li_root_massive_completion_comparison_attack.md`.
Keeping the first five Gamma terms and the complete dyadic bound gives
`omega^2>6429/40000=4/25+29/40000`. Keeping two positive Gamma tail terms
against the FULL dyadic error proves for every j
`(4/25)c_j-c_(j+1)>(3/409600)(1/64)^j`, hence
`C''<(4/25)C` at positive clocks and V=omega^2 C-C''>0.
The exact completed split gives
`S=E-V`, `E=P''-omega^2 P-2(4-omega^2)sinh(2t)`.
However the tempting stronger arithmetic estimate E<=0 is FALSE eventually:
V has a positive sinh(2t/5) lower bound, whereas |S| is at most
`A(omega^2+1/150)t exp(t/300)`. Thus E/V->1 and E>0 eventually.
The ratio ceiling 4/25 is sharp: c_j/(4/25)^(j+1)->1 and
c_(j+1)/c_j->4/25 while all finite ratios are strictly below it.
The needed one-sided inequality E<=V still has no proof. This records an
actual-source test, not a counterexample to S<=0 or completed-clock positivity.

## Current direct theta-source attempt

Return to the installed single-source theta kernel B_theta, retaining its
factor-ONE identity `F*B_theta=t B_theta'`. For S=F''-omega^2F the genuine
candidate forcing is
`J_S=S*B_theta=t B_theta'''+2B_theta''-omega^2 t B_theta'-m0 B_theta`.
Writing nu_j for the actual normalized raw theta moments, its coefficient
on `t^(2j)/((2j)!)^2` is exactly
`nu_(j+1)/(2j+1)-(2j omega^2+m0)nu_j`.
The constant term vanishes since nu_1=m0. The installed source recurrence
`303nu_(j+1)<=(32j+17)nu_j`, together with omega^2>4/25, makes every j>=1
coefficient strictly below -nu_j/4. The ALL-clock forcing estimate is
`J_S<-(B_theta-1)/4<0` at positive clocks. The full source, every fixed
derivative and all convolution admissions passed complete paper audits:
[theta forcing and inverse boundary](../../../2-fully-proven/li-clock-theta-forcing-inverse-boundary.md).
The sharper constant is `eta=2omega^2+m0-49/909>1/4`, with
`J_S<=-eta(B_theta-1)` and `J_S'<=-eta B_theta'`.
This negative convolution does not by itself prove S<=0; Lean remains OPEN.

There is already a concrete actual-kernel test against unrestricted inverse
positivity. With K=B_theta', the same source identity yields
`F'+F'*K=2B_theta''+tB_theta'''`, whose right side is strictly positive,
whereas the audited actual F' is negative cofinally. The stronger odd-input
test is included in final291 `/tmp/li_producer_massive_theta_forcing_attack.md`,
SHA256 `f7f219376559c6411960d839726a9c6ade09bbab81b1cb83426065f077f05cc2`.

The stronger test uses the genuine causal solution of `u+u*K=t`.
Compact Volterra iteration gives an odd entire real solution with u'(0)=1.
If u stayed nonnegative, its fixed positive initial mass and the actual
kernel lower bound `K(v)>=(nu_2/144)v^3` would make u*K eventually exceed
t, a contradiction. A proposed source-specific contour proof further
places u in the same exponential growth class: the normalized ordinary
theta generator is `Phi(z)=XiC(-Iz)/XiC(0)`, and reciprocal-plane integrand
`1/(p^2 Phi(1/p))` has all its nonzero singularities at
`p=-I*(xiSpectralPoint q)^(-1)`. Complete reciprocal square
summability and the strict imaginary bound supply one uniform strip
strictly narrower than 1/300. A rectangle enclosing that strip, its finite
radial bound and zero gives a genuine contour estimate for u. Root and
Producer have independently closed this contour argument on paper, and
the complete final packet passed root's whole-proof review.
The response u is for the actual kernel but is not the target F or S.
Their source-specific sign remains OPEN.

Root's stronger coefficient test is recorded in
`/tmp/li_root_theta_resolvent_coefficient_boundary.md`, SHA256
`420b525658dbe7c6f5fd0253e2c4efaeb0eb90049bd3e6a4409bb7500d923f19`.
The odd entire resolvent r=-u'' satisfies `r+r*K=K` and r'(0)=nu_1/2>0.
The actual input K has strictly positive coefficients at EVERY odd degree.
If r were nonnegative, its equation would give r<=K; Cauchy bounds for the
entire ordinary generator make K of every positive exponential type,
so the genuine Laplace identity holds for all p>0 under that supposition:
`R(p)=1-1/Phi(1/p)`. Positivity then gives integral r=1, while
`(1-R(p))/p<=2p/nu_1` gives integral t*r=0, contradicting r'(0)>0.
Thus r is negative somewhere, still in the same strict sub-1/300 growth
class. This full root proof passed independent paper audit; Lean OPEN.

For the literal target forcing `g=-J_S'`, the exact compact-convolution
resolvent formula is `-S=g-r*g`. The all-clock source coefficient calculation
gives g>=K/4 coefficientwise. That coefficient cone already contains K,
whose inverse r changes sign. The actual remaining comparison is therefore
`r*g<=g` at EVERY positive clock, using the particular g; this comparison
has not been proved. No inverse positivity or RH consequence is claimed.

## Current first-crossing test

The audited direct source test keeps `S+S*K=-g`, K=B_theta', g=-J_S'.
If S is negative before a first positive zero T, its exact endpoint law is
`g(T)=integral_0^T (-S(s))K(T-s) ds` and
`S'(T)=-g'(T)+integral_0^T (-S(s))K'(T-s) ds`.
A source-specific bound on this last weighted integral could prevent an
upward crossing. The coarse quotient estimate is unavailable:
K(v)=(nu_1/2)v+O(v^3), hence K'(v)/K(v) is unbounded as v decreases to zero.
The vanishing S(T)=0 must be retained inside the endpoint weight. Replacing
the nonnegative history -S by g cannot supply a global comparison: both
`(g*K)/g` and `(g*K')/g'` are unbounded above cofinally for the literal g.
The complete [source-history boundary](../../../2-fully-proven/li-clock-theta-source-history-boundary.md)
also proves strictly increasing actual g/K and coefficient increments
greater than 6047/22725. Its qualitative inverse counterexample does not
preserve this quantitative increment bound or the full actual ratios.

The [signed-mass boundary](../../../2-fully-proven/li-clock-theta-resolvent-signed-mass-boundary.md)
proves that both signs of the actual r have infinite ordinary mass and
share the exact weighted integrability threshold p>beta, where
beta=max_q abs(Im((xiSpectralPoint q)^(-1))). It does not prove beta=0.
Both new papers pass complete audits; Lean formalization remains open.
The exact source comparison r*g<=g, and hence crossing exclusion, remain
OPEN. No negative actual S/F witness has been obtained.

### Audited quantitative-ratio and finite-jet boundary

The complete [tail-inverse proof](../../../2-fully-proven/li-clock-theta-tail-inverse-boundary.md)
passes full root/independent paper audits. EVERY complete tail K_J of the
SAME actual K has an exact inverse positive near zero and negative somewhere.
Adding a sufficiently large multiple of K_J to the actual g retains any
preassigned finite odd input and response jets and ALL actual quantitative
ratio-increment lower bounds, yet yields a negative inverse value.
This changes the forcing; it supplies no negative actual -S witness.
The construction violates the untested actual narrow band
`2j*omega²+m0-49/909 <= alpha_j < 2j*omega²+m0`
and the exact moment-ratio formula. These complete source constraints remain
available for the literal r*g<=g comparison. The positive tail classification
and finite-jet obstruction are paper-proved; Lean formalization remains OPEN.

### Literal moment-ratio tightening proved on paper

The next source calculation retains the exact formula
`g=omega²*(K+t*K')+m0*K-(K+t*K')''`.
Complete independent paper/source audit proves
`nu_(j+1)/((2j+1)*nu_j) -> 0` from the actual first-atom likelihood
comparison and Ward identity, with a consequent
`(K+t*K')''/K -> 0`. The exact raw-moment ratio and its three source
bounds now pass all local Lean/source/compiler/axiom/integration checks;
R0 cancels in the normalized ratio. Full D/K formalization is next.
No transfer of this relative forcing estimate through the signed inverse
is admitted, and no new sign of the literal response is claimed.

## Log

- 2026-10-01 — Derivative first leaf24 is now fully source/compiler/axiom checked: both complete reviews, exact direct/named checks, imported all24 foundational reports and wiring/API pass. Full two-leaf survivor remains open. Root opens the [literal integrated-clock sign test](../../li-clock-integrated-source-sign.md), retaining the exact source and auditing its eventual-sign receiver; Producer continues the literal massive-source ratio attack.

- 2026-10-01 — Tail-inverse178/independent118 audits pass: every actual positive kernel tail has a sign-changing inverse; no finite literal jet plus quantitative ratio-increment lower bounds can orient all inputs. Exact actual ratio band remains untested. MixedLimit26 completes proof/axiom/direct/named checks and wiring. Derivative first24 passes both whole-source reviews and exact tree direct check; named/imported-axiom gates are running. Latest global lint passes catalog freshness but reports eleven unrelated unwired modules. Neither full two-leaf survivor is complete.

- 2026-10-01 — Complete source-history251 and signed-mass159/independent71 audits pass. Literal majorant ratios are cofinally unbounded; both resolvent signs share a sharp exponential integrability boundary. Exact quantitative forcing ratios remain a possible source constraint, not a proved orientation. Both survivors recorded in Stage2; RH and the actual r*g comparison remain open.

- 2026-10-01 — Complete final291/root121 theta audits pass. All-clock negative forcing, strict sub-1/300 inverse contour admission and actual positive-coefficient inverse obstruction promoted to Stage2 with complete paper proof. Exact remaining actual comparison is r*g<=g; no RH-bearing sign or new Lean theorem claimed.

- 2026-10-01 — Whole Current305 and Producer233 audits pass: exact entire E/EJ, every-positive-type remainders, all-p Laplace admission, Gamma compatibility roots and both-sign R/Q. Derivative160/independent192 give cofinal F' and G signs with full resonant/variation survivors. Mixed-profile503 typed plan reviewed and two-leaf implementation released. New massive Dirichlet source S is under direct attack; exact arithmetic/completion ratio cancels to one but its side remains open. No RH-bearing sign has been proved.

- 2026-10-01 — Root checks a potential overstrength in the growth-selected Neumann argument: a globally nonpositive combined forcing would imply F'>=0, whereas the required target is only F>=0. Under RH the full derivative should be a uniformly almost-periodic cosine sum with zero mean, positive at zero, so global derivative nonnegativity may already be impossible. This is a conjectured obstruction pending direct corpus/source audit, not a claimed theorem or a substitute for the target. Full signed R/Q source audits and mandatory survivor formal planning continue separately.

- 2026-10-01 — New direct attempt initiated after the failed comparisons: apply `(d^2/dt^2-4)^2` to the SAME complete identity J=2F*B, canceling its exact double exponential leading mode before any estimate. Candidate endpoint calculation is `(d^2-4)^2 J=2F'''+2(B''(0)-8)F'+2F*((d^2-4)^2B)`. Producer is auditing all endpoints and attempting an actual arithmetic sign estimate with the known growth bound; two-sided remainder control alone is not accepted as orientation. No new theorem or successful sign claimed.

- 2026-09-30 — Original objective and current source frontier rechecked. Prior turn finalized relative Volterra38; this turn returns to the missing compensation sign. One stale frontier sentence claiming the relative expansion remained Lean-open was corrected. Root normalized-forcing comparison and two disjoint direct source attacks initiated; no hard sign proved.

- 2026-10-01 — Complete394-line actual ratio-band paper independently audited PASS: [exact source correction](../../../2-fully-proven/li-clock-theta-exact-ratio-band.md). Actual delta_j→0 and D/K→0; SAME correction inverse v is negative cofinally. This defeats positive-order transfer for that component, while literal y=omega²F+m0r−v remains open. No RH result; exact survivors await Lean.

- 2026-10-01 — Four exact theta ratio/source bounds now complete locally in Lean. Mixed-profile second leaf24 also passes both full-source reviews, named/direct checks and imported all24 foundational axiom reports; all50 two-leaf exports are indexed and wired. Derivative-oscillation second leaf18 passes both full-source reviews, named/direct checks and imported all18 foundational axiom reports; all42 two-leaf targets pass owned checks. Root read both complete final certificates and every imported axiom report. Index47749 fresh; lint74901 reports11 unrelated unwired modules, no owned error. Literal sign stays OPEN.

- 2026-10-01 — Integrated source cumulant349/independent root audit PASS: actual third Lah bracket positive throughout0<z<300 despite kappa3<0 near0; complete reciprocal raw germ has exact radius and infinitely many ratio drops; genuine whole-line tilted Ward identities retain the unknown signed correlations. All-order source inequality remains OPEN. Same-B/K fixed-shift flattening paper125/independent148 now PASS; [corrected final139 paper](../../../2-fully-proven/li-clock-theta-kernel-flattening.md) records the existing B degree-escape overlap. Fixed shifts still do not control the full signed history. Exact D/K nine-public scratch implementation is released; no new tree claim for that survivor yet.
