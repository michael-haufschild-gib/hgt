# PM: actual logarithmic convolution and signed covariance balance

- **Stage:** 1-in-progress
- **Type:** actual-source upper-energy proof attempt
- **Target:** the complete signed canonical energy at arbitrarily small positive real damping; no unknown bound is introduced as a Lean premise.

## Corpus basis and failed moment step

Search168 was partial, inventory65072 complete and compiler freshness mixed. All20 candidate statements,20 source statements and both ingredient steps were inspected. The returned alternative Ramanujan sources do not identify the PM source. Direct inspection of `ZetaGaussianTwistedMoment` shows off-diagonal suppression requires Gaussian width large relative to the integer twist; it cannot cover bounded frequencies while those twists grow. `MatomakiTeravainenTwistedFourthMoments` retains explicit `MTWattBound`/`MTDeshouillersIwaniecBound` hypotheses. Neither supplies the actual complete joint moment.

Search169 was partial, inventory65077 complete and compiler freshness mixed. All20+20 statements and both ingredients were inspected; generic logarithmic-phase results are inapplicable. Exact source search located `DirichletLogDerivation`, `Sieve.MoebiusLogRecursion`, `Sieve.DivisorSwap`, and the current actual PM divisor coefficients and centered prefixes. It found no PM logarithmic centered recursion.

## Source-specific mechanism

Write c(n)=sum_(d|n) mu(d)d^(-epsilon), alpha=Re(1/zeta(1+epsilon)), r(n)=c(n)-alpha for n>=1, R(N)=sum_(n<=N)r(n), and

`b(d)=Lambda(d)*(1-d^(-epsilon))`,
`l(n)=sum_(d|n)Lambda(d)*d^(-epsilon)`.

Logarithmic differentiation in the finite Dirichlet convolution ring gives the exact identities

`c(n)*log n = sum_(d|n)b(d)*c(n/d)`,
`r(n)*log n = sum_(d|n)b(d)*r(n/d) - alpha*l(n)`.

For epsilon>0, both b and l are nonnegative. Thus centering exposes an explicit negative forcing, not an unknown error term. Summing through the exact divisor swap gives

`sum_(n<=N)r(n)*log n = sum_(d<=N)b(d)*R(floor(N/d)) - alpha*sum_(d<=N)Lambda(d)d^(-epsilon)*floor(N/d)`.

Finite Abel summation then yields R(N)log N as this expression plus the entire lower-prefix logarithmic sum. Multiplication by the actual R(N)/(N(N+1)) and finite summation gives a signed quadratic balance retaining every mixed dilation and forcing term.

The coefficient law follows by twisting the existing Mobius logarithmic derivative identity with the completely multiplicative real power weight, then applying the existing logarithmic Leibniz rule to c=mu_epsilon*zeta. The centered law uses sum_(d|n)Lambda(d)=log n exactly. No analytic continuation or convergence hypothesis is needed for these finite identities.

## Hard conjecture and present limit

The proposed producer is coercivity of this complete centered quadratic balance on the literal actual prefix: the combined dilation covariance and explicit forcing should leave a positive canonical energy margin after the complete logarithmic lower-prefix term is retained. A pointwise sign for R, dropping the forcing, or treating the positive convolution kernel as a contraction is not justified. The exact finite law is being formalized to expose the actual terms before attempting this coercivity estimate. This is not an upper bound or an RH proof.

## Concrete coercivity question

Let E_N=sum_(1<=n<=N)R(n)^2/[n(n+1)] and let D_N,P_N,F_N be the three full covariances in the companion finite-identity theorem. The current source-specific conjecture is: for each epsilon>0 there is a finite C_epsilon>=0 such that

`D_N-alpha*F_N <= C_epsilon*(1+E_N)`

for every N. It is not asserted in Lean. The lower-prefix operator is of Hardy type and can be paid by a fixed multiple of E_N; this separate operator bound is not yet proved in this card. With that bound, the exact logarithmic balance absorbs the tail where log n exceeds C_epsilon plus the Hardy cost, leaving only a finite head. That would give the required uniform E_N bound and actual admission. The difficult arithmetic estimate is the displayed combined covariance, not a sign of either term separately.

The complete finite coefficient, centered prefix and three-covariance identities passed the full scratch check with no diagnostics. They are promoted in `PMPowerDampedMobiusLogConvolution.lean` and wired once; targeted old-mode leaf build is running. Paper proof and audit are tracked separately in `../3-formalized/pm-logarithmic-divisor-balance.md`. No coercivity conclusion or RH claim.

## Test of separating the two arithmetic covariances

A further paper test predicts that separate boundedness of D_N and F_N is false even in the already admitted regime epsilon>1. There the fractional-part representation is uniformly absolutely dominated. The periodic mean of frac(n/d) is (d-1)/(2d), so the expected actual integer-prefix mean is

`beta_epsilon=(alpha_epsilon-Re(1/zeta(epsilon)))/2 > 0`.

The normalized positive forcing tends to

`K_epsilon=sum_(d>=1)Lambda(d)*d^(-1-epsilon) > 0`.

If the two elementary mean passages and logarithmic averaging are verified, they give `F_N/log N -> beta_epsilon*K_epsilon` and, using the exact energy identity with bounded R, `D_N/log N -> alpha_epsilon*beta_epsilon*K_epsilon`. Their leading logarithmic divergences then cancel only in D_N-alpha_epsilon*F_N. This remains a paper candidate, not a newly proved Lean theorem. Search170 checks existing actual mean and averaging tools before any formalization.

This test is directed at the combined coercivity proof: no finite upper bound for either separate covariance may be used. For small damping, the absolute domination used in this test is unavailable; it cannot be extrapolated into the missing upper estimate.


2026-10-04 audit closure: all twelve public exports of the finite logarithmic balance are fully audited; leaf build60s, final actual-file Lean exit0 empty, all standard axioms only, umbrella once, indexes refreshed. Lint12 unrelated unreachable leaves, none own. The combined small-damping coercivity conjecture is still open. Search170 completed (not partial), inventory65089 complete, mixed compiler freshness; all20 candidate/20 source statements and both ingredient steps were inspected. It returns the existing actual fractional-part representation and damped L-series identity but no integer remainder-mean or joint covariance limit. The paired-divergence test remains paper-only; it must not be extrapolated to small damping.

All owned build/audit/search/index processes are terminal. Completed scratch, axiom queries, searches168-170 and logs cleaned. Continue on the actual combined small-damping covariance; the finite identity audit must not be repeated without a code change. The lower-prefix Hardy estimate and the large-damping separate-divergence test are supporting questions, not replacements for that hard arithmetic estimate.

## Centered divisor semigroup test (2026-10-04)

**Outcome: no advance in the small-positive-damping upper bound.** The finite logarithmic balance is already audited and was not rebuilt. The following calculations are paper work, not new Lean exports. They test a producer for the actual combined covariance; the route is not retired.

Search171 (inventory65091), search172 (65094), search173 (65098), and search174 (65102) completed without a partial flag. Every returned candidate/source statement and ingredient group was inspected. Inventories were complete; compiler freshness was mixed, semantic coverage unmeasured, and background refresh incomplete. Search171 returns the actual Mobius/Mangoldt convolution and generic inequalities with extra covariance/coercivity hypotheses. Search172 returns the actual divisor source, gcd valuation minimum, and unrelated finite Markov norms. Search173 supplies no applicable divisor-semigroup estimate. Search174 supplies no actual centered-prefix sign theorem; its sign and damping hits use other sources. None supplies an unconditional bound for D_N-alpha*F_N. Direct source checks also covered `DampedMobiusSumsZeroFree`, the actual centered energy/variance leaves, and the prior phase-window/Jensen tests in `pm-centered-divisor-dyadic-energy-budget.md`.

Let `D_epsilon f(n)=n^(-epsilon)f(n)` and use `*` for finite Dirichlet convolution. For n>0 define

`T_epsilon f = zeta * D_epsilon(mu*f) = c_epsilon * D_epsilon f`.

Complete multiplicativity of the power weight and `mu*zeta=delta_1` give the semigroup identity `T_epsilon T_delta=T_(epsilon+delta)`. Its row weights are

`T_epsilon f(n)=sum_(d|n) d^(-epsilon)c_epsilon(n/d)f(d)`.

For epsilon>=0 they are nonnegative and sum to one: apply the convolution identity to the constant arithmetic function zeta. Thus this is a positive Markov action on coefficient sequences. Its prime-power transition from exponent r ends at j<r with weight `p^(-j*epsilon)(1-p^(-epsilon))`, and stays at r with weight `p^(-r*epsilon)`. This finite formula does not require constructing an infinite random integer.

The crucial failure of the attempted inference is that natural density is not invariant. The initial point mass delta_1 has density zero; its image is c_epsilon, with the already proved positive density alpha_epsilon. Hence the uncentered prefix-energy summands tend to alpha_epsilon^2 and cannot be summable. Row-stochasticity and coefficient sup-norm contraction therefore do not establish contraction in the canonical centered prefix norm. No centered contraction was proved or assumed. The existing canonical finite-prime aperture divergence also forbids replacing the actual natural cutoff by a uniformly bounded prime aperture.

For a finite-support coefficient sequence f the exact centered image would instead be

`sum_m f(m)m^(-epsilon)R_epsilon(x/m)`

with its full finite support retained, including m>x where `R_epsilon(x/m)=-alpha_epsilon*x/m`. Its density is `alpha_epsilon*sum_m f(m)m^(-1-epsilon)`. Omitting those terms loses the density subtraction. Applying this formula to delta_1 returns the same unresolved actual remainder; it is not an independent upper estimate.

A second paper derivation retains centering directly in the damping derivative. Put

`K_epsilon=sum_(d>=1)Lambda(d)d^(-1-epsilon)`.

The finite coefficient derivative and absolutely convergent density derivative give

`partial_epsilon c_epsilon = (Lambda(d)d^(-epsilon))*c_epsilon`,
`partial_epsilon alpha_epsilon=alpha_epsilon*K_epsilon`,
`partial_epsilon R_epsilon(x)=sum_(d>=1)Lambda(d)d^(-epsilon)R_epsilon(x/d)`.

For fixed x and epsilon>0 the last series has only finitely many terms with d<=x; its remaining tail is exactly `-alpha_epsilon*x*sum_(d>x)Lambda(d)d^(-1-epsilon)`, which converges absolutely. Thus centering is retained by that tail, rather than discarded as an external error. No infinite Hilbert-norm interchange is justified by this pointwise identity.

For the continuous canonical energy truncated at X, the proposed next estimate is a lower bound for its damping derivative, uniform in X and in epsilon on each compact positive interval. A bound `partial_epsilon E_epsilon,X >= -C_eta*(1+E_epsilon,X)` on eta<=epsilon<=1/2 would propagate the known half-damping energy bound backward to eta by an elementary differential inequality. This is an unproved arithmetic conjecture, not a Lean premise or a substitute theorem. Its signed pairing is precisely the actual remainder against the complete centered Mangoldt dilation series. The absolute dilation norm again demands the half-damping threshold, so an absolute operator estimate is insufficient. Keep this as a possible attack on the existing combined-covariance target; do not promote the semigroup identities alone as an upper-bound advance.

The earlier phase-window idea was checked against the prior working log rather than repeated: infinite vertical averaging gives a finite diagonal for positive damping, but fixed-window mean-value error retains `sum_(d<=N)mu(d)^2/d^(2*epsilon)`. Its limit interchange remains unpaid. Neither that averaging nor a pointwise sign for the centered remainder has been used.

For precision, the last candidate uses `E_epsilon,X=integral_(0,X) R_epsilon(x)^2 dx/x^2`, including the exact interval 0<x<1. At finite X its derivative is twice

`Q_epsilon,X=sum_(d>=1)Lambda(d)d^(-epsilon) integral_(0,X) R_epsilon(x)R_epsilon(x/d) dx/x^2`.

The finite-X interchange has a direct absolute majorant: `|R_epsilon(x)| <= (1+alpha_epsilon)x`, so the integrated absolute d-term is at most `(1+alpha_epsilon)^2 X Lambda(d)d^(-1-epsilon)`. This does not give a uniform-X estimate. With `g_epsilon,X(u)=exp(-u/2)R_epsilon(exp u)` for u<=log X and zero otherwise, the same term is `d^(-1/2)` times its translation autocorrelation at log d. The hard target is therefore the signed Mangoldt-weighted autocorrelation of this exact source, with its prescribed exponential tail, not arbitrary test vectors or the absolute sum of translation norms.

Search175 completed (inventory65107 complete, mixed compiler freshness, semantic coverage unmeasured, background refresh incomplete); all20+20 candidate/source statements and both ingredient steps inspected. The lower bound for a reciprocal Mobius tail by a different physical energy, a primitive-ratio identity, and generic covariance equalities do not supply an upper estimate for this actual Q. No numerical jobs, Lean edits, builds, or additional axioms were used this turn. Searches171-175 are terminal and their owned temporary outputs are cleaned after inspection. The hard combined-covariance bound remains open; the new centered-flow estimate is paper-only and unproved.

## Density-normalized flow and continuum cancellation test (2026-10-04)

**Upper-bound status unchanged.** Previous turn supplied evidence changing the next proof attempt, but no small-damping energy theorem. This turn tested the actual derivative current rather than adding a conditional receiver. No Lean source was changed. All formulas in this section are paper calculations awaiting formal audit; no no-go or RH result is declared closed.

The density-normalized function `v_epsilon(x)=R_epsilon(x)/(alpha_epsilon*x)` obeys

`partial_epsilon v_epsilon(x)=sum_d Lambda(d)d^(-1-epsilon)*(v_epsilon(x/d)-v_epsilon(x))`.

Here the rates are nonnegative and have finite sum K_epsilon. This is the conservative normalization missing from the preceding coefficient-level argument. It does not establish the needed contraction: dilations preserve dx/x, whereas the canonical energy is `alpha_epsilon^2*integral v_epsilon(x)^2 dx`. On dx the norm of v(x/d) gains sqrt(d), again producing the unpaid sum `sum Lambda(d)d^(-1/2-epsilon)`. Moreover v=-1 below x=1, so its own global L2(dx/x) norm is infinite; even the invariant-measure contraction cannot be applied to v without treating this boundary. This diagnosis uses the literal density tail, not a general assertion about Markov operators.

A direct actual-source stress test rejects termwise nonnegative truncated correlations. Write alpha=alpha_epsilon and

`I_epsilon,2(a)=integral_(0,2) R_epsilon(x)R_epsilon(x/a) dx/x^2`.

The source definition gives R=-alpha*x on 0<x<1 and R=1-alpha*x on 1<x<2. For every a>=2, R(x/a)=-alpha*x/a almost everywhere on this head. Thus the exact paper law is

`I_epsilon,2(a)=-alpha*(log 2-2*alpha)/a`,
`E_epsilon,2=1/2-2*alpha*log 2+2*alpha^2`,
`Q_epsilon,2=-alpha*K_epsilon*(log 2-2*alpha)`.

The corpus theorem `tendsto_pmPowerDampedDivisorDensity_re_div_parameter` gives alpha/epsilon ->1, and alpha>0 is already proved. Hence every dilation a>=2 has strictly negative head correlation at sufficiently small positive damping. This concerns the truncated actual source; it makes no claim about the full correlation on (0,infinity). Its finite cost is allowed by the proposed lower bound with 1+E. Do not replace the full signed estimate by a termwise sign, and do not present this elementary head calculation as the hard upper-bound advance.

A second test asks whether the source's moving Mellin zero removes the continuum part of Q. For 0<epsilon<1/2 there is a paper route to the unconditional weighted endpoint

`integral_0^infinity |A_epsilon(t)|*t^(-epsilon) dt < infinity`,
`mellin A_epsilon (1-epsilon)=0`.

Its corpus basis is the exact raw-prefix Haar head, arbitrary logarithmic savings for raw-prefix square energy, the existing finite Abel identity, and convergence of sum_(n<=N)mu(n)/n to zero. Split the weighted raw-prefix norm at t=1/(N+1). The Haar head has bounded weighted norm. Cauchy-Schwarz on the complementary interval gives a tail O_epsilon(N^epsilon/log^2 N), using a sufficiently strong existing logarithmic energy saving. Finite Abel summation then has a vanishing boundary and summable gap norms O(1/(n log^2 n)). Its weighted L1 limit is the literal source, and each finite Mellin value at s=1-epsilon is the seed factor times sum_(n<=N)mu(n)/n. The backward dyadic reconstruction transfers weighted L1 admission and the zero to F_epsilon(t)=R_epsilon(1/t). This endpoint has not been formalized here, and no extension to epsilon>=1/2 follows from that Cauchy-Schwarz step.

Even granting this endpoint does NOT cancel the complete critical quadratic continuum. Put R_X=R on (0,X) and zero elsewhere, and `M_X(s)=integral R_X(x)x^(-s-1) dx`. The absolutely justified finite-X correlation factorization is

`integral_0^infinity a^(-epsilon) integral_0^infinity R_X(x)R_X(x/a) dx/x^2 da = M_X(epsilon)*M_X(1-epsilon)`.

The second factor tends to zero. The complementary first factor has no proved uniform bound in the small-damping range; the weighted endpoint alone permits growth of order X^(1-2*epsilon). Therefore multiplying the vanishing moment by that factor is an invalid zero-limit argument. A continuum subtraction must retain this product as a boundary term. Formalizing the weighted endpoint alone would not pay this missing quadratic estimate, so it has not been promoted as a substitute for the hard task.

The active next object remains the complete Q_epsilon,X, equivalently the earlier combined logarithmic covariance. A usable compensated-prime estimate must retain both the actual signed dilation correlations and the complementary Mellin boundary product. Generic invariant-measure contraction, positivity of individual terms, and dropping the continuum boundary all fail to establish that estimate. No conclusion about RH or its negation follows from these tests.

Search176 completed, inventory65113; search177 completed, inventory65117; search178 was partial, inventory65118. Every candidate/source statement and generated ingredient group was inspected. Inventories complete, compiler freshness mixed, semantic coverage unmeasured, background refresh incomplete. The unfiltered derivative/dilation hits mostly concern other sources. The PM-filtered query returns the actual initial Mellin formula and the L2-dependent continuation; the latter cannot establish unconditional small-damping admission. Relevant raw-prefix, endpoint, density-limit, and harmonic-partial source statements were inspected directly. All owned searches are terminal; temporary outputs176-178 cleaned after inspection. No numerical experiments, build processes, or Lean scratch files were created this turn.

One useful algebraic refinement of the retained boundary is available for the next hard estimate. For 0<epsilon<1/2, let I_X(a) be the correlation of R_X with its dilation, as in the factorization above. Reciprocity gives `I_X(1/a)=a*I_X(a)`, hence

`M_X(epsilon)M_X(1-epsilon)=integral_1^infinity (a^(-epsilon)+a^(epsilon-1))*I_X(a) da`.

The complementary prime current `Qtilde=sum_d Lambda(d)d^(epsilon-1)I_X(d)` is harmless relative to E_X: Cauchy-Schwarz gives `|I_X(d)|<=E_X/sqrt(d)`, and `sum Lambda(d)d^(epsilon-3/2)` converges for epsilon<1/2. Thus the actual hard current Q equals the symmetric prime-minus-continuum form, plus the displayed Mellin boundary product, minus Qtilde. The nontrivial next inequality is a lower bound for the symmetric compensated form TOGETHER WITH that boundary product. Discarding the product reintroduces the failed limit argument. This decomposition is not an upper-energy theorem and should not become another conditional receiver; its purpose is to target the precise arithmetic cancellation against available prime/continuum source laws.

Endpoint caution for that refinement: the absolute Qtilde constant is only finite for each epsilon<1/2 and diverges as epsilon approaches1/2. It is not uniform on [eta,1/2], so it cannot by itself anchor the proposed backward differential inequality at the known half-damping endpoint. Any propagation proof must retain the complementary term near that endpoint or prove a separate uniform cancellation there. The fixed-epsilon combined-logarithmic-covariance target remains valid independently of that propagation attempt.

## Retained-current and damping-curvature attempts (2026-10-04)

**No upper-bound advance this turn.** The work below tests two possible proofs of the actual bound; neither closes it. No Lean source, axiom, receiver, or numerical experiment was added. The already audited logarithmic balance was not rebuilt. The route and its hard conjecture remain active.

Search179 completed without a partial flag, inventory65128; search180 was partial, inventory65132. All20 candidate and20 source statements from each search, and the generated ingredient groups (present only in179), were inspected. Inventories were complete, compiler freshness mixed, semantic coverage unavailable, background refresh incomplete. Search179 supplies Mellin convolution and finite Mobius floor identities, not the joint lower bound. Search180 supplies no actual PM damping-convexity theorem; the actual endpoint-cutoff upper bound it returns explicitly assumes source admission.

Direct checks of the current-producing leaves matter here. `summable_norm_deningerVonMangoldtAutocorrelation` requires an exponential autocorrelation bound with exponent above one; that bound has not been established for this PM source. `PairedCompletedEulerCurrent.polar_sub_prime_real` uses a finite exponential packet with damping bounded strictly above one half. Its prime-current summability cannot be carried to the missing small-damping regime by the identity alone. The full Weil-positivity input in `riemannHypothesis_iff_exists_weilPositiveFull_summable_deficit` is RH-equivalent and cannot be assumed. None of these statements pays the actual compensated form plus retained Mellin product. Finite Nyman coefficient prefixes have a zeta factor in their Mellin transform, but spatial truncation of the actual R does not preserve those Mellin zeros; replacing one cutoff by the other requires retaining the source-change terms.

A direct interpolation attempt was also tested on the literal remainder, rather than inferred from these other sources. At each finite X, introduce the pointwise dilation operators

`T_epsilon f(x)=sum_d Lambda(d)d^(-epsilon)f(x/d)`,
`U_epsilon f(x)=sum_d Lambda(d)log(d)d^(-epsilon)f(x/d)`.

On the actual R, R' and their fixed-X restrictions, the tails carry the same linear density term as above. For epsilon in a compact positive interval, their weighted scalar majorants are sums of Lambda(d), Lambda(d)log(d), and their convolution against d^(-1-eta). These converge. Thus the paper differentiation retains the complete tail and gives

`R'=T_epsilon R`,
`R''=(T_epsilon^2-U_epsilon)R`,
`E_epsilon,X''=2*integral_(0,X)(T_epsilon R)^2 dx/x^2
  +2*integral_(0,X)R*(T_epsilon^2-U_epsilon)R dx/x^2`.

These are paper identities, not new Lean exports. They do not establish convexity. The finite Dirichlet coefficient of T^2-U at every prime power p^k, k>=1, is exactly `-(log p)^2*p^(-k*epsilon)`: the k-1 ordered two-power decompositions are offset by the k from log(p^k). At p^a*q^b for distinct primes it is `2*log(p)*log(q)*(p^a*q^b)^(-epsilon)`. Consequently the proposed proof by nonnegative convolution coefficients fails. Negative coefficients alone do NOT show that actual E has negative curvature; the full actual pairings remain unsigned and must be estimated jointly. No convexity countertheorem is claimed.

Uniform convexity of these finite-X energies between their right limit at damping zero and damping one half would itself prove the missing admission: the first endpoint is at most one and the half-damping endpoint has the existing uniform energy bound. Neither endpoint admission, coefficient positivity, nor scalar analyticity supplies this convexity. The already audited failure of a canonical Hilbert tangent at zero also prevents replacing the missing estimate by a uniformly bounded first-order source expansion.

The next proof attempt must therefore estimate the actual signed current directly, including its density tail and the natural-cutoff source change. Replacing the missing first-variation estimate by an equally unproved curvature sign is not progress. The target remains `D_N-alpha*F_N <= C_epsilon*(1+E_N)`, or a genuinely cutoff-uniform lower estimate for Q that can be anchored at half damping. No generic positivity, Mellin-zero deletion, or interpolation hypothesis will be inserted to discharge it.

## Natural-cutoff transfer and retained primitive current (2026-10-04)

**The hard upper bound is still unproved.** The previous turn counts as evidence changing the next action, not as an energy advance. This turn inspected the literal source-change formula and tested a small-density contraction before working out a boundary-retaining primitive formulation. No new Lean source or receiver was added, and no existing proof was rebuilt.

Search181 completed, inventory65136; search182 was partial, inventory65143. All20 candidate/20 source statements from181 and20 candidate/4 source statements from182, plus both searches' proposed ingredient groups, were inspected. Inventories were complete; compiler freshness mixed, semantic coverage unavailable, refresh incomplete. Generic signed-measure variation does not pay signed cancellation. The PM-filtered hits return the exact transfer, its summable absolute kernel, and already known prime-aperture obstructions. Direct current-state reads covered the audited logarithmic balance, the cutoff-prime difference/quadratic laws, the exact harmonic hyperbola split, and the transfer/product/mass formulas.

The small-density contraction attempt fails at its proposed norm estimate. In the exact transfer, write `K_epsilon(m,r)=pmPowerDampedRamanujanTransfer epsilon m r` and `w(m)=|a_epsilon(m)|`. The product formula gives

`K_epsilon(m,1)=w(m)`, `sum_m K_epsilon(m,1)=1`.

Thus alpha_epsilon becoming small does not make the full undilated channel small: summing all m restores mass one. The absolute double-kernel mass is at least one before any r>1 term is counted. This excludes the proposed strict contraction from that absolute mass, not a possible signed source-specific estimate. The r=1 inputs still have different natural cutoffs `Q/m`; replacing them by one common vector would discard the very source change needing control. Likewise, the cutoff-prime sign theorem for invariant inputs does not apply to these varying actual prefixes.

A paper calculation now retains the continuum term as a finite-cutoff energy identity instead of dropping a product of Mellin moments. For 0<epsilon<=1/2 put

`a=1/2-epsilon`,
`g(u)=exp(-u/2)*R_epsilon(exp u)`,
`k(u)=integral_(v<=u) exp(a*(u-v))*g(v) dv`,
`h(u)=g(u)+a*k(u)`.

These are defined from the actual source, with no L2 assumption and no Mellin-zero hypothesis. For u<0, `g(u)=-alpha*exp(u/2)` and `k(u)=-(alpha/epsilon)*exp(u/2)`. Every finite-upper-limit integral is therefore defined, and k is locally absolutely continuous with `k_u=h` almost everywhere. For L=log X, integration of `(k^2)'=2*k*g+2*a*k^2` gives the exact paper law

`integral_(-infinity,L) g*k = k(L)^2/2-a*integral_(-infinity,L) k^2`.

Here k is precisely the continuum dilation of g: with

`T_epsilon f(u)=sum_d Lambda(d)d^(-epsilon-1/2)*f(u-log d)`,
`C_epsilon f(u)=integral_0^infinity exp(a*v)*f(u-v) dv`,
`P_epsilon=T_epsilon-C_epsilon`,

one has `k=C_epsilon g`. Consequently the complete original current is

`Q_epsilon,X=integral_(-infinity,L) g*(P_epsilon g)
  +k(L)^2/2-a*integral_(-infinity,L) k^2`.

The positive cutoff square and the negative primitive energy must both remain. This identity does not bound either term uniformly in X. It is a sharper bookkeeping statement than setting the moving Mellin moment to zero, not an upper-energy theorem.

Differentiating the past integral with `a_epsilon=-1`, using the complete actual damping flow, gives the further paper system

`partial_epsilon k=P_epsilon k`,
`partial_epsilon h=P_epsilon h`.

The first equality follows from `partial_epsilon C_epsilon=-C_epsilon^2` and commutation of the past dilation integrals; the second uses h=g+a*k and C_epsilon*g=k. On compact positive damping intervals, fixed-upper-limit interchanges have the same convergent density-tail majorants as the original flow, with an additional logarithm for the kernel derivative. No global Hilbert interchange is used.

This leaves a concrete possible attack: the actual joint primitive energy `F_epsilon,L=integral_(u<=L)(k^2+h^2)` satisfies

`partial_epsilon F=2*integral_(u<=L)(k*P_epsilon k+h*P_epsilon h)`.

Since g=h-a*k and 0<=a<1/2, a bound for F controls the original truncated energy. The displayed joint signed current has no separated `1/(1/2-epsilon)` absolute Hardy constant. A cutoff-uniform lower bound for it, together with a proved uniform half-damping F anchor, would support backward propagation. Neither ingredient is supplied here: half-damping admission of g alone does not prove admission of its primitive k, and a general operator bound for P is not being assumed. The next hard work is the source-specific joint prime-minus-continuum pairing, with this explicit anchor obligation retained. Do not formalize this reduction as a substitute for estimating that pairing.

Searches181-182 are terminal; their owned temporary outputs were cleaned after inspection. No numerical experiments, Lean scratch files, or live build processes remain from this turn.

## Half-damping primitive anchor and direct current test (2026-10-04)

**Contribution:** a dependency-based paper proof of the primitive anchor, not a proof of the small-damping current estimate. No Lean theorem is claimed. The prior turn changed the next proof attempt through the exact transfer-mass test and retained primitive formulation; it did not advance the upper bound. This turn continued with the actual source and did not replace the missing estimate by a general positivity premise.

Search183 completed, inventory65149; search184 completed, inventory65151. All20 candidate/20 source statements and the proposed ingredient groups in each search were inspected. Inventories complete, compiler freshness mixed, semantic coverage unavailable, background refresh incomplete. Direct source reads included the full existing logarithmic remainder proof and its private estimate, the source Mellin identity and centered-difference identity, plus the newly returned Deninger and Gamma/quantile statements.

The half-damping primitive anchor has the following paper proof.

1. The proof of `pmPowerDampedDivisorRemainder_eventually_log_four` uses the strict hypothesis epsilon<1/2 only to obtain epsilon<1 and `4<=8*(1-epsilon)`. Both arguments still hold at epsilon=1/2. The inspected private `pmc_scaled_remainder_bound` already only requires 0<epsilon<1. Thus the same proof yields `|R_(1/2)(N)|<=1+C*sqrt(N)/log(N)^4` eventually. This extension has not been edited into Lean or compiler-audited.
2. For real x, the exact difference from the integer remainder is `-alpha*(x-floor(x))`. Hence the integer estimate gives `|g_(1/2)(u)|<=C1*exp(-u/2)+C2/u^4` for large positive u. On u<0, g is exactly `-alpha*exp(u/2)`. In particular g is in L1 and L2.
3. For real s in (1/2,3/4), the literal centered-difference identity and the inspected Fermi Mellin formula give `integral_0^infinity R_(1/2)(x)*x^(-s-1) dx=ζ(s)/(s*ζ(s+1/2))`. The common integrable majorant at infinity is a constant times `x^(-3/2)+1/(x*log(x)^4)`; on (0,1) one can use a constant times x^(-3/4). Dominated convergence therefore reaches s=1/2. The right side tends to zero because `1/ζ(1+delta)=alpha_delta ->0`, using the existing small-damping density limit. Consequently `integral g_(1/2)=0`.
4. At a=0, `k_(1/2)(u)=integral_(-infinity,u)g= -integral_(u,infinity)g`. The latter is `O(exp(-u/2)+u^(-3))` as u tends to infinity; the exact negative-u expression is `-2*alpha*exp(u/2)`. Thus k is in L2, h=g at this damping, and the joint primitive energy has a finite uniform cutoff ceiling.

This proves the proposed anchor on paper without a zero-free or RH hypothesis. It does not give a neighborhood of admitted damping parameters. Formalizing the anchor alone would not discharge the hard producer, so no supporting-only Lean work was substituted for the current estimate this turn.

The direct current test keeps the cumulative prime error paired with the literal joint autocorrelation. For fixed cutoff L, set

`V(v)=integral_(u<=L)[k(u)k(u-v)+h(u)h(u-v)] du`, `sigma=1/2+epsilon`,
`F=V(0)`, `Epsi(x)=psi(x)-x`.

For v>=max(L,0), the second argument lies in the exact negative-u head, so `V(v)=B_L*exp(-v/2)`, with its actual signed coefficient B_L retained. At fixed L the source has finitely many jumps on every bounded interval, an explicit exponentially decaying negative tail, and finite total variation there. Translation against the integrable source makes V locally absolutely continuous; its derivative includes those literal source jumps.

Stieltjes integration by parts gives the paper identity

`integral_(u<=L)[k*P_epsilon k+h*P_epsilon h]
  =F+integral_0^infinity Epsi(exp v)*exp(-sigma*v)*(sigma*V(v)-V'(v)) dv`.

The term F is the lower endpoint: Epsi(1)=-1. The upper endpoint vanishes using the exact V tail and epsilon>0. Thus neither the finite-cutoff boundary nor the arithmetic jumps have been omitted. Fixed-L convergence is not a uniform-L bound.

Trying the existing arbitrary-logarithmic prime-error envelope in absolute value fails to pay this expression uniformly. Its kernel before the actual autocorrelation factor has size allowed by `exp((1/2-epsilon)*v)/v^A`, for every fixed A. For epsilon<1/2, no fixed logarithmic saving makes that a summable uniform majorant as the active lag window grows. The needed cancellation is specifically between Epsi and `sigma*V-V'` of the actual Mobius-derived source. No sign, replacement covariance hypothesis, or deletion of the V' jump terms is justified. The hard target remains a lower bound for this complete pairing by `-C_eta*(1+F)`, uniformly in cutoff and eta<=epsilon<=1/2.

The other-source hits do not supply that bound. `exists_deningerAutocorrelationExpBound` is unconditional on its all-weight Meyer target, but membership of the present source in that target is neither established nor automatic (its prescribed negative-u tail only has one fixed exponential rate). The inspected Gamma/quantile lower bound retains an aperture-dependent completed-error mismatch and a quantile chi-square cost. Neither cost has a uniform bound supplied by that theorem; it cannot be imported as the missing PM coercivity constant.

No numerical jobs, Lean edits, axioms, builds, or live scratch processes were introduced. Searches183-184 are terminal, and their owned temporary outputs were cleaned after inspection. Continue on the actual paired prime-error term; do not spend another turn merely repackaging it or re-auditing the existing finite logarithmic identity.

## Strict logarithmic gap and positivity tests (2026-10-04)

**Assessment: no new arithmetic upper bound.** The preceding half-damping primitive anchor is still paper-only. This turn did not prove either the complete prime-error current estimate or small-damping admission. The new sufficient target below is not being counted as a frontier theorem or inserted as a Lean premise.

Search185 completed with inventory65155, search186 with65160, search187 with65162. All20 candidate and20 source statements in each search, and their proposed ingredient groups, were inspected. Inventories complete; compiler freshness mixed, semantic coverage unmeasured, background refresh incomplete. Direct source checks included the actual divisor product/positivity and second-moment results, the Mobius-log paraproduct, the reflected-current cancellation, the cofinal zero-translation proof, and the finite-prime divergence theorem. These returned no estimate for the missing actual signed pairing.

The exact Mobius--Mangoldt identity rewrites the damping current as its damping derivative; this supplies no independent lower bound. The reflected cancellation concerns an increment paired with the sum of its two reflected shifts. It does not determine the sign of the self-correlation in the PM current. A correction to the previous entry: `RHTower.tendsto_ccmOutgoingQuantileGammaChiSquare_atTop` in `CCMActualHeadSignedCompletedErrorGammaProducer.lean` actually proves divergence of the outgoing quantile chi-square cost. Its unsigned cost therefore cannot furnish the proposed cutoff-uniform coercivity constant. This does not rule out the complete signed producer.

### A weaker sufficient target, with its paper implication

For fixed epsilon>0, retain the literal discrete E_N, logarithmic energy J_N, dilation covariance D_N, prefix covariance P_N, and forcing covariance F_N from the audited leaf. A possible target weaker than a constant relative bound is

`D_N-alpha*F_N <= theta*log(N+1)*E_N + C*(1+E_N)`

for some 0<=theta<1 and C>=0 independent of N. It would suffice to prove this for damping parameters cofinally tending to zero. **No such theta has been proved for the actual source.** The strict inequality theta<1 is the hard condition, not a numerical parameter to optimize.

Here is why this target still reaches RH, rather than only a weaker endpoint. The finite Hardy matrix in P_N has entries, for k<n,

`sqrt(k*(k+1)/(n*(n+1)))*log(1+1/k) <= sqrt(2)/n`.

The Schur weight n^(-1/2), together with the integral bounds for the sums of k^(-1/2) and n^(-3/2), bounds its finite l2 norm by an absolute constant. Consequently |P_N|<=C0*E_N. This is a paper estimate, not a newly audited Lean lemma. The audited balance then gives

`J_N <= theta*log(N+1)*E_N + C1*(1+E_N)`.

Put e_n=E_n-E_(n-1)>=0. Finite Abel summation gives exactly

`J_N = log(N+1)*E_N - sum_(k=1..N) E_k*log((k+1)/k)`.

For t>=0 set H(t)=E_floor(exp(t)) and A(t)=integral_0^t H(s)ds. At t_N=log(N+1), the sum in this display equals A(t_N). With d=1-theta>0, the hypothesized gap therefore implies

`(d*t_N-C1)*E_N <= C1+A(t_N)`.

For t in [log N,log(N+1)), one has A(t_N)=A(t)+(t_N-t)H(t) and 0<=t_N-t<=log 2. Hence, after choosing a fixed sufficiently large T,

`H(t) <= 2*(C1+A(t))/(d*t)` for t>=T.

Increase C1 to at least one if necessary. The positive locally absolutely continuous function B=C1+A satisfies B'<=2*B/(d*t) almost everywhere on [T,infinity). Integrating this differential inequality proves a polynomial bound in t, and therefore E_N<=C2*(1+log(N+1))^K for a finite K. This argument permits an unbounded E_N; it does not assert canonical L2 admission at this stage.

Abel summation of the nonnegative e_n now gives sum_n e_n*n^(-delta)<infinity for every delta>0. The exact real-prefix correction `R(x)=R(floor x)-alpha*fract(x)` transfers this to

`integral_1^infinity |R(x)|^2*x^(-2-delta) dx < infinity`.

Cauchy--Schwarz makes the tail Mellin integral absolutely convergent when `Re(s)>(1+delta)/2`. The sign of delta here is positive. Since arbitrarily small delta>0 are allowed, the Fermi difference A_epsilon(t)=R(1/t)-2*R(1/(2*t)), which vanishes for t>1, has an analytic Mellin transform on Re(s)>1/2. Local analyticity follows by taking a strict delta margin on each compact subset; no boundary L2 assertion is needed. For R itself the elementary head restricts its unmodified Mellin integral to Re(s)<1, so the continuation argument uses the Fermi difference.

Its actual initial Mellin identity consequently continues in cleared form to that half-plane. The already inspected zero-translation/isolation proof then applies for cofinally small epsilon. This establishes the sufficiency of the proposed gap on paper. It does not establish the gap. No new conditional receiver was formalized.

### Attempts to produce the gap

The actual product formula gives 0<=c_epsilon(n)<=1, and the second-moment leaf proves the limiting mean of r_epsilon(n)^2. Neither result bounds the square of sum_(n<=N) r_epsilon(n). A proposed independent-coefficient or independent-prime variance estimate must retain this cumulative correlation; dropping it is exactly the missing step. Likewise, positivity of the logarithmic kernel alone does not provide a strict fraction of log(N+1) in the actual quadratic form.

The random finite-prime sieve version has a definite problem, already exposed by an audited corpus theorem. For a finite prime set P choose independent Bernoulli exclusions B_p of means p^(-epsilon). The resulting undamped finite-sieve Fermi source has expectation exactly `pmFinitePrimePowerDampedFermiSource P epsilon`: this is a finite expansion of the Euler factors. Hilbert Jensen therefore bounds the squared norm of the latter by the randomized second moment. But `pmCanonicalPrime_eventually_exceeds_every_budget` and `tendsto_pmCanonicalPrime_norm_atTop` prove that these mean-source norms diverge along the canonical prime exhaustion whenever 0<epsilon<1/2. Thus the proposed uniformly bounded randomized second moment is impossible. This applies to that finite-prime family; it says nothing against admission of the actual natural-cutoff limit. No new route retirement or independently formalized no-go is claimed.

The positive logarithmic recursion was also tested as a renewal equation for C_N/N. Its nonnegative normalization controls the density scale N. It does not contract the critical normalization R_N/sqrt(N): replacing a signed quotient correlation by its positive mass loses the required scale. No critical contraction was derived. The next proof attempt must keep the natural cutoff and the complete signed dilation/forcing correlation, or the equivalent actual prime-error pairing. Repeating coefficient second moments, finite-prime averaging, or a conditional Gronwall receiver would not advance this problem.

No Lean files changed and no builds were run. No unconditional RH proof or falsification was obtained. Searches185-187 are terminal; owned search outputs are removed after inspection. The goal remains active.

## Natural quotient blocks and two retained source moments (2026-10-04)

**Assessment: the signed upper bound remains open.** The preceding turn changed this attempt by excluding finite-prime randomization. Here the natural quotient blocks and density forcing were kept together. Their two explicit drift terms cancel on paper, but the resulting kernel was not bounded in critical energy. No new Lean theorem, RH proof, or route retirement is claimed.

Search188 completed (inventory65168); PM-filtered search189 was partial (inventory65169). Both returned20 candidate and20 source statements; these and the proposed ingredient groups were inspected. Inventory complete, compiler freshness mixed, semantic coverage unmeasured, refresh incomplete. Current-state reads verified the exact log recursion, small-damping remainder estimate, actual initial Mellin/Dirichlet formulas, and the right-half-plane Mangoldt logarithmic derivative. The conditional covariance cancellation theorem returned by189 still assumes admission and cannot supply it.

Fix 0<epsilon<1/2. All quantities below are real, alpha=Re(alpha_epsilon), a=1-epsilon, and zeta(a) denotes the real value on this real argument. Let

`K=sum_(d>=1) Lambda(d)*d^(-1-epsilon)`,
`B(x)=sum_(d<=x) Lambda(d)*(1-d^(-epsilon))`,
`T_N=sum_(d<=N) Lambda(d)*d^(-epsilon)*floor(N/d)`,
`S_N=sum_(d<=N) Lambda(d)*(1-d^(-epsilon))*R_floor(N/d)`.

Two paper moment identities, both with absolutely convergent prefix-weight series, are

`sum_(m>=1) R_m/(m*(m+1)) = alpha*K`,
`sum_(m>=1) R_m*(m^(-a)-(m+1)^(-a)) = -alpha*zeta(a)`.

For the first, finite divisor interchange in the ordered sum of r_n/n gives a sum of damped Mobius coefficients times harmonic numbers. Subtract alpha times the ordinary harmonic sum. The uniform harmonic-number remainder and the absolutely convergent series of |mu(d)|*log(d)/d^(1+epsilon) give the limit `-sum mu(d)*log(d)/d^(1+epsilon)`. The exact Mobius-log convolution and absolute interchange identify it as alpha*K. Abel summation and R_N/N->0 give the displayed prefix moment. Absolute prefix convergence follows already from the elementary O(N^(1-epsilon)) bound.

For the second, the existing O(N^(1-epsilon)/log(N)^4) estimate permits locally uniform ordered Abel continuation of the centered coefficient series to Re(s)>a and a dominated real limit s down to a. Its initial formula is `zeta(s)*(1/zeta(s+epsilon)-alpha)`. At a the inverse zeta factor tends to zero, giving -alpha*zeta(a). The endpoint Abel boundary R_N*N^(-a) vanishes; the prefix differences are absolutely summable by the fourth logarithmic saving. The coefficient series themselves are ORDERED partial-sum limits, not claims of Lean `Summable` for r_n/n or r_n/n^a. No unordered interchange of these conditional coefficient sums is used.

Regrouping the finite divisor sum gives `S_N=sum_m R_m*(B(N/m)-B(N/(m+1)))`, with only m<=N contributing. Define for every x>0

`q(x)=B(x)-x+x^a/a`,
`V_N=T_N-K*N-zeta(a)*N^a/a`.

For every integer N>=1, the two moments give the exact paper cancellation

`S_N-alpha*T_N = sum_(m>=1) R_m*(q(N/m)-q(N/(m+1))) - alpha*V_N`.

The infinite tail is essential. In particular, for m>N both B arguments vanish but q does not: the corresponding kernel difference is

`-N/(m*(m+1)) + N^a/a*(m^(-a)-(m+1)^(-a))`.

It cannot be truncated away. Also `K*N-T_N=sum_d Lambda(d)*d^(-epsilon)*fract(N/d)>=0`, including d>N; its signed product with R_N is not a free favorable term in the energy. The second subtraction is what matches its N^a contribution. These observations prevent two proposed sign shortcuts.

The attempted inference from the two cancellations to critical coercivity fails at the remaining signed q/V correlation. The original log-convolution identity makes its ordered Dirichlet symbol the negative derivative of `zeta(s)*(1/zeta(s+epsilon)-alpha)`. At a hypothetical zeta zero rho with zeta(rho-epsilon) nonzero, that expression still has a pole at rho-epsilon; differentiation increases its order. Removing the two real drift terms does not remove this translated zero contribution. This is a conditional stress test of the proposed argument, not an assertion that an off-critical zero exists. No square-root bound can be inferred from the moment cancellations alone.

The useful next action is therefore an estimate for the actual signed correlation after these subtractions, retaining the full m>N tail and V_N. Formalizing the two moments alone, applying another absolute logarithmic envelope, or importing admission into the covariance theorem would not resolve this remaining problem. No Lean edits/builds or numerical jobs were introduced. Searches188-189 are terminal; their owned outputs are cleaned after inspection. Goal remains active.

## Weighted record cutoffs and the deleted-core test (2026-10-04)

**Assessment: no complete-source upper bound.** The previous turn supplied diagnostic evidence, not an arithmetic energy advance. This attempt used the exact prime update on the literal moving prefixes. Search190 was partial (inventory65175), search191 completed (inventory65179); all20 candidate and20 source statements and proposed ingredient groups in each were inspected. Inventories complete; compiler freshness mixed, semantic coverage unmeasured, refresh incomplete. No hypothetical input from the returned ingredient groups was used to prove admission.

Write A_L for the actual finite damped Mobius Fermi prefix and w(m)=|a_epsilon(m)|. The inspected transfer formula has input `A_floor(Q/(m*r))(r*t)`; it is not a common vector independent of m. For the squared-prefix input at r=1, put E(L)=||A_L||^2 and H(m)=E(floor(Q/m)), with E(0)=0. At a prime update let U=floor(Q/m), L=floor(Q/(p*m)), and B=A_U-A_L. The source change is exactly

`E(L)-E(U) = -2*Re< A_L,B > - ||B||^2`.

The cutoff boundary contributes further negative squares. The displayed mixed pairing has no proved sign. Discarding it would repeat the invalid invariant-input argument.

A weighted-record variant does give one paper inequality. Suppose kappa>0 and Q>=1 is a record for E(k)/k^kappa among 1<=k<=Q. The complete prime difference J in `pmRamanujanPrimeCutoffDifference` obeys

`J_(p,Q)(H) <= E(Q)*(p^(-kappa)*sum_(m>=1) w(m)*m^(-kappa)-alpha)`

`             <= E(Q)*(p^(-kappa)-alpha)`.

Indeed its positive part is the sum of w(m)*E(floor(Q/(p*m))) over p-nonmultiples m<=Q/p, bounded by the record inequality. Its negative part includes m=1 with weight alpha. The full weight mass is one. Thus this one squared-prefix prime bias is nonpositive once p^(-kappa)<=alpha; no termwise sign of the mixed prefix pairing is assumed. This statement is paper-only and has not been promoted to a Lean producer.

The extension needed for the actual transfer did not follow. For r>1 the relevant endpoint is floor(Q/r), which need not be a record even when Q is. The full quadratic law also contains J(f*g), not only J(g^2). Polarizing two separate scalar bounds does not give a bound on their difference. A common cutoff controlling the complete matrix of dilation pairings was not obtained. In addition, the transfer's r=1 channel has total mass one and still contains the original varying Mobius prefix, so a bound for centered prime features acting on a fixed admitted vector would not establish admission of this input.

Taking a record over all prime-deleted cores would strengthen the desired theorem to a false uniform estimate. The existing literal complementary sector at Q=P^2 is precisely the denominator sum with factors p in (P,2P] removed, retaining the original coefficients and omitting q=1. Its head energy has ratio one to the large-prime sector energy. The inspected source proofs give the latter a positive lower multiple of P^(1-2*epsilon)/log(P)^2. Consequently these deleted cores themselves cannot have a uniform bound, or a uniform Q^kappa ceiling for every kappa>0. The already formalized positive survivor is the complete mixed cancellation: the full source is much smaller than either sector, and their normalized mixed energy tends to -1. This is an application of existing results, not a newly formalized route retirement.

A density correction was examined without assuming that it solves this problem. For a finite excluded prime set P, the absolutely convergent infinite Ramanujan coefficient expansion gives the deleted coefficient

`c^P(n)=a_P*product_(p|n,p notin P)(1-p^(-epsilon))`,

`a_P=product_(p in P)(1-p^(-1-epsilon))`.

Its asymptotic density is still alpha. Before the spatial cutoff reaches any excluded prime, its discrete centered prefix is exactly

`R^P(N)=a_P*R(N)+(a_P-1)*alpha*N`.

This identifies the short-head drift and its exact correction; it supplies no bound after N crosses the excluded primes and is not an identity for a finite natural-denominator truncation without its remainder. The returned finite-deletion admission theorem concerns the undamped smooth-count source, not this positive-damping problem. Neither this theorem nor the short-head formula proves a uniform corrected-core energy estimate.

The remaining task is still a joint estimate for the complete natural-cutoff source, including its varying cutoff and mixed dilation channels. The scalar record inequality and density correction are insufficient individually. No Lean files changed, no builds or numerical jobs ran, and no unconditional RH result was obtained. Searches190-191 are terminal and their owned outputs are cleaned after inspection. Goal remains active.

## Full pair kernel with the physical cutoff retained (2026-10-04)

**Assessment: no hard covariance bound proved.** This attempt retained the complete pair kernel rather than bounding one prime marginal. Searches192-194 completed without a partial flag (inventories65184,65188,65188). All returned candidate/source statements and ingredient groups were inspected. Inventory complete; compiler freshness mixed, semantic coverage unmeasured, background refresh incomplete. Search193 mostly returned inapplicable generic kernels;194 was restricted to the actual PM power-damped modules. Its proposed ingredient group supplies LOWER energy bounds, not the needed upper bound.

`RoutePNativeSignedPairComparison.native_signed_pair_comparison` does not close this problem. Its source is the critical clock head built from `mu(d)*sqrt(d)*divisorContinuousUnitHead(x/d)`, with prime gain `p^(-1/2)`. The signed-pair covariance is comparable to that same head's energy. No absolute ceiling or identification with the present PM source follows. The lcm-pair-fibre inversion returned by192 is also an exact decomposition without an estimate.

The actual positive Haar expansion and its cutoff repairs were then inspected. The uncorrected positive prefix has already-proved linear energy growth. Density correction and endpoint correction are already formalized; their energy formulas retain the unknown R_epsilon energy. They must not be used as unconditional admission estimates.

Here is the resulting PAPER-ONLY kernel calculation. Write H for the real supported dyadic Haar, c_n=c_epsilon(n), N>=1, and

`K_N(n,m)=integral_(1/N,infinity) H(n*t)*H(m*t) dt`, for 1<=n,m<=N.

The literal PM source agrees with sum_(n<=N)c_n*H(n*t) on this integration interval. Consequently its truncated physical energy is the COMPLETE quadratic sum in K_N. Put K(n,m)=max(0,2/max(n,m)-1/min(n,m)), the audited full Haar Gram. If a=min(n,m), b=max(n,m), then

`K_N(n,m)=K(n,m)-[1/N-2*min(1/N,1/(2*a))+2*min(1/N,1/(2*b))]`.

This follows by integrating the two cutoff indicators defining each H; the bracket is exactly the omitted initial-interval pairing. In particular, for n,m<=N/2 it is 1/N, whereas for N/2<n<=m<=N the retained kernel is 1/m-1/N. There are negative off-diagonal entries. The full Gram's entrywise positivity therefore gives no sign for the retained kernel's pair increments.

A bounded constant-source term can be separated without introducing alpha. Let `row_N(n)=sum_(m<=N) K_N(n,m)` and P(t)=floor(1/t)-2*floor(1/(2*t)). On t>=1/N, the finite unweighted Haar sum is exactly P(t), which is zero or one. The full pairing of H(n*t) with P(t) is O(1/n^2): with p(x)=floor(x)-2*floor(x/2), the primitive of p(x)-1/2 is bounded, so integration by parts gives

`I(n):=integral_(n,infinity) p(x)/x^2 dx = 1/(2*n)+O(1/n^2)`;

the pairing is I(n)-2*I(2*n), and its leading terms cancel. Removing (0,1/N) changes each row by at most 1/N. Thus `sum_(n<=N)|row_N(n)|<=C` for an absolute C. This argument involves exact identities and integral estimates, not numerical experiments.

Define the signed pair-increment form

`V_N(c)=1/2*sum_(n,m<=N) K_N(n,m)*(c_n-c_m)^2`.

Finite expansion gives `E_N^physical=sum_n c_n^2*row_N(n)-V_N(c)`. Since the actual coefficients lie in [0,1], the first term has absolute value at most C. The hard problem is therefore a LOWER bound on V_N for the actual prime-product coefficients; a bound on its absolute summands loses the required cancellation. A uniform lower bound would give admission; a subpower lower bound would give the corresponding weaker continuation target. No such lower bound was obtained. The upper bound V_N<=C follows from nonnegative energy and is the wrong direction.

The attempt to derive the lower bound from coefficient positivity and density alone fails. For example, bounded coefficients `c_n=a+b*n^(-delta)` with 0<delta<1/2, a,b>0, a+b<=1 have positive density a. Integral comparison gives their Haar source in the reciprocal variable as `b*(1-2^delta)/(1-delta)*x^(1-delta)+O(1)`. Their retained energy grows as a positive multiple of N^(1-2*delta). This is a paper test of the generic inference, NOT a counterexample for the actual PM coefficients and NOT a route retirement.

The prime-product condition was retained in the final attempted estimate. At a new prime, `c'=c-theta*h`, where theta=p^(-epsilon) and h_n=c_n*1_(p|n). Polarizing V gives the exact update `V(c')=V(c)-2*theta*V(c,h)+theta^2*V(h)`. Neither remaining term has a sign from the retained kernel. Bounding prime masks independently again discards the mixed arithmetic correlation. The unresolved next step is a joint lower estimate for these updates on the actual natural cutoff, or directly for V_N(c_epsilon); no uniform estimate over deleted cores is assumed.

These are paper diagnostics and a reformulation, not a new Lean producer or a solved hard frontier problem. No Lean changes/builds, numerical jobs, new axioms, or RH conclusion. Searches192-194 are terminal; owned search outputs are removed after inspection. Goal remains active.

## First-band obstruction to a separate positive-current budget (2026-10-04)

The certificate card is `../3-formalized/pm-prime-update-positive-current.md`. The exact first band of the canonical prime core is the full source plus the positive sum of missing primes. Existing unconditional logarithmic remainder cancellation and prime-window lower bounds make the full source uniformly negligible relative to that sum on the reciprocal slab `[3P/2,7P/4]`. This gives a genuine positive core slab and an energy floor; it does not bound the full signed source energy.

The paper consequence is that the positive quadratic prime-update current at `N=8P^2` exceeds a positive multiple of `P^(1-4*epsilon)/log(P)^3`. For `epsilon<1/4`, separate control of these positive terms by every positive power is false. The complete mixed current must remain in any proposed producer. No growing-cofactor PNT expansion is assumed: its variation loss was not controlled.

All three new modules passed their actual-file Lean checks and targeted `lake --old build` leaf builds. The bounds module proves uniform relative smallness of the full source, uniform relative approximation of the literal prime core by the missing-prime sum, and a positive lower bound on its real part. The current module proves the localized energy floor, the actual prime-insertion identity and current dilation identity, the power lower bound, and divergence after division by every power below the stated threshold. All three modules are wired once into the umbrella; the formal index was regenerated. All eighteen exported theorem axiom audits passed with only `propext`, `Classical.choice`, `Quot.sound`. Global lint reports thirteen unrelated unreachable modules and no new PM failure. The separate positive-current budget branch is closed with its positive survivor in `../5-failed/pm-separate-positive-prime-current-budget.md`. RH and the full covariance bound remain open.

### The coupled square scale

Search200 completed without a partial flag (inventory65256). All twenty candidate and twenty source statements, plus its proposed ingredient group, were inspected. Inventory complete; compiler freshness mixed, semantic coverage unmeasured, background refresh incomplete. The undamped deleted-prime floor identity, existing reciprocal-source identification and old conditional prime-budget receiver do not supply the needed small-damping mixed estimate. The proposed cusp-Euler-factor linkage was not an applicable proof.

The new first-slab result localizes the unresolved pairing. For a prime `p` and `t` in `[4/(7*p^2),2/(3*p^2)]`, the dilated factor `F_<p(p*t)` has reciprocal coordinate in `[3*p/2,7*p/4]` and is controlled by the new positive slab theorem. Its paired factor `F_<p(t)` has reciprocal coordinate in `[3*p^2/2,7*p^2/4]`. No sign or upper bound for their complete mixed sum follows from the first-slab estimate.

A PAPER-ONLY finite inversion describes the remaining factor. Let `r_P(m)` be one when every prime factor of the positive integer `m` is at least `P`, and zero otherwise. The local divisor identity `mu*r_P=mu_<P`, with the completely multiplicative damping retained, gives

`F_<P(t)=sum_(m<=floor(1/t)) r_P(m)*m^(-epsilon)*A(m*t)`.

This is a finite source identity: expand the right side, group `m*d=n`, use `fermi_d(m*t)=fermi_(m*d)(t)`, and use the divisor identity. All terms with `m*d>1/t` vanish by physical support. For `P>=2` and `P^2<=x<2*P^2`, the surviving rough integers are one, primes, and products of two primes counted once including prime squares. The two-prime cofactor lies in `[1,2)`, where the full source equals one. Consequently the inversion becomes

`F_<P(1/x)=A(1/x)+sum_(q prime>=P,q<=x) q^(-epsilon)*A(q/x)`

`            +sum_(P<=q<=r, q,r prime, q*r<=x) (q*r)^(-epsilon)`.

This algebraic expansion has not been exported as a Lean theorem here and supplies no new mixed-current bound. It identifies a concrete next attack: retain the prime-convolved full source jointly with the semiprime contribution in the square-scale pairing. A growing-cofactor PNT estimate based on total variation still has the unresolved loss recorded earlier; no such estimate or sign is assumed. The hard target remains the complete cutoff-dependent compensation `M_epsilon(N)-Q_epsilon(N)/2`, not a separate bound on either current.

## Subexponential prime-cofactor split and audited boundary moments (2026-10-04)

The active detailed proof card is `pm-prime-square-coupled-source.md`. A new
paper mechanism addresses the variation loss above: split at cofactor
`H=exp((log x)^alpha)` with `1/3<alpha<1/2`. The corpus's unconditional
square-root-log PNT error absorbs any fixed power of H in the finite head.
The log-four source envelope and retained prime-density factor bound the tail
by `O(x^(1-epsilon)/(log x*(log H)^3))`. Together these are smaller than the
second-order prime term. The full paired square-scale sign is still pending
Lean; the detailed card records the finite inversion, head and tail estimates,
semiprime diagonal, and uniform-gap argument without treating them as premises.

The actual source's needed boundary moments are now formally closed in
`PMPowerDampedMobiusBoundaryMoments.lean`: global real reciprocal log-four
envelope, absolute second logarithmic moment, admitted zeroth/first moments,
zero signed mass, exact first signed moment `-D_epsilon`, and
`D_epsilon -> log 2`. The seven exported theorems and two definitions all passed
axiom audits with only the standard three logical axioms. Targeted `lake --old`
leaf build passed (53 seconds for the leaf); final actual-source Lean check
passed empty after the final edit. One umbrella import, regenerated formal
index, no umbrella build. Global lint has twelve unrelated unreachable-module
errors and no PM failure. Certificate: `../3-formalized/pm-power-damped-boundary-moments.md`.

This removes a concrete analytic input from the square-scale proof, but does
not yet bound the actual prime convolution or the full energy. The next work
is the signed prime-convolution transfer, using exact finite divisor sums for
the head and prime-density savings for the complete tail. The route's hard
open problem remains the global mixed-current compensation; RH is not proved
or falsified. Searches201–206 are terminal, inspected, and their owned outputs
have been removed; search207 investigates the direct Abel tail estimate.


### Signed prime-head transfer closed (2026-10-04)

Route PM still seeks the complete signed compensation bound. The missing
head transfer is now formalized in `PMPowerDampedMobiusPrimeHead.lean`:
three exports identify the literal signed prime sum, its exact reciprocal
boundary kernel, and a uniform error for growing cofactor cutoffs. Targeted
`--old` leaf build, final actual-file check and all three axiom audits passed;
only the standard three axioms occur. Module wired once and indexed. Global
lint has thirteen unrelated unreachable modules, no PM failure. See
`../3-formalized/pm-signed-prime-head-transfer.md`.

Searches207–209 and the exact remaining mechanism are recorded in
`pm-prime-square-coupled-source.md`. The tail now has a direct decreasing
Abel-weight paper proof preserving `1/log(P)` and a first Lean draft.
Centering the truncated kernel reduces its limit to dominated convergence
against the first absolute logarithmic moment plus a quantitative zero-mass
tail. This removes an unnecessary long-range integral transfer and explicit
second-order remainder. The actual prime convolution, rough inversion with
squares, square-core sign and global signed compensation remain unproved.


### Prime and boundary tails closed (2026-10-04)

`PMPowerDampedMobiusPrimeTail.lean` closes the actual-source prime tail with
its essential prime-density factor and the quantitative boundary mass tail
`O((log H)^(-3))`. All three exports passed targeted old leaf build, final
actual-file Lean check and axiom audit (standard three only). The leaf is
wired once and indexed. Global lint has eighteen unrelated unreachable
modules, no PM failure. Certificate: `../3-formalized/pm-prime-and-boundary-tails.md`.

The next conjecture is the actual centered-kernel estimate, with error
`C*(L/log(H)^3+1/log(H)+1/L)` for `L>=2*log(H)`. Its paper proof uses the
exact kernel identity and the audited second logarithmic moment, then
`L=s^5,H=exp(s^2)` forces convergence to the negative boundary jet. This
advances the signed prime convolution needed for the square-scale core
sign. Complete signed energy compensation remains open; no RH conclusion.


### Actual boundary kernel closed (2026-10-04)

`PMPowerDampedMobiusBoundaryKernel.lean` now proves both the finite centered
kernel error and its actual negative-jet limit. Both exports passed targeted
old leaf build, final actual-file Lean check and axiom audit (standard three
only). Wired once, indexed; global lint twelve unrelated unreachable leaves,
no PM failure. Certificate: `../3-formalized/pm-actual-boundary-kernel.md`.

The full prime-convolution draft combines this with the audited head/tail
estimates. Its paper proof is uniform for `sqrt(X)/2<=a<=sqrt(X)`, covers
all sufficiently large real X via the inverse fifth-power log substitution,
and identifies the normalized sum with `-Re(D_epsilon)`. Its first Lean
check is running. This advances the paired source sign; the finite rough
inverse and square-inclusive semiprime count are next. Complete signed
energy compensation, and hence the RH goal, remain open.


### Complete signed prime convolution closed (2026-10-04)

`PMPowerDampedMobiusPrimeConvolution.lean` proves the actual normalized
prime sum tends uniformly to `-Re(D_epsilon)` for lower cutoffs between
`sqrt(X)/2` and `sqrt(X)`, at every sufficiently large real X. Three
unconditional parameter-domain theorems plus the actual sum definition
passed targeted old leaf build, final actual-file Lean check and all four
axiom audits (standard three only). Wired once, indexed; global lint twelve
unrelated unreachable leaves, no PM failure. Certificate:
`../3-formalized/pm-signed-prime-convolution.md`.

The next draft proves the exact rough-factor dilation identity directly
from integer Möbius inversion and the literal finite Fermi-source sums.
This avoids a new damping ring homomorphism and retains repeated primes.
Its first check is running in `/tmp/pm_rough_inverse_work.lean`. The joint
prime/semiprime source sign and complete signed compensation remain open.


### Exact rough inversion closed (2026-10-04)

`PMPowerDampedMobiusRoughInverse.lean` proves the exact finite positive
rough-dilation expansion of every finite-prime core, for every real damping
parameter. Repeated prime factors are retained. Targeted old leaf build,
final actual-file Lean check and axiom audit passed (standard three only).
Wired once, indexed; global lint twelve unrelated unreachable leaves, no PM
failure. Certificate: `../3-formalized/pm-exact-rough-inverse.md`.

The square-scale decomposition now needs only the exact rough-integer
classification and the square-inclusive semiprime count. The classification
draft is in `/tmp/pm_prime_square_work.lean`. `Finset.sym2` supplies the
correct `(J^2+J)/2` pair count including squares. The uniform source sign
and complete signed energy compensation remain open.

### Prime-square decomposition closed (2026-10-04)

`PMPowerDampedMobiusPrimeSquareDecomposition.lean` proves the literal
full-source/prime/rough-composite decomposition on P^2<=X<2*P^2 and the
square-inclusive weighted bound `(J^2+J)/2 * P^(-2*epsilon)`. Targeted old
leaf build, final actual-file Lean and all three axiom audits passed with
standard axioms only. Wired once, indexed; global lint twelve unrelated
unreachable modules, no PM failure. Certificate:
`../3-formalized/pm-prime-square-source-decomposition.md`.

The next hard step is the uniform joint negative sign on the square slab,
using the already audited negative prime-convolution limit. Complete
signed-energy compensation remains unresolved.

### Uniform square-slab sign closed (2026-10-04)

`PMPowerDampedMobiusPrimeSquareSign.lean` proves uniform negative actual
core on X=yP^2, 3/2<=y<=7/4, for all sufficiently small positive damping.
Endpoint-correct prime counting and square-inclusive mass retain the
complete source. Targeted old leaf build, final actual-file Lean and
all-three-export axiom audit passed with standard axioms only. Wired once,
indexed; global lint nineteen unrelated unreachable modules, no PM failure.
Certificate: `../3-formalized/pm-prime-square-source-sign.md`.

Next: pair this negative source with the audited positive first-band
factor and integrate the resulting negative mixed density. Complete signed
compensation M-Q/2 remains the RH-strength open problem.

### Negative mixed current escape closed (2026-10-04)

`PMPowerDampedMobiusNegativePrimeCurrent.lean` proves the actual weighted
mixed density negative on the square slab and its complete negative part
larger than every N^kappa, kappa<1-2*epsilon, along N=8P^2, for every
sufficiently small positive epsilon. Eleven exports; targeted old leaf
build, final actual-file Lean and all axiom audits passed with standard
axioms only. Wired once, indexed; global lint twelve unrelated unreachable
modules, no PM failure. P3: `../3-formalized/pm-negative-mixed-prime-current.md`.
P5 with positive survivor: `../5-failed/pm-separate-negative-mixed-current-budget.md`.

Hard target remains the complete `Mpositive-Mnegative-Q/2` lower bound.
The next scratch `/tmp/pm_prime_balance_work.lean` proves exact pointwise
finite-prime energy telescoping, for subsequent forced positive compensation.

### Complete signed balance closed (2026-10-04)

`PMPowerDampedMobiusPrimeEnergyBalance.lean` proves the exact physical
energy identity E=seed+Q-2(Mplus-Mminus), for every real epsilon and N>=1,
without canonical L2 admission. Eight exports pass targeted old leaf build,
final actual-file Lean and standard-three-axiom audit; wired once,indexed.
Global lint twelve unrelated unreachable modules, no PM failure.
Certificate: `../3-formalized/pm-complete-prime-energy-balance.md`.

Next actual hard estimate: integrate the log-four source envelope to prove
E(N)*log(N)^4/N^(1-2*epsilon)->0, then force leading positive compensation
against the proved negative-current escape. The stronger bounded remainder
Mplus-Mminus-Q/2 is still unresolved. Reciprocal-transport scratch:
`/tmp/pm_energy_budget_work.lean`.

### Leading complete-current compensation closed (2026-10-04)

`PMPowerDampedMobiusPrimeCompensation.lean` proves actual normalized energy
negligibility and one-sided leading positive compensation. Both exports
pass the targeted old leaf build (26s), final actual-file Lean with empty
output and separate axiom audit with the standard three axioms only.
Wired once; global lint twelve unrelated unreachable modules, no PM failure.
Certificate: `../3-formalized/pm-leading-prime-compensation.md`.

This advances the forced global cancellation law but does not improve the
positive-power residual to the RH-strength bound. Continue on the actual
joint logarithmic dilation/forcing covariance or the equivalent complete
prime-current remainder. Do not repeat the finished audits.

## Positive-ground-state completion test (2026-10-04)

**Assessment: no hard upper bound from this test.** The new leading current
compensation is audited separately; it must not be bootstrapped through
its own exact energy identity to claim a smaller remainder.

Search220 completed, inventory65384 complete, mixed compiler freshness,
semantic coverage unmeasured and refresh incomplete. All20 candidate and20
source statements and its proposed group were inspected. Polynomial
Hamiltonian ground states and generic dilation adjoints are different
operators. The applicable input is the audited positive logarithmic
recursion for the literal divisor coefficients.

A direct PAPER calculation tests using its positive uncentered solution
C_n=sum_(j<=n)c(j). For 1<=k<n, let a_nk be the sum of b(d) over those
2<=d<=n with floor(n/d)=k, plus log((k+1)/k). Then a_nk>=0 and the exact
uncentered Abel law is `log(n)*C_n=sum_(k<n)a_nk*C_k`. Put
w_n=1/(n(n+1)), R_n=C_n-alpha*n, and g_n=R_n/C_n (C_n>=1).
For finite N, direct expansion gives

`sum_(n<=N) w_n*R_n*(log(n)*R_n-sum_(k<n)a_nk*R_k)`
` = (1/2)*sum_(k<n<=N)w_n*a_nk*C_n*C_k*(g_n-g_k)^2`
` + (1/2)*sum_(k<=N)(w_k*log(k)*C_k^2`
`       -C_k*sum_(k<n<=N)w_n*a_nk*C_n)*g_k^2`.

The last column defect has no favorable sign. At k=1 its positive row
term is exactly zero, and the n=2 lower-prefix edge already makes its
column term strictly negative. Thus the proposed inference from a
positive uncentered solution to nonnegative critical quadratic form is
invalid. Both terms must remain together; dropping the column defect
loses precisely the needed signed cancellation. No route retirement or
new Lean no-go is claimed, and no trivial completion identity is promoted
as an arithmetic upper estimate.

Next test keeps physical truncation in a Bernoulli prime expansion of the
actual coefficients. The previously rejected uniform WHOLE-half-line
finite-core second moment must not be reused. At the natural horizon,
finite independent prime exclusions have expectation c_epsilon(n) for
all n<=N, so their actual Haar energy gives a possible Jensen majorant.
The question is whether its complete expectation, including the mean
component and all prime intersections, has a uniform or subpower bound.
Merely bounding its variance would leave the original unknown mean energy
untouched. This is a new proof attempt, not an asserted estimate.

## Natural-horizon random-prime second-moment test (2026-10-04)

**Assessment: no independent energy ceiling obtained.** Search221 completed,
inventory65385 complete, mixed compiler freshness, semantic coverage
unmeasured and refresh incomplete. All20 candidate and20 source statements
and the proposed group were inspected. The complete-period Ramanujan
formula has a different averaging variable. Generic Bernoulli covariance
identities do not bound the present original physical horizon.

The following is a PAPER derivation, not a Lean export. Fix epsilon>0 and
N>=1. For each prime p<=N take an independent Bernoulli exclusion with
probability theta_p=p^(-epsilon). Write Y(n) for the indicator that n has
no excluded prime divisor, c(n)=E[Y(n)], and H for the actual dyadic Haar.
On t>1/N, put Z(t)=sum_(n<=N)Y(n)H(n*t). Its mean is exactly the actual
A_epsilon(t); every included integer keeps its full prime-factor set.
Independence gives

`E[Y(n)Y(m)]=c(lcm(n,m))`
` =c(n)c(m)*sum_(d|gcd(n,m),d squarefree)lambda(d)`,
`lambda(d)=product_(p|d)theta_p/(1-theta_p)`.

Consequently, with B_d(t)=sum_(n<=N,d|n)c(n)H(n*t), exact finite
interchange gives

`E[integral_(1/N,infinity)Z(t)^2 dt]`
` =sum_(d<=N,d squarefree)lambda(d)*integral_(1/N,infinity)B_d(t)^2 dt`.

The d=1 term is exactly the unknown E_epsilon(N). Bounding only the
nonconstant random components cannot bound it.

A sharper second pass retains the actual multiplicative masks. For each
prime p, with c_p=1-theta_p and D_p f(t)=f(p*t),

`B_p=c_p*sum_(j>=1)theta_p^(j-1)*D_p^j A`.

This sum is pointwise finite on the physical horizon, since A vanishes
above1. For squarefree d the mask is the product of these commuting
operators over its prime factors. On the fixed truncated L2 space,
`norm(D_p f)<=p^(-1/2)*norm(f)` because dilation moves the lower endpoint
upward; it does not request the missing whole-half-line admission. Thus

`E_epsilon(N) <= E[integral Z^2] <= C_epsilon*E_epsilon(N)`,
`C_epsilon=product_p(1+theta_p*(1-theta_p)/(sqrt(p)-theta_p)^2)<infinity`.

The last product is finite for each fixed epsilon>0: its prime increment
is at most a constant times p^(-1-epsilon). Finite-horizon integrability
is already audited. These calculations explain why replacing the actual
energy by this random second moment does not itself create a contraction:
the mean term remains with coefficient one. No independent estimate for
the complete random second moment has been proved. This is a failed proof
step, not a claim that the moment bound is false and not a retired route.
The two-sided paper comparison is not being formalized as a substitute for
the hard arithmetic estimate.

Next hard conjecture remains a strict logarithmic gap for the complete
actual dilation-minus-forcing covariance, or directly a subpower lower
bound on Mplus-Mminus-Q/2. Any random-prime proof must now control its
complete mean-bearing second moment by arithmetic information independent
of E_epsilon(N). Current masks and their norms supply no such information.
No RH or negated-RH theorem was obtained. All new leading-compensation
exports remain fully audited; no repeated build or numerical job is needed.
