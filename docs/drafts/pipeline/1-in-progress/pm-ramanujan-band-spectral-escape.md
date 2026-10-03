# Route PM: complete-band spectral escape

- **ID:** pm-ramanujan-band-spectral-escape
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / proof attempt
- **Source:** actual complete denominator band, joint residue, critical zeta zeros, raw Mobius moving-window obstruction.
- **Goal relevance:** identify and control the residual moving energy after the proved complementary cancellation. Global small-damping admission remains the final hard producer.

## Question and scope

For S_X(N)=sum_(X<q<=2X) a_epsilon(q) P_q(N), fixed-N profile convergence does not decide whether X^epsilon S_X converges in the original anchored Hilbert norm. Test the conjecture that a nonzero component of this normalized energy escapes to N comparable with X. No selected prime or cofactor lower bound will suffice: every term of S_X must remain.

The sufficient RH producer only needs a positive damping margin, for example energy of S_X minus its fixed-coordinate profile bounded by C_epsilon X^(-epsilon). Strong convergence of the normalized remainder is not required. Neither a spectral escape theorem nor that upper bound is currently proved here.

## Exact two-variable mechanism to establish

Write alpha=1/zeta(1+epsilon), J_s(q)=sum_(d|q) mu(q/d)d^(1-s). For q>1 the audited finite fractional-part identity gives

    integral_0^infinity P_q(floor(1/t)) t^(s-1) dt
      = zeta(s) J_s(q)/s,       0<Re(s)<1.

Keep X continuous and its literal natural band (floor X, floor(2X)]. Define the moving vector B_X(x)=X^(epsilon-1/2) S_X(floor(X*x)). Its squared L2(dx/x^2) norm is X^(2epsilon) times the original band energy. Put z=w+1/2 and r=epsilon+s-z. In the initial absolute domain Re(z)>1, 0<Re(s)<1, its two-variable Mellin expression is predicted to be

    alpha * zeta(s)/s * (1-2^(-r))/r
      * [zeta(1+z-s)/zeta(z) * H_epsilon(z,s) - 1].

The subtraction of 1 retains exclusion of q=1. The apparent r=0 singularity is removable. The complete arithmetic Euler series is now audited below; the literal cutoff integration and physical Hilbert identification still need proof.

The local factor is exact algebra. For prime p let

    a=p^(-1-epsilon), b=p^(s-z-1), c=p^(-z).
    H_p = (1-a+b-c)(1-b)/[(1-a)(1-c)]
        = 1 + (b-a)(c-b)/[(1-a)(1-c)].

Near Re(z)=Re(s)=1/2 the correction is O(p^(-3/2)) (with a positive epsilon-dependent margin). At s=z=rho on the critical line, b=1/p and |c|=1/sqrt(p), while 1-a+b>1; hence no local numerator vanishes. A summable majorant on an open neighborhood, the product, its continuity/scale holomorphy and its nonvanishing are now formalized below.

The z=s pole from zeta(1+z-s) represents the stationary fixed-coordinate profile. After removing that pole, zeros of zeta(z) may retain a moving spectral contribution. At a critical zero rho, zeta(s)zeta(1+rho-s)H_epsilon(rho,s) is not identically zero as a function of s near rho: the zero and pole at s=rho reduce its vanishing order by one, rather than killing the whole germ. This is a proposed analytic route to a full-band escape profile, not yet a proof of a norm floor.

## Hard obligations

1. The literal primitive/band Mellin identity and infinite arithmetic Euler identity are audited. Establish the remaining literal cutoff integral to obtain the two-variable quotient with every boundary retained.
2. Justify the Hilbert or compact-test continuation through the stationary pole; scalar formal Euler algebra alone is insufficient.
3. Prove a nonzero moving-profile contribution using the existing critical-zero machinery, retaining all complementary terms.
4. Return to the upper-bound producer with the escaped component included. An obstruction to strong normalized convergence does not obstruct the weaker sufficient energy bound and does not prove or refute RH.

## Research log

2026-10-02: Previous complementary cancellation is audited progress. Search129 complete, inventory current at1188207, semantic coverage unmeasured; all returned candidates/source statements and ingredients inspected. It returned exact signed decompositions but no clock upper bound. Search130 complete with mixed freshness (coverage1188213/current1188214); its generated positivity ingredients are unrelated to the physical source and unusable. Direct corpus inspection supplies finite Nyman Mellin transforms and the existing critical Mertens log-tent mechanism. Search131 checks prior band/moving-shell work before new Lean code. No new mathematical bound is claimed.

## Stronger target exposed by the two-variable calculation

Test the unconditional statement: for every epsilon>0 there is c_epsilon>0 such that, for every fixed vector F in L2(dx/x^2), arbitrarily large real X satisfy

    ||X^epsilon S_X - F|| >= c_epsilon.

This would rule out strong normalized convergence to any fixed profile, while leaving the damping-margin RH producer intact. The proposed positive survivor is a nonzero moving spectral profile of the complete actual band, not a lower bound on an extracted sector.

A concrete contradiction mechanism now separates the two possible energies. Let U_X F(x)=X^(-1/2)F(X*x); U_X is unitary in L2(dx/x^2). If X^epsilon S_X converges strongly to F, then B_X=U_X(X^epsilon S_X) is bounded and differs from U_X F by a norm-null error. On the critical Mellin line s=1/2+i*tau, U_X multiplies the transform by X^(i*tau). Therefore, for every real gamma,

    delta * integral_(X>=1) X^(-delta-i*gamma) B_X dX/X -> 0

in Hilbert norm as delta decreases to zero. For U_X F this follows from the multiplier delta/(delta+i*(gamma-tau)), bounded by one and tending to zero almost everywhere; the norm-null error follows by splitting the X integral at a fixed large cutoff.

Choose an actual critical zero rho=1/2+i*gamma, of finite order m>=1. Choose a compact critical-frequency interval I close to gamma but disjoint from it. The Euler correction is now proved jointly continuous, holomorphic in z, and nonzero near (z,s)=(rho,rho). On I, zeta(s) is nonzero by isolatedness, zeta(1+rho-s) is finite and nonzero, and the band factor has nonzero numerator because Re(epsilon+s-rho)=epsilon>0. A compact L2 frequency test can consequently give a nonzero integral of the leading zeta(z)^(-1) coefficient.

Pair the exact two-variable transform with that test. In the initial absolute domain the result is the scalar transform of B_X. Under the hypothesized boundedness of B_X it analytically continues to Re(w)>0. Use a horizontal tube about Im(w)=gamma disjoint from I: the band denominator epsilon+s-z never vanishes there, so no removable-singularity shortcut is needed. Clearing zeta(z), continuation should retain the exact identity. As w=delta+i*gamma approaches the boundary, it forces delta^m times the tested transform to a nonzero limit. The Hilbert Abel limit above is zero when m=1; boundedness makes it zero when m>1. This is the proposed contradiction.

Remaining essential verification: Mellin-Plancherel identification of the bounded frequency test and boundary continuation after pairing. Literal cutoff integration is now fully audited below. Normal convergence and nonvanishing of H are audited. Remaining obligations are not available assumptions. The raw-Mobius window theorem alone proves none of them for this complete band.

## Initial paper estimate for the Euler correction

For epsilon>=0, Re(s)=1/2 and Re(z)>=3/8, set a,b,c as above. Then |a|<=p^(-1), |b|<=p^(-7/8), |c|<=p^(-3/8). The denominator has norm at least (1/2)*(1-2^(-3/8)). Thus |H_p-1| is bounded by a fixed multiple of p^(-5/4), uniformly on this whole region. The prime sum converges by the corpus p-series theorem. At s=z with Re(z)>0, b=1/p and 0<a<=b; hence 1-a+b>=1>|c|. Every local numerator is nonzero, and the absolutely convergent product is nonzero. These estimates identify the exact analytic correction required by the spectral argument, rather than estimating the physical signed energy by absolute values.

## Lean checkpoint

`PMRamanujanBandMellin` now identifies the literal reciprocal primitive with a finite Nyman combination and derives its complete Mellin divisor symbol. The complete natural-band transform and prime symbol are included. All seven exports passed the targeted old-mode leaf build, final actual-file Lean check and standard-axiom audit. Umbrella wired once; global lint has ten unrelated unreachable modules and no finding for this leaf. See `../3-formalized/pm-ramanujan-band-mellin.md`. This closes the finite-source transform obligation, not the infinite Euler interchange or spectral escape theorem. Search131 was partial (text retrieval interrupted), with complete inventory and mixed freshness; all returned candidate/source statements and ingredients were inspected. Its Sonin reflection and critical-zero data do not supply the missing actual-band Hilbert continuation.

### Integer cutoffs and bounded spectral tests

The spectral pairing must use a compact frequency interval, not point evaluation of a general L2 Mellin transform. The corpus `MobiusLaplaceMellinPlancherelBridge` supplies an exact Mellin--Fourier line law and Plancherel for an L1∩L2 logarithmic source. The new finite band satisfies this for each cutoff; passage to the scale transform must use a bounded L2 frequency pairing. This avoids falsely treating critical Mellin point evaluation as a bounded Hilbert functional.

The initial absolute double-series estimate can keep its divisor sum: |a(q)|<=q^(-1-epsilon) and |J_s(q)|<=sum_(d|q)d^(1-Re(s)). After q=d*m, the majorant factors as sum d^(-Re(z)) times sum m^(Re(s)-1-Re(z)), finite when Re(z)>1 and 0<Re(s)<1. No reciprocal-zeta assertion below the absolute-convergence line is used in this step.

A real-cutoff obstruction alone is not yet the desired integer-cutoff result. If normalized natural bands at all integers converged strongly, interpolation to real X adds at most the denominator 2*floor(X)+1, plus a scalar factor tending to one. The needed atom error is X^epsilon*|a(q)|*sqrt(G(q,q))->0 for q comparable with X. A divisor-sum bound for the primitive Hilbert norm, sqrt(G(q,q))<=C*sum_(d|q)sqrt(d), followed by a subpower divisor-product bound, would supply this. It must be proved and audited, not inferred from a single fixed-q bound. A cofinal integer result would still not automatically assert a floor at every dyadic cutoff.

### Local analytic correction — current proof attempt

The correction majorant has been extended to Re(z)>=3/8 and Re(s)<=9/16, an open neighborhood of the two critical lines after making the inequalities strict. The same denominator floor gives |H_p-1|<=C*p^(-19/16). This supplies local uniform convergence in both variables; separate holomorphy in z and joint continuity suffice for the compact-frequency residue argument. Local numerator nonvanishing at s=z on the critical line yields a joint neighborhood free of correction zeros.

The source-specific prime identity is

    [alpha+a_epsilon(p)*J_s(p)*p^(epsilon+s-z)]*(1-p^(s-z-1))
      = alpha*(1-p^(-z))*H_p(z,s).

It follows from the actual prime-weight recursion and the audited prime divisor symbol, retaining alpha. `PMRamanujanBandEulerCorrection` now proves this identity, absolute and locally uniform product convergence, joint continuity, holomorphy in z, diagonal nonvanishing and nonvanishing on a joint neighborhood. All fifteen exports passed targeted old-mode build, final actual-file Lean and standard-axiom audits. Umbrella wired once; lint has thirteen unrelated unreachable modules and no own finding. Closed card: `../3-formalized/pm-ramanujan-band-euler-correction.md`. The infinite arithmetic-series identity has now been closed in the separately audited series leaf below; its multiplicativity and majorant proofs are independent of this local analytic argument.

Search132 was partial with semantic retrieval unfinished: index1188647, coverage1188658/current1188660, complete inventory, mixed compiler freshness, semantic coverage unmeasured. All20 candidate statements and all20 source arguments were inspected. The generic EulerProduct theorem and the corpus complex-power arithmetic function provide reusable mechanisms. The suggested character-correction chain concerns a different source and supplies no actual-band identity or energy bound.

### Actual infinite arithmetic identity — fully audited

The new series proof gives J_s as the convolution of the zero-clamped complex power n^(1-s) and Mobius. It proves exact coprime factorization of J_s, of the denominator product, and of the normalized actual coefficient. The bound |a_epsilon(q)|<=q^(-1-epsilon) dominates the actual series term by the absolute L-series term of J_s at 1+z-s. Convolution summability closes this majorant for Re(z)>1 and Re(s)<1.

The prime-power series has only its exponent-zero and exponent-one terms. EulerProduct.hasProd and the audited actual prime identity then give

    zeta(z) * sum_q a_epsilon(q)*J_s(q)*q^(epsilon+s-z)
      = alpha*zeta(1+z-s)*H_epsilon(z,s),

for epsilon>0, Re(z)>1, Re(s)<9/16. `PMRamanujanBandEulerSeries` has thirteen exports; all passed the targeted old-mode build, final actual-file Lean and standard-axiom audits. Umbrella wired once. Lint has eleven unrelated unreachable modules, no own finding. Closed card: `../3-formalized/pm-ramanujan-band-euler-series.md`. This identifies the infinite arithmetic series. The cutoff integral has subsequently been audited below; physical Hilbert continuation remains missing.

For the next bridge it suffices to integrate the already identified finite-band spatial Mellin symbol over the cutoff X. Denominator q occurs exactly on X in [q/2,q), and q>=2 makes this interval a subset of X>=1. Integrating X^(r-1), r=epsilon+s-z, gives q^r*(1-2^(-r))/r when r is nonzero. Absolute interval integrals are bounded by C_r*q^(Re(r)); the audited arithmetic majorant should justify interchange of q and X. This preserves the q=1 subtraction and both literal cutoff boundaries.

A separate three-variable absolute estimate in the original spatial coordinate is unnecessary for the proposed contradiction. After the finite-band Mellin--Plancherel bridge, hypothesized strong convergence gives a uniform Hilbert bound. Cauchy--Schwarz on the compact frequency interval then justifies the cutoff/frequency interchange in the initial domain. These are proof steps to discharge, not new analytic premises in an exported receiver.

Search133 (cutoff-integral bridge) was partial with semantic retrieval unfinished: index1189028, coverage1189051/current1189053, complete inventory, mixed compiler freshness, semantic coverage unmeasured. All20 candidate statements and all20 source arguments were inspected. Returned generic indicator and unrelated Gamma/Euler bounds do not prove the literal moving-band integral. Direct Mathlib inspection supplies `hasSum_integral_of_summable_integral_norm`, the positive-interval complex-power integral, and interval dilation. The planned norm bound uses exact dilation from [q/2,q) to [1/2,1), producing a fixed integral constant times q^(Re(r)); it is paid by the actual series majorant. `/tmp/pm_band_cutoff.lean` now passes a foreground scratch check: exact cutoff membership, literal indicator-sum expansion, and the single-interval complex-power integral. It has not been promoted as a finished module. The summable integral-norm bound and full cutoff interchange remain to be proved.

### Hilbert implementation and strength of the proposed survivor

The reciprocal source f_X(t)=S_X(floor(1/t)), extended by zero on t<=0, lives in ordinary L2(dt); its squared norm is the original discrete energy. The moving vector becomes X^(epsilon-1/2)*f_X(t/X). Under the existing logarithmic Mellin map at sigma=1/2, this is translation by log(X) of the normalized source's logarithmic vector. Thus the corpus L2 translation/Fourier machinery can implement the Hilbert Abel argument without inventing a new weighted Hilbert space.

For the uniform cofinal distance floor, take any fixed F and suppose L=limsup_X ||X^epsilon f_X-F|| is finite. Local boundedness of the finite bands then gives the needed global norm bound. The translated F contribution has vanishing normalized Abel mean, while the remainder's normalized Abel pairing is bounded in limsup by ||test||*L. A simple critical zero's nonzero scalar residue would force L>=|residue|/||test||, independent of F. A higher-order zero would contradict every finite L. This strengthens a mere nonconvergence contradiction to the stated positive cofinal floor. It does not establish an unconditional Abel-profile limit: without an energy bound, off-line growth could prevent the original Abel integral from converging close to the boundary. Keep that distinction in the formal theorem.

Historical checkpoint superseded: the complete cutoff leaf is now built, wired and audited. Current active scratch is the Hilbert bridge, described below.


### Compact residue test — next constructive step

On a compact critical-frequency interval I close to gamma but disjoint from gamma, retain the full residue numerator

    A(tau)=alpha*zeta(s)/s * (1-2^(-(epsilon+s-rho)))/(epsilon+s-rho)
             * zeta(1+rho-s)*H_epsilon(rho,s),  s=1/2+i*tau.

Choose the interval inside the audited nonzero neighborhood of H and the punctured isolation neighborhood of the critical zero of zeta(s). The Re=1 nonvanishing theorem applies to zeta(1+rho-s), since tau differs from gamma. The band numerator is nonzero because Re(epsilon+s-rho)=epsilon>0. Hence A is continuous and nonzero on I. The explicit scalar test conjugate(A)*indicator(I) is in L2 and pairs the residue to integral_I |A|^2>0. This replaces an unspecified nonzero test with a constructive witness. Compact frequency pairing, holomorphic dependence under that pairing, and the Hilbert Abel limit still require Lean proofs; no residue conclusion is claimed yet.

Search135 returned twenty candidate statements and twenty source arguments; all were inspected. It was partial in semantic retrieval, inventory complete with mixed compiler freshness. The logarithmic Mellin--Fourier bridge is applicable after actual-band L1 and L2 admission. Its generated Gamma-energy step concerns a different source and is not applicable here. Active `/tmp/pm_band_hilbert.lean` now contains unverified proofs of logarithmic source support, finite-band norm control, L1/L2 admission and the complete critical Mellin--Plancherel identity. It has not been promoted or built while the cutoff leaf audit is running.


### Cleared-identity refinement: multiplicity is unnecessary

The contradiction can avoid zero order and Laurent expansions entirely. At any critical zero rho, differentiability gives zeta(rho+delta)/delta -> zeta'(rho). The cleared tested identity has left side

    [zeta(rho+delta)/delta] * [delta * testedScaleTransform(delta+i*gamma)].

Under the fixed-profile convergence assumption the second bracket tends to zero by the Hilbert Abel argument; the first has a finite limit even at a multiple zero. The right side tends to the explicitly positive compact-test pairing. Thus the contradiction needs only first differentiability at rho. This is a simplification of the proposed proof, not a proved spectral escape conclusion.

For the uniform cofinal floor, a finite limsup distance L bounds the normalized Abel remainder by ||test||*L. The cleared identity then gives |paired numerator| <= |zeta'(rho)|*||test||*L. Using 1+|zeta'(rho)| in the denominator yields a positive floor without a zero-multiplicity case split; when zeta'(rho)=0, every finite L would already contradict the identity. Remaining work is the same actual-band Hilbert pairing and its boundary continuation.


Search136 inspected all twenty candidate statements, twenty source arguments and both generated ingredient steps. Retrieval was partial in text retrieval, inventory complete and compiler freshness mixed. The discrete Deninger Abel-tail lemmas expose the fixed-head/small-tail argument, but do not establish a continuous Hilbert translation mean. The proposed Schwartz/periodic decay chain is inapplicable to an arbitrary L2 profile. The required continuous translation Abel result therefore remains a proof obligation; its Fourier multiplier delta/(delta+i*(gamma-tau)) is bounded by one and tends to zero almost everywhere, providing the direct dominated-convergence proof plan.


### Literal cutoff identity — fully audited

`PMRamanujanBandCutoffMellin` closes the exact interval membership, window norm scaling, summable integral norms, integrability of the actual complete cutoff integrand, interchange, and q=1 subtraction. Its cleared identity is the formula in `../3-formalized/pm-ramanujan-band-cutoff-mellin.md`. All sixteen public declarations passed targeted old-mode build (only this leaf built, 192 seconds), final actual-file Lean and standard-axiom audits. Umbrella wired once; global lint has twelve unrelated unreachable modules and no own finding. The earlier Search133 scratch checkpoint is superseded by this full audit.

The active Hilbert scratch is being checked next. No complete signed-energy ceiling, compact tested continuation, spectral escape theorem or RH conclusion is yet proved.


### Scalar Abel pairing suffices

Only the fixed compact test is needed for the contradiction. The Fourier transform of an arbitrary fixed L2 profile, multiplied by the compact L2 test, lies in L1 by Cauchy--Schwarz. Its normalized translation Abel pairing is the integral of that product times delta/(delta+i*(gamma-tau)). This multiplier has norm at most one and tends to zero away from the singleton tau=gamma; dominated convergence gives the required scalar zero limit. The norm-null profile remainder is handled by a fixed-head/small-tail split. Thus a new operator-valued Hilbert Abel resolvent is unnecessary; prove this scalar pairing directly from the actual translation law.

First Hilbert scratch check exposed elaboration/API errors and a default-heartbeat timeout in implicit source inference for the Fourier identity. The repairs use explicit source arguments and cast normalization, with no heartbeat increase. The repaired scratch is checking; it remains unpromoted.


Next exact norm obligation: for g(u)=exp(-u/2)*S(floor(exp u)), substitution x=exp(u) gives integral |g|^2 = integral_(x>1)|S(floor x)|^2/x^2. Apply the audited `hasSum_stepGram` separately to Re(S) and Im(S), then use Complex.sq_norm/normSq_apply to recover the literal complete energy sum. This works for the complex finite band and does not require a separate proof that its weights are real. The actual complete square is retained throughout; no growing-cutoff upper estimate follows from finite-source boundedness.


### Current checkpoint — Hilbert prefix passes

`/tmp/pm_band_hilbert.lean` now passes foreground `lake env lean` with exit 0 and no diagnostics. It contains the actual complete logarithmic band source, exact identification with the reciprocal Mellin source, measurability, negative-half-line support, finite-band bound, L1 and L2 admission, critical Mellin trace, exact Fourier identification and the critical-line Plancherel norm identity. Explicitly typed scalar/band measurability witnesses fixed the final elaboration error. Explicit source arguments and cast normalization removed the earlier timeout; no heartbeat increase was used.

This remains an active scratch prefix: the original discrete-energy norm identity, actual moving-dilation law and bounded compact test must be added before promoting the complete Hilbert bridge. No new Hilbert project module, umbrella import or axiom audit is claimed. All owned processes are terminal. Only `/tmp/pm_band_hilbert.lean` and its empty check log remain as active scratch; completed cutoff and search artifacts were cleaned. RH and the small-damping signed-energy ceiling remain open.


### Direct critical-frequency carrier

The exact finite-band Hilbert bridge has passed the complete scratch check, including the original discrete-energy norm and the bounded literal L2 test. Its leaf is now under targeted build/final audit; it will be recorded as closed only after those checks.

A simpler implementation of the moving argument can work directly with these actual critical-frequency vectors. Let V_X be the literal critical Mellin vector for floor(X)<q<=floor(2X), and F_X=X^epsilon*V_X. Multiply by the corpus unitary `MellinL2.fourierPhaseMulUnitary (log(X)/(2*pi))`, whose literal multiplier is exp(i*tau*log(X)). The moving vector then has representative X^(epsilon+i*tau)*T_X(tau) and exactly the original normalized energy norm (with the proved factor 2*pi). This is the same actual source transform, not an independent model.

Under hypothetical fixed-profile convergence of F_X, the scalar Abel argument applies directly to its L2 frequency representative. Returning the cofinal floor to arbitrary physical profiles can use the exact norm identity for differences of two scaled complete bands; no new scaled Mellin unitary on every possible profile is required. That difference identity still needs proof. For F=0 the frequency norm already equals the original energy by the new bridge.

Search138 inspected all twenty candidates, twenty source-argument statements, the generated translation proposal and both ingredient steps. Retrieval was partial in semantic retrieval; inventory complete, compiler freshness mixed. Direct source inspection confirms logTranslationCLM h acts by f(u+h), is unitary, and conjugates under Fourier to `fourierPhaseMulUnitary h`. The new cutoff phase uses h=log(X)/(2*pi), so its frequency variable is the critical ordinate tau. The generated sine-increment variant is unnecessary for this argument.

### Actual Hilbert bridge closed; frequency-gap Abel refinement

`PMRamanujanBandHilbert` is fully audited: targeted old-mode leaf build passed in 249 seconds, mandatory final actual-file Lean passed without diagnostics, and all twenty-two public axiom queries use only the standard axioms. Umbrella wired once; lint reports eleven unrelated unreachable modules and no own finding. The earlier scratch-only checkpoints are superseded. Closed card: `../3-formalized/pm-ramanujan-band-hilbert.md`.

The compact residue test was already chosen on an interval I disjoint from gamma. Keep this separation: d=dist(gamma,I)>0. On that support, the normalized scalar Abel multiplier has modulus at most delta/d. Consequently its pairing against a fixed L2 profile is bounded by (delta/d)*||test||*||profile|| and tends to zero directly. No general arbitrary-frequency dominated-convergence theorem is needed for this contradiction. The actual Laplace/Fubini identity and the small-tail profile-remainder estimate still require proof. This refinement shortens the same source-specific argument; it supplies no unproved energy premise.

Search139 returned complete retrieval with complete inventory (64583 files), mixed compiler freshness and unmeasured semantic coverage. All twenty candidates, twenty source arguments and both generated ingredient steps were inspected. Finite phase averages and unrelated Abel source identities do not prove the required continuous frequency-gap Abel estimate. The direct spectral-gap bound is based on the actual phase unitary and the audited L2 pairing, rather than those unrelated proposals. Active moving-carrier scratch is under its first check.

The full moving-carrier scratch now passes, including the literal cutoff transform and integrability. Its promoted leaf `PMRamanujanBandMovingMellin` passed a targeted old-mode build (only this leaf built, 261 seconds), the final actual-file audit without diagnostics, and all nine standard-axiom queries. Umbrella wired once; lint reports thirteen unrelated unreachable modules and no own finding. Closed card: `../3-formalized/pm-ramanujan-band-moving-mellin.md`. The scalar Abel scratch proves product integrability by the exact majorant exp(-delta*u)*|f(tau)|, then Fubini and the half-line complex-exponential integral identify the resolvent. After two elaboration repairs, it is checking together with the actual L2 phase-unitary pairing. No Abel leaf has been promoted yet.

Search141 inspected all twenty candidate statements, twenty source arguments and both generated ingredient steps. Retrieval was complete, inventory64589 complete, compiler freshness mixed and semantic coverage unmeasured. The corpus `eventually_riemannZeta_ne_zero_nhdsNE` is directly relevant to the compact nonzero numerator. Mathlib also supplies the unconditional closed/discrete actual zeta-zero set, so the same isolation can be obtained with lighter imports. The Re>=1 nonvanishing theorem and the already audited joint Euler-correction neighborhood supply the other two analytic factors. The dyadic factor is nonzero because its power has modulus 2^(-epsilon)<1. These are the next actual numerator proof obligations; no simplicity assumption is needed.

### Abel phase proof — checked scratch

The complete `/tmp/pm_band_abel.lean` prefix passed foreground Lean with no diagnostics. It proves the integrable two-variable phase majorant, the exact scalar Laplace/resolvent identity, the spectral-gap normalized Abel zero limit, and its specialization to the actual corpus L2 phase unitary acting on any fixed L2 profile. The sign-normalization repair uses explicit inverse-negation identities; no heartbeat increase was needed. A separate public integrability theorem for the actual scalar phase pairing has just been added and still requires checking. This is not yet a promoted or audited project leaf. The residue nonzero-interval draft is under its first check; compact positive testing and full source continuation remain open.

The extra scalar-pairing integrability statement has also passed. The four-export Abel leaf is promoted and wired; targeted old-mode build passed in43s and final actual-file Lean passed with no diagnostics. Axiom queries are checking. The first residue check found only API/elaboration failures: numeral coercion in the complex-power norm, unavailable `ext` registration, and `Tendsto.prodMk` yielding product filters rather than product neighborhoods. Repairs use an explicit real coercion, `Complex.ext`, and `prodMk_nhds`. A new continuity-away-from-gamma proof has been added; that whole repaired residue draft is still unverified.

The Abel leaf has now passed all four standard-axiom queries and is fully closed in `../3-formalized/pm-ramanujan-band-abel.md`. The repaired residue interval prefix reports no errors; the appended continuity proof exposed the local API's implicit point argument in `ContinuousAt.comp`. Those applications are repaired and the whole residue scratch is checking again. This prefix is not yet a promoted module, and no compact positive-test or spectral-escape conclusion is claimed.

### Next continuation proof, retaining the actual carrier

Under the contradiction's fixed-profile convergence assumption, the normalized actual frequency vectors are bounded for large X. On bounded X-intervals only finitely many natural cutoffs occur, so local boundedness follows from the proved exact norm and the scalar normalization. The tested moving scalar is therefore globally bounded on X>=1. Its measurability must be proved from the measurable cutoff indices and the actual phase pairing; no unknown arithmetic regularity premise may be inserted.

Its scale transform is then a Laplace transform in u=log X, holomorphic for Re(z)>1/2. On a narrow ordinate tube about gamma disjoint from the compact test support, the cleared arithmetic right side is also holomorphic: the factor zeta(1+z-s) has no pole there, r stays nonzero, and H has the audited local holomorphy and joint continuity. The exact initial identity in Re(z)>1 and connected-domain uniqueness should identify these scalar functions. At z=rho+delta, first differentiability of zeta and the checked fixed-profile Abel zero limit force the left side to zero; the norm-null profile remainder needs its own fixed-head/small-tail proof. The positive compact numerator integral would contradict this. None of the continuation, measurability or remainder obligations is currently claimed closed.

The existing `PMLogMobiusContinuation` gives a concrete reusable continuation mechanism. Extend the actual tested scalar q(X) by zero for X<=1 and put f(t)=q(1/t). Under the contradiction's proved bound, f is bounded near zero and zero for t>1. Once actual measurability/local integrability is discharged, Mathlib `mellin_differentiableAt_of_isBigO_rpow_exp` applies with b=0. The exact `mellin_comp_inv` law identifies the scale integral with mellin(f)(z-1/2). This avoids constructing a new general Hilbert-valued Laplace theory. The continuous compact-frequency arithmetic integral still needs its own parameter-integral proof. Local boundedness alone is not a substitute for the missing actual-source measurability.

Search142 returned complete retrieval with complete inventory64607, mixed compiler freshness and unmeasured semantic coverage. All twenty candidate statements, twenty source arguments and both generated ingredient steps were inspected. The Mathlib convergence theorem and `PMLogMobiusContinuation`'s actual proof provide the relevant reciprocal-source mechanism. The suggested unrelated extended-Sonin bounds do not establish this source's measurability or energy bound. Direct source inspection confirms `mellin_differentiableAt_of_isBigO_rpow_exp` and `mellin_comp_inv`; neither application is yet formalized for the moving band.

### Latest checkpoint — residue interval and continuity pass

The complete current `/tmp/pm_band_residue.lean` passes foreground Lean with exit0 and no diagnostics. Its four public declarations are the literal residue numerator, pointwise nonvanishing, a full nonzero punctured interval beside an actual critical zero, and continuity away from that ordinate. Explicit inner maps in `ContinuousAt.comp (f := ...)` remove the last inference failures. No heartbeat increase was used. This is still a scratch prefix; compact-test L2 admission, actual integrable pairing and strict positivity must be added before promotion. The dependency-closed paper statement is `../3-formalized/pm-ramanujan-band-residue-test.md`.

All owned processes are terminal. Only the checked residue scratch and its empty log remain as active scratch artifacts; completed Hilbert, moving-carrier, Abel and search artifacts have been cleaned. The three completed leaves are built, wired and audited. The goal remains active and unmet. No complete signed-energy ceiling, tested source continuation, spectral escape theorem or RH conclusion is claimed.

### Compact positive residue test — current turn

The previous goal turn was verified progress: three actual-source leaves were built and audited, and the residue prefix passed scratch Lean; the small-damping complete-energy ceiling was unchanged. This turn revalidated the current prefix, paper card and route map. The extended scratch now constructs the actual compact test, proves its L2 admission and integrable literal pairing, identifies that pairing with the squared-norm integral, and realizes an L2 vector with a positive frequency gap and strictly positive numerator pairing. It is under its first full check, not yet promoted.

Search143 was complete, inventory64609 complete, compiler freshness mixed and semantic coverage unmeasured. All twenty candidate statements, twenty source arguments and both proposed ingredient steps were inspected. The generic continuous compact-interval admission is applicable; no retrieved theorem constructs the actual numerator test. Local Mathlib API probes passed after fixing universe levels. The proof uses the actual nonzero interval and continuity, with no simplicity premise or unknown energy estimate.

The first extended residue check failed only at inference of the real-to-complex integrability target and rewriting the cast integral. Explicit complex target typing and direct `integral_ofReal` application repair those points; the whole scratch is checking again. The positive L2 witness retains an almost-everywhere equality to the literal indicator test, its exact support gap, integrability of its pairing and strict positivity.

Search144 was partial in filter/judgement and decomposition, with complete inventory64612, mixed compiler freshness and unmeasured semantic coverage. All twenty candidate statements and twenty source arguments were inspected; no ingredient sets were returned. The measurable natural floor and countable-family mechanisms are relevant. Direct Mathlib source gives `measurable_from_prod_countable_left`: a family measurable in its real variable and indexed by a countable discrete cutoff pair is jointly measurable. A new unverified `/tmp/pm_band_pairing.lean` uses this with the actual finite-band vectors, proves continuity of each fixed phase pairing by the integrable L2 product bound, and then composes with the literal floor indices and log cutoff phase. This addresses actual-source measurability, not an assumed arithmetic bound.


Search145 was partial in source retrieval, with complete inventory64618 and mixed compiler freshness. All twenty candidate statements, twenty source arguments and the proposed ingredient set were inspected. The suggested zero-density/finite-off-line chain does not prove critical-zero existence or RH. The useful source argument references Hardy's actual critical fiber. Exhaustive local search locates `HardyDyadicWindowTheorem.exists_riemannZeta_line_zero_dyadic`: beyond a positive threshold every dyadic interval has an actual critical-line zero. Its source statement is unconditional; it is reserved for instantiating the final escape theorem, not inserted as a new premise.

The residue leaf's targeted old-mode build passed (172 seconds), and mandatory final actual-file Lean passed with no diagnostics. Nine-export axiom audit is running. Lint reports eleven unrelated unreachable modules and no finding for this leaf. The moving-source scratch now also drafts an actual norm bound on every finite cutoff interval, using only the finite set of floor-indexed bands and monotonicity of the positive real power. This bound is local; the global bound needed by continuation must be derived internally from the fixed-profile convergence contradiction.


### Positive complete-residue test fully audited

`PMRamanujanBandResidueTest` is closed: nine exports, targeted old-mode leaf build172s, mandatory final actual-file Lean with no diagnostics, standard axioms only, umbrella wired once. Lint11 unrelated unreachable modules, none own. Card: `../3-formalized/pm-ramanujan-band-residue-test.md`. The actual compact test has a positive support gap and strictly positive pairing with the complete numerator. This advances the actual cleared-identity obstruction; it does not improve the global complete-energy ceiling or prove spectral escape/RH.

The next foreground scratch checks actual tested-scale measurability, local norm boundedness, joint guarded-trace measurability and literal L2 pairing integrability/identity. Search146 completed, inventory64622 complete, compiler freshness mixed. All twenty candidate statements, twenty source arguments and both ingredient steps were inspected. The generic joint-integrability/Fubini mechanism is useful; separate product domination is not supplied for the actual moving family. The planned proof uses the integrated L2 square bound and derives the global source bound internally from a convergence contradiction.


### Actual tested Fubini and continuation construction

Search147 completed, inventory64624 complete, compiler freshness mixed. All twenty candidate statements, twenty source arguments and both generated ingredient steps were inspected. The proposed half-plane contour decay chain is not our mechanism. The useful existing theorem is `HTGeometry.differentiableAt_integral_of_cauchy_dominated` in `CauchyDominatedIntegralHolomorphy`: it needs a local integrable bound on the holomorphic family itself, not an independently supplied derivative bound. Its current source signature was checked.

The current source scratch has verified joint measurability, local finite-cutoff norm bounds, a global norm bound derived from the proposed fixed-profile convergence, full two-variable integrability and Fubini. Integrated absolute pairing is bounded by the sum of the two L2 squared norms; the remaining scale weight is an integrable real power for Re(z)>1/2. The reciprocal tested source is bounded, locally integrable and zero above1, giving holomorphy through the existing Mellin theorem. Final reciprocal rewrites and the actual initially valid cleared identity are checking. No source-regularity or energy premise is postulated as unconditional.

Next arithmetic-side proof: use the complete kernel K(z,tau)=alpha*zeta(s)/s*B(epsilon+s-z)*(zeta(1+z-s)*H(z,s)-zeta(z)). For the positive critical zero supplied by Hardy and compact frequency interval [a,b] above its ordinate, the connected tube {Re(z)>3/8, 0<Im(z)<a} avoids all denominator zeros and zeta poles for tau in [a,b]. The kernel is jointly continuous and holomorphic in z there. A compact parameter ball times [a,b] supplies a uniform bound, and the compact L2 test is L1 there. Cauchy-dominated holomorphy therefore applies to the actual tested kernel. At rho the kernel is exactly the already-audited complete residue numerator. Analytic uniqueness and the variable-profile Abel remainder are still required; neither is claimed closed.


The entire tested-source scratch now passes with no diagnostics, including reciprocal Mellin holomorphy, actual scale-integrand integrability and the initially valid cleared arithmetic identity. The thirteen-export leaf `PMRamanujanBandTestedScale` is promoted and wired once; targeted old-mode build17s passed, final audit running. Its paper card is `../3-formalized/pm-ramanujan-band-tested-scale.md`. New `/tmp/pm_band_kernel.lean` drafts the literal complete kernel, joint continuity, parameter holomorphy, and compact L2-test holomorphy on the explicit upper ordinate tube. That draft has not been checked yet.


Search148 completed, inventory64631 complete, compiler freshness mixed. All twenty candidate statements, twenty source arguments and both ingredient steps were inspected. The Deninger discrete Abel limit and unrelated exponential-decay families do not supply the actual norm-null continuous-time remainder. The corpus's generic filter dominated-convergence theorem and exact `integral_comp_mul_left_Ioi` change of variables provide a direct new proof: delta times the Laplace average equals the integral of exp(-v)*b(v/delta). The profile remainder b tends to0 and is globally bounded using the already-derived actual source bound; for v>0, v/delta tends to infinity. Dominated convergence then gives the required Abel zero without a finite-head/tail bookkeeping lemma. This is a paper mechanism, not yet Lean-closed.

The arithmetic-side continuation paper proof is now recorded in `../3-formalized/pm-ramanujan-band-tested-continuation.md`. The draft contains joint kernel continuity, kernel and compact-test holomorphy, and analytic uniqueness for the complete cleared identity on the connected tube. It awaits its first check after the tested-source axiom audit.


The tested-scale leaf is fully audited: thirteen exports, targeted old-mode build17s, final actual-file Lean exit0 empty, standard axioms only, umbrella wired once. Card moved to `../3-formalized/pm-ramanujan-band-tested-scale.md`. Completed pairing/search artifacts are cleaned. The arithmetic continuation scratch is now in its first foreground check; its success is not yet claimed. The goal remains active and unmet.


The first full arithmetic-continuation check reached every declaration and failed at the joint-continuity composition's inferred map and two numeral simp names. A second check reduced this to explicit typing of the outer Euler map and the normalized base-point positivity goal. Those are repaired; the third check is running. No mathematical obstruction or hidden arithmetic bound appeared in these diagnostics. The compact-test holomorphy and identity-principle proof elaborate apart from those reported dependencies.

A new unverified `/tmp/pm_band_remainder.lean` implements the rescaled bounded-null Abel lemma and its actual specialization. The remainder is exp(-i*gamma*u) times the difference between the actual tested band at exp(u) and the phase pairing of the proposed fixed limit. Its measurability uses the audited tested-scale theorem; its norm-null property uses the phase isometry and strong convergence; its global bound uses the internally derived source bound. The draft is not Lean-checked or promoted yet.


The full arithmetic continuation scratch now passes with exit0 and no diagnostics. Explicit outer, inner and base-point parameters in `ContinuousAt.comp` resolved the final elaboration issue. All eight declarations are promoted in `PMRamanujanBandTestedContinuation`, wired once, and the targeted old-mode build is running. Final actual-file and axiom audits remain. The complete identity-principle argument is present; no boundary Abel contradiction is claimed yet.

Search149 completed, inventory64638 complete, compiler freshness mixed. All twenty candidate statements, twenty source arguments and both proposed ingredient steps were inspected. Actual log-Mellin substitutions are relevant; the proposed theta probability-law chain is not this source. The already audited Hilbert leaf uses the exact image-integral change-of-variables theorem. Together with the current Mathlib `Real.image_exp_Ioi`, this supplies the literal X=exp(u) substitution. It is drafted in the remainder scratch and still unverified. The full remainder paper proof is `../2-fully-proven/pm-ramanujan-band-profile-remainder.md`.


The complete tested-continuation leaf is fully audited: eight exports, targeted old-mode build185s, final actual-file Lean exit0 empty, standard axioms only, umbrella wired once. P3: `../3-formalized/pm-ramanujan-band-tested-continuation.md`. The remainder scratch is now in its first foreground check; no success is claimed yet. Completed kernel and search artifacts are cleaned. Goal remains active and unmet; the global small-damping signed-energy ceiling is unchanged.


The full remainder scratch passed exit0 with one unnecessary tactic-sequencing warning, now corrected. All seven declarations are promoted/wired in `PMRamanujanBandProfileRemainder`; targeted old-mode build is next. This includes the exact actual tested-scale Abel zero, not merely an abstract lemma. Final scalar residue contradiction is the next frontier.

Search150 was partial in text/source retrieval, inventory64649 complete, compiler freshness mixed. All twenty candidate statements, twenty source arguments and both ingredient steps were inspected. The generated Fokas/quotient-system chain is irrelevant. The useful current Mathlib statements are `HasDerivAt.tendsto_slope_zero_right` and `HasDerivAt.comp_ofReal`. Applied to w -> zeta(rho+w) at0, they give zeta(rho+delta)/delta -> zeta'(rho), with no simplicity premise. Together with the now scratch-proved delta*actual-transform ->0 and the continued identity, this forces the positive complete-residue pairing to vanish. Hardy's unconditional positive critical zero then discharges the intermediate zero parameter. The scalar contradiction is not yet Lean-checked.


The profile-remainder leaf passed its targeted old-mode build73s. Mandatory final actual-file audit is running; separate axiom audit remains. A new unverified `/tmp/pm_band_escape.lean` assembles the scalar contradiction, instantiates the actual positive Hardy zero, and derives a positive cofinal distance from each fixed L2 profile by negating metric convergence. This last positive constant may depend on the profile. The stronger common constant for all profiles, original physical-Hilbert transfer and integer/dyadic transfer remain separate obligations; no overclaim of the stronger target is made. The fixed-profile candidate is not yet retired.


The profile-remainder leaf is fully audited: seven exports, targeted old-mode build73s, mandatory final actual-file Lean exit0 with no diagnostics, standard axioms only, umbrella wired once. P3: `../3-formalized/pm-ramanujan-band-profile-remainder.md`. Lint11 unrelated unreachable modules; none own. The scalar contradiction scratch is checking for the first time. The global small-damping complete-energy ceiling is still open.

Search151 completed, inventory64656 complete, compiler freshness mixed. All twenty candidate statements, twenty source statements and both generated ingredient steps were inspected. The completion-construction chain is unnecessary: actual L2 is already complete. Current `Metric.cauchySeq_iff` and `cauchySeq_tendsto_of_complete` give a stronger positive survivor. No fixed limit implies a positive cofinal tail diameter; the triangle inequality yields one positive separation radius independent of the proposed profile. This new paper extension is recorded on the no-fixed-profile P2 card and awaits Lean checking.


The complete spectral-escape scratch passed with no diagnostics. Four exports are promoted in `PMRamanujanBandSpectralEscape` and wired once; targeted old-mode leaf build is running. Unconditional Hardy supplies the positive critical zero. The literal cleared identity, actual Abel zero and positive complete residue rule out every fixed strong limit, and L2 completeness gives one positive cofinal separation radius independent of the profile. No RH or energy upper bound follows.

Search152 completed, inventory64659 complete, compiler freshness mixed. All twenty candidate statements, twenty source statements and both generated ingredient steps were inspected. Its generated Frobenius/correlation chain does not apply to the anchored physical energy. The exact existing Plancherel identity can transport norm statements; the actual signed cutoff recurrence, rather than a selected sector or complete-period average, remains the next upper-bound mechanism to test. Search153 targets that recurrence.


The spectral-escape targeted old-mode leaf build passed144s; mandatory final actual-file audit is running. Four exported statements remain under final audit. Search153 completed with inventory64661 complete and mixed compiler freshness; all twenty candidate statements, twenty source statements and both ingredients inspected. The returned renewal kernels concern different sources and do not supply the required PM bound. Exact PM transfer source was inspected: the r=1 row has total absolute mass1, and positive higher rows remain. Therefore the direct triangle-inequality contraction attempt does not yield a coefficient below1; this is a diagnosis of that proof step, not retirement of the signed recurrence. The next source-specific estimate must retain the actual differences F_(Q/(pmr))-F_(Q/(mr)) and their signed boundary terms. Search154 filters the actual PM producer; search155 checks physical-Hilbert transport of the new uniform separation.


`PMRamanujanBandSpectralEscape` is fully audited: four exports, targeted old-mode build144s, final actual-file Lean exit0 empty, standard axioms only, umbrella once. P3: `../3-formalized/pm-ramanujan-band-no-fixed-profile.md`. The complete actual normalized critical-frequency family has a common positive cofinal distance from every fixed L2 vector. This is the strongest current positive survivor; it does not exclude bounded oscillation or prove the small-damping upper ceiling. Global lint13 unrelated unreachable modules, none own.

Search154 completed with inventory64667 complete, mixed compiler freshness. All20 candidate and20 source statements plus both ingredients inspected. Coefficient variance, the half-damping endpoint and absolute remainder bounds do not supply the missing cumulative small-damping energy estimate. Search155 was partial with inventory64671 complete and mixed compiler freshness; all20+20 statements and both ingredient steps inspected. Actual `dilationUnitary` and existing AE Fourier transport suffice for the exact physical vector identity. `/tmp/pm_band_physical.lean` is now in its first check, seven exports drafted; paper proof in `../2-fully-proven/pm-ramanujan-band-physical-separation.md`. Original signed-energy norm and every denominator are retained. Goal remains active and unmet.


Physical transfer scratch passed all seven exports; a redundant congruence/ring sequence was replaced by exact division simplification. `PMRamanujanBandPhysicalSeparation` is promoted/wired and its old-mode build is running; final audits remain. Search156 completed, inventory64673 complete, compiler freshness mixed. All20 candidate and20 source statements plus both ingredients inspected. The generated prime-power divisor chain does not supply the desired atom norm. Exact primitive floor expansion and periodicity instead give |P_q(N)|<=min(N,q)*tau(q); splitting the reciprocal energy at q gives at most2*q*tau(q)^2. Current `DivisorBound.card_divisors_le_const_mul_rpow` supplies subpower decay of the normalized single-atom norm. Integer transfer paper proof is recorded at `../2-fully-proven/pm-ramanujan-band-integer-separation.md`; no integer theorem is claimed verified.
