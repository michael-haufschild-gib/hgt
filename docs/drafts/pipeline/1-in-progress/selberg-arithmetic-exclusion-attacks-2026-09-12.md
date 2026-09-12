# Selberg arithmetic exclusion: direct attacks

- Date: 2026-09-12.
- Stage: in progress. Paper calculations below are not new Lean results.
- Target: exclude an actual congruence cuspidal complementary parameter nu>0.
- User correction: stop extending correspondence infrastructure without an argument that advances this exclusion.

## Chain and status

Actual Maass source -> real model and Hilbert isometry -> arithmetic exclusion -> lambda>=1/4. The first construction does not exclude the positive-definite complementary models. Full group equivariance also remains unfinished, but is not the current attack. No new Lean file is being promoted from the abandoned generator scratch.

The previous symmetric-power route card already proves that bounded degrees leave exceptional scalar parameters. Its inspected tensor and twist constructions do not produce compatible unbounded-degree automorphic lifts. Repeating those scalar consequences is not progress on the global construction.

## Attack 1: does the positive tail kernel force positive top stress?

The exact source formulas read this turn are `SelbergMaassPhaseStress.phaseStressXY_eq`, `phaseStressYY_eq`, `topPhaseFlux_eq`, and `core_cusp_phase_stress_bound`; the tail laws are `SelbergMaassKernelWronskian.coefficientWronskian_eq_tail` and `tailLoss_quadratic_nonneg`. They retain a signed, frequency-weighted boundary expression. Positivity of the unweighted kernel does not assign that expression a sign.

Here is a direct test using the same differential equation, without claiming a counterexample to congruence automorphy. Fix 0<lambda<1/4, nu=sqrt(1/4-lambda), Y>0. Define normalized decaying modes

    u_a(y) = sqrt(y) K_nu(a*y) / (sqrt(Y) K_nu(a*Y)),
    L_a = -u_a'(Y),                  u_a(Y)=1,
    u_a''(y) = (a^2-lambda/y^2) u_a(y).

For distinct positive integer frequencies a/(2*pi), b/(2*pi), put

    F(x,y) = z_a u_a(y) exp(i*a*x) + z_b u_b(y) exp(i*b*x).

This is a decaying, period-one cusp-strip solution. It is NOT asserted to satisfy modular inversion or the full congruence Maass conditions. Let

    T_Y(F) = integral[-1/2,1/2]
      (2*x*Re(conj(F_x)*F_y)
        + Y*(|F_y|^2-|F_x|^2+lambda/Y^2*|F|^2)) dx.

Direct finite expansion gives the Hermitian matrix of this quadratic:

    M_aa = Y*(L_a^2-a^2+lambda/Y^2),
    M_bb = Y*(L_b^2-b^2+lambda/Y^2),
    M_ab = epsilon*(a*L_b-b*L_a)/(b-a),
    epsilon = (-1)^((b-a)/(2*pi)).

The off-diagonal formula uses the exact endpoint term

    integral[-1/2,1/2] x*exp(i*(b-a)*x) dx = epsilon/(i*(b-a)).

It does not discard the x weight or the reversed ordered pair. The sign epsilon can be absorbed into z_b and does not affect the determinant.

The standard K and K-prime expansions, with real-argument remainder control, give

    L_a = a - lambda/(2*a*Y^2) + lambda/(2*a^2*Y^3) + O(a^-3).

For fixed distinct A,B>0 and a=R*A, b=R*B, therefore

    M_aa = lambda/(R*A*Y^2) + O(R^-2),
    M_bb = lambda/(R*B*Y^2) + O(R^-2),
    epsilon*M_ab = lambda*(A+B)/(2*R*A*B*Y^2) + O(R^-2),

    det M = -lambda^2*(A-B)^2/(4*R^2*A^2*B^2*Y^4) + O(R^-3).

Taking A=2*pi, B=4*pi, and natural R gives legitimate integer frequencies and a strictly negative determinant for all sufficiently large R. Thus this proposed universal top-positivity implication fails even after retaining the exact decaying Bessel ODE. No numerical evaluation was used. This does not disprove the full core-plus-side-plus-top comparison or the assertion for actual automorphic coefficients.

Analytic source verification: [DLMF 10.40](https://dlmf.nist.gov/10.40) supplies the K/K-prime expansions and remainder statements; [DLMF 10.17.1](https://dlmf.nist.gov/10.17#E1) supplies their coefficients. Substitution of 4*nu^2=1-4*lambda gives the displayed logarithmic slope. These sources support the asymptotic input; the stress matrix and determinant are the paper derivation here. The argument has not been checked in Lean.

### Positive survivor and second pass

For vector amplitudes with positive semidefinite loss Gram G, the two-mode matrix is M_ij*G_ij. If both diagonal masses are positive, its exact positivity criterion is

    |G_ab|^2/(G_aa*G_bb) <= M_aa*M_bb/|M_ab|^2

when M_ab is nonzero and the diagonal stress factors are nonnegative. At the above scale, the right side tends to 4*A*B/(A+B)^2, strictly below one. For ratio B/A=2 the limit is 8/9. Cauchy only gives a bound of one. Zero Gram-diagonal cases force their cross term to vanish.

This is a sharp two-mode diagnostic, not a sufficient condition for the full infinite matrix or for Selberg. It shows precisely why another unweighted Gram/Cauchy lemma cannot close top positivity. A second pass retained the Bessel dependence and endpoint phase; the negative determinant survives. The remaining viable target must use actual arithmetic coefficient relations or compensation by core/side terms. No entire proof route is retired. Lean status of this diagnostic and its Bessel instantiation: unformalized; no completed no-go claim.

## Attack 2: improve the actual prime-modulus collision estimate

The current corpus contains more than an individual-modulus geometric estimate. Source-read `KloostermanGlobalCollisionCentered.lean` proves

    E_collision <= (k+1)*U*V,

with k the modulus-family cardinality, U the aggregate pointwise response budget, and V its aggregate average budget. `KloostermanGlobalCollisionGram.lean` identifies E_collision with the exact common-period average of the squared off-diagonal response mass. These are actual finite arithmetic constructions, not an assumed spectral estimate.

For a family of distinct prime moduli p, write the actual weighted response as

    X_p(t) = w_p * sum[x unit mod p] A_p(x) exp(-2*pi*i*x*t/p),
    v_p = average[t mod p] |X_p(t)|^2
        = |w_p|^2 * sum[x unit mod p] |A_p(x)|^2,
    kappa_p = average[t mod p] X_p(t)^2.

Here A_p is precisely the source Fourier transform occurring in the existing `kloostermanGlobalModulusTimeResponse`. Each response has mean zero, since a unit frequency modulo a prime is nonzero. CRT makes functions of distinct prime coordinates independent in the complete-period average.

Put C(t)=|sum_p X_p(t)|^2-sum_p |X_p(t)|^2. Expand C^2. Terms with a prime appearing only once vanish. The two surviving pairings give the exact real identity

    average C^2 = sum[p != r] (v_p*v_r + conj(kappa_p)*kappa_r).

Since |kappa_p|<=v_p,

    E_collision <= 2*sum[p != r] v_p*v_r <= 2*(sum_p v_p)^2.

This is a dependency-closed finite paper proof for the actual prime-modulus responses. A second proof reads the same cancellation in frequency space: x/p-y/r has reduced denominator p*r, and fixed ordered coprime pairs have injective cross-frequency maps. Distinct unordered prime pairs cannot collide; each global fibre has at most two contributions. Apply the two-term squared-norm bound before summing. The within-pair equivalence and injectivity are already proved in `KloostermanCoprimeCrossPhaseFrequency.lean`; the across-prime-pair assembly was not found in the retained search results. This is a local corpus-duplication finding, not a literature novelty claim.

For comparable prime moduli, this eliminates both the family-cardinality factor and the pointwise-to-average modulus loss in the existing complete-period bound. It is not yet a new Lean theorem.

### Fail-and-pivot: complete periods do not give the spectral interval estimate

The existing terminal receiver pairs the aggregated coefficient A(z) with

    O_M(z) = sum[1<=m<=M] exp(2*pi*i*m*z/P),

where P is the common period. Its complete Parseval factor is P*(M mod P)-(M mod P)^2. The improved coefficient-energy bound alone still leaves this large factor. Replacing the actual interval average by the CRT average would be invalid.

For primes bounded by Q, cross-frequencies have reduced denominators <=Q^2. Generic rational-frequency separation is only >=Q^-4, so applying a generic separation-based large sieve at this stage does not by itself give a Q^2-scale estimate. This is the exact next arithmetic issue: control the signed coefficient/orbit pairing on the required finite interval, retaining source phases and nearby distinct frequencies. Exact-collision sparsity does not prove cancellation between nearby frequencies.

No short-interval bound strong enough to force every nu>0 to disappear has been proved. Do not formalize another generic receiver or claim this complete-period improvement closes Selberg before establishing its quantitative spectral use.

## Search and external screens

Custom searches used deep and hybrid lemma/method discovery for complementary amplification, weighted Schur kernels, Bessel/Stieltjes relations, collective Kloosterman cancellation and coprime fourth moments; lexical queries checked actual Hecke coefficients and coprime Kloosterman declarations. Deep amplification and weighted-kernel results were partial. The retained coprime search returned 29 declarations. Index coverage was source-heavy; source statements were inspected, and no new compilation is claimed. No usable actual Maass Hecke-coefficient theorem was returned by the lexical query; this is not a proof of corpus-wide absence.

The fourth-moment method search found the existing Steinhaus pairing argument and the exact coprime frequency equivalence. The generic anti-Loewner candidate assumes its all-matrix positivity input and does not prove the Bessel or arithmetic input. Unrelated Stieltjes and unitary results were discarded after inspecting their statements.

Broad arXiv screens used locality, regularity, dilation and impedance. Opened recent candidates were [Regularity for Subfactors](https://arxiv.org/abs/2609.10118), [Higher Regularity of Time-Periodic Solutions](https://arxiv.org/abs/2608.30658), and [Impedance Control via Generalized Output Regulation](https://arxiv.org/abs/2608.00756). Their stated results concern algebra normalizers, hyperbolic regularity under nonresonance conditions, and designed control laws. None supplies the required arithmetic short-interval cancellation. No theorem from those abstracts is used here.

## Verification and remaining work

No new Lean module, build, numerical experiment, or axiom was introduced after the user correction. The abandoned generator scratch has no passing result. The paper stress calculation checks the actual source signs, Fourier endpoint and analytic remainder; the prime-modulus calculation checks the exact source response and collision definitions. Both remain unformalized. No Selberg proof, improved eigenvalue bound, or completed no-go is claimed.

Continue with the signed short-interval prime-pairing estimate, or a source-specific bound for the complete core/side/top expression. An improvement must be propagated through its actual quantitative spectral consequence before being called progress on the quarter bound.

## Attack 3: test the spectral use before any formalization

The user repeated the requirement to attack the hardest problem. The prime-family result has NOT improved a spectral bound. A fresh lexical Kuznetsov search returned only the finite carrier `kloostermanPhysicalResidueModulusBilinear_eq`; its docstring explicitly leaves the Kuznetsov--Deshouillers--Iwaniec estimate for later. Deep reciprocity/method discovery found the literal modulus sum and single-modulus identities, not the required signed average estimate. Their source definitions were read.

In the classical trace formula, the geometric weights are tied to the spectral test through the Bessel transform. The proved estimate for a selected prime family is not a bound for the full geometric sum. No construction was supplied that inserts a prime indicator on that side and retains nonnegative spectral weights. For nontrivial congruence level one must also retain the modulus divisibility and character/cusp data; merely selecting ordinary prime moduli does not do that. Accordingly the complete-period result is not promoted as a Selberg advance or as the next coding task.

A concrete cancellation target is the smoothed counterpart of

    sum[c<=X, q divides c] S(m,n;c)/c = O_epsilon(X^epsilon),

with the appropriate character/cusp versions. [Diamantis--Friedberg--Stromberg, introduction](https://arxiv.org/html/2607.10786v1#S1) explicitly distinguishes this conjectural cancellation from their meromorphic continuation and estimates retaining exceptional terms. This paper was already in the prior route record; reopening it verifies the required implication, not a new literature discovery. No claim that its twisted theorem proves the target is made.

## Attack 4: additive reciprocity on the actual congruence sum

Try to prove cancellation directly instead of replacing the sum by a positive energy. Fix positive level q and nonzero integers m,n. Let phi be smooth with compact support in (1,2), and chi smooth with compact support strictly inside (0,1). Consider the bulk-ratio portion of the actual sum

    A_chi(X) = sum[q divides c] phi(c/X)/c *
      sum[0<a<c, gcd(a,c)=1] chi(a/c) e((m*a+n*inverse(a,c))/c),
    e(t)=exp(2*pi*i*t).

This is only a smooth bulk-ratio sector. Boundary sectors and their assembly are not discarded or claimed solved.

For coprime a,c, additive reciprocity gives

    inverse(a,c)/c = -inverse(c,a)/a + 1/(a*c) modulo integers.

Write c=q*k. Then gcd(a,q)=1 and inverse(c,a)=inverse(q,a)*inverse(k,a) modulo a. Poisson summation in k gives the exact transformed sector

    A_chi(X) = (1/q) * sum[a>=1, gcd(a,q)=1] (1/a) *
      sum[h integer] S(h,-n*inverse(q,a);a) * K_X(h,a/X),

where

    K_X(h,u) = integral[v>0] phi(v)*chi(u/v)/v *
      e(m*u/v + n/(X^2*u*v) - h*v/(q*u)) dv.

The sign and factor 1/q come from the ordinary Fourier convention exp(-2*pi*i*xi*k) and the change c=q*k. Both original coefficient indices and the inverse of the fixed level remain visible.

On this sector, u lies in a fixed compact subinterval of (0,infinity). Consequently K_X is uniformly rapidly decreasing in |h|, for fixed q,m,n, by integration by parts in v. Its leading kernel K_0 deletes only n/(X^2*u*v), with

    K_X(h,u)-K_0(h,u) = O_L(X^-2 * (1+|h|)^-L).

The trivial bound |S(h,l;a)|<=a and the O(X) possible a then bound the resulting transformed error by O(X^-1). This is a symbolic paper estimate, not a numerical experiment or a Lean theorem.

The h=0 term is also harmless: S(0,-n*inverse(q,a);a) is the Ramanujan sum c_a(n), whose absolute value is at most gcd(a,n)<=|n|. Its total contribution is O(1), since a is comparable to X and the prefactor is 1/a.

The attempt fails to gain a power of X on h!=0. After rescaling, the remaining phase is

    m*u/v - h*v/(q*u),

which has no growing X parameter. The dual modulus a is still comparable to X. Nonstationarity gives decay in the dual index h, not decay in X for its finitely many small nonzero values. Claiming repeated integration by parts yields X^-A here would be false. The surviving sum has Kloosterman modulus at the original scale and level-dependent inverse phases. It retains the difficult cancellation rather than proving it.

Positive survivor of this attempt: exact smooth-sector reciprocity separates a bounded Ramanujan part and an O(X^-1) kernel-replacement error from the same-scale nonzero dual modes. It does not control the latter, assemble the boundary sectors, or prove the subpower bound. Status: paper derivation, unformalized, no route retirement. Do not turn this transformation alone into another Lean milestone claimed to advance the quarter bound.

Current result of the hard-problem attacks: no improved spectral exponent, no all-level coercivity estimate, and no global lift construction. The outstanding arithmetic task is now explicit at the signed nonzero dual modes, rather than hidden in a norm, a positivity premise, or an unproved spectral transform.


## User correction: auxiliary amplification branch stopped

The user rejected the subsequent fixed-modulus amplification/character-mode investigation as a diversion from proving Selberg itself. That branch produced no improved spectral bound and no proof of arithmetic exclusion. No Lean source was added or built. Do not resume this branch or present its elementary operator identities as progress on the conjecture. The current task has no dependency-closed proof candidate for excluding all complementary exponents.

## Direct exclusion audit: global lifts and forced twist zeros

The following audit produced no improvement in the Selberg bound. It must not be counted as a new mathematical milestone or used to restart auxiliary formalization.

Fresh deep, hybrid, and lexical corpus searches for global symmetric-power automorphy found finite exponent packets, local character identities, and unrelated lift constructions. The inspected `GenericUnitaryExponentBounds.lean` explicitly concerns sums of rank-one model forms, not classification of arbitrary generic GL(n,R) representations. No construction of unbounded-degree global symmetric-power lifts of a general Maass representation was found. Search coverage was partly stale/pending in the first deep request; subsequent completed snapshots still give source retrieval, not new kernel verification.

The direct analytic attempt was to exclude an exceptional parameter by nonvanishing of a twist at a forced positive trivial zero. Write lambda=1/4-nu^2 with 0<nu<1/2, and let pi be the associated cuspidal GL(2) representation in the classical theory. Choose a primitive Dirichlet character chi whose archimedean parity makes pi tensor chi spherical. Set L_chi(s)=L(s,pi tensor chi), let Q_chi be its finite conductor, and put Gamma_R(s)=pi^(-s/2)*Gamma(s/2). Then

    Lambda_chi(s) = Q_chi^(s/2) Gamma_R(s+nu) Gamma_R(s-nu) L_chi(s).

Entireness and the simple pole of Gamma_R(s-nu) force L_chi(nu)=0. To obtain the full conjecture by this route one must prove nonvanishing for at least one twist of this same representation at that same point, for every possible positive nu. This is the classical positive-half-plane twist-nonvanishing route, already explicitly stated in [Luo--Rudnick--Sarnak, introduction, p. 390](https://www.math.tau.ac.il/~rudnick/papers/lrsGAFA.pdf); it is not a new reduction.

Attempted shortcut: reflect nu to 1-nu and use nonvanishing there. It fails exactly: Gamma_R(z) has residue 2 at zero, so the functional equation yields

    L_chi'(nu) = (epsilon_chi/2) Q_chi^(1/2-nu)
      * Gamma_R(1-2nu)/Gamma_R(2nu) * L(1-nu,dual(pi tensor chi)).

Thus even nonvanishing of the reflected value only makes the forced zero simple. It does not contradict the zero. Twisting by an imaginary norm power also moves the evaluation point and gamma pole together; it does not move this problem to central-value nonvanishing. No uniform nonvanishing theorem covering the required points was proved.

The last completed custom deep search (`/tmp/selberg_forced_zero_direct_0912c.json`, generation 884204, partial=false) returned character orthogonality, gamma-pole facts, and Dirichlet GL(1) nonvanishing statements. All 20 candidate statements and 20 source-argument statements were inspected. Its proposed ingredient set contains orthogonality and gamma-pole analysis only. In particular `LFunction_ne_zero_of_zeroAbscissa_lt` requires an already established location to the right of the zero abscissa and concerns Dirichlet L-functions, not these Maass twists. It does not close the arithmetic gap.

Recent primary sources checked for an applicable new input:

- [Balkanova--Frolenkov, September 10, 2026](https://arxiv.org/html/2609.11119v1), Theorem 1.3 and Section 2: nonvanishing at s=1/2 in a high-real-spectral-parameter family of level-one Maass symmetric squares. This is neither the twist family of one hypothetical exceptional representation nor the point s=nu (or s=2nu for its symmetric square).
- [Hagen, September 2026](https://arxiv.org/html/2609.11619v1), Section 2.1: the fixed L-functions are zeta, primitive Dirichlet, and primitive holomorphic cusp-form L-functions. Its moment theorem does not supply the missing Maass twist nonvanishing.
- [Jaasaari, September 2026](https://arxiv.org/html/2609.10446v1), introduction: unconditional low-rank Hecke-sign distribution, with Ramanujan assumptions in the general-rank result. No exclusion of a positive archimedean exponent follows from the statements inspected.
- [Newton--Thorne, 2026](https://annals.math.princeton.edu/2026/203-1/p04): the stated symmetric-power automorphy theorem covers regular-weight Hilbert modular forms. It does not construct the missing general weight-zero Maass lifts.

No Lean source was changed, no Lean process or build was launched, and no numerical experiment was run during this audit. All four owned custom-search sessions completed and were collected. Current mathematical status: no proof of arithmetic exclusion, no improved spectral exponent, and no justified next step that closes Selberg.

## Third consecutive arithmetic impasse: goal blocked

The next automatic continuation revalidated the current worktree, the finite-degree and generic-unitary packet sources, and the completed Hilbert isometry. None supplies arithmetic exclusion. Two further custom deep searches completed with partial=false (generations 884312 and 884325); all returned candidate and source-argument statements were inspected. They supplied existing Maass identities and unrelated algebraic facts, not the required theorem. The proposed Frobenius ingredient set even confuses the matrix Frobenius norm with arithmetic Frobenius, so it is inapplicable. A lexical Maass/Galois query is also polluted by the project namespace `GaloisForLFunctions` and is not evidence of a Galois realization. These searches are not an exhaustive impossibility proof.

A new direct transfer attempt examined [Koymans--Pagano--Shusterman, submitted September 10, 2026](https://arxiv.org/pdf/2609.11855), Theorem 1.1 and Sections 1.1--1.2. They prove density-one central nonvanishing for imaginary quadratic characters over F_q(T), with q=1 mod 8, using Jacobian Frobenius, towers of Galois extensions, and symmetric Artin pairings. Their decreasing spaces detect a square-root-of-q Frobenius eigenspace. A positive proportion of nonzero values would suffice for Selberg if obtained for the twists of each fixed hypothetical exceptional Maass representation at its forced zero. But the paper constructs neither those spaces nor a geometric realization for that family and point. No such realization was found in the inspected corpus. Transplanting the rank-decrease argument without its zero-detection theorem would simply assume the missing nonvanishing. The transfer attempt therefore does not prove exclusion.

This is the third consecutive turn reaching the same impasse after the user rejected auxiliary amplification: no available dependency-closed arithmetic proof argument and no meaningful next formalization step within the user's instruction to work on the actual conjecture. A new mathematical argument or applicable external theorem is needed to proceed from this state. The active goal is marked blocked, not complete; the original formalization objective and all verified work remain intact. No route is claimed impossible or retired. No new Lean source, build, axiom, or numerical experiment was introduced. Search sessions 25971 and 51231 are terminal and collected; the additional lexical search exited normally.

## Resumed source-first attack: current corpus, September 12

The user resumed the task and required current corpus statements and methods to supply the starting point. The proposed base-change search was set aside after this instruction. The goal is active again; the preceding blocked entry records historical status. This continuation proves no new spectral bound.

### Exact original-source target

Write L=N+1. `SelbergMaassCharacterCuspGlue.core_cusp_quarter_identity_one` gives, for an original exceptional Maass source and each residue r,

    C_r + B_r + R_r - J_r = (lambda - 1/4) M_r,

where C_r is `coreQuarter ... 1`, B_r is `boundarySum ... 0`, R_r is `squareSum ... 0`, J_r is half the integral of `pairedArcCurrent` over [0,1/2], and M_r is `coreMass ... 1 + tailMass ... 1`. These are literal source integrals and Fourier coefficients. The corpus proves R_r>=0. Establishing a nonnegative left side for a channel with M_r>0 would exclude that exceptional source. Summing a proved nonnegative estimate over every channel would also suffice once the positive total mass is retained. No such estimate was established here.

The alternative full-source formulation is equally concrete: `SelbergMaassFullGradient.cell_gradient_identity` identifies full physical energy E=lambda M, with M>0. The unresolved assertion is M<=4E. No model replacement or assumed intertwiner is needed to state either target.

### Attempt 1: transport the corpus's invariant-metric rigidity

Source mechanism: `HTGeometry/GomesJacobiPositiveMetric.lean` classifies positive invariant metrics of a two-dimensional Jacobi step by its discriminant. Proposed application: extract a closed finite collection of actual Maass ladder vectors and use positive metric rigidity to constrain the exceptional parameter.

The actual-source check rejects the finite truncation. In `MaassModelIntertwiner.lean`,

    raise v_m = c_m v_(m+1),
    c_m = (2 nu - 1 - 2m)/2,

with every c_m nonzero for the parameter attached to the exceptional source. The lifted vectors v_m are linearly independent (`modelVector_linearIndependent`). A nonempty finite collection has a largest weight m; raising its vector produces a nonzero multiple of an independent vector outside the collection. Thus this collection is not invariant. Compressing the derivative introduces an omitted boundary component and does not supply the exact invariant-metric equation. This is a paper deduction from the inspected source identities, not a newly checked Lean theorem.

Positive survivor: the actual infinite ladder and its positive pullback norm remain valid; they are already formalized in `MaassModelIntertwiner.lean` and `MaassModelHilbertForm.lean`. No duplicate lemma was added. This rejects this finite-truncation application, not every possible representation-theoretic route.

### Attempt 2: remove the seam with opposite Hardy traces

Source mechanism: `HTGeometry/HardyArcGluing.lean` proves the full-circle inner product of a Hardy trace with a conjugate Hardy trace equals the product of their constant coefficients. Its proof explicitly uses disjoint positive and negative Fourier supports away from zero. Proposed application: cuspidality removes the constant coefficient, so use that orthogonality to cancel the actual seam.

The required identification does not follow. `boundarySum_eq_residue_fourier` selects n=r mod L, a two-sided integer progression. Removing n=0 does not remove its negative frequencies. More directly, `radialFlux_seam_identity` identifies the actual current with

    Re < (P_upper,r - P_lower,-r) V, D_radial V >.

The core integration is on the curved modular arc and retains its normal Jacobian. It is not the unweighted full-circle Hardy pairing. Neither the character filter nor cusp mean zero supplies the needed Hardy membership and pairing identity. No assertion that every actual negative coefficient is nonzero is needed for this applicability failure, and no counterexample to the actual Selberg inequality is claimed.

Positive survivor: the original residue filter, exact projection-mismatch current, and its radial/angular energy remainder are already formalized. They preserve the coupling that the proposed cancellation would have discarded.

### Attempt 3: apply positive-frequency wave coercivity to the complete energy

Source mechanism: `ThetaCuspHawkingBMJointWaveCoercivity.lean` proves

    Re < rotatedWaveOperator J w u, u >
      = Re(w) (||u||_V^2 - ||Ju||^2 + |w|^2 ||Ju||^2),

and strict coercivity when Re(w)>0 and J is a contraction. Proposed application: use w=nu to exclude a solution of the original quarter-shifted equation.

The full-source algebra exposes the missing premise exactly. Put m=M(u), e=E(u). With ||u||_V^2=e+m and ||Ju||^2=m, the wave expression before rotation is e+w^2 m. The Maass target is instead

    e + (nu^2 - 1/4)m = 0.

Matching these with the unchanged norm requires w^2=nu^2-1/4=-lambda. Such a w has Re(w)=0, outside the proved coercive region. Keeping w=nu requires changing the norm to ||u||_V^2=e+(3/4)m. Then J is a contraction precisely when m<=e+(3/4)m, namely e>=m/4: the desired Selberg bound itself. This paper substitution retains the complete energy; it does not rely on a strip approximation or an omitted boundary.

Positive survivor: coercivity applies to the unshifted positive form e+nu^2 m. The source theorem already supplies that mechanism. Its quarter-shifted application remains circular, so no new receiver was formalized.

### Attempt 4: retain the adverse cusp block and eliminate it by Schur complement

Source mechanism: `HTGeometry/FiniteRankBoundarySchurIndex.lean` proves exact inertia and positivity criteria for B+VCV*, with Schur matrix -C^-1-V*B^-1V. Its positivity criterion requires B positive definite and -C positive definite, followed by a sign for the actual Schur matrix.

This has a concrete cusp input already in the corpus. `SelbergBesselAdverseModes.lean` proves

    seam(b,T,n)<0 iff n!=0 and |n|<radius(b,T),
    card(adverse(b,T))=2*(ceil(radius(b,T))-1).

`SelbergBesselBoundaryOperator.lean` identifies seam=physical frequency-amplitude, with positive compact correction amplitude<1/(2 exp(T)). The later Maass trace and gluing modules identify the original infinite Fourier sum, so the finite cusp sign classification is not a new task.

The attempted application remains incomplete: no positive bulk B and coupling V were constructed for the complete original core-cusp-seam expression, and no bound V*B^-1V<=-C^-1 was proved. Finiteness of the cusp's negative block does not establish that bound. Its size is not uniform in the level. The remaining problem is the actual core response and its arithmetic coupling to the adverse modes, with the seam retained; proving another abstract Schur identity would not advance it. This route is not retired.

### Search coverage and other screened methods

Twelve post-correction custom searches used the entire configured index, without a module restriction. Queries covered energy/boundary cancellation, signed reciprocal sums, spectral rigidity, Hardy traces, Kloosterman cancellation, finite-quotient invariance, Hecke positivity, two projections, Dirichlet-to-Neumann gluing, and broad uncertainty/observability methods. Deep results' candidate lemmas, source arguments, and proposed ingredient sets were inspected; selected definitions and proof bodies were read directly. This is whole-index retrieval, not a claim to have read every declaration.

Cached result files are `/tmp/selberg_corpus_*_0912f.json`, `/tmp/selberg_invariance_methods_0912g.json`, `/tmp/selberg_hecke_methods_0912g.json`, `/tmp/selberg_projection_methods_0912h.json`, `/tmp/selberg_dtn_methods_0912h.json`, `/tmp/selberg_actual_empty_0912i.json`, and `/tmp/selberg_cross_methods_0912i.json`. Several early deep requests reported partial results. Later completed snapshots reported generations 884450 and 884455, with up to 57,239 inventoried Lean/dependency/prose files. Compiler coverage remains predominantly pending or source-only; no new kernel verification is claimed. The strict lexical actual-type/IsEmpty query returned zero despite the directly inspected small-level theorem containing both terms. Consequently that result is not absence evidence.

Other source checks:

- `PeriodicSpectrumRigidity.lean` requires an even entire function and an actual one-sided arithmetic-progression exponential expansion. These hypotheses were not established for the Maass source or a source-faithful transform.
- `WeightedGraphSpectralGap.lean` receives its averaging estimate as a hypothesis. `CCMLogSymbolDirichlet.lean` likewise receives the positive symbol/coercivity or inverse bound needed by its application. Neither supplies the missing Maass inequality.
- `EulerSupportEnergyUncertainty.lean` proves a weighted Holder summability budget from coefficient-energy and support hypotheses. The required arithmetic coefficient-energy input for this Maass problem was not constructed.
- `SelbergMaassInversionGram.lean` supplies the exact arithmetic phase kernel and proves its absolute weights sum to one. Replacing it by absolute weights supplies a contraction estimate, not the required strict, quantitatively sufficient comparison with physical gradient energy.

Broad arXiv searches used recurrence, sewing, uncertainty, gluing, projection, reciprocity, coercivity, and rigidity. Primary-source checks included [Gomes, July 27](https://arxiv.org/abs/2607.24901), [Krivelevich--Lew--Michaeli, August 21](https://arxiv.org/abs/2608.21058), [Dewar et al., July 6](https://arxiv.org/abs/2607.05023), and [Arroyo-Rabasa, June submission with August-dated text](https://arxiv.org/html/2606.12061v1). These are screened transfers, not imported premises. The expander paper starts from expansion or an adjacency bound and proves framework rigidity. The complex-ellipticity definition requires full column rank at every nonzero complex frequency; the scalar Laplacian symbol vanishes at (1,i). Thus direct application to the Maass equation does not meet that definition. Switching to the gradient requires further structural hypotheses on the actual source measure and does not supply the missing quarter sign.

No new Lean source, build, axiom, heartbeat increase, or numerical experiment occurred in this resumed attack. The outcome is three rejected concrete transfers and an unresolved full-boundary Schur application, not arithmetic exclusion, an improved exponent, or an impossibility theorem.

## Whole-chain reassessment after the user's scope correction

The user explicitly rejected treating one selected obstruction as the only possible route. Every application below is assessed against the original target: exclude an actual congruence Maass source with 0<lambda<1/4. The energy identity, representation model, and analytic twist formulation are different ways to access that source; a failed transfer between two formulas does not retire any of these entire approaches. No new spectral bound was established in this continuation.

### A finite Gram/Kloosterman connection, followed through to the actual weights

The current sources give a direct paper identity. Put L=N+1, R=ZMod L, and psi=stdAddChar. Under the existing deck/residue identification, write U(a), Lw(b) for upper and lower unipotents. `HTGeometry/FiniteUnipotentFibres.lean` gives

    U(a)Lw(b)U(c) = [[1+ab, a+c+abc], [b, 1+bc]].

`SelbergMaassInversionGram.gramKernel_at_word` gives

    K(U(a)Lw(b)U(c)) = L^(-3) card(Ann(b)) psi(rb-s(a+c)).

For unit b, Ann(b) has one element. Fix matrix trace tau. Then a+c=(tau-2)b^(-1). Every determinant-one matrix with lower-left entry b and trace tau has a unique such presentation: a=(g00-1)b^(-1), c=(g11-1)b^(-1), and the determinant relation recovers the upper-right entry. Thus, summing over a and unit b,

    sum_{g: g10 unit, tr(g)=tau} K(g)
      = L^(-2) S(r,-s(tau-2);L).

This is an unweighted identity on the unit cell only, valid also for composite L. It does not discard the nonunit cell from the full Gram operator. The separate corpus theorem `HTGeometry/PoincareSeriesKloostermanPhase.sum_exp_phase_eq_kloostermanSum` already identifies the Poincare-series phases with Kloosterman sums; it does not identify the above finite trace slice with a full Maass spectral formula.

The actual pairing is not this unweighted sum. `SelbergMaassKernelWronskian.complexLoss_convolution` retains

    C_vw(g) = sum_q conj(v(q)) w(qg),
    <v,Tw> = sum_g K(g) C_vw(g).

For arbitrary v,w define

    A_vw(tau,b) = L^(-1) sum_a C_vw(U(a)Lw(b)U((tau-2)b^(-1)-a)).

Its unit-cell contribution is exactly

    L^(-2) sum_tau sum_{b unit}
      psi(rb-s(tau-2)b^(-1)) A_vw(tau,b).

Replacing A_vw(tau,b) by its average over b would leave a covariance remainder, as well as the separate nonunit contribution. Neither remainder has been bounded. Conjugacy averaging was not justified as preserving this pairing.

There is a sharper source check than merely observing an unknown weight. Let v,w be in upper residue channel s. `SelbergMaassCharacterProjection.characterProjection_intertwine` gives R(U(a))v=psi(sa)v, and similarly for w. Since the first inner-product slot is conjugate-linear,

    C_vw(U(a)Lw(b)U(c)) = psi(s(a+c)) C_vw(Lw(b)).

Consequently the inverse-b phase cancels in the actual trace-slice pairing:

    sum_{g: g10 unit, tr(g)=tau} K(g) C_vw(g)
      = L^(-2) sum_{b unit} psi(rb) C_vw(Lw(b)).

Alternatively, summing the original three parameters, including every nonunit b and its collision multiplicity, gives

    <v,Tw> = L^(-1) sum_{b in R} psi(rb) C_vw(Lw(b))
            = <v,Q_(-r)w>,

where Q_(-r) is the lower-unipotent character projection. This is exactly consistent with the existing definition T=P_s Q_(-r) P_s and self-adjointness of P_s. For general v,w the full pairing first projects them by P_s. The trace-slice cancellation assertion above is for the projected vectors, not an assertion that projecting preserves every restricted slice of the original unprojected pairing.

This check applies to the actual Fourier vectors: `SelbergMaassCharacterFourier.upperProjection_coefficientVector` identifies their channel as n mod L. Thus the attempted use of an unweighted Kloosterman estimate does not supply a new estimate for those vectors. The initial phase connection is valid; the proposed gain from it fails after the actual weights are restored. The surviving exact positive projection form is already present in the corpus. The displayed regroupings are paper deductions, not newly Lean-checked theorems, and do not warrant restarting the user-rejected finite-modulus amplification branch.

Whole-chain implication: fixed-level Gram geometry and arithmetic phases are related, but this relation does not replace the missing estimate in the full energy chain. It says nothing against cancellation across varying moduli with its own actual spectral identity, or against an arithmetic restriction obtained through global representations or L-functions.

### Spectral comparison: what the Wronskian does and does not test

The existing same-source cross-frequency identity is

    c_n''=(k_n^2-lambda/y^2)c_n,
    W_nm'=(k_n^2-k_m^2) B(c_n,c_m).

The explicit lambda/y^2 terms cancel. This does not make the coefficient vectors or boundary data independent of lambda; it means the displayed algebraic sign identity alone does not isolate the threshold 1/4.

A paper comparison using the same frequency but different spectral parameters gives W'=(lambda_2-lambda_1)uv/y^2 for W=u'v-uv'. If both decaying scalar solutions are positive and W tends to zero at infinity, lambda_1<lambda_2 implies -u'/u > -v'/v at the boundary. The construction and positivity hypotheses of this comparison were not discharged here. More importantly, even such monotonicity would still need a sign or invertibility anchor for the complete original core-plus-cusp response. It does not provide that anchor. The inspected `SuzukiShiftSpectralMonotoneRatio.lean` likewise explicitly needs an ordering hypothesis on its response/node pairs. Positivity of a spectral measure alone does not discharge that ordering.

Whole-chain implication: keep spectral-parameter dependence when testing an energy argument, but do not elevate one unproved Schur or boundary estimate into a claim that every Selberg proof must pass through it.

### Testing analytic injectivity against the actual family of forced zeros

The preceding twist route has one forced value L_chi(nu)=0 for each compatible twist of one hypothetical exceptional representation. Proposed transfer: use a corpus Mellin injectivity theorem to force the source to vanish.

`SoninMellinInjective.ae_eq_zero_of_laplaceRay_line_eq_zero` requires the transform of one L2 datum to vanish for every imaginary coordinate on a vertical line. `eq_zero_of_extendedMellinContinuation_eq_zero` requires one continued transform to vanish throughout a strip, together with the specified Sonin conditions. A collection of different twists vanishing at one point does not meet either hypothesis. The prior imaginary-norm-twist calculation also does not manufacture this missing line: both the function and its forced-zero point move together.

The search's proposed ingredient group mixed a Mobius/Dirichlet GL(1) Mellin identity in Re(s)>1 with a finite Xi-jet reconstruction theorem. It does not prove this Maass claim. Ordinary Mellin injectivity remains a valid existing positive result; neither a source realization in the relevant space nor completeness of these fixed-point twist functionals was constructed. The nonvanishing route remains open, not refuted.

### Effect on the alternative chains

| Chain | Established input inspected | Missing step capable of changing the target |
| --- | --- | --- |
| Full physical energy | E=lambda M, M>0; exact core/cusp/seam identity and original Fourier coefficients | An estimate implying E>=M/4 for the actual source, with all boundary coupling retained |
| Representation and parameter amplification | Actual infinite ladder and positive Hilbert model; finite-degree admissibility calculations | Arithmetic constructions imposing stronger restrictions on the actual parameter; model degree/rank growth alone is not such a construction |
| Global arithmetic cancellation | Literal Kloosterman phases and finite correlation identities | A sufficiently strong signed estimate across moduli, together with its actual Maass spectral connection |
| Twists and nonvanishing | Previously audited classical forced-zero reduction | Nonvanishing for a twist of the fixed hypothetical representation at its forced point, or a valid completeness argument for precisely these functionals |

The inspected `SymmetricPowerDegreeFamilies.lean` proves that every finite degree family still admits a positive model parameter, while infinitely many degree bounds force it to vanish. This limits a finite packet argument; it does not prove that global lifts cannot be constructed. `CoherentTower.lean` exposes another amplification mechanism: analytic roots of all powers 2^k force every finite zero order to be divisible by all 2^k. No such root family was constructed for these Maass L-functions. Taking logarithms across the very zeros to be excluded would assume the desired nonvanishing.

Subsequent attacks must test whether a candidate supplies one of the missing source-specific assertions above and whether it changes other chains. None of the local failures licenses an assertion that the corpus has no other method or that Selberg requires one chosen route.

### Evidence and process status

Additional whole-index queries covered parameter amplification, moment cancellation, spectral comparison, trace phases, weighted correlations, and twisted Mellin injectivity. Deep/method results were read through `candidate_lemmas`, `source_arguments`, and available proposed ingredient groups; relevant statements and proof bodies were checked directly. Method discovery is part of `--mode deep` and `source_arguments`; this CLI has no separate `--mode method`. The rejected invocation made no change.

Snapshots are `/tmp/selberg_actual_*_0912j.json`, `/tmp/selberg_chain_*_0912k.json`, `/tmp/selberg_weighted_operator_deep_0912l.json`, `/tmp/selberg_twist_boundary_methods_0912m.json`, and `/tmp/selberg_mellin_injectivity_0912n.json`. Several deep requests were partial; the final hybrid request completed against snapshot generation 884585. Whole-index retrieval is not an exhaustive reading or compiler audit of the corpus. Broad recent arXiv screening also checked interpolation and monotonicity, including [Cuenca--Patungan--Ragas, September 8 revision](https://arxiv.org/abs/2608.08198) and [Neumayer--Pozharska--Ullrich, September 1](https://arxiv.org/abs/2609.01578); no applicable Selberg implication was established from their abstracts.

All owned searches finished and their sessions were collected. No Lean process, build, numerical experiment, or Lean-source edit occurred. The original proof objective remains unfinished. This update records a corrected proposed transfer and the consequences for several chains; it is not a spectral improvement or a route retirement.

## Whole-chain source test: scalar theta probes and the cuspidal deck component

The target remains an unconditional exclusion for the actual congruence Maass source: equivalently, a source-specific arithmetic restriction eliminating a positive complementary parameter, or an estimate E>=M/4 in the already proved identity E=lambda M with M>0. This pass tested a different corpus family rather than assuming that one boundary estimate is the only route.

### Conjecture, source check, failure, and positive replacement

**Candidate transfer:** use the native theta-source positivity and occurrence machinery to constrain a hypothetical exceptional congruence Maass form.

`SelbergThetaNativeSource.modeSource` periodizes a height-only seed indexed by `XiZeroCopy`. Its proved full-modular invariance puts its scalar deck lift in the trivial deck component. The source-comparison card `sqb-native-spectral-source-comparison.md` concerns Xi-target occurrence and an RH route; it does not supply occurrence for an arbitrary congruence Maass form.

There is an exact obstruction for this particular linear transfer. For an actual hypothetical exceptional f, `SelbergMaassDeckAverage.sum_deck_values_zero` proves, at every z,

    sum_q deckVector_f(z)(q) = 0.

Its proof uses the existing level-one exceptional exclusion on the actual deck trace. For a full-modular scalar probe P, its deck lift W_P(z)(q)=P(z) therefore satisfies

    <W_P(z), deckVector_f(z)>
      = conj(P(z)) * sum_q deckVector_f(z)(q) = 0.

This displayed pairing identity is a paper deduction from the existing Lean theorem, not a newly compiled theorem. It concerns the pointwise deck pairing; no unproved finite-cover integration formula is being claimed. Periodization can produce nonzero horizontal Fourier coefficients while the scalar source remains full-modular invariant, so those coefficients do not evade this deck-component mismatch.

**Scope:** this rules out directly obtaining linear detection of the hypothetical exceptional source with this scalar family. It does not rule out the independent SQB/RH chain, quadratic weights involving P(z)|f(z)|^2, or source families in nontrivial deck components. It is not a retirement of theta methods or of Selberg routes.

**Positive replacement, on paper:** the actual source has detecting nonzero-frequency data. Nonzero continuous f gives a positive horizontal slice mass at some height. `SelbergMaassParseval.maass_mass_hasSum` then forces a nonzero Fourier coefficient on that slice; `SelbergExceptionalCuspMean.maassMean_subquarter_zero` and `SelbergMaassFourierModes.maassCoefficient_zero` exclude frequency zero. Height continuity of the coefficient allows a nonnegative smooth compact height test, supported where a fixed rotation of that coefficient has strictly positive real part, with nonzero coefficient pairing. A congruence Poincare probe retaining that horizontal phase would detect f by an appropriate unfolding identity. That last probe construction and its unfolding have not been formalized here. The corpus's general coset-unfolding framework is relevant infrastructure, not a proof of this exact source identity.

Nonzero frequency n need not have nonzero residue modulo the cusp width; do not replace this assertion by a nontrivial finite-residue claim. Detection also does not exclude the complementary parameter. A useful next estimate must constrain these actual detecting functionals strongly enough to change the spectral bound, rather than merely package their existence.

### Consequences for the other chains

- **Physical energy:** trivial-deck scalar probes fail as linear detectors, but scalar weights in a quadratic energy argument remain possible. The existing complete core/cusp/seam identity still requires an arithmetic estimate; the linear obstruction does not decide its sign.
- **Representation:** `MaassModelHilbertGenerators` identifies actual infinitesimal generators, and `MaassModelHilbertCompletion` constructs the completed isometry. Full group equivariance and invariant range are separate unfinished claims. `GenericUnitaryExponentBounds` treats specified rank-one block packets, not a classification of arbitrary generic unitary GL(n,R) representations. `SymmetricPowerDegreeFamilies` supplies parameter implications, not the required global arithmetic lifts.
- **Across-modulus cancellation:** `KloostermanDistinctModulusCompleteCorrelation` gives orthogonality over a complete product period and an explicit interval remainder. `KloostermanProductHarmonicQuadratic` bounds the actual off-diagonal expression using absolute values and a positive modulus budget. These inspected bounds do not supply the signed cancellation needed for a new spectral gain. This is a statement about those formulas, not an absence claim about the corpus.
- **Twists:** replacing scalar probes by nonzero-mode detecting functionals preserves the need for a source-specific completeness or nonvanishing theorem. The prior mismatch between many twisted functions at one point and one Mellin transform on a line remains unresolved.

Broad recent arXiv screening found [Xiyu Hu, September 4, 2026](https://arxiv.org/abs/2609.05652). Its finite-field incidence method uses escape from every proper subgroup and size restrictions to obtain a positive exponent gain. The paper verifies those hypotheses for its particular Mobius families. No realization or nonconcentration estimate for the actual Maass-weighted source was constructed here, and the gain is not a quarter-gap estimate. It suggests a hypothesis to test if an actual source family is found; it is not an applicable Selberg theorem at present.

### Retrieval and verification status

The additional whole-index searches cover global parameters, arithmetic cancellation, automorphy, cross-modulus expressions, native occurrence, and cuspidal source detection. Snapshots are `/tmp/selberg_global_parameter_0912o.json`, `/tmp/selberg_global_cancellation_0912o.json`, `/tmp/selberg_automorphy_0912p.json`, `/tmp/selberg_kloosterman_modulus_0912p.json`, `/tmp/selberg_native_occurrence_0912q.json`, and `/tmp/selberg_cuspidal_source_detection_0912r.json`. Candidate statements, source arguments, and available ingredient groups were inspected; selected actual definitions and proofs were read. The two global deep requests and final cuspidal request were partial. Automorphy and modulus hybrid requests and the native-occurrence deep request completed. Generations ranged from 884706 to 884722; compiler freshness was incomplete. Retrieval is not an exhaustive corpus or compiler audit.

All owned searches finished and were collected. No Lean process, build, numerical experiment, or Lean-source edit occurred. Progress is a source-checked change to which transfers remain plausible, with a positive detecting replacement on paper. No new eigenvalue bound or unconditional Selberg proof was obtained.

## Quadratic transfer test: the actual density retains a forced equation

The preceding scalar-probe obstruction left quadratic weights open. This pass tests that alternative on the actual source. The initial generator-integration search also found `HTGeometry/KrylovProjectedCompleteIncidenceLaw.norm_sub_taylorWithinEval_le_factorial`, a general Banach-valued remainder theorem. However, the current intertwiner card explicitly records the user's stop on generator/completion infrastructure. No generator scratch or infrastructure build was resumed. Completing that analytic correspondence would not establish the arithmetic exclusion now requested.

### Candidate: square the congruence source and descend to level one

Write F(z) for the actual finite deck vector and rho=||F||^2 for `SelbergMaassCongruenceTrace.density`. This density is full-modular invariant and nonzero. It is a literal quadratic construction from the original form, unlike the abstract tensor or packet results retrieved in this pass.

The positive hyperbolic Laplacian has the sign convention Delta=-y^2(d_x^2+d_y^2). `SelbergMaassTraceEnergy.trace_laplacian` and `SelbergMaassFullGradient.hyperbolicGradient_eq` give

    Delta rho = 2 lambda rho - 2 e,

where e is the actual hyperbolic gradient-energy density. Thus the quadratic descent produces a forced scalar equation, not a scalar Maass eigenform with an amplified spectral parameter. Its horizontal constant coefficient is also not removed by the original cuspidality: the average of a nonnegative, nonzero density is positive on some slice. Subtracting its global mean does not remove this height-dependent horizontal coefficient, and changes the equation to

    Delta (rho-rho_bar) = 2 lambda (rho-rho_bar) + 2 lambda rho_bar - 2 e.

The centered horizontal coefficient tends to minus rho_bar in the cusp, since the original finite sum of slice masses tends to zero, whereas rho_bar>0. Thus it does not vanish identically. The existing level-one cusp-eigenform exclusion cannot be applied to this centered forced source. This failure concerns this literal quadratic descent, not all tensor constructions, global functorial lifts, or quadratic methods.

### Retain the forcing: exact quartic identity on paper

Let a=y^2*angularEnergy, with the corpus's convention at density zeros. The already proved `SelbergMaassTraceRadial.density_mul_gradientDensity` gives, everywhere,

    rho e = (1/4)|grad_h rho|^2 + rho a.

Here the derivative of rho is the already defined `current`. In particular rho a>=0, including at common source zeros. The positive-Laplacian product rule now gives the pointwise identity

    Delta(rho^2) = 4 lambda rho^2 - 3 |grad_h rho|^2 - 4 rho a.

This is a paper deduction from the inspected source identities, not a new Lean theorem. The global passage has the following paper proof. Each actual deck component is bounded by `MaassCongruenceL2.source_bounded`, so rho is bounded. The proved finite mass and integrable e imply integrability of rho^2, rho e, |grad_h rho|^2 and rho a; the latter two are dominated by 4 rho e and rho e. Choose smooth full-modular cutoffs chi_H equal to one below cusp height H and zero above 2H, with H>2. On the unique height>H cusp chart these are fixed smooth functions of y/H; their hyperbolic Laplacians have a bound independent of H and are supported in that escaping cusp band. Green's formula applied to the smooth invariant rho^2 and compactly supported chi_H gives

    4 lambda integral chi_H rho^2
      = 3 integral chi_H |grad_h rho|^2
        + 4 integral chi_H rho a + integral rho^2 Delta chi_H.

The last term tends to zero by integrability of rho^2 and the uniform cutoff-Laplacian bound. Dominated convergence handles the other three terms. The quotient's paired sides contribute no boundary term; this is the invariant compact-support Green formula, not an omission of the earlier source seam. Therefore, writing all integrals over the full level-one modular quotient with hyperbolic measure,

    R = integral rho^2 > 0,
    D = integral |grad_h rho|^2,
    A = integral rho a >= 0,
    lambda R = (3/4) D + A.

`SelbergMaassPairPhaseEnergy.density_mul_angularEnergy` identifies A with the integral of the actual pair-current and phase-current squares (the y^2 cancels hyperbolic volume). This retains concrete source information lost by merely declaring the density positive. Neither the new cutoff argument nor this global quartic identity was compiled in Lean in this pass.

### Attempted scalar coercivity, failure, and the surviving target

Test the strongest conclusion of the proposed shortcut before building it. If a scalar Poincare estimate D>=Lambda*(R-M^2/V) were supplied for this density, where M=integral rho and V is quotient volume, the identity and A>=0 would give only

    lambda >= (3 Lambda / 4) * (1-M^2/(V R)).

Even granting Lambda=1/4, this lower bound is strictly below 3/16, since M>0. No scalar Poincare theorem on the modular quotient was constructed or claimed as an existing Lean input here. The torus Poincare theorems retrieved by deep search control horizontal variance, leaving the positive horizontal mean. The source-specific one-dimensional Brascamp--Lieb theorem likewise requires a curvature/weight realization that has not been supplied. Their constants cannot be transferred by identifying names such as variance or Fisher information.

The positive survivor is the exact retained target

    3 D + 4 A >= R.

With the quartic identity this is equivalent to the desired quarter bound for this actual source. It is not proved by positivity of A, and introducing it as an assumption would conceal the hard problem. A useful arithmetic result would need to bound the actual pair/phase-current energy together with density variation. Global lifts or twisted nonvanishing could still exclude the same source by different arguments; this identity is not claimed to be their necessary intermediate step. Conversely, scalar theta weights would need to control these retained terms or their weighted versions rather than inherit cuspidality from f.

### Retrieval, literature, and status

Whole-index requests this pass: generator integration and orbit uniqueness (`0912s/t`), unitary tensor/arithmetic transfer (`0912t/u`), weak containment and density variance (`0912v`), and quartic Fisher methods (`0912w`), saved as `/tmp/selberg_*_0912{s,t,u,v,w}.json`. Generator, actual-tensor hybrid, weak-containment hybrid, and quartic hybrid requests completed; orbit, tensor deep, and density-variance deep requests were partial. Inspected snapshots ranged from generation 884766 to 884783, with inventory complete and compiler freshness still largely pending/source-only. Candidate and method sections were inspected; source definitions used above were read directly. Some semantic fallbacks returned weak-order or quantum-gate statements instead of representation weak containment. Those are retrieval mismatches, not applicable ingredients or evidence that the corpus lacks a result.

One potentially relevant adelic hit was checked directly: `CCMRationalAdelicBruhatSimpleTensorTraceClass` estimates literal rational dilations f(bInf*q)*phi(q*b) and the resulting weighted shifts on l2(Q^x). Its bound is a fixed-base absolute-summability bound for archimedean/finite-adele Schwartz inputs. It does not construct a GL(2) Maass realization or an amplified automorphic parameter; no such source identification was established here.

Broad newest-first arXiv searches used `generation` and `continuation`. [Yamaguchi--Tajima, September 10, 2026](https://arxiv.org/abs/2609.11926) was screened at abstract level: its conversion theorem concerns finite-dimensional states with compact Lie group symmetries and a family of quantum Fisher matrices. No transfer to the actual noncompact Maass action or lower bound for A was established. It is not used in the quartic derivation.

The prior turn yielded evidence changing which source transfers to test; this turn followed its still-open quadratic alternative through the actual differential equation. No eigenvalue improvement, global arithmetic lift, generic-unitary classification, or Selberg proof was obtained. No Lean source was edited and no Lean/build or numerical process was launched. The full original objective remains incomplete.
