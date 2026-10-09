# Algebraic components forced by discrete cosine fibers

- **ID:** cosine-algebraic-fiber-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM ON PAPER; significant novelty unverified
- **Parent:** ../1-in-progress/labeled-lattice-section-periodicity.md; ../3-formalized/cosine-product-corner-unfolding.md
- **Target:** Classify all rational reflected-cosine repairs, including arbitrary diagonal basepoints.

## Exact theorem A [PAPER]

Let T(w)=cos(2π sqrt((w+1/12)/27)), interpreted by its entire even series, and Φ(w)=(T(w),T(-w)). For every irreducible affine algebraic curve D in C² which is neither vertical nor horizontal, and every finite subset B of D, the set

    {w in C : Φ(w) in D\B and w not in Z}

is infinite.

Consequence to audit: if R in C(X,Y) is nonconstant and three distinct complete fibers of R∘Φ lie in Z, then R belongs to C(X) or C(Y). If in addition (R∘Φ)(-w)=1/(R∘Φ)(w), no such nonconstant R exists. These statements concern this fixed source and rational repairs; they do not settle C2-P for arbitrary meromorphic maps or the actual Xi section.

The stronger real-line version is not proposed: algebraic projections of cosine/cosh pairs can have real fibers with nonarithmetic locations. Exact discreteness, not merely reality, is essential in the finite-coordinate case.

## Competing mechanisms and hostile audit

The product repair's second and third fibers suggest that each non-coordinate component at infinity generates offending points. A competing counterexample would be a non-coordinate algebraic curve whose entire pullback zero set, after finite exclusions, lies in Z. Test every boundary type, including repeated branches and finite coordinates ±1; a simple-root-only theorem cannot establish A.

Deep corpus query `rational cosine reflected polynomial fiber vertical horizontal component lattice rigidity`: all 20 candidate statements and 20 source arguments inspected, partial=false, errors empty, 68211 files inventoried; compiler freshness incomplete. The suggested cosine half-angle/lattice ingredient set is inapplicable. The separate deep query `analytic germ exponential flat curve discrete lattice second differences rigidity` found existing exponential-polynomial independence and qualitative exponential flatness, not the component theorem. Generic finite differences, algebraic normalization, local logarithms and submersions are classical and are not claimed as discoveries.

[Bhardwaj–McCulloch–Ramachandran–Woo, Integer-valued o-minimal functions](https://arxiv.org/html/2404.10737v1), introduction and Theorems 1.1–1.3 checked: broad integer-value-to-polynomial rigidity is already known under definability and growth hypotheses. Thus the discrete stabilization step below is not a novelty claim. Their estimates are not used. [Bergweiler–Eremenko](https://arxiv.org/abs/0808.3800) concerns real-line fibers and circle images, not the present algebraic-component conclusion. A full audit of the exact conclusion and curve-normalization machinery remains open.

**Preliminary verdict:** SURVIVES PRELIMINARY ATTACK, without novelty certification. The initial open core was the arbitrary boundary-branch construction and rational-pencil deduction. The paper closure below discharges it; the full theorem remains unverified in Lean.

## Paper proof: exact boundary charts

Set c=2π²/81 and Q(U)=27U²/(4π²)-1/12. Then U²+V²=c implies Φ(Q(U))=(cos U,cos V). Normalize the projective closure of D. A pole of either coordinate supplies a local parameter s with at least one pole. A nonconstant holomorphic coordinate has finite vanishing order at any finite limiting value. Passing to a finite ramified parameter is allowed and must be tracked.

### Both coordinates have poles

Write x=s^(-m)A(s), y=s^(-r)B(s), with m,r positive integers and A(0)B(0)≠0. Analytic submersions give units a,b satisfying

    a²-2A*a+s^(2m)=0, a(0)=2A(0),
    b²-2B*b+s^(2r)=0, b(0)=2B(0).

Choose local analytic logarithms α=log a, β=log b. For an integer N, put t=1/N, q=exp(-2πN), s=q*exp(ell), and

    C=2π(r-i*m),
    u=i*m*ell-i*α(s), v=i*r*ell-i*β(s),
    U=N*C+u, V=-i*N*C+v.

The exponential identities are exact: exp(iU)=s^(-m)*a(s) and exp(iV)=s^(-r)*b(s), because the omitted factors are exp(2πi*r*N) and exp(-2πi*m*N). Hence cos U=x(s), cos V=y(s).

The conic equation after multiplying by t is

    2*C*(u-i*v)+t*(u²+v²-c)=0.

At t=q=0 this is affine in ell, with derivative 4π(m²+r²)≠0. It therefore gives ell(t,q) analytic at the corner. Specialization provides exact intersection points. Moreover N^(-2)*Q(U_N) tends to 27(r-i*m)², whose imaginary part is -54*m*r≠0. Thus the points are eventually nonreal. The same nonzero scaled limit excludes a finite image set, without a magnitude estimate. Since s_N tends to zero through nonzero values, all prescribed finite exclusions B are eventually avoided by the normalized branch.

### One coordinate is finite

After exchanging x,y if needed, write x(0)=a0, x nonconstant, y=s^(-m)B(s). After replacing s by a square if a0=±1, construct an analytic u(s) with cos u(s)=x(s). This needs the exact order-two local normal form of cosine at its critical points, not an assumed inverse there. Write u0=u(0); u(s)-u0 has positive finite order.

Construct b, β as above for the pole coordinate. Put q=exp(-2πN/m), s=q*exp(ell), U=2πN+u(s), V=-2πi*N+v, with v=i*m*ell-i*β(s). Then the exact conic equation is

    4π*(u(s)-i*v)+t*(u(s)²+v²-c)=0.

Its ell-derivative at the corner is 4πm≠0, hence it gives another analytic branch. The points have the exact decomposition

    w_N = 27N²+(27u0/π)N+27u0²/(4π²)-1/12+δ_N,
    δ_N = 27/(4π²)*(u(s_N)-u0)*(4πN+u(s_N)+u0).

Finite-order factorization and the qualitative limit N*exp(-κN)→0 give δ_N→0. No error bound, rate estimate or zero-counting comparison is proposed. The mechanism still requires audit against the user's exclusion of estimating bounds: the intended proof uses the exact factorization and an existing qualitative limit, not an inequality criterion.

If all sufficiently late w_N lie in Z, their third finite differences lie in the closed discrete group Z and tend to zero. They are therefore exactly zero eventually. Consequently δ_N is eventually a polynomial of degree at most two; δ_N→0 forces that polynomial to vanish. Thus U_N²=(2πN+u0)². The negative alternative is excluded by multiplying by 1/N and taking the two distinct limits 2π and -2π. Hence u(s_N)=u0 eventually, contradicting the nonzero finite-order factor of u(s)-u0 at nonzero s_N. This excludes eventual lattice membership. Since w_N/N²→27, a finite set of exceptional w is impossible. Swapping coordinates replaces w by -w and preserves Z.

## Rational-pencil deduction

Represent R=P/Q with coprime polynomials. Each irreducible factor of P-λQ meets Q=0 at only finitely many points. Conjecture A therefore forces all these factors to be vertical or horizontal whenever the genuine λ-fiber of R∘Φ lies in Z. Thus each of three pencil members is a separated product A_j(X)B_j(Y).

Three distinct members have a linear relation with all coefficients nonzero. A sum of two decomposable tensors is decomposable only if their first factors or their second factors are proportional. Pairwise coprimality of the pencil members then makes their shared factor constant. It follows that all three members, hence P and Q, depend on one coordinate alone.

For the reciprocal conclusion, prove separately that Φ is Zariski dense. Fix arbitrary cos u0=a. The conic-correction submersion from the product repair supplies the points Q(u0+2πN), at which the second cosine coordinate has infinitely many distinct values: its reciprocal exponential coordinate tends to zero while 2z*y=1+z². A finite set of y-values would contradict this identity by a constant subsequence. Hence a polynomial vanishing on Φ vanishes on every vertical line. The reciprocal identity then becomes R(X)R(Y)=1, forcing a constant.

## Remaining work and positive survivor

- Audit analytic normalization, all ramified coordinate charts, exclusions and quantifiers; close every dependency on paper before Lean.
- Audit the exact general theorem externally, not just the elementary stabilization lemma.
- Formalize the boundary construction and component classification, then the pencil consequence. Keep the full rational class as the target; do not replace it with another single repair example.
- If the conjecture fails, retain a precise classification of boundary types that survive, including an actual exceptional component. Do not retire a class merely because one branch construction fails.

The paper conclusion concerns rational repairs of this fixed cosine source. No RH theorem, general C2-P theorem or Lean certificate for the full rational class is claimed.

## Normalization audit and a finite-jet construction

[Greenblatt, section 2, Theorem 2.1](https://arxiv.org/pdf/0807.2287) gives convergent Puiseux branches by finite Newton-polygon descent and local implicit functions. Only its analytic-curve result is relevant; its separate oscillatory-integral results are excluded. [Singular-curve preliminaries, Proposition 3.2 and Corollary 3.3](https://link.springer.com/article/10.1007/s00209-026-04027-2) explicitly state local Puiseux parametrization and global normalization. This verifies the classical paper dependency, not a novelty claim.

The corpus already proves formal Newton–Puiseux splitting in `NewtonPuiseuxSplitting.exists_prod_X_sub_C_map_expand`. Its coefficient ring is formal `PowerSeries K`; convergence must not be silently assumed. Deep normalization search returned no applicable analytic producer; all returned statements were inspected, partial=false, inventory complete and compiler freshness incomplete. The proposed monomial/adic ingredient set is inapplicable to complex convergence. Targeted searches for convergent Puiseux/analytic ramification also found no direct theorem.

A potentially cheaper exact bridge avoids analytic estimates and global Riemann-surface infrastructure. Given a formal root y(s) of an analytic polynomial f(s,Y) with nonzero formal derivative D=f_Y(s,y), let d=ord D and take m>d. Write y=p(s)+s^m*z(s), with p its finite truncation. Taylor's finite polynomial identity shows

    f(s,p+s^m Z) = s^(m+d)*G(s,Z),

where G is analytic, G(0,z(0))=0 and G_Z(0,z(0)) is the nonzero leading coefficient of D. Terms of degree at least two in Z acquire at least 2m powers of s; the strict inequality m>d is a valuation comparison, not an analytic remainder estimate. Divisibility of the constant term follows by substituting the formal root. Local IFT produces an actual analytic root with the same finite jet. Formal uniqueness can recover all coefficients if needed; the boundary construction needs only the actual analytic root and its pole orders.

To obtain a suitable polynomial, use a generic linear coordinate L=X+aY so the transformed irreducible curve equation is monic in Y up to a nonzero constant. Substitute L=t^(-1), Y=t^(-M)Z with an integer M clearing all coefficient denominators. This gives a monic polynomial over C[t]; formal Newton–Puiseux supplies a root after t=s^N. Separability over C(L) guarantees its formal derivative is nonzero. The analytic bridge then yields meromorphic x(s),y(s), with L=s^(-N), so at least one has a pole. Nonconstant x and y follow from irreducibility and the exclusion of coordinate lines. This is a concrete route to formalizing the normalization input. All generic-coordinate, valuation and separability details still require explicit verification before the paper is marked closed.

The finite-jet bridge itself has the following exact proof. With y=p+s^m*z and d=ord f_Y(s,y), finite Taylor expansion gives f(s,p)=-s^m*z*D+s^(2m)*H and f_Y(s,p)=D+s^m*H1. Hence every coefficient of f(s,p+s^m Z) is divisible by s^(m+d), and after division the special fiber is exactly lc(D)*(Z-z(0)). For polynomial f and polynomial truncation p the quotient is a polynomial, since divisibility in formal series means its finitely many low polynomial coefficients vanish. Local analytic IFT gives the required root. This avoids coefficient growth or convergence-radius estimates entirely. Generic-coordinate and separability work remains; the full class theorem is not yet claimed.

Deep query `formal power series algebraic root convergence analytic implicit derivative valuation truncation` was inspected in full (candidate statements and source arguments), partial=false, errors empty. It retrieved generic analytic convergence and implicit-function tools, not this algebraic-to-analytic producer. The proposed ingredient set would assume a convergence radius and is therefore insufficient. No additional Lean file was written for this bridge in this cycle.

## Paper closure of the normalization dependency, 2026-10-07

Let F(X,Y) be an irreducible equation of D, of total degree d. Its highest homogeneous part F_d is nonzero, so the polynomial a↦F_d(-a,1) is nonzero. Choose a outside its finite zero set, put L=X+aY, and divide F(L-aY,Y) by F_d(-a,1). The result is monic in Y, with coefficient p_j(L) of degree at most d-j. Thus

    G(t,Z)=t^d*F(t^(-1)-a*t^(-1)*Z,t^(-1)*Z)/F_d(-a,1)

is a monic polynomial in Z over C[t]; each coefficient is t^(d-j)*p_j(t^(-1)), a polynomial. No arbitrarily large scaling exponent is needed. Over C(t), irreducibility is preserved by the invertible changes L=1/t and Y=Z/t. Characteristic zero therefore makes G separable. A Bezout identity between G and its Z-derivative persists under t=s^N into C((s)): the field embedding is injective because the distinct powers s^(Nk) are linearly independent.

Formal Newton–Puiseux gives N>0 and a formal power-series root z(s) of G(s^N,Z). The Bezout identity makes G_Z(s^N,z(s)) nonzero. Apply the finite-jet argument proved above to obtain an analytic root z_an(s). Then

    y(s)=s^(-N)*z_an(s), x(s)=s^(-N)*(1-a*z_an(s))

are meromorphic germs satisfying F(x,y)=0 and x+a*y=s^(-N). At least one has a pole. Neither coordinate can be constant: a constant x or y would force F to vanish identically on that coordinate line (the other coordinate has infinitely many values by the displayed identity), contradicting irreducibility and the non-coordinate hypothesis. A finite excluded set B is avoided near s=0 because a pole coordinate minus each of its finitely many prescribed values retains the same nonzero leading coefficient.

For the finite-coordinate chart, the only omitted inverse issue is now explicit. If x(s)=1+s^k*A(s) with A(0)≠0, replace s by r², choose an analytic square root h(r) of -A(r²)/2, and solve sin(v/2)=r^k*h(r) near v=0 using its nonzero derivative. Then cos v=x(r²). If x(s)=-1+s^k*A(s), use h²=A(r²)/2 and u=π+v instead. For x(0)≠±1, an ordinary local cosine inverse applies. These constructions retain a nonconstant analytic u, so u-u0 has a finite positive order. Pole orders are multiplied by two under this ramification and remain positive integers.

The two boundary submersion calculations above now cover every possible meromorphic chart. In the finite-coordinate case the third-difference identity gives an eventual quadratic polynomial exactly: repeated summation of Δ³δ=0 yields δ_(N+k)=δ_N+k*Δδ_N+k*(k-1)*Δ²δ_N/2. Multiplication by k^(-2), then k^(-1), and uniqueness of limits force all coefficients to vanish because δ tends to zero. These are qualitative limit identities and discreteness, with no bound estimation. If only finitely many offending w existed, the nonzero limit of w_N/N² would exclude those finitely many values eventually, giving the contradicted eventual integer membership. Thus A holds with every finite exclusion B. The reciprocal statement follows through the separated-pencil and Zariski-density arguments already given.

**Paper status:** dependency-closed proof of A and its rational-repair consequence, using classical formal Newton–Puiseux, polynomial algebra and scalar analytic IFT. **Lean status:** not yet formalized; normalization and the two general boundary charts must all be supplied, not assumed in a final certificate. **Novelty status:** the full component classification survives the current preliminary search; significant novelty remains unverified. [Hauser, The classical Artin approximation theorems](https://homepage.univie.ac.at/herwig.hauser/Publications/hauser%20bams%20classical%20artin%20approximation%202017.pdf), introduction and implicit-function discussion checked, confirms that the formal-to-analytic bridge is classical machinery. It is not the scientific claim of this cycle.

## Formalization log, 2026-10-07

`AlgebraicFiniteJetBranch.exists_analytic_root` now supplies an actual analytic root of a bivariate polynomial from a formal root whose formal derivative is nonzero, preserving its constant term. The derivative may vanish at the origin. `exists_scaled_factor` proves the exact finite-jet division and linear special fiber. Targeted `lake build --old +GaloisForLFunctions.HTGeometry.AlgebraicFiniteJetBranch` passes (2734 jobs), and final direct `lake env lean GaloisForLFunctions/HTGeometry/AlgebraicFiniteJetBranch.lean` passes without diagnostics. The leaf is wired once. This closes one classical dependency, not the component theorem.

Corpus query `polynomial coprime derivative denominator nonzero bezout fraction field` returned the applicable existing `PolynomialBezoutDenominator.exists_bezout_of_isCoprime_map`. All 20 candidate statements and 20 source-argument statements were inspected; partial=false, errors empty, inventory complete, compiler freshness incomplete. Reusing this theorem supplies the denominator-cleared identity needed to keep the formal derivative nonzero under ramification. The ramified analytic root producer is the next verification step.

That producer is now verified as `AlgebraicRamifiedBranch.exists_ramified_analytic_root_of_irreducible`: every monic irreducible bivariate complex polynomial admits an actual local analytic root after some positive ramification. Generic separability is derived using Gauss's lemma and characteristic zero, not assumed in this endpoint. The separable version is also exported. Targeted build passes (3018 jobs); final direct `lake env lean GaloisForLFunctions/HTGeometry/AlgebraicRamifiedBranch.lean` passes without diagnostics. Both new leaves are wired once. Three axiom checks report only `propext`, `Classical.choice`, `Quot.sound`. Scoped whitespace checks pass.

Global lint exits 1 on seven unrelated unreachable modules: RHTower `WeilConeResonanceBudget`, `WeilConeResonanceMoments`; HTGeometry `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. Neither new leaf is flagged. No full or umbrella build, numerical experiment, heartbeat increase, commit or push.

**Cycle audit:** classical bridge, not a scientific novelty claim. The full class theorem is paper-only. The next formal obligations are the polynomial model of an arbitrary curve at infinity, the general two-pole and finite-coordinate charts, discrete stabilization, and the pencil consequence. Do not replace these with another single repair example.

Index refresh passes (three changed files, zero removals); LEAN_API, LEAN_GAPS and LEAN_OVERVIEW regenerated. All owned verification jobs reached terminal exits. Seven completed scratch files were deleted after recording their findings. Cross-session state is saved in Serena memory `rh/cosine_algebraic_branches_2026_10_07`.

## Normalization implementation alternative to investigate

A fixed-coordinate construction may avoid generic shears entirely. For irreducible F with both coordinates nonconstant, set x=1/t and clear the finitely many coefficient denominators in F(1/t,Y), obtaining Q(t,Y). Write a(t) for its nonzero leading coefficient and d for its Y-degree. The monic polynomial

    M(t,Z)=Z^d + sum_(j<d) q_j(t)*a(t)^(d-1-j)*Z^j

satisfies M(t,a(t)Y)=a(t)^(d-1)*Q(t,Y). Over C(t), inversion of the parameter, multiplication by a nonzero scalar and the invertible variable scaling preserve irreducibility, hence separability. Apply the verified ramified analytic producer to M. Then x(s)=s^(-N), y(s)=z(s)/a(s^N) are meromorphic and solve F away from zero. This produces a pole in x directly. This is another classical exact normalization proof, not a new scientific claim; its polynomial coordinate identities remain to be formalized.

Existing `HilbertIrreducibility/MonicScaling.lean` supplies `monicScale`, `monic_monicScale`, and the exact complex evaluation identity `bivEval_monicScale`; the entire file was inspected. `Polynomial.algEquivCMulXAddC` supplies the field-variable scaling equivalence. `Polynomial.reflect` and `eval₂_reflect_mul_pow` can clear reciprocal-parameter powers; `Bivariate.swap` is a polynomial algebra equivalence. No generic irreducibility-under-reversal API was found, so do not assume one. The monic-scaling path may be shorter than constructing a generic linear projection, but the existing complete paper proof does not depend on this implementation choice.

The projection query `plane curve monic generic linear coordinate projective infinity polynomial` returned no applicable producer; all candidate and source-argument statements were inspected, partial=false and errors empty, inventory complete, compiler freshness incomplete. A separate query `rational three fibers four points quadratic harmonic cross ratio` likewise found no applicable classification. A possible stronger one-coordinate classification is deferred until the current component theorem is verified; it is not substituted for the remaining geometric work.

## Fixed-coordinate normalization verification, continued

`AlgebraicMonicScaling.exists_ramified_meromorphic_root` now removes the monicity requirement: a positive-degree bivariate polynomial irreducible over its parameter fraction field has a ramified meromorphic root. The exact scaling composition is verified; irreducibility follows from a field-variable algebra automorphism and multiplication by a unit. Qualitative isolated zeros ensure the denominator is nonzero on a punctured neighborhood. Targeted build passes (3025 jobs, with a replayed unused-simp warning in existing `HilbertIrreducibility/MonicScaling`); final direct `lake env lean GaloisForLFunctions/HTGeometry/AlgebraicMonicScaling.lean` passes without diagnostics. The new leaf is wired once.

The next scratch file `/tmp/cosine_reciprocal.lean` constructs the reciprocal-parameter polynomial by reflecting every coefficient at one common finite polynomial degree, and proves its exact evaluation identity and generic irreducibility via the existing rational-function inversion automorphism. This is the remaining algebraic step toward an actual meromorphic chart with x(s)=s^(-N), not a new generic normalization premise.

`AlgebraicReciprocalParameter` now verifies that construction, with constant-coordinate exclusions retained. Targeted build passes (3211 jobs); final direct audit passes without diagnostics. `AlgebraicInfinityBranch.exists_meromorphic_infinity_chart` combines it with monic scaling: for every irreducible bivariate polynomial with positive degrees in both coordinates, it constructs positive N and a meromorphic f with P(s^(-N),f(s))=0 near the puncture, f not locally constant, and s^(-N) eventually outside every finite set. Constant-coordinate exclusion is derived from irreducibility and the parameter degree. Its targeted build passes (3305 jobs); the final direct audit is in progress after removing an unused simp argument. Both leaves are wired once. This closes the construction of the normalization chart, not the full cosine component theorem.

The generic logarithmic coordinate step is now being checked in `/tmp/cosine_pole_unit.lean`: an analytic unit A and positive m give an analytic α satisfying exp(α)^2-2*A*exp(α)+s^(2m)=0 and exp(α(0))=2*A(0). A local logarithm is taken after dividing by the nonzero base value, so its analytic argument equals 1 at the basepoint regardless of the original unit's argument. The boundary branch proof then uses these logarithmic coordinates in its two-parameter submersion.

Final direct audit of `AlgebraicInfinityBranch.lean` now passes without diagnostics. The normalization premise is discharged by its actual endpoint; generic irreducibility, positive degrees, coordinate nonconstancy and finite exclusions remain explicit in the statement and proof. These are structural hypotheses defining the input curve, not assumptions of RH or of the desired cosine intersections.

## General pole coordinates and conic branch

`CosinePoleUnit` verifies the analytic unit, its normalized local logarithm, and the exact conversion from the quadratic unit identity to a cosine value. Its targeted build passes (2727 jobs). The general two-pole scratch proof also passes: `CosineTwoPoleCorner.exists_corner` constructs the analytic two-parameter conic branch; `conic_of_equation`, `firstLift_exp`, `secondLift_exp` and `cosine_lifts` verify the exact specialization, including the integer periods and both pole orders. The leaf is saved and wired; its targeted build and final direct audit remain pending. These are components of theorem A, not a certificate for A or RH.

The next obligation is the sequence endpoint: arbitrary analytic units with positive pole orders must supply actual cosine-pair points that are eventually nonreal and escape every finite set. Corpus query `sequence scaled nonzero limit finite range eventually avoids` returned 20 candidate and 20 source-argument statements, all inspected; partial=false, errors empty, inventory complete, compiler freshness incomplete. The finite-range stabilization hit does not supply the needed escape statement. A direct qualitative limit argument subtracts a constant candidate from the scaled sequence; its nonzero limit eventually excludes that constant. No norm estimate is needed. Work is in `/tmp/cosine_two_pole_sequence.lean`.

Latest global lint (normalization pass) reports five unrelated unreachable HTGeometry modules: `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`. The earlier two RHTower reachability errors have disappeared. No owned leaf is flagged.

The two-pole sequence endpoint now passes the scratch check and targeted build (3453 jobs). `CosineTwoPoleSequence.exists_nonreal_cosine_pair` takes arbitrary analytic units A,B and positive pole orders m,r; it constructs s_n→0 through nonzero points and actual w_n with the two prescribed cosine coordinates, eventual nonreality, and eventual avoidance of every finite set by both w_n and T(w_n). All logarithmic units and the conic branch are produced internally. The scaled limit is 27(r-im)^2, with imaginary part -54mr. Three final direct audits plus six axiom checks are running sequentially; no full-class Lean claim yet.

The finite-coordinate inverse admits one uniform construction even at ±1: for analytic f, write g=f^2-1. If g is not locally zero, its exact finite-order factorization gives g(s)=s^k*h(s), h(0)≠0. A local logarithm of h gives the analytic square root s^k*exp(log(h(s^2))/2) of g(s^2). If g is locally zero, use the zero root. Then E=f(s^2)+sqrt(g(s^2)) satisfies E^2-2*f(s^2)*E+1=0 and E(0)≠0. Its local logarithm supplies an analytic u with cos(u)=f(s^2). This removes the separate regular/critical inverse cases. It is a classical dependency, not a novel result. The first search returned no hits after a local worker disconnect (partial=true); lexical fallback and direct source inspection found only a zero-free disk square root and a domain theorem requiring an already existing meromorphic square. Neither handles arbitrary vanishing order after ramification directly. Scratch: `/tmp/cosine_ramified_inverse.lean`.

Additional hostile literature check: [Lastra–Sendra–Sendra, Symbolic Treatment of Trigonometric Parametrizations](https://link.springer.com/article/10.1007/s40304-023-00334-w), abstract, introduction and conclusion inspected, classifies real unirational varieties represented by independent circular/hyperbolic parameter blocks. Its independent-parameter hypothesis differs from the coupled conic logarithms here; it does not directly establish the discrete pullback-fiber conclusion. Broad exact-cosine and integer-zero searches returned no applicable replacement theorem. This is not proof of novelty.

The three pole leaves now pass their final direct `lake env lean` checks without diagnostics. Six axiom checks covering monic scaling, reciprocal parameter, normalization and all three pole leaves report only `propext`, `Classical.choice`, `Quot.sound`. Targeted corner build passes (2925 jobs). Latest lint still has the same five unrelated reachability errors; no clean global lint claim is made. The frontier map now records normalization and the general two-pole boundary endpoint separately from the still paper-only full classification.

Index refresh passes (zero changed files, zero removals after automatic search-index refresh). Scoped whitespace checks pass. Eleven completed scratch/search files were removed; active inverse and finite-corner scratch files remain. Anti-theatre and anti-laziness audits were posted: no certified scientific novelty or RH conclusion, classical dependencies distinguished from the full classification target.

`CosineRamifiedInverse.exists_nonconstant_cosine_inverse` now passes in scratch: analytic nonconstant f gives analytic u,H and positive k, with cos(u(s))=f(s^2), u(s)-u(0)=s^k*H(s), H(0)≠0 locally. Square-root ramification, both critical values, and nonconstancy are all discharged. Nonconstancy survives ramification because the power map approaches the puncture through nonzero points and an analytic nonconstant germ has isolated value fibers. The leaf is saved and wired, targeted/final audits pending. The one-finite/one-pole conic construction is being checked in `/tmp/cosine_finite_corner.lean`.

For discrete stabilization, polynomial reconstruction can be omitted entirely. If w_n=P(n)+δ_n with quadratic P and δ_n→0, then Δ³w=Δ³δ→0. Eventual integer values of w imply integer values of Δ³w; the existing closed-discrete stabilization lemma forces Δ³δ=0 eventually. An eventually constant sequence tending to zero is eventually zero. Apply this successively to Δ²δ, Δδ, δ, since all these differences tend to zero. This proves exact eventual δ=0 without a polynomial growth or coefficient bound. Corpus query `integer sequence finite differences polynomial tending zero eventual equality` returned 20 candidate and 20 source-argument statements, all inspected; partial=false, errors empty, inventory complete, compiler freshness incomplete. It supplied polynomial-difference annihilation but no direct endpoint. `DiscreteDilationGerm.eventually_eq_of_closed_discrete` is applicable and will be reused.

The finite-corner contradiction also simplifies: in the exact correction δ=K*(u(s_n)-u0)*(4πn+u(s_n)+u0), the first nonconstant factor is eventually nonzero by its finite-order unit factorization. The last factor is eventually nonzero because multiplying it by 1/n gives the nonzero limit 4π. Thus δ is eventually nonzero directly, contradicting the discrete stabilization conclusion. The separate square-sign alternatives are unnecessary in this implementation. Qualitative decay of n*s_n and exact factorization give δ→0. `CosineRamifiedInverse` targeted build passes (2728 jobs); `CosineFiniteCorner` scratch and targeted build pass (2927 jobs). Final direct audits remain pending. Active scratch work: `/tmp/cosine_quadratic_lattice.lean` and `/tmp/cosine_finite_sequence.lean`.

`CosineQuadraticLattice.eventually_zero_of_quadratic_integer_values` now passes scratch and targeted build (3377 jobs), and is wired. It proves the exact stabilization statement for arbitrary complex quadratic coefficients and a correction tending to zero. Only the existing closed-discrete lemma and repeated eventual-constant arguments are used. The finite-sequence identities and limits are now compiling; `/tmp/cosine_finite_fibers.lean` assembles them into the full finite-coordinate endpoint, including ramification, nonconstant inverse, actual source values, failure of eventual integer containment and escape from finite exceptions. This assembly has not yet been checked.

The finite-sequence scratch proof now passes without diagnostics. It verifies the exact quadratic decomposition, the correction's limit zero, its eventual nonvanishing and the scaled point limit 27. It reuses only `tendsto_pow_mul_exp_neg_scaled` from `PolyExpDecayLimit`, not that module's separate inequality theorem. Saved/wired as `CosineFiniteSequence`; targeted build and final direct audit pending. The meromorphic splitting query returned the applicable `MeromorphicAt.meromorphicOrderAt_nonneg_iff`; all 20 candidate and 20 source-argument statements inspected, partial=false, errors empty, inventory complete, compiler freshness incomplete. Together with `meromorphicOrderAt_eq_int_iff`, this supplies the final exhaustive split of the normalized curve chart into the two boundary cases.

`CosineFiniteSequence` targeted build passes (3534 jobs). The finite-fiber assembly is down to a function-composition elaboration issue; no mathematical gap has appeared, but it is not yet verified. A complete candidate assembly of theorem A is written in `/tmp/cosine_algebraic_components.lean`: normalize to (s^-N,f(s)); split f by its meromorphic order into an analytic extension or a positive pole; apply the appropriate verified boundary construction, reflecting w in the finite case. Projecting finite curve exceptions onto the pole coordinate makes them eventually avoided. If the off-integer pullback locus were finite, eventual avoidance of that finite source set would force eventual integer membership, contradicting the constructed sequence. This assembly has not yet been checked and is not a Lean certificate.

## Lean certificate (2026-10-09)

All three claims of the card (Theorem A, the three-fibre rational-pencil consequence, the
reciprocal non-existence) and the Zariski-density lemma they use are proved unconditionally.

| Card claim | Lean declaration |
|-|-|
| Theorem A: irreducible `D = {P=0}`, neither vertical nor horizontal, any finite `B ⊂ ℂ²` ⇒ `{w ∉ ℤ : Φ(w) ∈ D \ B}` infinite | `CosineAlgebraicComponents.offIntegerFiber_infinite` |
| Normalized chart at infinity `(s^{-N}, f(s))` | `AlgebraicInfinityBranch.exists_meromorphic_infinity_chart` |
| Two-pole boundary branch | `CosineTwoPoleSequence.exists_nonreal_cosine_pair` |
| Finite-coordinate boundary branch (incl. ±1, ramified) | `CosineFiniteFibers.exists_off_integer_cosine_pair` |
| Discrete stabilization | `CosineQuadraticLattice.eventually_zero_of_quadratic_integer_values` |
| Zariski density of `Φ` (fixed `cos u₀`, second coordinate unbounded) | `CosineRationalRepair.eq_zero_of_vanishing_on_cosinePair` |
| Irreducible non-vertical curve meets a non-multiple in finitely many points (Gauss + Bezout) | `CosineRationalRepair.common_zeros_finite` |
| Each irreducible factor of an integral pencil member is vertical or horizontal | `CosineRationalRepair.factor_coordinate` |
| Pencil members are separated products `A(X)B(Y)` | `CosineRationalRepair.separated_of_factors` |
| Sum of two separated products is separated only with proportional first or second factors | `CosineRationalRepair.separated_sum` |
| Three integral fibres ⇒ `R ∈ ℂ(X)` or `R ∈ ℂ(Y)` | `CosineRationalRepair.three_integral_fibers` |
| No nonconstant repair with three integral fibres and `R(Φ(-w))R(Φ(w)) = 1` | `CosineRationalRepair.no_reciprocal_repair` |

Formal reading.  `R = P/Q` with `IsRelPrime P Q`; the λ-fibre hypothesis `FiberIntegral P Q λ`
asks only that points with `Q(Φ w) ≠ 0` and `P(Φ w) = λ Q(Φ w)` be integers (weaker than the
complete-fibre hypothesis, so the theorem is stronger).  The reciprocal identity is required only
where both denominators are nonzero.  `three_integral_fibers` does not need `R` nonconstant.

Audit.
- `lake env lean` passes with no diagnostics on all 13 modules of the chain:
  `HTGeometry/{CosineAlgebraicComponents, CosineRationalRepair, CosineFiniteFibers,
  CosineTwoPoleSequence, AlgebraicInfinityBranch, AlgebraicReciprocalParameter,
  AlgebraicFiniteJetBranch, CosineFiniteSequence, CosineTwoPoleCorner, CosinePoleUnit,
  CosineRamifiedInverse, CosineFiniteCorner, CosineQuadraticLattice}`.
- Axiom audit over every declaration of these modules: 159 declarations, only `propext`,
  `Classical.choice`, `Quot.sound`.
- All 13 modules are wired once into `GaloisForLFunctions/HTGeometry.lean`.  Reused corpus inputs:
  `PolynomialBezoutDenominator.exists_bezout_of_isCoprime_map`,
  `DiscreteDilationGerm.eventually_eq_of_closed_discrete`, `LabeledCosineDescent.source_squareCoordinate`.

## Log (promotion)

- 2026-10-09: Theorem A assembly and rational-repair consequences formalized; promoted to stage 3.
