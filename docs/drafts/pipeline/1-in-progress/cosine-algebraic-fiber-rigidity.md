# Algebraic components forced by discrete cosine fibers

- **ID:** cosine-algebraic-fiber-rigidity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; significant novelty unverified
- **Parent:** labeled-lattice-section-periodicity.md; ../3-formalized/cosine-product-corner-unfolding.md
- **Target:** Classify all rational reflected-cosine repairs, including arbitrary diagonal basepoints.

## Exact conjecture A [OPEN CORE]

Let T(w)=cos(2π sqrt((w+1/12)/27)), interpreted by its entire even series, and Φ(w)=(T(w),T(-w)). For every irreducible affine algebraic curve D in C² which is neither vertical nor horizontal, and every finite subset B of D, the set

    {w in C : Φ(w) in D\B and w not in Z}

is infinite.

Consequence to audit: if R in C(X,Y) is nonconstant and three distinct complete fibers of R∘Φ lie in Z, then R belongs to C(X) or C(Y). If in addition (R∘Φ)(-w)=1/(R∘Φ)(w), no such nonconstant R exists. These statements concern this fixed source and rational repairs; they do not settle C2-P for arbitrary meromorphic maps or the actual Xi section.

The stronger real-line version is not proposed: algebraic projections of cosine/cosh pairs can have real fibers with nonarithmetic locations. Exact discreteness, not merely reality, is essential in the finite-coordinate case.

## Competing mechanisms and hostile audit

The product repair's second and third fibers suggest that each non-coordinate component at infinity generates offending points. A competing counterexample would be a non-coordinate algebraic curve whose entire pullback zero set, after finite exclusions, lies in Z. Test every boundary type, including repeated branches and finite coordinates ±1; a simple-root-only theorem cannot establish A.

Deep corpus query `rational cosine reflected polynomial fiber vertical horizontal component lattice rigidity`: all 20 candidate statements and 20 source arguments inspected, partial=false, errors empty, 68211 files inventoried; compiler freshness incomplete. The suggested cosine half-angle/lattice ingredient set is inapplicable. The separate deep query `analytic germ exponential flat curve discrete lattice second differences rigidity` found existing exponential-polynomial independence and qualitative exponential flatness, not the component theorem. Generic finite differences, algebraic normalization, local logarithms and submersions are classical and are not claimed as discoveries.

[Bhardwaj–McCulloch–Ramachandran–Woo, Integer-valued o-minimal functions](https://arxiv.org/html/2404.10737v1), introduction and Theorems 1.1–1.3 checked: broad integer-value-to-polynomial rigidity is already known under definability and growth hypotheses. Thus the discrete stabilization step below is not a novelty claim. Their estimates are not used. [Bergweiler–Eremenko](https://arxiv.org/abs/0808.3800) concerns real-line fibers and circle images, not the present algebraic-component conclusion. A full audit of the exact conclusion and curve-normalization machinery remains open.

**Preliminary verdict:** SURVIVES PRELIMINARY ATTACK as a research target, not as a novelty certification. First open core is a fully audited boundary-branch construction for arbitrary normalized algebraic curves, followed by the rational-pencil deduction. No new Lean theorem is claimed here.

## Proposed paper proof: exact boundary charts

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

## Rational-pencil deduction to audit

Represent R=P/Q with coprime polynomials. Each irreducible factor of P-λQ meets Q=0 at only finitely many points. Conjecture A therefore forces all these factors to be vertical or horizontal whenever the genuine λ-fiber of R∘Φ lies in Z. Thus each of three pencil members is a separated product A_j(X)B_j(Y).

Three distinct members have a linear relation with all coefficients nonzero. A sum of two decomposable tensors is decomposable only if their first factors or their second factors are proportional. Pairwise coprimality of the pencil members then makes their shared factor constant. It follows that all three members, hence P and Q, depend on one coordinate alone.

For the reciprocal conclusion, prove separately that Φ is Zariski dense. Fix arbitrary cos u0=a. The conic-correction submersion from the product repair supplies the points Q(u0+2πN), at which the second cosine coordinate has infinitely many distinct values: its reciprocal exponential coordinate tends to zero while 2z*y=1+z². A finite set of y-values would contradict this identity by a constant subsequence. Hence a polynomial vanishing on Φ vanishes on every vertical line. The reciprocal identity then becomes R(X)R(Y)=1, forcing a constant.

## Remaining work and positive survivor

- Audit analytic normalization, all ramified coordinate charts, exclusions and quantifiers; close every dependency on paper before Lean.
- Audit the exact general theorem externally, not just the elementary stabilization lemma.
- Formalize the boundary construction and component classification, then the pencil consequence. Keep the full rational class as the target; do not replace it with another single repair example.
- If the conjecture fails, retain a precise classification of boundary types that survive, including an actual exceptional component. Do not retire a class merely because one branch construction fails.

No RH theorem, C2-P theorem or universal rational-repair obstruction is claimed as proved by this card.

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
