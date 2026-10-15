# DR: vacuum regularity of an actual prime-curve source

Status: exact finite-C^k existence, derivative, and norm survivor formalized.
Actual-curve Taylor and truncation control formalized. The complete
smooth-germ obstruction remains paper work. No RH certificate.
DR and the unconditional RH goal remain active.

Previous turn ruled out automatic root gain from a normalized Frobenius
action. This cycle tests a different proposed producer: a holomorphic
function of a finite-energy prime vector, regular at the Euler vacuum.
The critical point is agreement on the actual arithmetic curve, not an
assumed extension on every finitely supported prime packet.

## Exact construction conjecture

Let P be the rational primes, H=ell^2(P,R), and

    v(sigma)_p = p^(-sigma), sigma>1/2.

On sigma>1 the genuine real Euler logarithm is

    L(sigma) = sum_p sum_(r>=1) p^(-r*sigma)/r = log zeta(sigma).

Candidate: there is a smooth germ G at 0 in H such that
G(v(sigma))=L(sigma) for every sufficiently large real sigma. A
holomorphic complex-Hilbert germ would in particular give such a germ.
Exponentiating G/d would supply a candidate marked root source, with
finite-energy ambient regularity that might control Kummer continuation.

The vacuum regularity requirement is explicit. This candidate does not
cover arbitrary functions defined only near nonzero points of the curve,
models with an independent singular first-trace coordinate, or families
with an additional unrestricted s parameter.

## Paper theorem: finite regularity and the first derivative

For every integer k>=1, any C^k germ G:H->R matching L along that real
curve satisfies

    DG(0)[e_p] = 1 for every prime p<=2^k.

Consequently ||DG(0)|| >= sqrt(#{p prime : p<=2^k}). There is no C^infinity
germ matching L, hence no holomorphic Hilbert germ. The obstruction uses
only the actual real Euler curve, with no off-curve interpolation premise.

Proof, with the coefficient separation step explicit:

1. v(sigma) belongs to H for sigma>1/2. For sigma>=1,
   ||v(sigma)||^2 <= 2^(-2*sigma) sum_(n>=2) (2/n)^2.
   Therefore ||v(sigma)||=O(2^(-sigma)) and v(sigma)->0.

2. The C^k Taylor formula at zero writes
   G(x)=sum_(j=0..k) A_j(x,...,x)+o(||x||^k), where each A_j is a
   continuous real j-linear form (including the factorial normalization).
   A_1=DG(0). Along the curve the remainder is o((2^k)^(-sigma)).

3. For sigma>1 the vector series sum_p p^(-sigma)e_p is absolutely
   convergent in H. Bounded multilinearity expands each Taylor term into
   the absolutely convergent ordered-prime series

       sum_(p_1,...,p_j) A_j(e_(p_1),...,e_(p_j))
                             * (p_1*...*p_j)^(-sigma).

   Regroup by the positive integer n=p_1*...*p_j. Absolute convergence
   justifies regrouping; each coefficient is a finite sum. At a prime p,
   only j=1 contributes, with coefficient DG(0)[e_p]. The constant term
   is supported at n=1. The Euler logarithm has prime coefficient 1.

4. If an absolutely convergent Dirichlet series D(sigma)=sum_n b(n)n^-sigma
   is o(M^-sigma), its coefficients at every positive integer n<=M vanish.
   Otherwise take the least nonzero coefficient n0<=M. Multiplying by
   n0^sigma, its tail tends to zero by dominated convergence: fix an
   abscissa sigma0 of absolute convergence and dominate the tail by
   n0^sigma0*|b(n)|*n^-sigma0. Each term with n>n0 tends to zero.
   Thus n0^sigma D(sigma)->b(n0), whereas the little-o hypothesis makes
   that limit zero, including the boundary case n0=M. Contradiction.

5. Apply step 4 to L minus the finite Taylor sum, with M=2^k. This gives
   the claimed prime coordinates. For S={p prime:p<=2^k}, the vector
   u=sum_(p in S)e_p has norm sqrt(|S|), while DG(0)[u]=|S|. The operator
   norm bound follows. A single C^infinity germ has the same DG(0) at
   every order k. Infinitely many primes force this bounded functional
   to have unbounded norm, a contradiction.

The same argument applies to a nonzero real multiple of L, with prime
coefficient that multiple. An analytic vacuum germ representing the
positive Euler d-th root of zeta would be nonzero and equal to 1 at zero;
its local logarithm, multiplied by d, would give the forbidden germ for L.
The known pole/gamma factor must be tracked separately: it is not silently
included in this statement about the zeta Euler germ.

Verdict on the stated smooth-vacuum producer: FALSE on paper. This is not a
no-go for DR, nor for all source-specific Hilbert constructions.

## Positive survivor: every finite smoothness order admits an exact model

For k>=1 set N=2^k and let q be the least prime greater than N. Put
alpha=log(q)/log(2)>k. Choose epsilon in (0,1/4). On (-epsilon,epsilon)
define

    T_k(t) = sum_(p>N) sum_(r>=1) t^(r*log(p)/log(2))/r,  t>0;
    T_k(t) = 0,                                          t<=0.

This is C^k, and all derivatives through order k vanish at zero. Here is
the required uniform derivative argument, not just pointwise vanishing:
choose delta with k<delta<alpha. For a=r*log(p)/log(2), the j-th derivative
of t^a/r has absolute value at most (a+k)^k*t^(a-j)/r for j<=k.
For 0<t<=epsilon this is at most

    t^(delta-j) * (a+k)^k * epsilon^(a-delta)/r.

The double sum of the latter coefficients is finite: epsilon^a=p^(-c*r)
with c=-log(epsilon)/log(2)>2, and the polynomial factors in r and log p
are summable against this decay. Uniform convergence on compact positive
t intervals gives the differentiated series. The displayed bound gives
T_k^(j)(t)=O(t^(delta-j)) for all j<=k. Inductively extending derivatives
by zero across t=0 proves C^k regularity and the vanishing jets.

Now, on a sufficiently small real Hilbert ball, define

    G_k(x) = sum_(p<=N) -log(1-x_p) + T_k(x_2).

This is an actual C^k function. At x=v(sigma), t=x_2=2^-sigma gives
t^(r*log(p)/log(2))=p^(-r*sigma), so G_k(v(sigma))=L(sigma) exactly for
all sufficiently large real sigma. Its derivative at zero has coefficient
1 on p<=N and 0 otherwise. Its norm is exactly sqrt(#{p prime:p<=N}).

Thus the finite-order lower bound is attained. Finite smoothness tests of
any prescribed order can match the actual arithmetic curve exactly; they
cannot be promoted to one smooth/holomorphic vacuum germ. The models G_k
depend on k. This does not construct compatible analytic root sections.

## Scope, parent theories, and current corpus audit

The core ingredients are ordinary Banach-space Taylor theory, absolute
Dirichlet-series uniqueness, unique prime factorization, and Hilbert
duality. Novelty/significance beyond those parent theories has not been
established. External novelty searches are excluded by user instruction.
Do not advertise the argument as a new field or an RH advance.

Current Lean files inspected:

- `RHTower/ProKummerLinearThresholdSelection.lean`: finite linear-capacity
  action is already RH-equivalent; it does not produce a source bound.
- `RHTower/PrimeFirstTraceCompleteNoEscapeUniversalityLaw.lean`: nonlinear
  closed graph obstruction assuming extension on all finite prime packets.
  Its stated hypotheses must not be replaced by actual-curve agreement.
- `RHTower/PrimeLogThetaRealAxisAmbientHilbertObstruction.lean`: a different
  literal-prime reporter obstruction, again with its precise source domain.
- `HTGeometry/FredholmEulerGermRigidity.lean`: scalar Euler-factor rigidity
  for a specified determinant, not this actual-curve smooth-germ theorem.
- `HTGeometry/BohrPrimeLinearInequality.lean`: prime coefficients of bounded
  Dirichlet series are controlled on a vertical strip. This is relevant
  parent machinery, not a proof of a smooth-vacuum producer.
- `HTGeometry/SmallGrowthDirichletCoefficientSeparation.lean` and
  `HTGeometry/DirichletUniqueness.lean`: dominant-term separation machinery.

No exact matching theorem was found in the searches inspected so far;
this is not a claim of exhaustive absence from the corpus or literature.

## Outstanding work

1. Audit the exact smooth-germ obstruction and finite-C^k survivor against
   current Taylor and Dirichlet machinery; keep quantifiers as above.
2. Decide the scientific contribution relative to the parent results.
   New Lean infrastructure alone does not meet the research goal.
3. Finish the actual-curve prime-coefficient obstruction. The exact finite-C^k
   construction, derivative, and norm are formalized below; do not retire
   the candidate before the remaining closure work.
4. Continue at the actual source attachment with the singular first-prime
   coordinate retained. Smooth finite-energy vacuum regularization cannot
   be assumed to supply it. The requested half-strip remains uncertified.

## Formal work completed and exact remaining scope

The companion draft
`route-dr-prime-curve-vacuum-coefficient-work-2026-10-15.lean` now proves
coefficient separation under a decaying scaled limit and under the
little-o condition in step 4. It derives these from Mathlib's actual
`LSeries.tendsto_cpow_mul_atTop` and handles every coefficient n<=M,
including n=M. Its final direct `lake --old env lean` check exited 0.
The scratch axiom audit for the little-o theorem returned only propext,
Classical.choice, and Quot.sound. An initial cast mismatch was corrected
before the successful checks.

At this initial coefficient-only checkpoint, only a dependency was proved;
the complete vacuum-regularity theorem and positive survivor were not
formalized. Production integration of the positive survivor and later
dependencies is recorded below. The coefficient draft remains active.

For the next proof step, the C^k coefficient extraction can avoid a full
multivariable Peano theorem. When k>=2, all primes p<=2^k satisfy p<2^k.
A Taylor polynomial of degree k-1 with O(||x||^k) remainder therefore
suffices. Apply the existing scalar `taylor_mean_remainder_bound` to
t |-> G(t*x), with a uniform bound on the k-th Frechet derivative near 0.
Its coefficients are the diagonal multilinear Taylor forms. Handle k=1,
p=2 directly by Frechet differentiability and its little-o remainder.
This keeps the original sharp finite-order statement intact.

Remaining formal steps at that checkpoint were the actual far-Euler curve,
multilinear expansion, prime-coefficient identification, Hilbert norm, and
finite-C^k model. Current scope is recorded at the end of this card.
Do not retire this candidate before the positive survivor is audited and
formalized, or mistake the completed coefficient dependency for that work.

All five corpus searches completed with partial=false and no reported
errors, with stale coverage and unavailable semantic coverage warnings.
Some current source was inspected directly. Search results are not treated
as fresh compiler verification of unrelated modules.

Anti-theatre / anti-laziness: the inspected source gives a broader all-packet
nonlinear graph obstruction; the current paper argument uses only one
arithmetic curve and retains a precise finite-smoothness survivor. This
distinction is real, but significance beyond the standard parent theories
is not established. No RH rung was gained. No known proof step was rejected
for effort. The outstanding formal work is recorded explicitly instead of
claiming a finished no-go or using it to abandon DR.

## Exact finite-smoothness source now formalized

Production module:
`formal/GaloisForLFunctions/RHTower/PrimeCurveFiniteSmoothModels.lean`,
namespace `RHTower.PrimeCurveModel`, wired into the RHTower umbrella.

`exists_finiteSmoothGerm` proves, without an RH or continuation premise,
that for every natural k there is a function G on real ell^2(primes) and
a positive radius epsilon with G of class C^k on the ball at zero, and

    G((p^-sigma)_p) = log |zeta(sigma)|   for every real sigma>1.

On this real Euler domain zeta is positive, so this is the intended Euler
logarithm. The proof explicitly identifies the prime-power sum with the
prime logarithms and invokes Mathlib's genuine zeta Euler product. The
function is defined globally; smoothness is asserted on the explicit ball.
Thus the formal source identity holds for every sigma>1, including curve
points outside that ball. This strengthening follows from ordinary
absolute convergence and does not assert regularity outside the ball.

The radius is `min(exp(-(2*log(2)+1)),1)`, independent of k. The tail is
exactly the proposed zero extension, represented by `(max(t,0))^a`, not a
different extension on negative inputs. `iteratedDeriv_primeTail_zero`
proves all its scalar jets through order k vanish at zero.

Formal convergence proof: for nonnegative exponent a and integer j,
`a^j <= j!*exp(a)`. At radius exp(-(beta+1)), each derivative term is
bounded by a constant depending on j and beta times exp(-beta*a).
For a=(r+1)*log(p)/log(2), beta=2*log(2), the weight is p^(-2*(r+1)).
It is bounded by p^-2*(1/4)^r. The prime p-series and the geometric series
give absolute summability. This proves local termwise differentiation at
zero as well as away from zero; no continuation estimate is assumed.

The actual prime curve belongs to ell^2 for sigma>1/2, verified directly
by the real p-series. Adding the finite logarithmic head gives the model
on the Hilbert ball. The model depends on k. No compatible analytic root
sections or zero-free half-strip follow from this theorem.

Validation: direct `lake --old env lean` on the production module exited
0 with no output. Scratch axiom audits for `exists_finiteSmoothGerm`,
`iteratedDeriv_primeTail_zero`, and `finiteSmoothModel_eq_log_norm_zeta`
contained only propext, Classical.choice, Quot.sound. Formal lint passed
(exit 0), with repository large-file warnings. No full or umbrella build.
`scripts/formal_tools.py index` also exited 0 and refreshed the generated
API, gap, overview, and search index. All four owned scratch/search files
were removed and their absence checked; no owned process remains live.

At that existence checkpoint, the derivative/norm and actual-curve
obstruction were still outstanding. The derivative/norm are now proved
as recorded below. The sharp regularity classification is not yet complete.

Anti-theatre / anti-laziness: this is a verified source construction, not a
new scientific novelty claim or an RH advance. Its parent mechanisms are
standard smooth series, Euler products, and Hilbert spaces. It closes the
required positive side of the tested vacuum candidate without assuming
arithmetic continuation. The hard Kummer-gluing obstacle remains open.
Next work stays on this exact boundary and the retained singular first
trace; no argument is abandoned because it is difficult.

## Current formal proof mechanism for the obstruction

The explicit finite model removes a redundant Euler-log expansion from
the no-go proof. Given a proposed C^k matching germ G, set F=G-G_k.
Then F vanishes on the actual prime curve for all sufficiently large real
sigma. It remains to prove that this forces DF(0)[e_p]=0 for p<=2^k.
The model derivative is the finite prime coordinate reader; its Riesz
representative is the finite prime indicator vector. Its squared norm is
the number of retained primes. These statements also close the sharp
positive survivor, without a continuation premise.

For k>=2, use the following exact radial Taylor bound. If F is C^k on
the ball of radius r and its kth Frechet derivative has norm at most C
there, then for ||x||<r,

    |F(x)-sum_(j<k) D^j F(0)[x,...,x]/j!|
       <= C*||x||^k/(k-1)!.

Proof: apply scalar Taylor's theorem to t |-> F(t*x), t in [0,1]. Its
jth derivative is D^j F(t*x)[x,...,x], by composition with the continuous
linear map t |-> t*x. The kth derivative is bounded by C||x||^k. The
displayed bound uses the available nonsharp scalar remainder constant;
no endpoint coefficient is lost because every prime <=2^k is strictly
less than 2^k when k>=2. Continuity of the kth derivative provides C on
a smaller ball. The k=1 endpoint p=2 uses the Frechet little-o remainder.

Truncate the prime curve to primes <=2^k. Its remaining Hilbert norm is
O((2^k+1)^(-sigma)): square the norm, factor this exponential decay,
and dominate the residual prime sum by the convergent integer p-series
at sigma=1. Local Lipschitz continuity transfers the vanishing equation
to the truncated curve with the same error order. The finite Taylor
polynomial now expands into a finite sum of exponentials n^(-sigma),
where n is an integer product of retained primes. At a prime p, only
degree one contributes. Coefficient separation forces that coefficient
to vanish. The remaining formal work is these radial Taylor, truncation,
finite multilinear expansion, and prime-product identification steps.
This is a proof refinement of the recorded paper theorem, not a new
scientific conjecture or a claim that the half-strip is certified.
