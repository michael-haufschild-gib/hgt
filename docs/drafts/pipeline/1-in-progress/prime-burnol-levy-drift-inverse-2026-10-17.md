# Positive prime-clock evolution: exact drift loss and inverse admission

Status: IN PROGRESS. Candidate contribution 14; **not counted**.
Paper proof below is complete at the mathematical level. Lean construction and
final significance audit remain. This card does not assert a classification of
all positive C0 semigroups from arbitrary operator data.

## Exact target

Let H be the literal complex Burnol L2 half-line, with
K_h f(u) = u/(u+h) f(u+h), and let k_p be its actual critical-prime
Laplace columns. Take arbitrary d,kappa >= 0 and a finite positive measure eta
on [0,infinity) with eta({0})=0. Put

    q(z,h) = (1+h)/h * (1-exp(-z*h))  (h>0),   q(z,0)=0,
    psi(z) = kappa + d*z + integral q(z,h) d eta(h),   Re z>0.

Equivalently, nu=(1+h)/h eta is an arbitrary positive Levy jump measure with
integral min(1,h) d nu < infinity and no zero atom. Infinite total jump mass
is allowed. Finite eta, zero atom, d and kappa are natural data conditions;
analyticity, physical positivity and prime-core admission are conclusions.

Construct on H the positive C0 contraction semigroup E_t whose actual prime
eigenvalues are exp(-t*psi(log p)). Prove, for every t>=0,

    ker E_t = {f : f=0 almost everywhere on (d*t,infinity)}.

For the finite actual-prime backward graph

    R_t^fin = span_C {(k_p, exp(t*psi(log p))*k_p) : p prime},

prove the exact closed graph relation

    closure R_t^fin = {(E_t v,v) : v in H}.

Its domain is dense, its vertical fibre is exactly the initial-window L2
space above, and each nonempty output fibre is one translate of that space.
Consequently the backward prime action is closable exactly when d*t=0.
For every datum, including positive drift, selecting the solution orthogonal
to the initial-window space gives a closed, densely defined minimum-norm
inverse. No additional source-admission or graph-core hypothesis remains.

The exact norm is ||E_t||=exp(-kappa*t). Drift is intrinsic:
psi(x)/x -> d as x -> infinity. Infinite jump activity is not information
loss: with d=0, even infinite-activity evolution remains injective.

Include the actual-prime infinite-activity datum

    nu = sum_p (1/p) delta_(1/p),
    eta = sum_p 1/(p*(p+1)) delta_(1/p),
    psi(z) = sum_p (1-exp(-z/p))/p.

The eta measure is finite, nu has infinite mass, psi(x)->infinity, and for
every t>0 its backward prime action has a closed unbounded inverse. Thus the
result admits a concrete arithmetic infinite-jump class, beyond bounded
finite-jump generators.

## Internal comparison and attacks

Only local Lean is mathematical evidence. External novelty is not claimed.

- Contributions 7 and 9 classify finite positive shift measures and bounded
  finite-jump generators. Neither admits infinite jump activity.
- Contribution 11 constructs closed accretive generators and their C0
  contractions. It does not classify physical positivity, evolution kernels,
  or backward prime graph closures. An injective resolvent does not imply an
  injective evolution: literal K_h is a counterexample.
- `BurnolHalfLineWeightedShift` gives the actual shift formula and feature
  eigenvalues. `BurnolWeightedShiftSingularSequence` supplies essential
  boundary information, not the pure-jump/drift reconstruction law.
- `PrimeBurnolPositiveMeasureClassification` supplies the finite-measure
  representation of each positive bounded operator; it alone says nothing
  about injectivity of an infinite-activity limit.
- A proposed blanket Hardy-Smirnov classification was not selected. The
  actual Burnol reproducing kernel is cubic, so a Hardy multiplier-domain
  classification cannot be transferred without proving its applicability.
- A generic Levy-subordination existence theorem alone is a BRIDGE and
  would not be counted. The candidate is the complete drift-loss and inverse
  admission law, with actual infinite-prime jump data.
- The proposed coefficient companion Xi determinant was rejected: the
  corpus already has `thetaSourceEntireDet2_eq_XiC_normalized` for an actual
  source operator. Static Gaussian/GNS source replacement was not selected;
  it would still need the native covariance and dynamics identification.

Attack verdict: SURVIVES PRELIMINARY ATTACK for the exact statement above.
The crucial potential counterexample is loss of injectivity under strong
limits of invertible finite-jump operators. The tail-inverse argument below
rules it out for zero drift; mere strong convergence would not suffice.
No RH, zero locations, numerical experiment or fitted covariance is used.

## Dependency-closed paper proof

1. **Kernel admission.** For Re z>=0 and h>0,
   |1-exp(-z*h)| <= min(|z|*h,2). The first bound follows by integrating
   z*exp(-z*s) over 0<=s<=h; the second is the triangle inequality.
   Splitting h<=1 and h>1 gives |q(z,h)|<=2*(1+|z|).
   On Re z>=delta>0, its z derivative is (1+h)*exp(-z*h), bounded
   by 1+1/delta (use delta*h*exp(-delta*h)<=1). Thus finite eta
   dominates both the kernel locally and its derivative. Differentiation
   under the integral proves holomorphy. Re q>=0, so Re psi>=kappa.

2. **Finite-jump exhaustion.** Set epsilon_n=1/(n+1), and
   nu_n=((1+h)/h eta)|_[epsilon_n,infinity). Its mass is at most
   (1+1/epsilon_n)*eta([0,infinity)), hence finite, and it has no zero
   atom. Its jump exponent j_n is the q integral over the same set.
   The omitted q integral tends to zero at each z by dominated convergence
   and eta({0})=0. The same bound gives local uniform convergence. The
   remainder has nonnegative real part and is itself holomorphic.

3. **Actual forward evolution.** The corpus's accretive-symbol construction
   applies to psi, with no admission assumption. It gives E_t, its semigroup
   law, strong continuity, and all complex feature eigenvalues, hence the
   actual-prime ones. The finite approximants are the product of K_(d*t)
   with the finite-jump exponential including killing. They preserve the
   physical positive cone and have norm <=1. Their prime eigenvalues tend
   to those of E_t. Density of the actual prime span and the uniform norm
   bound give strong convergence on all H. The positive cone is closed,
   so E_t preserves it.

4. **Pure jumps are injective.** First set d=0 and write P_t for E_t.
   Let P_(t,n) be the bounded finite-jump exponential from step 2,
   including the same killing. It has the bounded inverse X_(t,n), the
   opposite bounded-generator exponential. All these operators commute,
   by equality on the dense actual-prime span. The product

       P_t X_(t,n) = X_(t,n) P_t

   has symbol exp(-t*(j-j_n)); it equals the accretive evolution of the
   omitted positive jump tail. In particular its norm is <=1. Its prime
   eigenvalues tend to one, so it converges strongly to I. If P_t f=0,
   every X_(t,n)P_t f=0, and the strong limit gives f=0. This explicitly
   repairs the invalid inference 'strong limit of invertibles is injective'.

5. **Drift is the entire kernel.** Feature uniqueness gives
   E_t=P_t K_(d*t)=K_(d*t) P_t. Injectivity of P_t implies
   ker E_t=ker K_(d*t). The shift formula and the change of variable
   s=u+d*t show K_(d*t)f=0 iff f=0 almost everywhere for s>d*t;
   u/(u+d*t) is nonzero for u>0. This proves the exact kernel law.
   If d*t>0, nonzero interval indicators belong to the kernel. Arbitrarily
   many disjoint subinterval indicators are linearly independent there.
   If d*t=0, K_0=I and the kernel is zero.

6. **The entire backward graph is admitted.** The relation
   R={(E_t v,v):v in H} is closed, since it is the equation E_t v=u.
   Each backward prime graph point belongs to R because its forward
   eigenvalue is nonzero. Conversely the continuous map
   v |-> (E_t v,v) takes each prime feature to a nonzero scalar multiple
   of a backward prime graph point. Density of the prime span therefore
   puts every point of R in the backward graph closure. This proves
   equality. Every prime feature is in Ran E_t, so the domain is dense.
   Subtracting two graph points gives the stated output-fibre description.
   The finite prime action is well-defined by the existing linear
   independence of distinct positive-rate features.

7. **Canonical recovery after loss.** Let V=ker E_t, a closed subspace.
   Every v decomposes as v_V+v_perp. Since E_t v_V=0, every nonempty
   output fibre has exactly one element in V-perp. Its graph is the
   intersection of R with H x V-perp, hence closed, and its domain is
   Ran E_t, hence dense. Orthogonality gives
   ||v_perp+w||^2=||v_perp||^2+||w||^2 for w in V, proving unique
   minimum norm. For positive drift this is literal deletion of the
   arbitrary initial interval, not a new imposed source norm.

8. **Intrinsic normalization.** Dominated convergence gives psi(x)->kappa
   as x decreases to zero. For x>=1, q(x,h)/x is bounded by 2 after
   splitting h<=1 and h>1, and tends to zero for every h>0. Therefore
   psi(x)/x->d. The bound Re psi>=kappa gives ||E_t||<=exp(-kappa*t),
   by the bounded-symbol realization. The positive-rate eigenfeatures
   and x down to zero give the reverse inequality. Thus drift and killing
   are intrinsic scalar limits, rather than a choice of presentation.

9. **Actual infinite prime activity.** For prime p, 1/(p*(p+1))<=1/p^2,
   and the prime p-series converges. Hence eta above is finite and has
   no zero atom. Multiplication by (1+h)/h at h=1/p gives exactly 1/p.
   Euler's prime harmonic divergence gives nu([0,infinity))=infinity.
   At positive x the exponent terms are nonnegative and increase to 1/p
   as x tends to infinity. Given M, choose a finite prime set whose
   harmonic sum exceeds 2M, then x large enough that its exponential
   factors are each at least 1/2. This proves psi(x)->infinity without
   interchanging divergent Bochner integrals. With zero drift step 4
   gives injectivity. Backward feature eigenvalues exp(t*psi(x)) are
   unbounded for t>0, so no bounded operator can realize the inverse.

## Formalization plan

1. Kernel bounds, finite control measure and holomorphic exponent; finite
   truncations and scalar limits. Verify recalled library names in /tmp.
2. Actual positive evolution and strong approximation by finite-jump clocks.
3. Bounded inverses of truncations, contractive tails, pure-jump injectivity.
4. Literal weighted-shift kernel and complete backward prime graph/fibres.
5. Closed minimum-norm recovery and actual-prime infinite-activity example.
6. Targeted leaf builds, public declaration/axiom audit, source hashes,
   umbrella wiring, generated index and authoritative lint. Final significance
   review precedes any contribution count.

Use one owned Lean process, normal heartbeat limits, no umbrella build.
Preserve foreign changes. The frontier map remains read-only.
