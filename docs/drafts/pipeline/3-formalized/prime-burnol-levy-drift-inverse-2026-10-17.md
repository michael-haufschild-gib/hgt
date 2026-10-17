# Positive prime-clock evolution: exact drift loss and inverse admission

Status: FORMALIZED. Verified contribution 14, counted once.
Dependency-closed paper proof, targeted Lean checks, public axiom audit,
signature audit and final significance review completed on 2026-10-17. This card does not assert a classification of
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
   as x decreases to zero. For x>=1, q(x,h)/x is bounded by 3 using
   the uniform bound ||q(x,h)||<=2+x, and tends to zero for every h>0. Therefore
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

## Historical formal checkpoint — before final audit

Targeted single-worker builds passed for:

- `HTGeometry/LevyLaplaceKernel`: uniform kernel and derivative bounds.
- `HTGeometry/LevyLaplaceExponent`: integrability, holomorphy, accretivity.
- `HTGeometry/LevyLaplaceTruncation`: exact split and vanishing small-jump tail.
- `HTGeometry/LevyFiniteJumpMeasure`: actual finite cutoff measures and integral identity.
- `RHTower/PrimeBurnolLevySymbol`: natural data, actual prime evolution, C0 and semigroup laws.
- `RHTower/PrimeBurnolLevyEvolution`: finite-cutoff strong convergence, positivity, literal drift factorization.

Their final build logs are empty. `RHTower/PrimeBurnolPureJumpInjectivity`
also passed with an empty log: exact bounded backward-cutoff cancellation,
strong convergence of contractive tails to identity, pure-jump injectivity,
and reduction of the general kernel to the literal drift shift.
`HTGeometry/BurnolWeightedShiftKernel` also passed: exact a.e. tail-zero
criterion, explicit nonzero initial-window vector, shift injectivity iff zero
shift. `RHTower/PrimeBurnolLevyInverseGraph` passed: exact backward prime graph
closure, initial-window vertical fibre, fibre cosets, single-valuedness iff zero
drift time, and dense evolution range. `RHTower/PrimeBurnolLevyMinimumInverse`
passed: an actual closed densely defined partial linear inverse, exact graph
intersection with the kernel orthogonal complement, Pythagorean decomposition,
minimum norm and unique minimizer. These final build logs are empty.

`RHTower/PrimeBurnolLevyPrimeAction` passed with an empty log: actual-prime
linear independence, a well-defined finite-prime backward action, and closability
exactly when drift time is zero. `HTGeometry/LevyLaplaceLimits` passed with
an empty log: the jump exponent tends to zero at the origin and its ratio to
the real rate tends to zero at infinity. `RHTower/PrimeBurnolLevyAsymptotics`
also passed with an empty log: intrinsic killing/drift limits, exact norm
`exp(-t*killing)`, and an obstruction to bounded recovery whenever the exponent
diverges, including the closed minimum-norm inverse at zero drift.
`RHTower/PrimeBurnolPrimeLevyMeasure` passed with an empty log: the literal
control measure is finite with no zero atom; its exponent has the stated
prime-series formula, and its actual jump measure has infinite mass.
The concrete divergence and unbounded-inverse specialization are written;
their final leaf remains to check.
No umbrella wiring, generated index, final axiom audit or lint for this candidate
yet. These helpers are parts of one candidate, not separately counted results.
Verified ledger remains **13/100**.

## Final verification and significance — 2026-10-17

All fifteen leaves passed targeted `lake --old env lean -j 1 -o ...` checks
with empty final logs. The final concrete-prime example passed too: its
exponent diverges, its forward evolution is injective with norm one, and its
actual backward-prime graph is the graph of a closed unbounded inverse at
every positive time. No full or umbrella build and no heartbeat increase.

A separate /tmp import audit checked all 136 named public definitions and
theorems. Every axiom list contains only `propext`, `Classical.choice` and
`Quot.sound` (or a subset). A second /tmp file printed all 25 principal
signatures and 12 defining objects. The physical Hilbert carrier, actual prime
columns, natural measure hypotheses, graph equality, minimum-norm inverse and
concrete infinite-prime measure were inspected; no admission, RH, positivity
or injectivity premise was smuggled into the data. All fifteen source hashes
matched their checked versions, all objects were fresh, and every leaf occurs
exactly once in its theorem-area umbrella.

`scripts/formal_tools.py index` exited 0. Both `lint` and
`lint --check-generated` exited 1 solely for concurrent foreign unwired module
`GaloisForLFunctions.RHTower.CHMDResolventNodalCrossPositivityAndBalancedRayleighExcess`,
plus 381 existing large-file warnings. No own-module, forbidden-declaration or
generated-index error was reported. Foreign work was preserved.

The last deep novelty search covered an inventory of 61,576 Lean files and
1,084,559 declarations, but returned partial results because its final judging
stage produced malformed JSON; semantic completeness was not measured and
compiler freshness was mixed. Its proposed unrelated jump-set ingredient was
rejected. A subsequent lexical search for pure-jump injectivity returned only
this contribution's own theorem. Direct source searches for pure jumps,
backward-prime graphs, subordinators and drift kernels found no competing
result beyond the previously audited source mechanisms. These are internal
comparison checks, not a proof of external novelty or exhaustive semantic
coverage. Direct kernel-checked Lean remains the evidence.

**Counting decision:** this is one structural result. The bounded inverse of
each cutoff cancels the full pure-jump evolution into a contractive tail that
converges strongly to identity. That mechanism proves injectivity even when
the cutoff inverses have no common bound. Combining it with literal drift
support and actual-prime density admits an entire new infinite-activity
positive evolution/recovery class and resolves its exact graph obstruction.
The explicit prime-harmonic source proves this class is not restricted to
bounded finite-jump generators. The analytic estimates, graph helpers and
minimum-norm construction are not separate contributions.

Limits: no classification of arbitrary positive semigroups from operator data;
no self-adjointness, RH, bounded inverse in the infinite-prime example, or
external publication novelty. The paper's usual equivalence with the standard
Levy integrability parametrization is explanatory; Lean takes the finite
control-measure data displayed above. The frontier map was never written.

### Checked source fingerprints

| Leaf | Lines | Named public declarations | SHA-256 |
|---|---:|---:|---|
| `HTGeometry/LevyLaplaceKernel` | 160 | 14 | `71e89c0f45ad076ecbd03089474852115e358526d1ed9bf1dea4da5ee408241e` |
| `HTGeometry/LevyLaplaceExponent` | 73 | 8 | `0e46e6f5d1e21f4903b663d4d7d68aeb300fdb69cd150b9573272832cae7e875` |
| `HTGeometry/LevyLaplaceTruncation` | 92 | 9 | `789b0bfae2a8e218930e5f6cefa3837888d2e252b82c4934d22cf2915f60c69f` |
| `HTGeometry/LevyFiniteJumpMeasure` | 69 | 7 | `3c84538b218c8a4c1886a851d1be0558dc722d4e7354704c66952d0597a484a9` |
| `HTGeometry/BurnolWeightedShiftKernel` | 76 | 3 | `1b1ad66445350ae618e89ea50ee9ea18e2f6f1950f50b535d09a372dcecf75d1` |
| `HTGeometry/LevyLaplaceLimits` | 74 | 4 | `f3cb04444cd4832a5fba98257bd601eafb5fac04be1f5b7d43e6ce268e1ddd8a` |
| `RHTower/PrimeBurnolLevySymbol` | 83 | 15 | `1c0215262d93713d10ef4fe625bc476740751ee2836e5d53b1742cb575b6d411` |
| `RHTower/PrimeBurnolLevyEvolution` | 115 | 9 | `98e2b6d7979236196e3c581d9090e36e3219d5e859ceabc94e2e8f86e8e7427e` |
| `RHTower/PrimeBurnolPureJumpInjectivity` | 72 | 5 | `b9153e3aef72457a1f743dd5d9e06ca347c9593ef1ca5b1b366cb5ba578be161` |
| `RHTower/PrimeBurnolLevyInverseGraph` | 153 | 14 | `ebe4f1a6657ea7a654093f5734359fe7d029b1aa61821149aa83090334188217` |
| `RHTower/PrimeBurnolLevyMinimumInverse` | 116 | 14 | `a9a01d70ad344885a8fac26281486f1926b49c2c2e9f3bd41f119dbed28bbda1` |
| `RHTower/PrimeBurnolLevyPrimeAction` | 85 | 5 | `132f66589fd93e182674cc0898eeb78ff73af5d5183b67a64e4307281f30e29e` |
| `RHTower/PrimeBurnolLevyAsymptotics` | 131 | 8 | `715130099a806c3166059a4f243239255ba838bebfce27162cfcc9d2bc100d95` |
| `RHTower/PrimeBurnolPrimeLevyMeasure` | 104 | 11 | `4fa3050101b31f55df08f551be6f0cc40d10b74856621ea8b40cd8f275c6317e` |
| `RHTower/PrimeBurnolPrimeLevyExample` | 110 | 10 | `ebe6a19fb41e59215d69627a20196eb51a14c3fcac8381b14768e0fb5e0e8751` |

Owned temporary audit/search/build artifacts cleaned after persistence: 83 files.
