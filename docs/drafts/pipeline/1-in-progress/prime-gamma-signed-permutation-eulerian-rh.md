# Prime--Gamma signed-permutation Eulerian limit and RH

- **ID:** `prime-gamma-signed-permutation-eulerian-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [SIGNED-COXETER CHAIN]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/BornSectorExchange.lean`,
  `formal/GaloisForLFunctions/RHTower/BornGradedKMSClassification.lean`,
  `formal/GaloisForLFunctions/RHTower/SignedReflectionParity.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailTelescope.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSource.lean`
- **Statement:** `[CONJECTURE]` Functional-equation reflection upgrades finite ordered prime words
  to signed permutations whose completed descent weights are a nonnegative specialization of a
  stable type-B Eulerian polynomial.  A cofinal locally uniform limit of these negative-rooted
  polynomials is the square-coordinate centered Xi function, implying RH.

## Why this detour is different

The state space is the hyperoctahedral Coxeter group, not a zero divisor, graph, moment measure, or
operator spectrum.  Prime labels provide an order through `log p`; the functional equation provides
the sign/reflection bit; the statistic read by the consumer is descent across adjacent ordered
letters.  Real-rootedness comes from stability-preserving Coxeter insertion recurrences.

## Finite consumer

For a signed permutation `sigma` in the type-B Weyl group `B_N`, let `des_B(sigma)` be its type-B
descent number.  The ordinary type-B Eulerian polynomial

```text
B_N(u)=sum_(sigma in B_N) u^des_B(sigma)
```

has only negative real zeros.  More strongly, stable multivariate type-B Eulerian polynomials
refine each descent by its position and sign sector.  Any common-phase nonnegative specialization
of that stable refinement remains real-rooted, and its positive coefficients put its zeros on the
negative real axis.

This multivariate refinement is essential: arbitrary positive weights on signed permutations do
not inherit real-rootedness.

## The closed chain

Let `A` again be the normalized square-coordinate function

```text
XiC(z)/XiC(0)=A(-z^2),
A(u)=sum_(n>=0) a_n u^n,
a_n=thetaCuspRawEvenMoment(n)/((2n)! thetaCuspRawEvenMoment(0)).
```

Seek a triangular family of completed signed-permutation packets `E_N`:

```text
ordered prime labels log p_1 < ... < log p_N
  + functional-equation reflection / graded parity
  -> signed prime words in B_N
  -> nonnegative local weights attached to signed descent positions
  -> stability-preserving specialization E_N(u) of the multivariate type-B Eulerian polynomial
                                                               [OPEN CORE A]
  -> every zero of E_N is negative real                         [KNOWN]
  -> E_N(0)=1 and E_N -> A locally uniformly on compact sets    [OPEN CORE B]
  -> Hurwitz confines every zero of A to the negative real ray
  -> XiC(z)/XiC(0)=A(-z^2) confines every XiC zero to the real axis
  -> RH.
```

Conversely, RH supplies negative-rooted polynomial sections through the paired Xi product, so the
consumer end is exact.  The new science must be the source-derived signed descent specialization,
not a factorization using Xi zeros.

## The raw order-blind Euler model is closed

Raw Euler weights multiply over prime content and are invariant under reordering a fixed set of
letters.  If the reflection sign sector is also weighted independently of descent position, then
after constant normalization every size-`N` packet is just a linearly rescaled universal type-B
Eulerian polynomial

```text
B_N(c_N u).
```

Its first two nonconstant coefficients are

```text
[u] B_N(u)   = 3^N-(N+1),
[u^2]B_N(u)  = 5^N-(N+1)3^N+binom(N+1,2).
```

If `c_N` is chosen so that the linear coefficient tends to `a_1>0`, then

```text
[u^2] B_N(c_N u)
  -> a_1^2 lim_N [u^2]B_N/[u]B_N^2
  = 0,
```

because the ratio is asymptotic to `(5/9)^N`.  But the theta source has

```text
a_2/a_1^2 = 0.46518380969515456525408779214656... > 0.
```

Therefore no order-blind multiplicative Euler weighting, under any scalar activity rescaling, can
converge coefficientwise or locally uniformly to `A`.

## Positive statement from the no-go

Completion must create a genuinely order-sensitive positive cocycle.  The minimal datum is a local
factor

```text
kappa_N(p_i,p_j; sign_i,sign_j)
```

attached when adjacent signed prime letters form a descent.  It must satisfy the insertion
recurrence of the stable multivariate type-B polynomial.  The raw no-go proves that dependence only
on the unordered prime content is insufficient; adjacent prime ratios, the Gamma seam, or the
graded half-shift must survive until after descents are formed.

This gives an exact first test: for two and three prime labels, compute the completed weights of
all signed orders, group them by refined descent set, and test whether the insertion from `B_2` to
`B_3` is realized by one of the known stability-preserving operators.  A failed recurrence leaves
its signed insertion defect as the positive invariant.

## Candidate source mechanism

The corpus already formalizes a completed graded sector swap in the Bost--Connes/KMS picture and
reflection-graded pair signatures.  The proposed bridge is:

```text
KMS integer/half-integer sector exchange
  -> sign change of a reflected prime letter
  -> type-B simple reflection
  -> descent-position variable
  -> stable signed Eulerian insertion operator.
```

The bridge must be proved on finite prime words before any thermodynamic/KMS limit.  Equality of
ungraded partition functions is insufficient because the raw no-go shows that the missing
information is precisely order-sensitive.

## Attacks and positive successors

1. **Order-blindness attack.**  Multiplicative weights constant on signed reorderings reduce to a
   scaled universal Eulerian polynomial and have vanishing normalized quadratic coefficient.
   **Positive successor:** the exact descent-local completion cocycle above.
2. **Arbitrary-weight attack.**  A positive weighted sum of descent monomials need not be stable.
   **Positive successor:** prove that the weights arise by nonnegative specialization of the known
   multivariate stable polynomial or by its stability-preserving insertion operator.
3. **Type-A collapse attack.**  Forgetting reflection loses the sign sector and merely recovers
   ordinary permutations.
   **Positive successor:** identify the functional-equation involution with a type-B simple
   reflection and retain its boundary descent at position zero.
4. **Inverse-descent attack.**  One can solve finite linear systems to fit a desired polynomial by
   weighted permutations.
   **Positive successor:** weights must be local functions of prime/Gamma data and compatible under
   Coxeter insertion; no Xi coefficient may define an individual permutation weight.
5. **Coefficient-only attack.**  Agreement through finitely many descent numbers does not control
   zeros in the limit.
   **Positive successor:** prove compact normality and locally uniform convergence from a common
   insertion recursion and source weight bounds.
6. **Signed-cancellation attack.**  The functional equation naturally carries signs, while the
   stable specialization requires a common nonnegative phase.
   **Positive successor:** realize signs as the signed-permutation state, leaving the numerical
   descent activities nonnegative.  If a negative activity remains, preserve it as a frustration
   cocycle and retire the stable consumer.

## Primary parent results

- M. Visontai and N. Williams, *Stable multivariate W-Eulerian polynomials*,
  <https://arxiv.org/abs/1203.0791>;
- P. Brändén and M. Leander, *Multivariate P-Eulerian polynomials*,
  <https://arxiv.org/abs/1604.04140>, for the poset/linear-extension enlargement.

## Kill conditions

Retire the raw order-blind model by the quadratic-coefficient asymptotic above.  Retire the completed
model if the finite signed weights cannot be expressed through a stability-preserving descent
specialization, if the insertion defect is nonzero under every canonical Gamma/KMS grading, or if
the normalized family lacks a nonzero locally uniform limit equal to `A`.  Preserve the insertion
defect, any stable restricted signed-word class, and any exact completion-induced Coxeter action as
positive results.

## Gates

- [x] type-B stable finite consumer identified
- [x] two-ended signed-permutation-to-RH chain closed
- [x] raw order-blind Euler weighting rigorously excluded by coefficient asymptotics
- [x] positive descent-local completion cocycle isolated
- [x] first finite insertion test stated
- [ ] completed weights of all signed orders on two and three prime labels extracted
- [ ] stability-preserving type-B insertion recurrence proved or defect computed
- [ ] cofinal signed-descent family constructed
- [ ] locally uniform limit identified with `A`
- [ ] RH capstone formalized
