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

has only negative real zeros.  More strongly, Visontai--Williams refine a signed word by its
descent-top set, ascent-top set, and number of negative letters.  The top attached to an adjacent
pair is the maximum absolute label, not its position and not the ordered edge.  Their polynomial
`B_N(x,y;q)` is stable for `q>0`, and nonnegative real specialization followed by diagonalization
remains real-rooted.  Positive coefficients then put its zeros on the nonpositive real axis.

This distinction is essential.  Position-indexed Eulerian refinements can fail stability, and
arbitrary positive weights on signed permutations do not inherit real-rootedness.

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
  -> nonnegative top-label activities, or a new proved stable refinement
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

The former proposed minimal datum was a genuinely order-sensitive positive local factor

```text
kappa_N(p_i,p_j; sign_i,sign_j)
```

attached when adjacent signed prime letters form a descent.  The four-letter fiber-curvature theorem
in `../3-formalized/needs-audit/prime-gamma-descent-top-fiber-curvature-obstruction.md` now shows that direct
specialization of the Visontai--Williams polynomial forces every positive-sector `2 x 2`
multiplicative minor of `kappa` to vanish.  Hence `kappa` is rank-one separable on descending pairs.
Generic order-sensitive Gamma curvature cannot survive as a scalar top activity.

The first tests are now two-tiered.  Extract two- and three-label completed weights to identify the
candidate source law, but also extract four-label weights and compare the fiber-colliding words
`(3,1,4,2)` and `(3,2,4,1)`.  Their weight ratio is the first scalar-stability discriminator.  A
nonunit ratio is the signed insertion curvature and rules out direct top specialization even if the
`B_2 -> B_3` recurrence passes.

## Candidate source mechanism

The corpus already formalizes a completed graded sector swap in the Bost--Connes/KMS picture and
reflection-graded pair signatures.  The proposed bridge is:

```text
KMS integer/half-integer sector exchange
  -> sign change of a reflected prime letter                 [NOT YET CONSTRUCTED]
  -> type-B simple reflection                                [NOT YET CONSTRUCTED]
  -> top-signature support or matrix holonomy
  -> proved stable signed Eulerian or determinantal operator.
```

The bridge must be proved on finite prime words before any thermodynamic/KMS limit.  Current corpus
only proves a global exchange of two completed analytic sectors; it does not act on individual
prime letters.  `SignedReflectionParity.lean` further proves that functional-equation sign controls
fixed-point order parity and explicitly fails away from the fixed point.  Equality of ungraded
partition functions is therefore insufficient to manufacture a letterwise Coxeter action.

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
7. **Top-fiber attack.**  The known stable polynomial is indexed by ascent/descent tops, not ordered
   adjacent edges.  The words `3142` and `3241` have identical type-B top signatures but descent
   edge products `kappa(3,1)kappa(4,2)` and `kappa(3,2)kappa(4,1)`.
   **Verdict:** `FALSE` for generic scalar edge cocycles.  **Positive survivor:** four-label
   multiplicative curvature; compatibility forces curvature zero and positive kernels become
   rank-one.  **Stronger replacement conjecture:** completion curvature changes allowed signed-word
   support or enters a matrix-stable pencil before scalarization, rather than weighting edges in a
   fixed top-signature fiber.
8. **Global-to-letter reflection attack.**  Corpus functional-equation reflection is one global
   involution and its signed parity theorem reaches only the fixed point.
   **Verdict:** `FALSE` for the claim that reflection alone canonically signs every prime letter.
   **Positive survivor:** any genuine letter sign must be supplied by a source disintegration
   compatible with the global sector exchange; it cannot be inferred from Xi symmetry.

## Gate-1 reset and current conjecture loop (15 August 2026)

- `[LITERATURE]` Visontai--Williams stability tracks `DT_B`, `AT_B`, and negative-letter count; its
  insertion operator is `(q x + y) + (1+q)xy partial`.  It does not accept arbitrary edge weights.
- `[CORPUS]` The four-letter curvature obstruction and positive rank-one classification are
  `[LEAN-PROVED]` at
  `../3-formalized/needs-audit/prime-gamma-descent-top-fiber-curvature-obstruction.md` and
  `formal/GaloisForLFunctions/HTGeometry/SignedEulerianTopFiberCurvature.lean`.
- `[CORPUS]` `PrimeWordEnsembleBoundaryTomography.lean` recovers support-cardinality aggregates,
  not word order.  `BornSectorExchange.lean` exchanges completed sectors globally.
  `SignedReflectionParity.lean` proves fixed-point-only parity reach.  None constructs a signed
  prime-word action.
- `[FALSIFIED]` Direct generic adjacent-edge specialization inside the known type-B stable cone.
- `[CONJECTURE]` **Support-curvature transmutation:** the completed prime--Gamma four-letter
  curvature selects or transports signed-word histories, and the resulting support class or
  Hermitian pencil has a proved stability-preserving insertion law whose normalized scalar
  specialization converges locally uniformly to `A`.
- `[PROVED FINITE SURVIVOR]` The first-trace Boolean Euler connection already has nonzero
  support-valued square curvature, while completed-face scalar characters kill it.  A rank-two
  Pluecker/Gram pencil retains any four-label curvature `Delta` as the stable coefficient
  `Delta^2 z w`; see
  `../3-formalized/needs-audit/prime-gamma-signed-eulerian-curvature-plucker-lift.md`.
- `[OPEN CORE]` Construct the cofinal source matrix `K_N` from literal all-prime
  Euler--Gamma/Mobius curvature sections and prove that
  `det(I+u K_N K_N^T)` converges locally uniformly to `A(u)`.  First close the trace and squared
  two-minor comparisons with `a_1,a_2`; no Xi coefficient or zero may define an individual source
  column.
- `[FALSIFIED METRIC]` Literal nested first-trace edges in uniform Boolean `L^2` have normalized
  quadratic coefficient at most `13/98`, while theta moment log-convexity forces
  `a_2/a_1^2 >= 1/6`.  No scalar normalization can repair the gap; see
  `../3-formalized/needs-audit/prime-gamma-uniform-boolean-gram-quadratic-no-go.md`.
- `[REFINED OPEN CORE]` Build the Gamma/co-Poisson metric on nonnested two-face curvature sections.
  Any candidate must reduce the Gram inverse-participation ratio below `2/3` and pass the exact
  degree-two theta comparison before an all-degree construction is attempted.

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
- [x] direct scalar descent-local cocycle generically excluded by four-label curvature
- [x] four-letter curvature invariant and rank-one positive survivor paper-proved
- [x] corrected first decisive finite insertion test from rank three to rank four
- [x] literal support-valued source insertion curvature located
- [x] curvature-preserving stable Pluecker/Gram finite consumer constructed
- [x] uniform Boolean Gram metric excluded by exact rational quadratic gap
- [ ] completed weights of all signed orders on two and three prime labels extracted
- [ ] completed weights on the fiber-colliding four-label pair extracted
- [ ] Gamma/co-Poisson metric on two-face curvature sections constructed
- [ ] source curvature sections identified with completed signed-word columns
- [ ] cofinal Gram family constructed from all-prime Euler--Gamma/Mobius source
- [ ] trace and squared-minor coefficient comparisons proved
- [ ] locally uniform limit identified with `A`
- [ ] RH capstone formalized
