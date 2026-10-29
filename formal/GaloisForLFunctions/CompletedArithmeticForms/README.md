# Quantitative theory of completed arithmetic forms

Namespace `GaloisForLFunctions.CompletedArithmeticForms`; umbrella `CompletedArithmeticForms.lean`.

**Question.** Which relations in an explicit arithmetic or theta source give a lower bound for its
complete signed form, and preserve that bound through the compression, accumulation, and limits
needed by its arithmetic conclusion?

A completed form retains the terms that can alter its sign: prime and archimedean contributions,
polar coordinates, boundary terms, and mixed entries. Its positive components are comparison
objects. The programme studies inequalities connecting those components to the original form.

**Motivation.** A positive block can lose its reserve to a Schur complement; accumulation creates
off-diagonal covariance; smoothing can destroy sharp-source recovery; fixed-parameter convergence
can fail along the exhaustion required by a criterion. Exact source identities and positive finite
sections therefore require quantitative transfer theorems.

## Objects and language

| Object | Mathematical data |
|---|---|
| Source | An explicit prime, divisor, theta, or causal distribution with its exact identities |
| Domain | The finite packet, test space, or summability class on which the form is defined |
| Complete form | A signed quadratic or sesquilinear form retaining every source contribution |
| Comparison form | A nonnegative form identified directly from the source |
| Radical | Null directions requiring separate treatment |
| Reserve | A quantitative lower bound in a stated norm or on a stated quotient |
| Completion cost | The remainder, mixed block, or boundary term between source and comparison forms |
| Transfer | A proved identity or inequality under a specified map of source domains |
| Exhaustion | A simultaneous range of rank, conductor, aperture, horizon, or cutoff |
| Endpoint tolerance | Positivity, semiboundedness, finite index, a count error class, or a census allowance |

A **source comparison** bounds the complete form by a controlled quantity on its natural domain.
A **relative estimate** measures a remainder against the reserve it consumes. A **successor reserve**
is the Schur complement permitting enlargement of a positive section. A **completion domain**
specifies which infinite signed combinations are legitimate.

These terms supply no positivity assumptions. A structure containing the missing source inequality
as a field has not proved that inequality.

## Mechanisms

**Arithmetic Gram completion.** Primitive cyclotomic prefixes give a genuine overlap Gram.
A divisor family yields an explicit discrete bridge kernel. Exact radicals and inverse operators
can turn this identity into a norm estimate.

**Successor compensation.** A strict finite section has a native source Schur integral.
A reusable identity must control this integral as rank grows, or control any developing radical.

**Signed completion on a domain.** A difference of positive Grams can represent a complete source.
Its negative channel must be paid by terms present in that source. Divergent channels cannot be
assigned an unrestricted positive finite part.

**Accumulation and covariance.** Summing divisor coefficients before measuring their error creates
a new quadratic form. Its unequal-pair terms and infinite tail belong to the estimate.

**Quantitative transfer.** Compression, interpolation, inversion, and cutoff changes carry norms
and constants. The endpoint determines which losses are permissible.

**Signed dispersion.** A centered correlation functional may admit a useful upper bound without
individual correlation asymptotics. Its window, centering, parity, and normalization remain fixed.

## Foundational theorems in the corpus

1. **Cyclotomic Gram and radical.** For primitive-prefix Grams $G_m$,
   $$
   \sum_{i,j}a_i a_jG_m(k_i,k_j)
   =\sum_{\zeta\ {\rm primitive}\ m}\left|\sum_i a_i\sum_{r<k_i}\zeta^r\right|^2.
   $$
   Vanishing is equivalent to divisibility of the prefix polynomial by $\Phi_m$.
   See [Gram completion](../CriticalArithmeticCorrelationTheory/TheArithmeticCurvatureHasAnExactGramCompletion.lean)
   and [radical classification](../CriticalArithmeticCorrelationTheory/CyclotomicDivisibilityClassifiesTheOverlapGramRadical.lean).

2. **Divisor completion.** For $0\le i,j\le Q$,
   $$
   \sum_{m\mid Q,\ m\ne1}G_m(i,j)=Q\min(i,j)-ij.
   $$
   See [AllDivisorConductorsRecoverTheDiscreteBridge](../CriticalArithmeticCorrelationTheory/AllDivisorConductorsRecoverTheDiscreteBridge.lean).
   This fixes the actual arithmetic comparison kernel, including its cross entries.

3. **Prime packet uniformity.** At fixed modulus, one prime-window horizon controls every finite
   complex residue Gram packet. Affine multiplier and shift can vary arbitrarily with the horizon.
   See [PrimeResidueWindowsControlEveryGramPacket](../CriticalArithmeticCorrelationTheory/PrimeResidueWindowsControlEveryGramPacket.lean)
   and [ActualAffinePrimeWindowsAreUniformInTheirParameters](../CriticalArithmeticCorrelationTheory/ActualAffinePrimeWindowsAreUniformInTheirParameters.lean).

4. **Signed theta sections.** For $s_a(2n)=(-1)^n k_a^{(2n)}(0)$, $s_a(2n+1)=0$, the full
   $H_{a,7}=[s_a(i+j)]_{i,j<7}$ is positive definite for $0<a<1/2$.
   A strict $H_{a,n}$ has nonnegative successor exactly when
   $$
   \int_0^\infty r\sinh(ar)\,
   \mathrm{thetaCuspNativeSuccessorSource}(a,n,r/2)\,dr\ge0.
   $$
   The all-order signed Hankel cone is equivalent to RH.
   See [rank-seven strictness](../RHTower/ThetaCusp/ThetaCuspCenterMixedSeventhRankStrict.lean),
   [native successor](../RHTower/ThetaCusp/ThetaCuspCenterMixedSuccessorSource.lean), and
   [signed-jet completeness](../RHTower/ThetaCusp/ThetaCuspCenterMixedSignedJetCompleteness.lean).

5. **Cumulative divisor covariance.** Euler-deletion finite error energy equals
   $$
   \sum_{j,k\le T}c_jc_k
   \left(\frac1{\max(j,k)}-\frac1{T+1}\right).
   $$
   Full energy includes the literal infinite tail.
   See [EulerDeletionAveragedDivisorCovariance](../RHTower/EulerDeletionAveragedDivisorCovariance.lean).

6. **Light channels and their domain boundary.** The reflected Suzuki current plus its
   negative-light Gram equals its positive-light Gram on every finite source and height packet.
   An unrestricted positive extension of the divergent sharp prime source is impossible.
   See [light completion](../RHTower/Suzuki/SuzukiWallFieldLightConeKernelCompletion.lean) and
   [finite-part obstruction](../RHTower/Suzuki/SuzukiCofinalPositiveFinitePartNoGo.lean).

7. **Endpoint precision.** Count has additive stabilizer
   $\mathcal Q=\{\delta:\sum_{n\le x}\delta(n)=O(\sqrt x\log^2x)\}$.
   Complete all-generator tower positivity instead determines every coefficient from $n=2$.
   See [count precision](../ArithmeticOfSquareRootPrecision/PrecisionClassesAndTheCount.lean) and
   [tower rigidity](../ArithmeticOfSquareRootPrecision/TowerPositivityIsPrecisionExact.lean).

## Arithmetic Green norm and exact Schur cost

For a period $Q\ge1$, coefficients $a_i$ on $1\le i<Q$, and
$P_a(\zeta)=\sum_i a_i\sum_{r<i}\zeta^r$, define the complete divisor-conductor energy
$$
E_Q(a)=\sum_{m\mid Q,\ m\ne1}\sum_{i,j}a_i a_jG_m(i,j).
$$
Its coefficient reserve has an exact positive remainder:
$$
4E_Q(a)=Q\left[\left(\sum_i a_i\right)^2+\sum_i a_i^2\right]
+\sum_{m\mid Q,\ m\ne1}\sum_{\zeta\ {\rm primitive}\ m}|(1+\zeta)P_a(\zeta)|^2.
$$
Thus the completed arithmetic Gram controls total mass and coefficient square mass simultaneously.
Its interior radical is zero. The proof uses the complementary multiplier $1-\zeta$, whose
Parseval energy is exactly the bracketed coefficient norm.
See [CyclotomicCoercivity](CyclotomicCoercivity.lean), especially
`divisorGramEnergy_completion`, `divisorGramEnergy_coercive`, and
`divisorGramEnergy_eq_zero_iff`.

The same form has a local inverse. Extend an interior coupling $b$ by $b_0=b_Q=0$, and put
$$
(Lb)_i=2b_i-b_{i-1}-b_{i+1},\qquad
D_Q(b)=\sum_{0\le i<Q}(b_{i+1}-b_i)^2.
$$
Then $B_Q^{-1}=L/Q$ on the interior, and
$$
E_Q(a)-2\sum_i a_i b_i+\frac{D_Q(b)}Q
=E_Q\left(a-\frac{Lb}Q\right)\ge0.
$$
Consequently
$$
\max_a\left(2\sum_i a_i b_i-E_Q(a)\right)=\frac{D_Q(b)}Q,
$$
with equality exactly at $a_i=(Lb)_i/Q$ on every interior coordinate.
The two boundary differences belong to the cost. This gives an attained, exact payment for a
mixed coupling in the actual completed arithmetic Gram.
See [DirichletSchurCost](DirichletSchurCost.lean), especially
`bridgePotential_inverse`, `bridgeSchur_completion`, and `bridgeSchurCost_isGreatest`.

Application to a completed Weil block requires identification of its coupling in these coordinates
and an arithmetic bound for this variation energy. The Green inverse alone supplies neither.

## Accumulation, dual variation, and a joint truncation bound

For arbitrary real increments $c_j$, let
$$
C_T(c)=\sum_{1\le n\le T}\frac{(\sum_{j\le n}c_j)^2}{n(n+1)}.
$$
The exact coordinate change $a_j=c_j/j$, $Q=T+1$, gives
$$
E_{T+1}(a)=(T+1)C_T(c),\qquad
4C_T(c)=\left(\sum_{j\le T}\frac{c_j}{j}\right)^2+
\sum_{j\le T}\frac{c_j^2}{j^2}+\frac{R_{T+1}(a)}{T+1}.
$$
Thus accumulation has an explicit coercive norm and a positive cyclotomic remainder.
Its mixed-coupling payment is also local:
$$
2\sum_{j\le T}c_jb_j-C_T(c)\le D_{T+1}(w),\qquad
w_j=jb_j\ (1\le j\le T),\quad w_0=w_{T+1}=0.
$$
Both conductor factors cancel exactly. The cost concerns variation of the weighted coupling,
not its absolute coordinate size.

For the actual Euler-deletion increments at $1\le X<M$, write $F_{X,M}$ for the full
error energy. Its literal coordinate tail obeys the simultaneous estimate
$$
0\le F_{X,M}-C_T(c)\le\frac{(M+1)^2}{T+1}.
$$
This follows from the source bound $|1-\mathrm{modular}(X,M,n)|\le M+1$ and the
telescoping carrier tail. It specifies a horizon large enough for any prescribed truncation
allowance, including when the outer cutoff grows. The estimate does not bound the accumulated
source energy at the inner-cutoff strength required by the Euler-deletion criterion.
See [DivisorCovariance](DivisorCovariance.lean), particularly `cumulativeEnergy_completion`,
`cumulativeEnergy_schur_bound`, and `fullErrorEnergy_truncation_bounds`.

## Place in the research

| Programme | Connection |
|---|---|
| ArithmeticCastelnuovoSeveri, ArithmeticOrientationGeometry | Complete Weil geometry, orientation, and index |
| CriticalArithmeticCorrelationTheory | Arithmetic Grams, radicals, residue averaging |
| TransMetzlerWeilPositivity | Complete positive overlap range and profile-dependent exhaustion |
| ArithmeticIndexDescent | Joint Gamma, prime-power, polar, coarse, and detail reserves |
| EffectiveArithmeticHodgeTheory, HeckeKreinToeplitz | Height localization and orbit-kernel classification |
| ConjugateDiagonalGeometry | Positive depth metric and moving theta reconstruction |
| ArithmeticOfSquareRootPrecision | Error classes for counting and exact-source positivity |
| TransThresholdPairCorrelation | Signed coalescent functional and census thresholds |
| ThetaCusp, Suzuki, CCM, Li clock modules | Actual analytic and causal source forms |

The height Hasse theorem and orbit-kernel converse Krein–Langer theorem are established inputs.
A source-side upper index bound is a different theorem. Sharing an RH endpoint does not establish
a norm-preserving transfer between programmes.

## Research questions

1. **Signed theta successors.** Can native compensation propagate rank-seven strictness to arbitrary
   rank? The first explicit residual is the order-seven successor integral. Degenerating reserves
   require quantitative bounds or controlled radicals.

2. **Macroscopic overlap.** Can the actual completed Weil operator at a fixed nondegenerate ratio
   such as $3/2$ be compared to the cyclotomic Gram with cross-annulus and Schur costs paid?
   Can this comparison follow a profile-compatible exhaustive schedule?

3. **Census dispersion.** Can the actual bandwidth-$4/3$ coalescent surplus satisfy
   $(1/18+o(1))N$ in the receiver's windows, including model, cutoff, and collar errors?

4. **Euler deletion.** Which arithmetic relations control actual cumulative covariance and its
   infinite tail with subpower growth at the inner cutoff?

5. **Restricted completion.** Can the complete Suzuki rectangular Ward defect be bounded below on
   its natural domain? Can the actual CCM first-clock source have an eventual constant lower bound?

6. **Theta-clock history.** Can the source budget exclude every guarded zero? The guarded-zero set
   is unconditionally finite, so an eventual condition on that set is insufficient.

7. **Depth and index.** Can arithmetic readings give a sufficiently small Hecke-defect upper bound
   or an upper bound for the complete index? Height certificates detect index without bounding it.

8. **Strip precision.** Can actual normalized Chebyshev energy satisfy the $5/3+\varepsilon$ or
   $3/2+\varepsilon$ exponent bound? Can both detector Gram contributions enter the exact
   five-sixths feasible region?

9. **Transfer calculus.** Which concrete source maps preserve reserves, radicals, domains, and
   endpoint tolerances under simultaneous limits?

These include RH-equivalent targets. Fixed-rank or fixed-parameter theorems contribute without
settling the full questions.

## Tools to develop

- Source residual estimates in the arithmetic Green norm; inverse and coercivity laws for partial
  conductor families and irregular arithmetic packets, including their radicals and boundaries.
- Native successor estimates with rank-dependent reserves and controlled degeneracy.
- Completion theorems combining divergent signed channels on the correct domain.
- Arithmetic covariance estimates after accumulation, with exact tail control.
- Comparison inequalities tracking conductor, rank, aperture, profile, horizon, and cutoff together.
- Signed dispersion estimates for the actual centered census functional.
- Precision-preserving source bridges with all analytic inputs discharged.

## Traps

| Temptation | Mathematical obstruction |
|---|---|
| Spend the same reserve in several blocks | Combined Schur cost can exceed it |
| Ignore a comparison radical | A remainder can act on its null directions |
| Bound absolute successor rows uniformly | Actual fixed-overlap fibers grow logarithmically |
| Infer all-order positivity from finite theta sections | The complete signed hierarchy is RH-equivalent |
| Insert an arbitrary positive mixer | Faithful phase-natural mixing can be rigid or equivalent to the desired sign |
| Extend divergent positive masses to all sequences | No positive extension exists on that domain |
| Discard cross terms after coefficient estimates | Cumulative covariance measures unequal pairs |
| Use an eventual guarded-zero condition | The guarded-zero set is unconditionally finite |
| Exchange fixed and exhausting quantifiers | A growing schedule needs a joint horizon |
| Demand exact rigidity from a count theorem | Count permits the nontrivial class $\mathcal Q$ |

## Success and contribution criteria

A contribution proves an unconditional new source estimate, exact decomposition, sharp boundary,
classification, or transfer theorem. It specifies domain, normalization, radical, parameter range,
and arithmetic consequence. Source identifications and analytic inputs are discharged in Lean;
an unproved estimate cannot be hidden in a structure or imported hypothesis.

A comparison controls its complete remainder in the norm it uses. A limit retains relevant boundary
and cross terms. A negative result identifies its exact class and extracts a nontrivial positive
survivor. A source-independent lemma contributes when it supports a proved actual-source application.

Full success requires answers to the research questions and tools at their stated endpoint strengths.
A collection of criteria alone does not supply the missing inequalities.
