# Euler-deletion factorization boundaries

## Status

All statements below are unconditional Lean theorems. They do not prove RH and introduce no
axioms. They delimit the source category in which a deletion-signature producer could exist.

## 1. Repeated-generator obstruction

For

`a_P(n)=1-P[P divides n]`,

direct case splitting on `P divides n` gives

`a_P(n)^2=(P-1)+(2-P)a_P(n)`.

Hence `a_2(n)^2=1`, and summing its first `N` square coefficients gives exactly `N`. The bounded
coefficient-prefix hypothesis used by Abel summation is therefore not closed under repetition.
After subtracting the constant square component, only `(2-P)a_P` remains; for `P=2` this is zero.

Lean: `EulerDeletionQuasiShuffleCylinderSquareNoGo.lean`, especially
`blockDeletionCoefficient_sq_eq`, `sum_blockDeletionCoefficient_two_sq`, and
`blockDeletionCoefficient_centered_sq_eq`.

## 2. Literal composite interference

The actual modulus-product source is an interleaving:

`source_(PQ)=source_P+insert_P(source_Q)`.

At a multiple `Pk`, the inserted term is exactly `P^(1-s)` times the `Q` source at `k`. In the
square-summable chamber `Re(s)>1/2`, the real overlap of the two legs is strictly negative for
`P,Q>1`. Consequently

`energy(source_(PQ)) < energy(source_P)+energy(insert_P(source_Q))`.

Thus literal modulus multiplication cannot be replaced by independent or orthogonal replication.
The exact interference is source data that any refinement must retain.

Lean: `EulerDeletionCompositeInterference.lean`, especially
`deletionMellinSource_mul_eq_add_inserted`, `tsum_deletionSource_inserted_pair_re_neg`, and
`deletionMellinSource_composite_energy_strict`.

## 3. Commutative shadow collapse

Let `L : ℂ →L[ℝ] A`, where `A` is a complete commutative normed real algebra. Commutativity combines
the chronological exponentials exactly:

`Development_P,s,L(N) = exp(L(sum_(n<N) a_P(n+1)(n+1)^(-s)))`.

At a zeta zero `rho` with positive real part, the scalar deletion prefix tends to zero. Continuity
of `L` and of the exponential then gives

`DevelopmentLimit_P,rho,L = 1`.

Therefore scalar and commutative developments retain no zero-location datum beyond the already
known level-one closure.

Lean: `EulerDeletionNoncommutativeAbelianShadow.lean`, especially
`eulerDeletionDevelopment_eq_exp_map_prefix` and
`eulerDeletionDevelopmentLimit_eq_one_of_zeta_zero`.

## Consequence for the live conjecture

A surviving construction must be squarefree, noncommutative in a genuinely useful sense, and
quasi-shuffle rather than merely Magnus/Chen: it must retain the diagonal bracket erased by
ordinary commutative exponential development. It must also turn literal composite interference
into a proved associated-graded boundary or correction. Assuming independent replication,
discarding the interference, or analytically admitting the constant channel repeats a closed
failure.

## 4. Exact squarefree factorization grade

For coprime `P,Q`, put

`I_(P,Q)(n)=a_Q(n)-a_P(n)a_Q(n)`.

Direct divisibility arithmetic proves

`I_(P,Q)(n)=P [P divides n] a_Q(n/P)`.

Thus this is exactly the literal inserted `Q` source on the common integer clock, not an abstract
replacement. On one complete `PQ` block, the singleton and interaction grades satisfy

`sum a_Q(a_Pa_Q)=0`,

`sum (a_Pa_Q)^2=PQ(P-1)(Q-1)`,

`sum I_(P,Q)^2=P sum a_Q^2=P^2Q(Q-1)`.

The factor `P` therefore exists as an exact uniform source law, with the interaction retained as an
orthogonal squarefree grade.

Lean: `EulerDeletionFactorizationGraded.lean`, especially
`deletionFactorizationInsertion_eq_cofactor_of_coprime`,
`sum_single_mul_interaction_product_block_eq_zero`, and
`deletionFactorizationInsertion_uniform_replication_scale`.

## 5. Mellin deformation kills static descent

Uniform orthogonality is not preserved by the actual Dirichlet weight. For `alpha>1` and coprime
`P,Q>1`, Lean proves the exact cross-grade pairing

`sum_n a_Q(n)(a_Pa_Q)(n)n^(-alpha)`

`=Z(alpha)(1-P P^(-alpha))(1+Q(Q-2)Q^(-alpha))>0`.

Hence the interaction is not a zero boundary in the weighted convergence chamber. The separate
coefficient-mean descent in `EulerDeletionMeanInterferenceDescent.lean` proves the complementary
no-go: if the Mellin factor is stripped before averaging, interference vanishes and the recovered
factor is `P` for every exponent because

`P^(2-2 sigma) P^(2 sigma) / P=P`.

So neither static option selects the critical exponent: keeping the weight produces nonzero mixing;
removing it erases the exponent. A surviving architecture must construct a genuinely weighted,
zero-specific chronological transgression. Merely quotienting the interaction or recovering the
coefficient mean is closed failure.

Lean: `deletionFactorizationGradeCross_eq_of_coprime`,
`deletionFactorizationGradeCross_pos_of_coprime`, `recovered_interference_zero`, and
`recovered_dilation_factor`.

## 6. Scalar factorization order is flat

For any coefficient stream `x`, cofactor insertion

`(I_P x)(n)=P[P divides n]x(n/P)`

obeys `I_P I_Q=I_(PQ)=I_Q I_P`. Nested scalar cutoffs obey the matching law

`floor(floor(N/P)/Q)=floor(floor(N/Q)/P)=floor(N/(PQ))`.

Therefore a factorization-order anomaly cannot come from the one-indexed insertion action or its
nested cutoff. Any surviving transgression must retain strict multi-index inequalities such as
`Pm<Qn` and a nontrivial conditional grouping; collapsing them to cofactor floors erases the only
remaining order datum.

Lean: `deletionCoefficientInsertion_comp`, `deletionCoefficientInsertion_comm`, and
`deletionNestedCofactorCutoff_comm`. The corpus theorem `floorTransform_comp` gives the parallel
general transform statement.

## 7. Depth-two schedule boundary is not an annihilator

The two strict chronological regions and their common diagonal satisfy the finite polarized
quasi-shuffle identity. Passing to a simultaneous deletion zero with `Re(rho)>1/2` gives

`forward+conjugate(reverse)=-diagonal`.

For the singleton/interaction factorization grades, Section 5 proves that the diagonal is strictly
positive. Thus natural depth-two schedule comparison retains the Mellin defect with a minus sign; it
does not force the defect to vanish. This kills the first strict-order transgression. Any remaining
schedule anomaly must occur at depth at least three and must not reduce to ordinary quasi-shuffle
associativity.

Lean ingredients: `endpoint_mul_star_endpoint_eq_cross_add_reverse_add_bracket`,
`eulerDeletionCrossLimits_quasiShuffle_zero`, and
`deletionFactorizationGradeCross_pos_of_coprime`.

## 8. Additive flatness and multiplicative curvature

For the finite same-clock weighted pairing

`B_alpha,N(x,y)=sum_(n<N)x(n)y(n)n^(-alpha)`,

bilinearity makes the usual four-term additive associator identically zero:

`B(x,y)+B(x+y,z)-B(y,z)-B(x,y+z)=0`.

Thus merely moving to three additive inputs cannot evade the depth-two no-go. A different object
survives when the multiplication of deletion moduli is retained. Define

`K_alpha(P,Q,R)=D_alpha(P,Q)+D_alpha(PQ,R)-D_alpha(Q,R)-D_alpha(P,QR)`,

where `D_alpha` is the Mellin grade-one/grade-two cross term from Section 5. For positive
pairwise-coprime `P,Q,R`, Lean proves

`K_alpha(P,Q,R)`

`=Z(alpha)(Q Q^(-alpha))(1-P P^(-alpha))(Q-1)(1-R^(2-alpha))`.

If `P,Q,R>1` and `alpha>1`, every factor except the last is positive. Consequently `K_alpha<0`
for `1<alpha<2`, `K_alpha=0` exactly when `alpha=2`, and `K_alpha>0` for `alpha>2`. In particular,
if `1/2<sigma<1`, then `K_(2 sigma)<0`.

This is an unconditional signed factorization boundary, not an RH criterion. A hypothetical zeta
zero supplies closed deletion endpoints, but no proved theorem currently forces this curvature to
vanish there. Any continuation must construct that zero-fibre annihilation independently; assuming
equality of the two factorization trees would assume the missing step.

This last warning has a closed algebraic form. Give `Nat × Real` the defect-graded product

`(P,a) star_alpha (Q,b)=(PQ,a+b+D_alpha(P,Q))`.

Its second-coordinate associator is exactly `K_alpha(P,Q,R)`. Consequently this natural central
lift is not associative for pairwise-coprime nontrivial moduli when `1<alpha<2`. Associativity of
ordinary modulus multiplication does not descend through the added defect coordinate. A future
annihilation theorem must construct and justify a zero-fibre observation or quotient; it cannot
cite base associativity.

Lean: `EulerDeletionFactorizationCurvature.lean`, especially
`deletionWeightedPairingPrefix_additive_associator_zero`,
`deletionFactorizationGradeCurvature_eq_of_pairwise_coprime`,
`deletionFactorizationGradeCurvature_eq_zero_iff`, and
`deletionFactorizationGradeCurvature_neg_of_half_lt_sigma_lt_one`,
`deletionFactorizationGradedMul_associator_second`, and
`deletionFactorizationGradedMul_not_associative_of_pairwise_coprime`.
