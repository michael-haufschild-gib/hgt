# Cofinite tail-Gram polarization law

- **ID:** `cofinite-tail-gram-polarization-law`
- **Stage:** 3-formalized
- **Type:** GENERAL HT CONSTRAINT LAW / POSITIVE GEOMETRY
- **Scientific status:** `[NOVELTY UNVERIFIED]`

## Statement

Let `c_1,...,c_m : I -> C` be a finite family.  It is linearly independent modulo finitely
supported functions if and only if, after deleting an arbitrary finite set `F` of coordinates,
there is a square packet `i_1,...,i_m in I\F` whose evaluation Gram matrix

```text
G_F(r,s) = sum_(k=1)^m conj(c_r(i_k)) c_s(i_k)              (1)
```

is strictly positive definite.

Equivalently, the tail matroid is the matroid of deletion-robust strict Gram apertures.  No fixed
packet is privileged; strict positivity can be recovered beyond every finite coordinate patch.

If every coefficient has unit modulus, every diagonal entry of `(1)` equals `m`.  With arbitrary
strictly positive row weights `w_k`, the weighted diagonal is `sum_k w_k`, independent of the
orientation label.

## Infinite weighted form

Assume `I` is countable, `w_i>0`, and all sums below converge absolutely.  Put

```text
Gamma_F(r,s) = sum_(i notin F) w_i conj(c_r(i)) c_s(i).      (2)
```

Then tail independence is equivalent to strict positive definiteness of `Gamma_F` for every
finite `F`.  Indeed,

```text
x* Gamma_F x = sum_(i notin F) w_i |sum_r x_r c_r(i)|^2.   (3)
```

The right side is positive for every `x!=0` and every finite deletion exactly when the support of
every nonzero coefficient combination is infinite.

More generally, if the weights are merely nonnegative, the radical is

```text
rad Gamma_(F,w)
  = {x : sum_r x_r c_r(i)=0 for every i notin F with w_i>0}. (3a)
```

Therefore two summable nonnegative weights with the same positive support induce exactly the same
radical.  The positive-weight chamber is an isoradical metric chamber: weights choose lengths and
angles, while their support alone chooses constraints.

For unit-phase prime coefficients and `w_p=p^(-sigma)`, `sigma>1`, every diagonal of `(2)` is

```text
sum_(p notin F) p^(-sigma),                                 (4)
```

the cofinite all-positive prime-zeta carrier.  Off-diagonal entries are cross-Hadamard prime
Dirichlet carriers.

## HT consequence

Once the classical Dirichlet-series Jacobian transfer is applied, differential algebraic
independence of a finite prime-Dirichlet family is equivalent to deletion-robust strict positivity
of the cross-Hadamard Gram family `(2)`.  The operator-tail differential matroid therefore has a
canonical positive realization; positivity is not merely an external decoration.

For phase orientations the all-positive source occurs on every diagonal.  Thus an arbitrarily
high-rank differentially free family has one common quadratic Hadamard norm:

```text
F_u star F_u^sharp = P_+,                                  (5)
```

where `F_u^sharp(s)=conj(F_u(conj(s)))` and `star` denotes coefficientwise multiplication.

## Geometry

The finite family is simultaneously:

1. free in the ordinary differential field precisely when its operator tails are independent;
2. a strict Gram frame beyond every finite coordinate deletion;
3. a family of Hadamard-unit vectors with common diagonal `P_+` in the phase case.

This is the sought polarization of the differential building: subspace rank becomes cofinite Gram
rank, while the all-positive prime source is the common norm-square rather than a chosen vertex.

For a Gibbs/KMS family of weights `w_p(beta)>0`, changing inverse temperature inside the
summability region changes only the metric.  The tail matroid and every cofinite radical remain
fixed.  A constraint transition can occur only at support loss, a non-summable boundary requiring
renormalization, or after adjoining a transverse polarization.

## RH application boundary

For zeta, `(2)` gives a matrix-valued positive lift of the prime-zeta carrier on `Re(s)>1`.  A new
RH route would require a continuation of this matrix kernel for which:

- the common diagonal is linked by Euler plethysm to `zeta`;
- affine functional-equation reflection acts as matrix adjunction;
- strict or semidefinite positivity of the continued reflected kernel is equivalent to the
  absence of off-line divisor mass.

The tail-Gram law supplies the convergence-half-plane positivity automatically.  It does not
prove that such positivity survives analytic continuation.

## Attacks

1. **Frame-theory collision.**  Linear independence is equivalent to positivity of a Gram matrix,
   and cofinite deletion is a standard robustness condition.  The abstract finite theorem may be
   a direct frame-theoretic corollary.
2. **Schur-product collision.**  Positivity of sums of rank-one matrices and stability under
   Hadamard products are classical.  Scientific novelty can only lie in the exact equivalence with
   the operator-tail differential matroid and the common prime-zeta diagonal.
3. **Finite/infinite distinction.**  The formal theorem currently proves the exact cofinite finite
   packet equivalence and the summable weighted equivalence.  The remaining distinction is
   analytic: turning the weighted coefficient kernel into a continued function-valued kernel.
4. **Continuation attack.**  Positivity on `Re(s)>1` is unconditional and may carry no information
   about the continued divisor.  The route becomes significant only if a nontrivial reflection
   compatibility survives continuation.
5. **Novelty gate.**  Audit deletion-robust frames, full-spark frames, phase retrieval, matrix-valued
   Dirichlet series, Hadamard products, and reflection-positive kernels.

## Parent-theory audit

- Alexeev--Cahill--Mixon, *Full Spark Frames* (JFAA 2012), confirms that finite erasure-robust
  evaluation packets and full-spark Gram conditions are established frame theory.
- Adamo--Neeb--Schober, *Reflection positivity and Hankel operators -- the multiplicity free
  case* (arXiv:2105.08522), confirms that reflection-positive Hankel realizations belong to an
  established operator-theoretic parent theory.
- Searches for weighted Gram radicals, matroid basis polynomials, KMS weight deformations, and
  coefficientwise Dirichlet/Hadamard products did not locate the exact combined statement:
  operator-tail differential independence equals every cofinite full-support Gram aperture,
  all full-support summable metrics are isoradical, and every unit-phase family has the same
  all-positive prime-zeta diagonal.

The first two ingredients are therefore `[BRIDGE]`.  The three-way synthesis remains
`[NOVELTY UNVERIFIED]`; absence from this search is not a novelty proof.

## Formal surface

`formal/GaloisForLFunctions/HTGeometry/CofiniteTailGramPolarization.lean` proves:

- `TailCoefficientIndependent.linearIndependent_on_compl`;
- `TailCoefficientIndependent.exists_cofinite_posDef_evaluationGram`;
- `tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram`;
- `cofiniteWeightedGramEnergy_eq_zero_iff_on_positiveSupport`;
- `cofiniteWeightedGramEnergy_zero_iff_same_positiveSupport`;
- `cofiniteWeightedGramEnergy_eq_zero_iff`;
- `cofiniteWeightedGramEnergy_zero_iff_change_weight`;
- `tailCoefficientIndependent_iff_cofiniteWeightedGramStrict`;
- `tailCoefficientIndependent_iff_cofiniteWeightedGramStrict_of_phase`;
- `cofiniteWeightedHadamardEntry_phase_diagonal`;
- `cofiniteEvaluationGram_phase_diagonal`.

## Gates

- [x] exact finite deletion-robust Gram law isolated
- [x] complete paper proof of finite and summable weighted forms
- [x] source-level formal proof of the finite law without hypotheses
- [x] narrow module build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formalize the infinite summable weighted equivalence `(2)`--`(3)`
- [ ] connect to the analytic operator-tail capstone
- [ ] construct and attack a reflection-compatible matrix continuation
- [x] focused primary-literature and parent-theory audit; independent specialist search remains
