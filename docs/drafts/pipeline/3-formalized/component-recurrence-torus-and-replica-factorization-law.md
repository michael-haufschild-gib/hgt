# Component recurrence tori classify all completed return collisions

- **ID:** `component-recurrence-torus-and-replica-factorization-law`
- **Stage:** 2-fully-proven
- **Type:** DEPENDENCY-CLOSED PAPER PROOF / ORBIT CLOSURE /
  ALL-ORDER RETURN LAW / SPECTRAL FORM FACTOR
- **Date:** 2026-07-30
- **Stage:** 3-formalized
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [ABSTRACT BRIDGE NOT NOVEL ALONE]`
- **Parents:**
  `hypergraph-local-projective-spectral-factorization.md`,
  `local-interaction-replica-collision-extremality.md`

## Setup

Let a finite Hamiltonian factor into \(c\) noninteracting components,
\[
 H=\sum_{r=1}^{c}
 I\otimes\cdots\otimes H_r\otimes\cdots\otimes I
\]
on
\[
 \mathcal H=\bigotimes_{r=1}^{c}\mathbb C^{D_r}.
\]
Write the simple component energies as \(E_{r,a}\),
\(1\le a\le D_r\), and assume:

1. each component spectrum is maximally projective;
2. the component rational gap modules are mutually transverse.

These hypotheses hold generically for every finite local interaction
hypergraph by
`hypergraph-local-projective-spectral-factorization.md`.

Choose reference labels \(a_r^0\), define
\[
 \omega_{r,a}=E_{r,a}-E_{r,a_r^0}\quad(a\ne a_r^0),
\]
and put
\[
 R=\sum_{r=1}^{c}(D_r-1).
\]
The combined list of \(R\) frequencies is rationally independent.

## Theorem A — exact recurrence torus

Let \([U]\) denote a unitary modulo global phase. Then
\[
 \boxed{
 \overline{\{[e^{-itH}]:t\in\mathbb R\}}
 =
 \Phi\!\left(\prod_{r=1}^{c}\mathbb T^{D_r-1}\right),
 }                                                       \tag{1}
\]
where, in the total product energy basis \(x=(x_1,\ldots,x_c)\),
\[
 \Phi(z)_x=\prod_{r=1}^{c}z_{r,x_r},
 \qquad z_{r,a_r^0}=1.                                 \tag{2}
\]
The map \(\Phi\) is an injective continuous group homomorphism. Hence the
orbit closure is canonically isomorphic to
\[
 \boxed{\prod_{r=1}^{c}\mathbb T^{D_r-1}.}             \tag{3}
\]

For every continuous real or complex function \(f\) on the projective
unitary group,
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}
 \int_{-T}^{T}f([e^{-itH}])\,dt
 =
 \int_{\prod_r\mathbb T^{D_r-1}}f(\Phi(z))\,dm(z).
 }                                                       \tag{4}
\]

### Proof

The total energy of \(x\) is
\[
 E_x=\sum_rE_{r,x_r}.
\]
Relative to the total reference label \(x^0=(a_r^0)_r\),
\[
 e^{-it(E_x-E_{x^0})}
 =
 \prod_re^{-it\omega_{r,x_r}}.                         \tag{5}
\]
Thus the projective orbit is the image under \(\Phi\) of the linear torus
flow
\[
 t\longmapsto
 (e^{-it\omega_{r,a}})_{r,\ a\ne a_r^0}.
\]
Rational independence of the combined frequency list makes this flow dense
and Haar-equidistributed on \(\mathbb T^R\) by Kronecker--Weyl.

The map \(\Phi\) is plainly a continuous homomorphism. To prove
injectivity, suppose \(\Phi(z)\) and \(\Phi(w)\) differ by one global phase.
Hold every coordinate except \(x_r\) at its reference value and divide by
the all-reference coordinate. This gives
\(z_{r,x_r}=w_{r,x_r}\) for every \(r,x_r\). Hence \(z=w\).
A continuous injection from compact \(\mathbb T^R\) to the Hausdorff
projective unitary group is a homeomorphism onto its image. This proves
`(1)`--`(3)`, and Kronecker--Weyl gives `(4)`. \(\square\)

## Theorem B — component-histogram collision law

Index total energy eigenstates by
\[
 \Omega=\prod_{r=1}^{c}\{1,\ldots,D_r\}.
\]
Let \(p_x>0\), \(\sum_xp_x=1\), be arbitrary spectral weights and define
\[
 F(t)=\left|\sum_{x\in\Omega}p_xe^{-itE_x}\right|^2.
\]
For \(m\ge1\), draw two independent \(m\)-samples
\[
 X_1,\ldots,X_m,\qquad Y_1,\ldots,Y_m
\]
from \(p\). For component \(r\), let
\[
 N_r(X)(a)=\#\{s:(X_s)_r=a\}.
\]
Then
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}F(t)^m\,dt
 =
 \mathbb P\!\left(N_r(X)=N_r(Y)\text{ for every }r\right).
 }                                                       \tag{6}
\]

### Proof

The finite-spectrum replica expansion says the long-time moment is the
probability that the two replica samples have equal total energy:
\[
 \sum_{s=1}^{m}E_{X_s}=\sum_{s=1}^{m}E_{Y_s}.          \tag{7}
\]
Using the component energy sum, the difference in `(7)` is
\[
 \sum_{r=1}^{c}\sum_{a=1}^{D_r}
 \bigl(N_r(X)(a)-N_r(Y)(a)\bigr)E_{r,a}.               \tag{8}
\]
Each component coefficient vector in `(8)` is balanced because both
histograms have mass \(m\). Mutual transversality makes `(8)` vanish only
if every component summand vanishes. Maximal projective rank inside
component \(r\) then forces
\[
 N_r(X)=N_r(Y).
\]
The converse is immediate from `(8)`. Thus the energy-collision event is
exactly the joint component-histogram event, proving `(6)`. \(\square\)

For one connected component, `(6)` says the complete joint empirical
histograms must agree. This is the universal permutation collision floor.
For multiple components, distinct joint histograms with the same marginal
histogram in every component survive. Those and only those are the
factorization-forced excess collisions.

## Theorem C — exact component product law for the spectral form factor

Put \(D=\prod_rD_r\) and
\[
 X_D(t)=\frac1D|\operatorname{Tr}e^{-itH}|^2.
\]
Define
\[
 a_{d,m}
 =
 \frac1{d^m}
 \sum_{\substack{k\in\mathbb N^d\\|k|=m}}
 {m\choose k}^{2}.                                    \tag{9}
\]
Then for every \(m\ge1\),
\[
 \boxed{
 \lim_{T\to\infty}\frac1{2T}
 \int_{-T}^{T}X_D(t)^m\,dt
 =
 \prod_{r=1}^{c}a_{D_r,m}.
 }                                                       \tag{10}
\]

### Proof

Tensor-sum evolution factorizes:
\[
 e^{-itH}=\bigotimes_re^{-itH_r},
\qquad
 X_D(t)=\prod_r
 \frac1{D_r}|\operatorname{Tr}e^{-itH_r}|^2.           \tag{11}
\]
Theorem A makes the component phase variables independent under completed
time sampling. The connected all-order collision calculation on component
\(r\) gives its \(m\)-th moment \(a_{D_r,m}\). Haar integration of the
product in `(11)` therefore factorizes and gives `(10)`.

Equivalently, take uniform \(p_x=1/D\) in Theorem B. Uniform samples have
independent component coordinates, so the histogram-collision events are
independent over \(r\). Multiplication by \(D^m=\prod_rD_r^m\) turns each
component fidelity floor into \(a_{D_r,m}\). \(\square\)

## Corollary — fixed-component thermodynamic classification

Let the number \(c\) of components be fixed and let every \(D_r\to\infty\).
For every fixed \(m\),
\[
 a_{D_r,m}\longrightarrow m!,
\]
and hence
\[
 \boxed{
 \lim_{\min_rD_r\to\infty}
 \lim_{T\to\infty}
 \frac1{2T}\int_{-T}^{T}X_D(t)^m\,dt
 =
 (m!)^c.
 }                                                       \tag{12}
\]
The completed law of \(X_D\) converges weakly to the product of \(c\)
independent unit-mean exponential random variables.

### Proof

The finite-component moment limit \(a_{d,m}\to m!\) follows by separating
multiplicity vectors with \(m\) distinct occupied indices from the
lower-order repeated-index contribution. The component phase tori are Haar
independent, so their finite-size laws form a product measure. Each
component law converges to \(\operatorname{Exp}(1)\); weak convergence of
finite product measures and continuity of multiplication give the stated
product law. Equation `(12)` follows either from `(10)` or from moments.
\(\square\)

## Exact interaction meaning

Joining two previously disconnected components of dimensions \(A\) and
\(B\) changes the generic recurrence torus from
\[
 \mathbb T^{A-1}\times\mathbb T^{B-1}
\]
to
\[
 \mathbb T^{AB-1}.
\]
The dimension gain is
\[
 (AB-1)-(A-1)-(B-1)=(A-1)(B-1).                       \tag{13}
\]
At every replica order, the same link replaces equality of two marginal
histograms by equality of the full joint histogram. Equations `(6)` and
`(13)` are two forms of the same factorization loss.

The link may be arbitrarily small only in the completed-time statement.
No finite-time discontinuity is asserted.

## Hostile audit

1. **Is the torus law merely classical?** Yes, once rational
   transversality is supplied. It is `[BRIDGE]`, not standalone novelty.
2. **Can \(\Phi\) identify distinct component phase points projectively?**
   No; comparison with the all-reference coordinate isolates every
   component phase.
3. **Can total energy cancellation occur between components?** Not under
   the mutually transverse gap-module hypothesis, which is generic by the
   parent theorem.
4. **Do arbitrary state weights factor?** They need not. Theorem B does not
   assume factorized weights; it gives a joint marginal-histogram event.
   Only the uniform SFF specialization factorizes probabilistically.
5. **Does `(10)` assume random Hamiltonians?** No. Randomness is Haar
   completed-time sampling of one deterministic orbit, supplied exactly by
   Kronecker--Weyl.
6. **Does the product-exponential limit cover a growing number of
   components?** No. The corollary fixes \(c\). A growing-factor
   log-normal limit is a separate theorem and is not claimed here.
7. **Does this prove a first-return time or finite mixing time?** No. It
   classifies orbit closure and completed statistics.

No paper-proof dependency remains. All three theorems and the corollary are
formalized unconditionally; see the Lean progress section below.

## Lean progress `[LEAN-PROVED]`

Theorem B was already formalized in
`formal/GaloisForLFunctions/HTGeometry/ComponentReplicaCollisionLaw.lean`
(`factorizedOn_replica_energy_eq_iff_componentMultiplicity_eq` and
`finiteSpectralSurvivalFidelityMean_factorizedOn_tendsto_componentCollisionMass`, i.e. `(6)`).
This closure adds four modules.

`HTGeometry/TupleHistogramCount.lean` builds the missing combinatorial bridge:

- `card_tupleHistogram_fiber`: exactly `multinomial k` tuples of length `m` realize the
  multiplicity vector `k`.  Mathlib has no such fibre count; the proof splits a tuple into its
  first entry and its tail and lands on the corpus Pascal rule `multinomial_sum_update_pred`;
- `card_componentHistogram_fiber`: over a product alphabet the count of tuples with prescribed
  component histograms is the product of the component multinomials.

`HTGeometry/ComponentSpectralFormFactorProduct.lean` proves Theorem C:

- `sum_multinomial_piAntidiag_eq_sum_tuple` and its pair form convert every multinomial-weighted
  replica sum into a plain tuple sum;
- `histogramCollisionCount X m` is `∑_{|k|=m} multinomial(k)^2` and
  `replicaFormFactorCoefficient X m` is `a_{d,m}` of `(9)`;
- `componentHistogramCollisionCount_eq_prod` is the component factorization of the collision event;
- `fidelityReplicaComponentCollisionMassOn_microcanonical` evaluates the uniform collision mass, and
  `card_pow_mul_componentCollisionMass_eq_prod` together with
  `tendsto_componentFormFactorMoment` is `(10)`:
  `D^m · lim_T avg |Tr e^{-itH}|^{2m}/D^{2m} = ∏_r a_{D_r,m}`.

`HTGeometry/ComponentFormFactorExponentialLimit.lean` proves the corollary:

- `histogramCollisionCount_eq_sum_multinomial` exhibits the count as an average multinomial
  coefficient, bounded above by `m!` and below by `m!` times the number of injective tuples
  (`multinomial_tupleHistogram_of_injective`, `card_injective_filter`);
- `tendsto_replicaFormFactorCoeff`: `a_{d,m} → m!`, by squeezing with
  `(d - m)^m ≤ d.descFactorial m`;
- `tendsto_prod_replicaFormFactorCoeff` is `(12)`: a fixed number of components whose dimensions all
  grow gives `(m!)^c`.

`HTGeometry/ComponentRecurrenceTorus.lean` proves Theorem A in the phase-torus model, where a
diagonal unitary modulo global phase is exactly a phase function normalized at the reference label:

- `phaseEmbed` is `Φ` of `(2)`, `phaseEmbed_add` its homomorphism law, `continuous_phaseEmbed` its
  continuity and `phaseEmbed_injective` the injectivity of `(1)` (the proof compares with the
  all-reference coordinate, exactly as on paper);
- `phaseEmbed_clockPhasePoint` identifies the embedded Kronecker flow with the projective phase of
  the total energy, and `card_componentGap` gives the fibre dimensions `D_r - 1` of `(3)`;
- `closure_range_phaseEmbed_clockPhasePoint` is `(1)`: the orbit closure is exactly `range Φ`;
- `hasHaarTimeAverage_comp_phaseEmbed` is `(4)`, obtained from the corpus unique-ergodicity theorem
  `hasHaarTimeAverage_of_continuous`.

Rational independence of the combined gap list enters exactly where the paper uses it, as the
hypothesis `RationallyIndependentSequence (componentGapFrequency energy a₀)`; component projective
independence enters Theorem C through `ComponentProjectivelyIndependent`.  Both are hypotheses of
the paper theorems, not added assumptions.

`#print axioms` on all capstones: `propext`, `Classical.choice`, `Quot.sound` only.
`lake build GaloisForLFunctions.HTGeometry` is green with the four modules wired in.

## Gates

- [x] exact torus embedding and injectivity
- [x] Kronecker--Weyl orbit closure and Haar law
- [x] arbitrary-weight component collision classification
- [x] exact finite-size uniform SFF product
- [x] fixed-component product-exponential limit
- [x] exact Lean formalization (component-histogram law, torus embedding, SFF
  product and asymptotics all closed)
- [ ] independent specialist review
