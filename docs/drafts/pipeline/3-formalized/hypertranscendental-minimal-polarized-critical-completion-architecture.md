# Five nonconservative forgetful functors force the minimal HT completion architecture

- **ID:** `hypertranscendental-minimal-polarized-critical-completion-architecture`
- **Stage:** 3-formalized
- **Type:** GENERAL HT MINIMALITY THEOREM (paper + Lean 4)
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [NOVELTY PROVISIONAL PASS] [SIGNIFICANCE PASS] [NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/MinimalHTCompletionArchitecture.lean`
- **Parents:**
  `../../3-formalized/hypertranscendental-algebraic-bulk-completion-boundary.md`,
  `../../3-formalized/hypertranscendental-two-scale-factorial-wall.md`,
  `../../3-formalized/hypertranscendental-controlled-cohomology-and-bornological-shape.md`
- **Statement:** On an explicit test class of one-generator HT sources, prime-orientation
  realizations, Möbius chart changes, and two-scale transport profiles, five natural forgetful
  theories are nonconservative.  Therefore any theory conservative on this class must retain an
  external source groupoid, signed Hermitian polarization, a critical Gevrey product bornology,
  and the full controlled nonabelian transport germ.

## 1. Meaning of conservative

The theorem does not assume that a complete HT classification already exists.  A proposed
invariant is called **conservative for a stated predicate** when equality of the invariant forces
equality of that predicate on the test class.  Each part below names one predicate and supplies an
exact pair or family on which a natural forgetful invariant is equal while the predicate differs.

This separates necessity from sufficiency.  The theorem proves that the displayed structures
cannot be forgotten.  It does not yet prove that retaining all of them is complete.

## 2. Algebraic forgetfulness is nonconservative

Let `x,y` be any one-generator HT elements over the same differential base `F`.  For every finite
`L`, their marked jet fields are canonically equivalent:

```text
F(x,Dx,...,D^(L-1)x) ~= F(y,Dy,...,D^(L-1)y),
D^i x |-> D^i y.                                               (1)
```

Consequently every invariant factoring through a fixed finite marked differential-algebraic stage
is constant on all such sources.  It cannot reconstruct a source functional equation, analytic
domain, continuation law, or polarization unless that datum is supplied externally.

### Positive consequence A

The algebraic body is the universal free differential-rational field

```text
U_F=F(X_0,X_1,...),                 D X_i=X_(i+1).              (2)
```

The minimal source-sensitive input is not another algebraic invariant of the HT generator.  It is
an independently given source constraint groupoid acting on `(2)`.

## 3. Unpolarized analytic completion is nonconservative

The universal prime-orientation family supplies finite chambers `J`.  The established project
theorems give simultaneously:

1. every chamber generates the same embedded differential field;
2. all orientation carriers generate the same compact-open completed ring after the common
   rational Cauchy atoms are adjoined;
3. the relative Hermitian response form of chambers `J,L` has exact negative inertia `#(J\L)` and
   exact positive inertia `#(L\J)`.

Thus field plus ordinary analytic completion is identical while the Krein orientation varies
through every finite relative signature.

### Positive consequence B

A conservative source realization must retain a signed Hermitian polarization, not merely norms,
absolute sizes, or an unpolarized completed ring.  Positivity is the distinguished
zero-negative-index chamber of this polarization.

## 4. Noncritical Gevrey admissibility is nonconservative

For the tangent Möbius chart

```text
M_a(z)=z/(1-az),
```

the `k`th derivative normalized by `(k!)^sigma` has norm

```text
G_(sigma,k)(a)=(k!)^(1-sigma)|a|^(k-1).                        (3)
```

Its consecutive ratio is `(k+1)^(1-sigma)|a|`.  Hence:

```text
sigma<1:  every a!=0 has an unbounded profile;
sigma=1:  boundedness has a proper wall |a|=1 and square summability a wall |a|<1;
sigma>1:  every finite a has a bounded, square-summable profile.                  (4)
```

Subcritical admissibility collapses the local chart group to the identity.  Supercritical
admissibility identifies every finite Möbius scale as tame and erases the finite wall.  Only the
critical order retains both nontrivial comparison morphisms and a proper boundary.

### Positive consequence C

Any completion category intended to detect analytic chart degeneration must use Gevrey order one,
up to an exponential rescaling that changes the wall radius but not the critical exponent.

## 5. A single cofinal direction is nonconservative

On the product of source depth and observable order, define

```text
h(n,k)=max(k-n,0).                                               (5)
```

Every fixed order `k` eventually has value zero, and the order-cofinal diagonal has `h(n,n)=0`.
Nevertheless the full product profile is unbounded.  Therefore ordinary cofinality in the index
order does not preserve bounded flatability.

For an arbitrary profile `p:I->X` into a pseudometric transport space, the exact positive
criterion is metric-bornological cofinality:

```text
there is C such that every p(i) lies within C of some p(phi(j)).                  (6)
```

Under `(6)`, the full profile is bounded if and only if the sampled profile is bounded.  This
holds without commutativity or coordinates.

### Positive consequence D

The completion must live over the full source-depth by observable-order bornology and may localize
only at comparisons cofinal in the realized transport metric.  One ray, diagonal, or row-by-row
limit is insufficient.

## 6. Every finite rate spectrum is nonconservative

For any nonempty finite family of positive rates `r_1,...,r_m` tending to infinity, put

```text
q(n)=min_i r_i(n),                   h(n)=sqrt(q(n)).            (7)
```

Then `h` is unbounded but `h(n)/r_i(n)->0` for every `i`.  Hence every prescribed finite family of
Lyapunov, Cartan, polynomial, logarithmic, or other normalized rates can vanish on a nontrivial
bounded-primitive obstruction class.

### Positive consequence E

The invariant must retain the full controlled growth germ, or an equivalent conservative object,
rather than any finite spectrum of exponents.

## 7. Minimal architecture theorem

### Theorem

Any invariant conservative for all five predicates above on the stated test class must retain at
least the following independent data:

```text
(i)   an external source constraint groupoid acting on the free HT bulk;
(ii)  signed Hermitian/Krein polarization;
(iii) critical Gevrey order-one bornology on the full source x observable scale cone;
(iv)  the complete controlled nonabelian transport germ, localized only at
      metric-bornologically cofinal comparisons.                              (8)
```

**Proof.**  If `(i)` is forgotten, equation `(1)` identifies all finite algebraic source data.  If
`(ii)` is forgotten, the prime-orientation family has equal field and completion but different
exact inertia.  If the Gevrey exponent in `(iii)` is below or above one, `(4)` respectively
destroys every nonidentity chart or erases every finite wall.  If the product bornology in `(iii)`
is replaced by one cofinal direction, `(5)` loses an unbounded profile.  If `(iv)` is replaced by
finitely many normalized rates, `(7)` loses a nonzero growth class.  Thus every listed datum is
necessary. `QED`

No claim of logical independence in a formal axiomatic theory is needed: the witnesses show
independence as information channels on the concrete test class.

## 8. First positive converse on two model strata

Necessity is not the only result.  Two independent components are already complete on exact model
families.

1. **Analytic chart stratum.**  The critical Möbius profile is

   ```text
   Jet_crit(a)(k)=a^k.
   ```

   Its `k=1` coordinate is `a`, so `Jet_crit` is injective.  This is Lean-formalized as
   `mobiusCriticalJetProfile_injective`.

2. **Polarization stratum.**  The labeled Krein--Hamming geometry separates finite prime
   orientation chambers: its distance is zero exactly when the chambers are equal, and its two
   directed inertia counts recover the signed symmetric difference.

Thus critical completion is faithful on the Möbius chart family and polarization is faithful on
the prime-orientation family.  What remains open is descent: proving that these complete local
coordinates, the external source action, and controlled transport glue conservatively on one
nonabelian source category.

## 9. What the theorem changes

The candidate unified object is no longer an unspecified topology, a clock, a scalar capacity, or
a Tannakian slogan.  Its minimum possible architecture is fixed by theorem:

> a polarized, critically Gevrey, multifiltered controlled realization of an external constraint
> groupoid on the universal free HT field.

This is a lower-bound classification of viable theories.  Any proposed universal HT object
omitting one component is already falsified by an explicit witness.

The open medal-scale statement is the converse:

**[CONJECTURE: MINIMAL-ARCHITECTURE COMPLETENESS.]**  The derived comparison stack built from `(8)`
is conservative for every persistent source-natural reconstruction obstruction.  Continuation,
monodromy, spectral incompleteness, positivity failure, and noncanonical boundary conditions are
derived invariants of that one stack.

A counterexample remained significant because it could force additional independent HT structure.
The obstruction-chain audit has now done so.  The exact successor theorem
`source-producer-integral-realization-minimality.md` proves that a distinguished source-effective
section and an integral/ramified realization cannot be recovered from the four channels in `(8)`.
The current unconditional lower bound is therefore six channels, not four.  The theorem on this
card remains the proved first layer rather than being silently restated.

## 10. External novelty gate

The parent theories are substantial and must not be renamed as discoveries:

- free differential polynomial and rational fields;
- differential-algebraic jet/prolongation spaces;
- parameterized differential Galois torsors and constrained cohomology;
- difference Riemann--Hilbert and Tannakian comparison torsors;
- weighted composition operators and weighted Hardy spaces;
- Gevrey classes and factorially weighted jets;
- Krein--Langer negative-square theory;
- bornological coarse geometry and controlled cohomology.

Primary parent checks included:

- Rosen, *Prolongations in differential algebra*, https://arxiv.org/abs/math/0510235;
- Chatzidakis--Harrison-Trainor--Moosa, *Differential-algebraic jet spaces preserve internality to
  the constants*, https://arxiv.org/abs/1311.3546;
- León Sánchez--Meretzky, *Parameterized D-torsors in differential Galois theory*,
  https://arxiv.org/abs/2603.03658;
- Adamczewski--Dreyfus--Hardouin, *Hypertranscendence and linear difference equations*,
  https://arxiv.org/abs/1910.01874;
- Lechner--Li--Queffélec--Rodríguez-Piazza, *Approximation numbers of weighted composition
  operators*, https://arxiv.org/abs/1612.01177;
- Bunke--Engel, *Coarse cohomology theories*, https://arxiv.org/abs/1711.08599;
- *Norm-controlled cohomology of transformation groups*, https://arxiv.org/abs/2007.02649.

Targeted searches found no paper proving the five-way nonconservativity theorem or deriving the
minimal architecture `(8)` for hypertranscendental analytic functions.  This is a provisional
literature pass, not a priority proof.

The scientific delta is not the conjunction of fashionable nouns.  It is the explicit minimality
proof: each deletion is killed by a different exact witness, three of them source-realized and the
remaining two universal controlled-geometry counterexamples.

## 11. Significance and anti-theatre gate

- `[NOVELTY — PROVISIONAL PASS]` No exact external theorem or framework matching `(8)` was found.
- `[SIGNIFICANCE — PASS]` The theorem rules out broad classes of possible HT field theories and
  leaves a sharply defined minimum rather than an unconstrained search space.
- `[ANTI-THEATRE — PASS]` The proof distinguishes classical parent ingredients from the new
  minimality package and does not promote the open converse.
- `[PAPER VERDICT]` This theorem warrants a foundational paper together with the Gamma analytic
  source instance and the exact orientation witness, subject to specialist literature review.
- `[MEDAL-SCALE VERDICT]` The lower bound is not medal-scale by itself.  Proving
  source-effectivity reconstruction for the now-forced six-channel architecture is the medal-scale
  objective.
- `[RH BOUNDARY]` No RH statement occurs.  A completed-zeta realization would be only a downstream
  test of the general correspondence.

## 12. Formal certificate

New Lean declarations:

- `hypertranscendentalFiniteJetEquiv`;
- `hypertranscendentalFiniteJetEquiv_generator`;
- `IsUniformlyBoundedAround`;
- `IsMetricBornologicallyCofinal`;
- `uniformlyBoundedAround_of_metricBornologicallyCofinal`;
- `uniformlyBoundedAround_iff_subsample_of_metricBornologicallyCofinal`;
- `movingBoundaryProfile_fixedOrder_eventually_zero`;
- `movingBoundaryProfile_diagonal_bounded`;
- `movingBoundaryProfile_not_uniformlyBounded`;
- `diagonal_not_bornologicallyCofinal_for_movingBoundary`;
- `iteratedDeriv_mobiusTangentGerm_zero`;
- `normalizedIteratedDeriv_mobiusTangentGerm_zero`;
- `mobiusCriticalJetProfile_injective`;
- `gevreyTwoNorm_mobiusTangentGerm_zero`;
- `gevreyTwoNorm_mobiusTangentGerm_zero_le_exp`;
- `mobiusGevreyProfile_apply`;
- `mobiusGevreyProfile_uniformlyBounded_iff_eq_zero_of_lt_one`;
- `mobiusGevreyProfile_critical_uniformlyBounded_iff`;
- `mobiusGevreyProfile_critical_sq_summable_iff`;
- `mobiusGevreyProfile_uniformlyBounded_of_one_lt`;
- `summable_sq_mobiusGevreyProfile_of_one_lt`;
- `continuousMobiusGevreyTrichotomy`;
- `tendsto_finiteRateMinimum_atTop`;
- `tendsto_finiteRateInvisibleProfile_atTop`;
- `tendsto_finiteRateInvisibleProfile_div_zero`;
- `finiteRateInvisibleProfile_not_uniformlyBounded`;
- `finiteRateSpectrumLowerBound`;
- `minimalHTCompletionArchitecture`;
- `sourceSectionDivisorBlindness`;
- `integralRealificationBlindness`;
- `sourceProducerIntegralLowerBound`;
- `integralOrbitDivisor_has_nsmul_root_iff`.

Existing Lean declarations used for the polarization witness include:

- `universalFacetOrbitPrimeOrientedSource_differentialAdjoin_eq`;
- `primeOrientationCompletedRing_eq`;
- `universalPrimeChamberRelativeKreinProbe_exact_neg_inertia`;
- `universalPrimeChamberRelativeKreinProbe_exact_pos_inertia`.

The continuous-real-exponent form of `(4)`, the finite-rate theorem, and the combined five-channel
minimality lower bound are encoded by `continuousMobiusGevreyTrichotomy`,
`finiteRateSpectrumLowerBound`, and `minimalHTCompletionArchitecture`.  The last theorem packages
necessity only; it does not assert the open Minimal-Architecture Completeness converse.
The final three declarations are the formally certified successor channels described in
`source-producer-integral-realization-minimality.md`.
The final root criterion is the integral algebraic core of the first positive triptic
source-effectivity model.

## Gates

- [x] prove and formalize marked finite-jet homogeneity
- [x] prove and formalize unpolarized field/completion blindness and exact polarization witness
- [x] prove the full Gevrey trichotomy; formalize representative subcritical, critical, and
      supercritical regimes
- [x] prove and formalize the product-scale one-path no-go
- [x] prove arbitrary-pseudometric bornological reconstruction
- [x] prove finite-rate invisibility
- [x] prove and formalize critical-chart completeness on the Möbius model
- [x] identify existing polarized completeness on the prime-orientation model
- [x] state the exact minimal positive replacement for every no-go
- [x] run targeted external parent searches
- [ ] obtain specialist external novelty review
- [x] formalize the continuous Gevrey trichotomy and finite-rate theorem
- [ ] prove or falsify Minimal-Architecture Completeness
