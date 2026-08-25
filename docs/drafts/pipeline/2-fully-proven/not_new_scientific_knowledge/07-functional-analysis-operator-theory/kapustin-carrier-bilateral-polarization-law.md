# Kapustin's exact carrier requires a source-selected full-sector polarization

- **ID:** `kapustin-carrier-bilateral-polarization-law`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Kapustin's exact Krein-space Hilbert--Polya operator; Makarov--Poltoratski
  Beurling--Malliavin theory for Toeplitz kernels
- **Statement:** Every nonzero bounded analytic Kapustin gauge has a critical-line metric weight
  with positive and negative sets of positive measure.  Hence every admissible Kapustin carrier has
  Krein index `(infinity,infinity)`.  A Hilbert--Polya realization retaining this exact spectrum must
  replace the scalar analytic gauge metric by an external source-selected polarization that acts
  coercively on an entire infinite-dimensional sign sector.

## Goal

Kapustin's 2024 theorem constructs, for each admissible analytic gauge `phi`, an exact
Krein-self-adjoint operator whose point spectrum contains

```text
1/(rho(1-rho))
```

for every nontrivial zeta zero `rho`.  The operator is already present; the unresolved
Hilbert--Polya question is whether the gauge can make its metric definite.

This card determines the sign type of every gauge in the analytic class, rather than only the
explicit powers.  It is a Kapustin-specific discharge of a construction law already isolated in
the pipeline:

> the exact carrier can be Hilbertized only by an external, source-selected full-sector
> polarization; selecting another scalar analytic gauge in the same half-plane can never suffice.

## Setup

Let

```text
H_R={s in C: Re s>1/2}
```

and let `phi` be any nonzero member of `H-infinity(H_R)`.  Its nontangential boundary values are
nonzero almost everywhere.  Define, for almost every real `t`,

```text
q_phi(t)
 =(2pi)^(-3/2+it) phi(1/2+it)/Gamma(1/2+it),

p_phi(t)=Re q_phi(t).                                      (1)
```

Kapustin's admissible gauges satisfy the stronger bound

```text
|phi(s)| <= C |s|^(-beta)
```

and therefore belong to this bounded analytic class.

When `phi(conjugate(s))=conjugate(phi(s))`, the weight `p_phi` is even.  Kapustin's symmetric
carrier is

```text
K_phi={f in L2(R,|p_phi(t)|dt): f(-t)=f(t)}.               (2)
```

## Theorem A: no one-sided analytic gauge has constant sign

For every nonzero `phi in H-infinity(H_R)`, both sets

```text
{t: p_phi(t)>0},
{t: p_phi(t)<0}                                            (3)
```

have positive Lebesgue measure.

### Proof

#### 1. Rotate the gauge to the upper half-plane

Put

```text
Phi(z)=phi(1/2-iz),             Im z>0.
```

Then `Phi in H-infinity(C_+)`.  On the real boundary write, almost everywhere,

```text
Phi(x)/|Phi(x)|=exp(i psi(x)).                              (4)
```

The known reciprocal-gamma factor at `s=1/2-ix` has phase

```text
vartheta(x)=arg Gamma(1/2+ix)-x log(2pi),                  (5)
```

where the continuous branch is chosen with `vartheta(0)=0`.  Thus the phase of `q_phi(-x)` is
`vartheta(x)+psi(x)`.

Assume first, for contradiction, that `p_phi>=0` almost everywhere.  There is a measurable real
function `b` with

```text
|b(x)|<=pi/2,
exp(i psi(x))=exp(-i vartheta(x)+i b(x)).                  (6)
```

Define the smooth unimodular symbol

```text
U_0(x)=exp(2i vartheta(x)).                                (7)
```

Equation `(6)` gives

```text
exp(-2i psi)=U_0 exp(-2ib).                                (8)
```

#### 2. Positivity would create a nonzero Toeplitz kernel

For a unimodular symbol `U`, write `N^r[U]` for the `H^r(C_+)` Toeplitz kernel in the
Makarov--Poltoratski convention.  Since

```text
conjugate(exp(-2i psi)) conjugate(Phi)=Phi,
```

the nonzero function `Phi` belongs to

```text
N^infinity[U_0 exp(-2ib)].                                 (9)
```

Let

```text
b_0(z)=(i-z)/(i+z)
```

be the standard upper-half-plane Blaschke factor.  The Smirnov--Kolmogorov bounded-phase theorem,
equation (1.8) of Makarov--Poltoratski, says

```text
||gamma||_infinity<pi/r
  => N^r[conjugate(b_0)^(2/r) exp(i gamma)] is nonzero.
```

Apply it with `r=1/2` and `gamma=2b`.  Since `||2b||_infinity<=pi<2pi`, there exists a nonzero

```text
G in N^(1/2)[conjugate(b_0)^4 exp(2ib)].                   (10)
```

Toeplitz kernels multiply: multiplying `(9)` and `(10)` gives

```text
Phi G in N^(1/2)[U_0 conjugate(b_0)^4].                   (11)
```

The product is nonzero and belongs to `H^(1/2)` because `Phi` is bounded.

#### 3. The reciprocal-gamma Toeplitz kernel is trivial

Set

```text
V=U_0 conjugate(b_0)^4=exp(i eta).
```

Differentiating `(5)` gives

```text
vartheta'(x)
 =Re digamma(1/2+ix)-log(2pi)
 =log(|x|/(2pi))+O(|x|^(-2)).                             (12)
```

The Blaschke phase derivative is `O(|x|^(-2))`.  Hence

```text
eta'(x)=2log(|x|/(2pi))+O(|x|^(-2))                       (13)
```

at both ends of the line.  In particular `eta` is eventually strictly increasing and

```text
eta(-infinity)=-infinity,
eta(+infinity)=+infinity.                                 (14)
```

Let `S(x)=exp(ix)`, the boundary values of the exponential inner function, and write

```text
V=(V conjugate(S)) S.
```

The phase `eta(x)-x` has derivative bounded below by a positive constant at both ends and has the
limits in `(14)`.  It is therefore not `0`-almost decreasing in the precise
Makarov--Poltoratski sense.  Theorem A(i) of their super-exponential Toeplitz-kernel theorem, with
`kappa=0` and `epsilon=1`, yields

```text
N^+[V]=0.                                                  (15)
```

Since every `H^(1/2)` Toeplitz-kernel element is a Smirnov-class kernel element, `(15)` contradicts
the nonzero element `(11)`.  Thus `p_phi>=0` almost everywhere is impossible.

Apply the same argument to the nonzero bounded analytic gauge `-phi`.  Its weight is `-p_phi`, so
`p_phi<=0` almost everywhere is also impossible.  Therefore both sets in `(3)` have positive
measure.  This proves Theorem A.

## Theorem B: the exact carrier has index `(infinity,infinity)`

Assume Kapustin's Schwarz symmetry on `phi`.  Then `p_phi` is even.  The positive and negative sets
in `(3)` are even measurable sets of positive measure.  Even `L2` functions supported on either set
form infinite-dimensional positive- and negative-definite subspaces of `(2)`.  Hence

```text
ind_+(K_phi)=ind_-(K_phi)=infinity.                         (16)
```

This conclusion holds for every admissible Kapustin gauge, not only the power family.

## Positive Hilbert--Polya construction law

Let `J_phi=multiplication by sign(p_phi)` be the fundamental symmetry in the Hilbert majorant
`L2(|p_phi|)`, and let `P_-` project onto its negative sector.  If a bounded self-adjoint metric
correction `G` produces a positive metric,

```text
J_phi+G>=0,
```

then necessarily

```text
P_- G P_- >= P_-.                                         (17)
```

Thus every Hilbertization retaining Kapustin's exact spectrum must have all of the following
properties:

1. **Full-sector action:** it acts coercively on the entire infinite-dimensional negative sector.
2. **Essential size:** it is noncompact, infinite-rank, outside every finite Schatten class, and has
   essential norm at least one.
3. **Scalar Hardy-gauge escape:** it cannot be obtained by selecting another bounded analytic gauge
   in `H_R`; Theorem A rules out that entire scalar one-sided class.
4. **External source marking:** it must arise from a boundary operator or source geometry outside
   bounded analytic gauge multiplication.  A two-Hardy-space coupling is one possible realization,
   but is not forced by the sign theorem alone.

The exact spectral carrier is not discarded; its metric must be replaced by a source-selected
full-sector polarization satisfying `(17)`.  To advance RH through the Euler-source framework, that
polarization must be a pointed global incidence object coupling the weighted all-prime coefficient
tail, archimedean completion, and distinguished divisor/trace moments in a topology stronger than
compact-open regular-germ convergence.

## Relation to the pipeline

- `kapustin-power-gauge-infinite-krein-index.md` proved `(16)` and `(17)` for the explicit power
  gauges by Stirling oscillation.  The present theorem replaces that family calculation by a
  universal Hardy/Toeplitz argument.
- `../../1-in-progress/goldilocks-divisor-rigidity.md` already isolates that one-sided Hardy boundary
  spectrum is free, that orientation reversal alone is not the discriminating invariant, and that
  a successful weld must retain arithmetic pure-point/source marking.  The present theorem is a
  concrete reciprocal-gamma application, not the origin of that architecture.
- `faithful-krein-index-escape-stratification.md` already proves the positive operator profile at the
  general level: a faithful RH index must use a divisor-controlling topology or a distinguished
  Euler/source realization and must be allowed to be discontinuous, gapless, or non-Fredholm at the
  selector threshold.  Inequality `(17)` is the Kapustin-sector version of that requirement.
- `../new_scientific_knowledge/critical-center-euler-unit-trace-hankel-instability.md` gives the
  decisive Euler-source classification.  The Lean theorems
  `criticalDisc_analytic_odd_schwarz_mem_realClosedSpan_compl_finset`,
  `criticalDisc_analytic_odd_schwarz_mem_realEulerIncrementGroup_closure`, and
  `criticalDisc_continuous_finiteUnitInvariant_eq_base` prove that, after deleting any finite prime
  set, the FE--Schwarz regular-germ fibre is one genuine Euler-unit orbit closure and has a one-point
  maximal continuous quotient.  After the principal part is restored, the surviving quotient is
  precisely the divisor/multiplicity marking.
- The Lean inverse `normalizedTraceMomentGerm_oddTracePreimage`, its normalized-division bound, and
  `exists_close_even_schwarz_traceHankel_failure` identify the distinguished trace-moment marking and
  prove that trace-Hankel positivity is nowhere locally forced in the compact-open germ topology.
  Hence “external source marking” above has a precise meaning: weighted all-prime tail plus
  archimedean completion plus divisor/trace incidence, before passage to the regular germ.
- `shifted-xi-kernel-transverse-index-filtration.md` is a different
  exact carrier: its generalized de Branges negative index faithfully counts off-line zeros.  The
  Kapustin metric index is instead always two-sided infinite, so the two metrics must not be
  identified.
- `../../../../support-extraction-log.md` and `../../../door/G5-unitarity-gatekeeper.md` already identify
  the digamma term as the logarithmic archimedean Toeplitz potential in the explicit Weil operator.
  Formula `(13)` reuses that phase geometry in a different Toeplitz-kernel convention.
- The theorem does not constrain CCM, Suzuki, Sonin, prolate, or finite-Weil constructions.
- It does not constrain finite-prime approximants that carry the `Xi` divisor locally uniformly and
  satisfy the sub-log-square reflected-energy condition.  That viable cofinal route remains exactly
  as stated in
  `../../3-formalized/not_new_scientific_knowledge/finite-prime-logarithmic-boundary-transfer.md`.

## Corpus and novelty audit

- **Kapustin parent.** The 2024 paper constructs the Krein metrics and exact transformed-zero point
  spectrum, but does not classify the sign of every admissible gauge or state the external
  full-sector polarization requirement.
- **Toeplitz parent.** Makarov--Poltoratski prove the general triviality theorem for
  super-exponential Toeplitz kernels and the bounded-phase multiplier used above.  They do not apply
  it to the reciprocal-gamma phase or Kapustin's Hilbert--Polya carrier.
- **Literature search.** Searches through July 2026 located no paper connecting Kapustin's gauge
  family to Toeplitz-kernel density, no universal sign theorem for `p_phi`, and no statement of
  `(16)`--`(17)` for this carrier.
- **Internal parent comparison.** The corpus already contains the Hardy one-sidedness/orientation
  analysis, the reciprocal-gamma logarithmic phase, faithful Krein-index escape, and an
  unconditional Lean classification of the fixed-divisor FE--Schwarz regular-germ fibre.  The
  construction law claimed in the first draft was therefore a rediscovery of the existing
  Hilbert--Polya boundary, not a new branch.
- **Novelty verdict.** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]` The exact universal sign statement for
  Kapustin's gauge class is a useful specialization not previously recorded by name, but its proof
  is a direct collision of the Kapustin and Makarov--Poltoratski parents and its architectural
  consequence was already present in the corpus.
- **Significance verdict.** It closes scalar gauge selection inside one published exact carrier, but
  does not supply the missing source-selected polarization or a faithful transverse divisor index.
  It therefore fails the project's dual novelty-significance gate for new scientific knowledge.

## Gates

- [x] 0 -> 1: exact constant-sign question and Toeplitz-kernel falsifier isolated.
- [x] 1 -> 2: complete upper-half-plane rotation, bounded-phase cancellation, kernel product,
  Makarov--Poltoratski triviality, index, and polarization proof.
- [ ] 2 -> 3: no Lean formalization selected.  The present tree lacks Hardy/Smirnov Toeplitz kernels,
  canonical boundary phase, digamma asymptotics, and the Makarov--Poltoratski density theorem; a
  finite-dimensional wrapper would not formalize the analytic result.
- [ ] 3 -> 4: independent operator-theory review and publication-level parent audit remain.

## Route disposition

The first proposed positive target was a pointed global incidence metric

```text
G = G(weighted all-prime coefficient tail,
      archimedean completion,
      distinguished divisor/trace moments)
```

on a topology strictly finer than compact-open FE--Schwarz regular-germ convergence, such that:

1. `P_- G P_- >= P_-` on the complete negative sector;
2. the positive completion preserves the transformed-zero eigenvectors and yields a densely defined
   Hilbert-self-adjoint operator on a canonical arithmetic domain; and
3. its polarization carries a faithful transverse filtration agreeing with the off-line divisor
   count, rather than the divisor-blind constant index `(infinity,infinity)` of the raw Kapustin
   metric.

Another scalar analytic gauge is outside the surviving class.  A compact-open continuous reader of
the regular germ is also outside it by the one-point quotient theorem.  The weighted `M_0` tail does
not repair the problem because its joint graph with the regular strip field is dense in the product.
If the distinguished divisor/trace moments are retained faithfully, positivity of the resulting
metric is exactly RH.

Thus this formulation is now retired as an independent producer; see
`../../5-failed/kapustin-source-incidence-polarization.md`.  The positive reopening condition is
stronger: construct a pre-divisor quantized source incidence that does not factor through any of
those three readings and canonically produces the full-sector metric.

## References

1. V. V. Kapustin, *Hilbert--Polya Operators in Krein Spaces*, Siberian Math. J. 65 (2024),
   72--75, DOI `10.1134/S0037446624010087`.
2. N. Makarov and A. Poltoratski, *Beurling--Malliavin theory for Toeplitz kernels*, Invent. Math.
   180 (2010), 443--480, DOI `10.1007/s00222-010-0239-4`.
3. A. Poltoratski, *Toeplitz order*, J. Funct. Anal. 275 (2018), 660--697,
   DOI `10.1016/j.jfa.2018.02.006`.

## Log

- 2026-07-11 -- Kapustin gauge positivity rotated to an upper-half-plane phase problem.
- 2026-07-11 -- bounded positivity phase removed with the Smirnov--Kolmogorov multiplier; resulting
  reciprocal-gamma Toeplitz kernel proved trivial by Makarov--Poltoratski Theorem A(i).
- 2026-07-11 -- universal two-sided infinite index and external full-sector polarization requirement
  proved.
- 2026-07-11 -- mechanism-level corpus audit found the Hardy-orientation, logarithmic gamma-potential,
  faithful-index, and source-marking architecture already present; card downgraded to a
  Kapustin-specific bridge and the open core strengthened to a faithful source polarization.
- 2026-07-11 -- grounded the positive target in the unconditional critical-disc Lean theorems:
  cofinite real tangent completeness, nonlinear Euler-unit orbit density, one-point continuous
  quotient, odd-trace/even-moment inversion, and analytic trace-Hankel instability.
- 2026-07-11 -- weighted-tail and divisor-faithful readings audited: the former decouples and the
  latter is RH-equivalent.  The proposed pointed incidence metric moved to a terminal route card;
  only a new pre-divisor quantized source incidence can reopen it.

## Formalization progress (2026-08-24)

The positive full-sector construction law `(17)` and all operator-ideal consequences in items
1--2 are now unconditional Lean theorems:

- `GaloisForLFunctions.HTGeometry.FullSectorPolarizationLaw` proves the exact quadratic compression
  floor, its norm lower bound, noncompactness on an infinite-dimensional closed sign sector,
  infinite algebraic rank, and the sharp distance `1 ≤ ‖G - K‖` from every compact `K`.
- `GaloisForLFunctions.RHTower.FullSectorPolarizationEssentialNorm` identifies that uniform compact
  floor with `1 ≤ essentialNorm G` and excludes every `MemSchattenClass p G` for `0 < p`.

Both leaves pass direct Lean checking and targeted leaf builds.  The card remains Stage 2: Theorem A
(the universal reciprocal-gamma Toeplitz sign theorem), its measurable Hardy-boundary setup, and
Theorem B's application to the literal even weighted `L²` Kapustin carrier are not yet formalized.

## Formalization progress (2026-08-25)

Exact reusable infrastructure now present:

- `HTGeometry.DiskMultiplierOuterFactor`: canonical Szegő outer factor with original bounded
  multiplier boundary modulus;
- `HTGeometry.SzegoOuterCyclic`: unconditional cyclicity and dense Hardy multiplication range;
- `HTGeometry.DiskMultiplierInnerOuterFactor`: exact inner--outer factorization, including
  shift-commutant inner multiplier, Hardy isometry, unimodular boundary, and real-line product law;
- `RHTower.KapustinGaugeSmirnovCollision`: either one-sided sign assumption constructs a literal
  nonzero `SmirnovToeplitzKernelElement kapustinToeplitzSymbol`;
- `HTGeometry.MakarovPoltoratskiWeakPhase`: exact Kolmogorov little-weak-`L¹` endpoint contradiction
  for fixed reciprocal-Gamma phase;
- `RHTower.KapustinGaugeCarrier`, `HTGeometry.MeasurableEvenWeightedSignCarrier`, and full-sector
  polarization leaves contain exact Theorem B and operator-ideal consequences once Theorem A is
  discharged.

Open dependency-closed core: formalize one-way Makarov--Poltoratski basic criterion for the
real-analytic fixed symbol used here,

```text
SmirnovToeplitzKernelElement (x ↦ exp(i * kapustinToeplitzPhase x))
  → Nonempty (SmirnovToeplitzWeakPhaseWitness kapustinToeplitzPhase),
```

including inner/outer regularization and Kolmogorov little-weak-`L¹`. This exact bridge turns the
already constructed literal kernel element into unconditional sign contradiction; no surrogate
phase premise is acceptable.
