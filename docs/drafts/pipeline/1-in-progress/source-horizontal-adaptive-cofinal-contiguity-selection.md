# Source-horizontal adaptive cofinal-contiguity selection

- **ID:** SH-ACCS-C13
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean); arithmetic observer-orbit producer unresolved
- **Source:** Frankenstein seam joining abelian class-law absolute continuity, global formation
  properness, adaptive Fisher/KL occupation, Route-T dilation, and shared-reservoir amplification
- **Statement:** A fixed absolutely-continuous source pair cannot carry reflected adaptive Boolean
  marginals on every expanding horizontal scale unless centered rate is zero.

## Goal

Replace equality-style RH receivers by a source property already present in corpus. Convergent
abelian zeta class laws are mutually absolutely continuous. If completed prime--Gamma source can
realize every dilated horizontal grade as one Boolean observer orbit on two such fixed class laws,
absolute continuity itself annihilates off-line grade. This preserves prime label, Xi multiplicity
copy, and both reflection orientations before scalarization.

## Heavy conjecture loop

### C13.0 — fixed full-information budget

**Conjecture.** One fixed source pair `P,R` with finite symmetrized KL information supports Boolean
observers `q_n` whose marginals are

```text
P(q_n=true)=q_p(d^n |t|),
R(q_n=true)=q_p(-d^n |t|),
q_p(u)=p^u/(p+p^u).
```

Data processing bounds every reporter Jeffreys work by fixed source Jeffreys work. Adaptive work
has uniform lower bound

```text
J_p(u) >= (3/5) log(p) u,  u>=1,
```

so it diverges on every nonzero dilation orbit.

**Verdict: PROVED UNCONDITIONALLY IN LEAN.** Therefore fixed finite source information forces
`t=0`.

### C13.1 — finite KL is unnecessary

**Conjecture.** Quantitative information bound is shadow of qualitative source contiguity.

For `t≠0`, same observer events satisfy

```text
P(q_n=true) -> 1,
R(q_n=true) -> 0.
```

If `P << R`, finite-measure Radon--Nikodym uniform integrability forces every `R`-vanishing event
sequence to vanish under `P`. Contradiction.

**Verdict: PROVED UNCONDITIONALLY IN LEAN.** One-sided absolute continuity suffices; no KL
finiteness, source involution, conditional sufficiency, or hidden-fibre equality remains.

### C13.2 — actual arithmetic source specialization

**Conjecture.** Use existing convergent abelian zeta class laws as fixed sources.

**Verdict: PROVED AS SELECTION LAW.** Corpus theorem `classLaw_absolutelyContinuous` supplies
mutual absolute continuity for every pair of convergent parameter points. Thus only missing premise
is exact source-derived adaptive observer orbit. Lean structure
`SourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate` contains actual class-law parameters
and marginal equations; absolute continuity is not a certificate field.

For every multiplicity-labelled Xi copy at prime two and scale two, such certificates imply RH via
`riemannHypothesis_of_sourceHorizontalXi_adaptiveClassLawScaleOrbitCertificates`.

### C13.3 — shared-reservoir amplification as observer producer

**Conjecture.** Convert existing arbitrarily large, prime-labelled shared-reservoir packets into
the cofinal Boolean orbit by reading their orientation-sensitive inertia.

**Failure at current corpus boundary.** Matrices are deterministic source coefficients, not random
variables on abelian class laws. Raw inertia remains visible only after weight-dependent
normalization. Existing moment-neutral packets make weights collapse; promoting raw signs to
asymptotically perfect tests requires precisely an unbounded normalization or a probability-law
landing. Absolute continuity proves such a landing cannot exist off line, but corpus does not yet
construct it from arithmetic source.

**Strongest positive survivor.** Moment-neutral amplification and cofinal contiguity are dual
sides of one wall:

```text
source coherence (P << R)
  + coefficient-faithful cofinal orientation tests
  => no off-line horizontal class.
```

This reinterprets rank--trace failure. Spectral collapse is not merely insufficient trace size;
it is what prevents raw amplified index from becoming a statistically consistent source observer.
Any successful unbounded normalization must be source-derived on both orientations, and doing so
is already enough to force neutrality.

## Exact remaining producer

Construct, from completed prime--Gamma/abelian-group source rather than Xi conclusion, for every
`XiZeroCopy q` one family

```text
observer_n : AbelianZetaGroupClass -> Bool
```

on two fixed convergent class laws whose pushforwards are the exact reflected adaptive Bernoulli
laws at grades `2^n |2 Re(q)-1|`. Equivalent weaker target: a coefficient-faithful source readout
of shared-reservoir orientation whose forward error tends to zero and reflected error tends to
zero. Either target plus already-formal absolute continuity proves RH.

Rejected substitutes:

- independent hyperbolic tensoring: index and fixed-threshold moments scale together;
- raw shared-reservoir inertia without probability landing: deterministic detector only;
- same-source conditional invariance: already RH-equivalent;
- reflected-pair cancellation: automatic and orientation-erasing;
- changing source law at every scale: loses fixed-source contiguity and gives no contradiction.

## Formal module

`formal/GaloisForLFunctions/RHTower/SourceHorizontalAdaptiveFisherCofinalContiguitySelection.lean`

Key capstones:

- `sourceHorizontalPrimeAdaptiveJeffreysWork_linear_lower`
- `sourceHorizontalPrimeAdaptiveBoundedScaleWork_iff`
- `sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fixedSourceFiniteJeffreys`
- `tendsto_measure_zero_of_absolutelyContinuous_finite`
- `not_cofinalObserverSeparation_of_absolutelyContinuous`
- `sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_fixedSourceContiguity`
- `sourceHorizontalPrimeAdaptive_centeredRate_eq_zero_of_abelianClassLawScaleObservers`
- `riemannHypothesis_of_sourceHorizontalXi_adaptiveClassLawScaleOrbitCertificates`

## Gates

- [x] 0 → 1 in-progress: source-pure statement and exact producer socket
- [x] paper proof dependency-closed for selection and contiguity laws
- [x] unconditional direct Lean check
- [x] targeted module build
- [x] capstone axiom audit
- [ ] external novelty audit
- [ ] arithmetic class-law observer orbit
- [ ] RH

## Log

- 2026-08-12 — Fixed-source finite-Jeffreys selector proved.
- 2026-08-12 — Pivoted to qualitative absolute continuity; cofinal separation no-go proved.
- 2026-08-12 — Instantiated selector on actual mutually-AC abelian class laws.
- 2026-08-12 — Added multiplicity-resolved Xi certificate and RH endpoint.
- 2026-08-12 — Targeted module build passed; audited capstones depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
