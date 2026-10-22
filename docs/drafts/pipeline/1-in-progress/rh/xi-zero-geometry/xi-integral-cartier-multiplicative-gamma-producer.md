# Xi integral Cartier multiplicative Gamma producer

- **ID:** `xi-integral-cartier-multiplicative-gamma-producer`
- **Stage:** 1-in-progress
- **Type:** THEOREM PACKAGE (Lean) / OPEN GHOST-ERASURE PRODUCER
- **Source:** `rh-current-frontier-map.md` · horizontal source/Gamma seam
- **Statement:** Full Laurent source admits unconditional, coefficient-faithful Gamma evaluation in
  multiplicative formal group; obstruction to additive `I/I²` reporter is exactly discarded
  quadratic inversion term.

## Goal

Construct strongest unconditional producer supported by new bidirectional integral source. Test
whether full source inversion—not its first conormal truncation—forces desired additive Gamma Ward
descent. Preserve prime labels, divisor multiplicity, and both orientations.

## Gates

- [x] 0 → 1 in-progress: literal Laurent source, attack idea, and RH-strength endpoint identified
- [x] 1 → 2 fully-proven: full-source producer and descent classification `[PROVED HERE]`
- [x] 2 → 3 formalized: exact leaf build and axiom audit pass
- [ ] 3 → 4 publication-ready

## Heavy conjecture loop

### C1 — complex-period inheritance `[FALSIFIED]`

Conjecture: four-pi periodicity of literal theta source descends to every terminal Xi multiplicity
jet, forcing integral centered monodromy. Failure: source periodicity belongs to total spatial
complex-log source; terminal jet is a spectral coefficient in cut parameter. Required
translation-commuting spectral projection is absent and its fibrewise conclusion is already
Cartier descent/RH.

Positive survivor: missing operation is complex-log translation covariance of each Xi Riesz block,
not another scalar monodromy identity.

### C2 — commuting FE/Schwarz holonomy `[FALSIFIED]`

Conjecture: commuting source lifts of functional equation and Schwarz involution trivialize centred
holonomy. Failure: corpus proves commuting Klein-four square and scalar Hilbert-90 gauge
trivialization, while explicit off-line quartet carriers satisfy same square. Commutation exchanges
fibres; it does not fix them.

Positive survivor: any producer must use arithmetic/higher-rank gluing, not scalar symmetry.

### C3 — full multiplicative Gamma descent `[CLASSIFIED]`

Let `u(a)=exp(a)-1`, `v(a)=exp(-a)-1`. Strict Laurent inversion gives

```text
(q-1) + (q^-1-1) + (q-1)(q^-1-1) = 0.
```

The exact Gamma coefficients obey same law

```text
u(a) + v(a) + u(a)v(a) = 0
```

for every real `a`. Thus full source has unconditional coefficient-faithful reporter into
multiplicative formal group `x ⊕ y = x+y+xy`. Passing to `I/I²` kills product and leaves additive
defect `u+v=-uv=2(cosh(a)-1)`, which vanishes exactly at `a=0`.

Lean constructs the canonical Laurent ring evaluation at every Xi divisor and ordinary prime,
retains divisor multiplicity linearly, and keeps forward, inverse, and quadratic representatives.
Their evaluations are respectively `m(exp(a)-1)`, `m(exp(-a)-1)`, and their product term; strict
inversion makes their sum zero. The full multiplicative producer therefore exists unconditionally.

The same evaluation factors through additive Cartier conormal `I/I²` iff `a=0`. At the literal
prime-labelled Xi source this is iff `Re(rho)=1/2`, and universal descent is equivalent to RH.
Thus C3 does not prove RH: it identifies quadratic ghost erasure as exact RH-strength operation.
Lean source: `RHTower/FrankensteinXiFullIntegralGammaEvaluationProducer.lean`.

Scientific novelty is limited. Multiplicative formal group and logarithmic linearization are
standard and already formalized in `SourceNormalClockCurvatureLaw.lean`. New glue is source-selected
Xi specialization, linear multiplicity retention, and exact conormal-factorization theorem.
`[NOVELTY UNVERIFIED]`.

### C4 — integral Todd/unimodular linearization `[FALSIFIED]`

Conjecture: bidirectional integral source makes multiplicative-to-additive comparison unimodular;
its positive reflected Jacobian would equal one only at neutral grade. Failure: formal
logarithm/Chern character has rational denominators and is not an integral lattice automorphism.
Corpus already proves no nontrivial algebraic-group morphism between `G_m` and `G_a`; analytic log
linearizes every off-neutral positive character. Integral source alone cannot supply unimodularity.

Positive survivor: successful linearization must be singular/nonalgebraic and prove actual
integral-lattice preservation, not infer it from source coefficients.

### C5 — kill quadratic ghost by ordinary cyclicity `[FALSIFIED]`

Conjecture: realize exact ghost as a Hochschild degree-two boundary, then apply source cyclic
cocycle. Failure is coefficient-level. Product trace reads normalized boundary as one and is not a
cocycle; Kummer trace-derivation cocycle kills same boundary but does not read product coefficient.
Identifying them on physical chain is precisely ghost erasure.

Positive survivor: ghost has two inequivalent source readings—nonhomological product trace and
boundary-compatible Kummer cocycle. Producer must construct a selected relative cocycle whose
physical readout agrees with product trace while retaining boundary descent. Ordinary Hochschild
homology cannot do this.

## No-go closure

- **Exact killing mechanism:** additive `I/I²` linearization deletes quadratic inversion ghost;
  canonical evaluation descends exactly at neutral Gamma clock.
- **Strongest positive survivor:** unconditional coefficient- and multiplicity-faithful full-Laurent
  Gamma producer with exact three-term Ward identity.
- **New insight:** source/Gamma mismatch is formal-group linearization curvature, not absence of a
  bidirectional source class. Remaining core is selected relative ghost erasure, not Gamma
  evaluation or ordinary boundary cyclicity.
- **Status:** Lean complete; direct elaboration and exact leaf build pass; axioms only `propext`,
  `Classical.choice`, `Quot.sound`; module wired; no umbrella build.

## Log

- 2026-08-16 — created in progress; C1/C2 falsified; C3 frozen.
- 2026-08-16 — C3 paper-proved and formalized; C4/C5 falsified; exact relative ghost-erasure core
  isolated.
