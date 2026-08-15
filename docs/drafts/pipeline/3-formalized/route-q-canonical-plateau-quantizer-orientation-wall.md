# Route Q canonical plateau quantizer and orientation wall

- **ID:** `route-q-canonical-plateau-quantizer-orientation-wall`
- **Stage:** 3-formalized
- **Type:** THEOREM / structural decision
- **Routes:** Q primary; U comparison
- **Source:** `rh-current-frontier-map.md`, Route Q source-side quantization survivor

## Status labels

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NO RH CLAIM]`

## Question

Does existence of a label-sensitive positive-measure plateau quotient from the actual theta source
to the canonical Xi thermal atoms supply Route Q's missing producer, or does it merely transport
the already-known thermal orientation defect?

## Theorem Q-PLATEAU-WALL

Write

```text
lambda_j = xiThermalNode (xiThermalEnumeration j) > 0,
M_0      = normalizedPrimeArchMoment 0 = sum_j lambda_j,
mu_Xi    = sum_j lambda_j delta_(lambda_j).
```

Let `thetaSource.law` be the probability law of the literal all-integer theta-cusp density.  There
exists a measurable reporter `Q : R -> R` such that

```text
Q_*(M_0 thetaSource.law) = mu_Xi.                         (1)
```

Consequently every enumerated thermal node has a positive-source-measure fibre and, for every
`n >= 0`,

```text
integral Q(x)^n d(M_0 thetaSource.law)(x)
  = sum_j lambda_j^(n+1)
  = xiThermalPositiveMoment n.                            (2)
```

The reporter is a complete prime--archimedean moment witness exactly under RH.  More sharply, its
first nonconstant moment has exact excess

```text
integral Q d(M_0 thetaSource.law) - normalizedPrimeArchMoment 1
  = xiThermalOrientationEnergy >= 0,                       (3)
```

and equality in `(3)` is equivalent to RH.

## Conjecture--attack--pivot loop

### Q-PLATEAU-EXIST — plateau existence supplies missing producer

**Attack.** Normalize `mu_Xi` by its unconditional mass `M_0`.  Every probability measure on a
standard Borel space is a measurable image of uniform measure on `[0,1]`.  The probability-integral
transform sends `thetaSource.law` to that uniform measure.  Composition gives `(1)` without RH.

**Verdict:** falsified as a producer.  Atomic target law forces positive fibres, so all
qualitative plateau requirements hold unconditionally.

### Q-PLATEAU-MOMENT — all-degree matching follows from quantization

**Attack.** Pushforward integration gives the first equality in `(2)`.  The self-weighted atomic
definition of `mu_Xi` gives the second.  Corpus thermal orientation identity gives `(3)`.

**Verdict:** falsified.  The entire mismatch is already visible in degree one; its sign is
the unconditional wrong direction, and equality is RH.

## Dependency-closed proof

Let `c = ENNReal.ofReal M_0`.  The compact Xi measure is

```text
mu_Xi = sum_j c_j delta_(lambda_j),   c_j = lambda_j > 0.
```

Termwise integration gives

```text
integral x^n d mu_Xi = sum_j lambda_j^(n+1)
                      = xiThermalPositiveMoment n.
```

At `n = 0`, the corpus identity `xiThermalPositiveMoment 0 = M_0` proves
`mu_Xi(R) = c`; hence `c⁻¹ mu_Xi` is a probability measure.  Standard-Borel measure
representation supplies measurable `f : Icc 0 1 -> R` whose pushforward of interval volume is
`c⁻¹ mu_Xi`.  Continuity of the literal theta CDF and the already-proved probability-integral
transform give

```text
(thetaSource.cdf)_* thetaSource.law = volume|_[0,1].
```

Thus `Q = f o thetaSource.cdf` is measurable and

```text
Q_*(c thetaSource.law) = c (c⁻¹ mu_Xi) = mu_Xi.
```

Evaluating this measure identity at `{lambda_j}` gives positive fibre mass because the `j`th
Dirac summand has weight `lambda_j > 0`.  Pushforward integration proves all moment identities.
For `n = 1`, the corpus second-moment decomposition is

```text
xiThermalPositiveMoment 1
  = normalizedPrimeArchMoment 1 + xiThermalOrientationEnergy,
```

where orientation energy is nonnegative and vanishes iff RH.  Substitution proves `(3)` and its
RH equality case.  Full moment-witness status implies RH by the existing prime--archimedean moment
representation theorem; RH implies status by the existing equality of positive thermal and source
moment towers.  No unproved premise enters any step.

## External novelty audit

- Classical content: measurable realization of a probability law on a standard Borel space,
  probability-integral transform, pushforward integration.  Mathlib's documented standard-Borel
  machinery explicitly reduces general laws to real/CDF constructions:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Disintegration/StandardBorel.html>.
- Nearest Xi/theta literature found concerns Fourier kernels, harmonic-oscillator integral
  representations, and real-rooted approximations, not a self-weighted Xi atomic pushforward or
  its exact orientation defect: <https://arxiv.org/abs/1502.06844> and
  <https://arxiv.org/abs/math-ph/0612086>.
- Targeted searches on 2026-08-15 found no external occurrence of the combined construction
  `sum lambda_j delta_(lambda_j)`, literal theta-law plateau fibres, and barycenter defect equal to
  an RH-equivalent orientation energy.  Novelty therefore remains unverified, not claimed.

### Positive survivor

Route Q does not need another existence theorem for a discontinuous plateau quotient.  It needs a
**source-intrinsic orientation law** that proves the canonical plateau barycenter is at most the
completed theta/source barycenter.  This single upper comparison is exactly sharp: the reverse
inequality and its defect are already unconditional.

## Route U comparison

Route U's global Nyquist work has the same shape/orientation split.  Polyphase reconstruction and
the signed null current remove the universal anti-diagonal ultraviolet mode unconditionally, but
they do not orient the finite diagonal remainder.  Route Q's plateau transport reconstructs the
entire canonical atomic law unconditionally, but does not orient its barycenter against the
completed source.  In both routes, reconstruction is kinematic and unconditional; only the
source-oriented scalar defect is arithmetic.

## Gates

- [x] 0 -> 1: exact falsifiable statement, hostile alternative, positive survivor
- [x] 1 -> 2: dependency-closed proof and external novelty audit
- [x] 2 -> 3: unconditional Lean theorem, axiom audit, exact leaf `.olean`, umbrella wiring
- [ ] 3 -> 4: independent significance audit and standalone exposition

## Lean closure

Proved, without hypotheses or new axioms, in
`formal/GaloisForLFunctions/RHTower/PrimeArchThetaCanonicalPlateauQuantizerOrientationWall.lean`:

1. unconditional power moments of `primeArchXiCompactMomentMeasure` equal
   `xiThermalPositiveMoment`;
2. normalized canonical Xi measure is a probability measure;
3. a measurable reporter from the literal theta law has pushforward
   `primeArchXiCompactMomentMeasure` after the native `M_0` scaling;
4. every thermal-node fibre is positive;
5. reporter moment-witness status iff RH;
6. first-moment excess equals `xiThermalOrientationEnergy`, hence vanishes iff RH.

## Log

- 2026-08-15 — Global antipodal diagonal-equipartition conjecture for Route U rejected by existing
  quadratic-shell anti-diagonal covariance.  Pivoted to shared reconstruction/orientation split.
- 2026-08-15 — Q-PLATEAU-WALL formulated; paper and Lean attacks started.
- 2026-08-15 — Dependency-closed proof completed.  Exact leaf `.olean` built with
  `lake env lean -o ...PrimeArchThetaCanonicalPlateauQuantizerOrientationWall.olean ...lean`.
  Axiom audit of the capstone and core transport/defect theorems reports only `propext`,
  `Classical.choice`, and `Quot.sound`.  Module imported by `RHTower.lean`; umbrella not built.
