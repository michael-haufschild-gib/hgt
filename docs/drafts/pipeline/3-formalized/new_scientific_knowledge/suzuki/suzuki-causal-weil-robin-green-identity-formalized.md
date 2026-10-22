# Suzuki causal Weil--Robin Green identity — formalization certificate

- **Stage:** 3-formalized
- **Paper proof:**
  `./suzuki-causal-weil-robin-green-identity.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalWeilRobinGreenIdentity.lean`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Formalized core

Lean proves exact cancellation of Suzuki screw primitive denominators by `z^2`, leaving Robin
boundary current plus completed Weil exterior:

```text
z^2 R_g = exp(i a z)(i z U(a) - U'(a)) + E_(-g'').
```

It also proves uniqueness of exterior channel from screw exterior and boundary jets, exact
recovery of delayed-hinge boundary--tail law, and characteristic-free connectors for denominators
`z^2*Xi` and `P*(z^2*Xi)`.

Key declarations:

```text
z_sq_mul_suzukiCausalWeilRobinReconstruction
suzukiCausalWeilRobinExterior_unique
suzukiCausalWeilRobinReconstruction_delayedHinge
z_sq_mul_suzukiDelayedHingeExteriorFromCut_eq_weilRobin
suzukiXiDenominator_mul_weilRobinReconstruction
suzukiCompoundDenominator_mul_weilRobinReconstruction
```

Physical twofold integration by parts, completed distribution identity `K=-g''`, and
compact-diagonal exterior invariance are dependency-closed paper theorems.  Lean formalizes exact
algebra consumed by compound-Bezoutian frontier; no RH, positivity, estimate, computation, or
nonvanishing premise is assumed.

## Integration

- imported by `GaloisForLFunctions.RHTower` umbrella;
- imported and summarized in `RiemannHypothesisSOTA2026`;
- active rooted-midpoint card replaces unspecified collective weld by exact open core
  `SUZUKI-MARKED-WEIL-ROBIN-CD`.

## Verification

- direct source check:
  `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCausalWeilRobinGreenIdentity.lean`;
- targeted SOTA build: `9448/9448` jobs;
- axiom audit: `propext`, `Classical.choice`, `Quot.sound` only;
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- global formal lint is blocked only by concurrently added unrelated unreachable module
  `GaloisForLFunctions.RHTower.MobiusLaplaceCriticalDilationPrimeEscapeLaw`.

