# Common-return two-moment kernels and sharp zero blocks

- **ID:** bvi-translated-prefix-observability
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); arbitrary-phase extension remains open
- **Contribution:** 007, one connected contribution; verified total **7 / 250**.
- **Source:** Contribution 004's residue model and contribution 005's exact initial
  and variance kernels; the translated-observation question following 006.
- **Statement:** Classify every observation window around the explicit return
  anchors `(k+a+1)*N!`, then identify the sharp detection window and its unique
  normalized second-difference extremizer.

## Scope

All public statements quantify over arbitrary natural parameters and real weights
without additional hypotheses. The anchor guarantees every required divisibility
and prevents natural subtraction from truncating a left sample. No condition on
`c(1)` or on the harmonic mean is assumed. These are finite exact theorems; no
asymptotic cancellation or detection bound at arbitrary phases follows.

## Closed paper result: exact common-return window kernels

The unrestricted phase conjecture remains open. Neither a proof nor a counterexample
was obtained from the shifted divisor equations. This is not a no-go or retirement.
Contribution 007 is the exact common-return classification,
including extremal rigidity; a future matching arbitrary-phase upper bound must not
be counted separately from its lower bound recorded here.

Write `L(M)=sievePrefixDiscrepancy N M c`, `H=Σ[1,N] c(d)/d`,
`S=Σ[1,N] c(d)`, and `D=H-S`. For natural `a,b,k`, choose the unconditional
anchor `P=(k+a+1)*N!`. Every positive `d≤N` divides `P`, and `P≥a`.

1. **Translation and reflection.** For every `t≥0`, `L(P+t)=L(t)`.
   For `t<P`, `L(P-(t+1))=D-L(t)`. Indeed, the residue model from 004 gives
   `L(M)=-Σ c(d)(M mod d)/d`. Divisibility gives the first identity; the exact
   complement `(P-(t+1)) mod d=d-1-(t mod d)` gives the second, including
   residue zero and divisor one. Thus no endpoint term is dropped.
2. **All radii.** Let `T=max(b,a-1)`. Vanishing on the actual interval
   `[P-a,P+b]` is equivalent to vanishing on initial indices `[1,T]`, together
   with `a=0 OR D=0`. If `a>0`, the sample `P-1` gives `D=0` because `L(0)=0`.
   The remaining left samples give exactly initial indices `0..a-1`; the right
   samples give `0..b`. Conversely these identities recover every interval point.
   This covers `a=0`, `b=0`, `N=0,1`, and the singleton `P` without premises.
3. **Two-moment kernel.** For positive left/right radii, `T≥1`. Put `s=min(T,N)`.
   By 005, initial vanishing means `c(d)=0` for `2≤d≤s` and
   `Σ[s+1,N] c(d)/d=0`. If `N=0` all sums are empty. If `N≥1`, splitting at `s`
   gives `H=c(1)` and `S=c(1)+Σ[s+1,N]c(d)`. Therefore `D=0` is exactly the
   second tail constraint `Σ[s+1,N]c(d)=0`. Both directions are proved; no
   normalization of `c(1)` or harmonic mean is assumed.
4. **Sharp centered detection.** At level `N=n+3`, the symmetric window of radius
   `N-2=n+1` has `2N-3` samples and `T=N-2`. Only coefficients `c(N-1),c(N)`
   survive. Their raw and harmonic sums vanish, and the two distinct positive
   denominators force both coefficients to zero. Thus the window vanishes iff
   the variance vanishes, using 005's exact variance kernel.
5. **Extremal rigidity and exact endpoints.** At level `N=n+4`, put `a=N-2`.
   On `[P-a,P+a-1]`, `T=N-3`. The two equations on the final three coefficients
   imply, uniquely for some real `λ`,
   `c(a)=λ*a`, `c(a+1)=-2*λ*(a+1)`, `c(a+2)=λ*(a+2)`;
   coefficients `2..a-1` vanish. This follows by writing the normalized final
   coefficients `x,y,z`: `x+y+z=0` and `a*x+(a+1)*y+(a+2)*z=0`, hence
   `x=z`, `y=-2z`. Conversely these coefficients satisfy both moment equations.
   For the canonical triple with arbitrary `λ`, the adjacent discrepancy values
   are `-λ*a` and `λ*a`, by the reflection identity and the first floor jump at `a`.
   Its variance is zero iff `λ=0`, because the terminal coefficient is `λ*N`.
   Thus every nonzero extremal direction has precisely the claimed zero block
   around this return. Arbitrary weights outside `[2,N]` remain invisible.

Significance: a return is not merely a zero of the dual energy. Reflection supplies
an additional observable moment, changing the exact nullspace from the one-moment
origin kernel to a two-moment tail kernel. Its smallest surviving direction is a
normalized second difference, and every sharp return-centered extremizer has that
form. This is one connected result, not separate credits for its identities and
witnesses. It makes no claim about all translated phases or asymptotic cancellation.

### Additional corpus audit

- `divisibility indicator consecutive interval linear independence zero run`:
  all 20 candidate statements, 20 source-argument statements and one ingredient
  set inspected. Partial generation 1449885; semantic coverage unavailable and
  reranking timed out. The proposed divisibility-ladder ingredient set does not
  prove interval independence. No competing classification was recovered.
- Exact lexical `residueCombination`: all six hits inspected. Existing private
  periodicity and public full-period means/covariances supply context, but not
  reflection or window kernels. Their relevant source bodies were inspected.
- `floor sum periodic reflection zero interval`: all 20 candidate statements,
  20 source-argument statements and one ingredient set inspected. Partial
  generation 1449909; semantic coverage unavailable and reranking timed out.
  Integral periodicity does not establish the needed discrete reflection identity.
- Both newly added field modules were inspected at declaration/doc level:
  `PrimeTailCalibrationAndMobiusDefect` and
  `DilatedCellScalingAndSecondOctaveFermiJumpBridge`. They do not state this kernel.
- Dependency-closed paper proof above reuses 004's residue model and 005's exact
  initial and variance kernels. The finite residue complement uses the existing
  core `Nat.mul_sub_mod` identity; its signature and isolated proof were verified
  in the installed toolchain before the field source check.

Paper/novelty audit and exact Lean verification are complete for this common-return package.

## Formal theorem package

Source: `formal/GaloisForLFunctions/BezoutValuationIncidence/ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`.
409 lines; 25 declarations: nine public theorems, four public definitions, twelve
private helpers. Central interfaces:

- `sieveReturnWindow_zero_iff`: complete all-radii kernel, including degenerate cases.
- `sieveReturnWindow_coefficient_kernel`: coefficient form using the exact initial kernel.
- `sieveReturnWindow_two_moment_kernel`: zero head plus harmonic/raw tail moments.
- `sieveReturnWindow_sharp_detection`: centered `2N-3` samples iff variance zero.
- `sieveReturnWindow_extremal_iff`: unique scalar and all coefficients of the
  `2N-4` window's kernel, modulo the invisible constant and out-of-level weights.
- `sieveReturnTripleWeight_zero_block`, `sieveReturnTripleWeight_variance_zero_iff`,
  `sieveReturnTripleWeight_adjacent_values`: exact witness, nontriviality and both
  adjacent values for every real scalar.

## Verification

- Named original-source audit passed with exit 0 and no diagnostics:
  `lake --old env lean -j 1 --root=/Users/michael/Documents/code/hgt/formal -o /tmp/bvi7-olean-cache/GaloisForLFunctions/BezoutValuationIncidence/ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.olean /Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/BezoutValuationIncidence/ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`.
- The temporary Lake root used a complete cloned project import closure: 9356
  project modules, zero missing. One foreground Lean process at a time; no full build.
- `/tmp/bvi7-axioms.lean` audited all 13 public declarations, exit 0.
  Every public theorem's closure is exactly `propext`, `Classical.choice`, `Quot.sound`.
  No added axioms, proof debt, opaque/unsafe declarations or heartbeat changes.
- Raw audit: `logs/bvi-root-2026-10-18-return-window-axioms.txt`.
- Source SHA-256: `ea7fd45d595e76066f25db9326c03e372f359781b4e89780b4087dabb1567670`.
- Olean SHA-256: `a0f1e40cc354839ca8177bb365a5db796ff68094ea0609a5511db533ad7df6c5`.
  Artifact installed atomically, newer than unchanged source; hashes verified.
- New leaf wired exactly once in `formal/GaloisForLFunctions/BezoutValuationIncidence.lean`.
- `scripts/formal_tools.py index` exited 0. All 25 source declarations, including
  private helpers, matched lexical index names/kinds/lines/module/path; all 13
  public entries matched the public cache and `LEAN_API.md`. The public cache
  deliberately excludes private helpers; the complete lexical index includes them.
- `scripts/formal_tools.py lint` exited 1 on five concurrent foreign omissions:
  BiScaleUncertainty `AffineFourierCorrelation`, `DivisorSieveAffineSpectrum`;
  BezoutValuationIncidence `DilatedCellScalingAndSecondOctaveFermiJumpBridge`,
  `EndpointHaarCellDecompositionAndWitnessPronicTransfer`,
  `PowerDampedPronicMultiplicativityAndRoutePMBridge`.
  There were 381 unrelated large-file warnings, no finding in this leaf, and no
  proof-debt finding. This is not a repository-wide passing gate.
- Field inventory at verification: 17 leaves, 14 wired. The three foreign field
  leaves above remain untouched. Every declaration statement in the two leaves
  added during this turn was inspected; their cell/pronic transfer results do not
  duplicate this return-window classification.
- No computations or numerical experiments. All paper identities and endpoints
  were proved symbolically. Serena rejected the leaf as ignored; targeted patches
  were used without changing ignore settings.
- Guarded cleanup removed all 18 owned temporary paths. Source and installed
  artifact hashes remained unchanged; all owned jobs are terminal.

## Open continuation and counting boundary

The arbitrary-phase conjecture is now isolated at
`docs/drafts/pipeline/0-backlog/bvi-arbitrary-phase-observation-horizon-2026-10-18.md`.
It remains unproved and is not retired. A matching uniform upper bound must not
receive separate credit for the lower-bound/classification package counted here.
No positive claim depends on that conjecture.

## Gates

- [x] Well-posed statement and local corpus/novelty audit, with partial coverage disclosed.
- [x] Dependency-closed paper proof of the exact common-return package.
- [x] Exact Lean source/axiom audits, wiring, exhaustive index and scoped verification.
- [ ] Publication-ready standalone exposition.
