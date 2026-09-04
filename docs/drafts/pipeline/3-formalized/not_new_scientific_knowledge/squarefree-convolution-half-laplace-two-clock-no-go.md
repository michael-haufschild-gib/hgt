# Squarefree convolution-half two-clock Laplace no-go

- **Stage:** 3-formalized
- **Classification:** not new scientific knowledge; internal route-closure theorem
- **Module:** `GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceTwoClockNoGo`
- **Primary theorem:**
  `not_poleClearedFirstTraceLaplaceTwoClockLocallyBounded_of_weightedDense`
- **Source card:**
  `docs/drafts/pipeline/5-failed/squarefree-convolution-half-laplace-two-clock-no-go.md`

## Statement

Let pole degree `κ_N` and positive heat time `τ_N` be independent.  If `κ_N≥24` eventually,
`τ_N→0`, and

`|τ_N-τ_(N+1)|≤C τ_(N+1)^(16/11)`

eventually, then the explicit pole-cleared two-clock Laplace family is not locally bounded on
`rightHalf`.

## Proof certificate

1. `squarefreeHalfLaplaceTimeSum_boundaryExteriorPoint` identifies the two-clock value at `6/11`
   with the canonical boundary heat profile sample.
2. The degree-`κ_N` pole lower bound is at least one after degree `24`.
3. Local boundedness of the normalized family therefore yields uniformly bounded late heat
   samples, regardless of the growth rate of `κ_N`.
4. The formalized `16/11` weighted mesh escape theorem contradicts those samples.

## Verification

- Direct source check: passed.
- Targeted build: passed (`13036/13036`).
- Umbrella: imported by `GaloisForLFunctions/RHTower.lean`.
- Forbidden declarations: none (`sorry`, `admit`, `axiom`, `opaque`, `unsafe`).
- Explicit `#print axioms` audit of three public theorems: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Repository-wide formal lint still reports unrelated pre-existing/concurrent umbrella failures;
  this module is umbrella-reachable.

## Research consequence

Pole/heat decoupling does not widen the dense-clock frontier.  A surviving literal Laplace family
must use heat gaps escaping every eventual `16/11` density bound, or introduce a source-derived
singular/nonlinear correction.  Neither condition supplies the report's missing scalar.
