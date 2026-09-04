# Squarefree convolution-half diagonal Laplace no-go

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-PROVED] [AXIOM-AUDITED] [NOT RH]`
- **Module:** `GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceDiagonalNoGo`

## Statement

The explicit pole-cleared diagonal Laplace family is not locally bounded on `rightHalf`:

`not_poleClearedFirstTraceLaplaceLocallyBounded`.

## Mechanism

1. Boundary pole amplification forces geometric suppression of samples at `t_N=1/(N+1)`.
2. Bounded coefficients and a Gamma-controlled exponential first moment bound adjacent reciprocal
   mesh variation by `1+4e`.
3. The full boundary heat profile is therefore bounded near zero.
4. Mellin transform, translation by `6/11`, and entire reciprocal Gamma continue the canonical
   convolution half across `s=1`.
5. Its squared Euler identity contradicts `zetaResidueUnit 1 = 1`.

No coefficient positivity, Selberg--Delange asymptotic, RH assumption, new axiom, or finite-cutoff
boundary term is used.

## Verification

- Direct production check: pass.
- Targeted build: `13034/13034`, pass.
- Umbrella import: wired.
- Public theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
- Repository-wide formal lint: new module is clean and umbrella-reachable; command remains red on
  unrelated pre-existing unreachable modules.
