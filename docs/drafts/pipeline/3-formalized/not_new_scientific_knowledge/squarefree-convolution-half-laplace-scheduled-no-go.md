# Squarefree convolution-half scheduled Laplace no-go

- **Stage:** 3-formalized
- **Classification:** not new scientific knowledge; internal route-closure theorem
- **Module:** `GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceScheduledNoGo`
- **Primary theorem:**
  `not_exists_bounded_samples_and_weighted_dense_gaps_of_tendsto_zero`
- **Source card:**
  `docs/drafts/pipeline/5-failed/squarefree-convolution-half-laplace-scheduled-frontier.md`

## Statement

For the canonical squarefree-convolution-half boundary heat profile at `Re(s)=6/11`, let
`τ : ℕ → ℝ` be positive and tend to zero.  Its samples cannot be eventually bounded while its
adjacent gaps satisfy any eventual estimate

`|τ N - τ (N+1)| ≤ C * τ(N+1)^(16/11)`.

Equivalently, bounded samples force escape from every such weighted dense-mesh bound.

## Proof certificate

1. `norm_squarefreeHalfBoundaryLaplaceCoeff_mul_natCast_le` retains the arithmetic boundary decay
   and bounds differentiated coefficients by `(n+1)^(5/11)`.
2. `norm_squarefreeHalfBoundaryLaplaceProfile_sub_le_weighted` integrates that first moment and
   yields the exact heat transport singularity `q^(-16/11)`.
3. `exists_adjacent_heat_mesh_of_tendsto_zero` proves coverage from the first crossing of any small
   heat time; monotonicity is unnecessary.
4. Bounded samples plus bounded weighted transport imply
   `SquarefreeHalfBoundaryLaplaceBoundedAtZero`.
5. Existing Mellin continuation and the nonzero zeta residue at one rule this out.

## Verification

- Direct source check: passed.
- Targeted build: passed (`13035/13035`).
- Umbrella: imported by `GaloisForLFunctions/RHTower.lean`.
- Forbidden declarations: none (`sorry`, `admit`, `axiom`, `opaque`, `unsafe`).
- Explicit `#print axioms` audit of ten public theorems: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Repository-wide formal lint reaches unrelated pre-existing/concurrent umbrella failures; this
  module is umbrella-reachable and was not listed among them.

## Research consequence

Dense heat clocks cannot repair the report's missing analytic half-divisor rung.  Any surviving
Laplace construction must use a clock with unbounded normalized gaps in the arithmetic
`16/11` metric, or abandon eventual sample boundedness.  This is a necessary-condition frontier,
not an RH proof and not evidence that sparse clocks work.
