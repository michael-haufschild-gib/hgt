# Weighted Möbius Mellin interchange and actual finite sources

**Lean complete for this component.** Eight public declarations in
`formal/GaloisForLFunctions/RHTower/ChronologicalWeightedMellin.lean`.
This is a dependency of the fixed-tail obstruction, not its full formal proof
and not an RH proof.

For w:ℝ→ℂ define the actual source S_w(t)=Σ_(n≥0) μ(n)w(nt). Lean proves:

- If Re s>1 and w has an absolutely convergent Mellin integral at s, then
  S_w also does, and M(S_w)(s)=M(w)(s)/ζ(s). Convergence is proved before
  the sum/integral interchange, using the exact dilation law for integral norms
  and summability of |μ(n)|n^(−Re s).
- If w vanishes beyond θ and θ<(N+1)t with t>0, then S_w(t) is exactly
  its finite sum through N. If θ≥0 and t>θ, the source is zero.
- Measurable w gives measurable S_w. If |w(x)|≤C for x>0, C≥0, and
  w vanishes for x>1, then |S_w(t)|≤2C/t for t>0 and S_w is locally
  integrable on (0,∞).

The Mellin theorem is not an assumption that a continuation represents an
arithmetic source: its conclusion is proved for the displayed infinite sum.
The inverse-time estimate is not the critical half-power estimate.

## Verification

Scratch `lake env lean /tmp/ChronologicalWeightedMellin.lean` passed.
Final requested-leaf audit
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ChronologicalWeightedMellin`
passed; only this leaf compiled, in 42 seconds. The umbrella import is wired;
no umbrella or full build was run.

All eight public declarations were printed through
`/tmp/chronological_weighted_axioms.lean`; the only dependencies are
`propext`, `Classical.choice`, `Quot.sound`. The authoritative formal lint
passed with existing file-size warnings. No numerical result is a proof input.
All owned Lean processes exited.

Audit artifacts: `/tmp/chronological_weighted_manifest.json`,
`/tmp/chronological_weighted_axioms.txt`, `/tmp/chronological_weighted_lint.txt`.

## Remaining exact dependencies

The [fixed-tail theorem](../2-fully-proven/chronological-finite-tail-obstruction.md)
now has its critical Abel boundary limit and analytic continuation for this
actual weighted source in the [weighted-boundary leaf](chronological-weighted-boundary.md).
Heat-transform separation, discrete projection convergence, integer-scale
transfer and the actual residual observation inequality still need Lean proofs.
The [growing-moment source and logarithmic window](../2-fully-proven/chronological-growing-moment-source.md)
also remain paper-only. No failed route has been retired on the strength of
this component.
