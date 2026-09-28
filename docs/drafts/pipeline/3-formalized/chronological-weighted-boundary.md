# Critical boundary obstruction for actual weighted Möbius sources

**This component is Lean-complete.** Five public theorems in
`formal/GaloisForLFunctions/RHTower/ChronologicalWeightedBoundary.lean`.
RH, bounded chronological repair [R], and the full fixed-tail geometric
obstruction remain open or awaiting their stated formal dependencies.

Let w:ℝ→ℂ be measurable, bounded on the positive half-line, and zero above
one. Write S_w(t)=Σ_(n≥0)μ(n)w(nt). For every critical zeta zero ρ,

    S_w(t)=o(t^(−1/2)) as t↓0  ⇒  M(w)(ρ)=0.

Consequently, if M(w)(ρ)≠0, there is ε>0 such that every interval (0,δ)
contains t with sqrt(t)|S_w(t)|>ε. This is a cofinal positive height, not
an eventual lower bound. No simplicity assumption on ρ is used.

The proof establishes δ M(S_w)(ρ+δ)→0 directly for locally integrable
sources; jumps at integer cutoffs cause no continuity gap. The low interval
uses the little-o bound and the exact integral of t^(δ−1). The remaining
compact interval has a uniform bound, and the source vanishes beyond one.
The actual Mellin identity from the preceding leaf continues on Re s>1/2
after multiplying by the entire residue unit (s−1)ζ(s). Its derivative at ρ
then forces the weight moment to vanish. The weight and critical-zero
conditions are explicit universally quantified inputs, not assumed RH or
unproved source estimates.

## Verification

- Scratch: `lake env lean /tmp/ChronologicalWeightedBoundary.lean`, passed.
- Final leaf: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ChronologicalWeightedBoundary`, passed; only the requested leaf compiled (4.4 seconds).
- All five public declarations: `#print axioms` in `/tmp/chronological_boundary_axioms.lean`; only `propext`, `Classical.choice`, `Quot.sound`.
- Authoritative `scripts/formal_tools.py lint`, passed with existing file-size warnings.
- Umbrella import wired; no umbrella/full build, numerical proof input, or owned stale Lean process.

Audit artifacts: `/tmp/chronological_boundary_manifest.json`,
`/tmp/chronological_boundary_axioms.txt`, `/tmp/chronological_boundary_lint.txt`.

The [fixed-tail theorem](chronological-finite-tail-obstruction.md) is now
Lean-complete. It uses the quantitative form added to this module:
`chronological_mellin_abel_bound` (a source at most `M t^(-1/2)` has Abel
boundary values at most `M`) and `chronologicalMobiusWeightedSource_norm_mellin_le`
(`|M(w)(ρ)| ≤ M |ζ'(ρ)|` at every critical zero); the little-o theorem above is
its `M → 0` case. No novelty or completed RH-proof claim is made.
