# Arithmetic averaging requires a nonvanishing logarithmic scale

**[BRIDGE G0], proved on paper and in Lean.** One leaf build and all twelve
public declaration axiom checks and authoritative lint passed (existing size
warnings only). Only propext, Classical.choice and
Quot.sound occur; no numerical input or additional axiom enters a proof.
Original bounded-array target [R] and general power-damping conjecture [G]
remain open. This theorem excludes only ε_N log N→0.

Put h(t)=1/t−1/(exp(t)−1), R_N(t)=exp(−t)+Σ_(k≤N)μ(k)h(kt), and
D_N(w)(t)=exp(−t)+Σ_(k≤N)μ(k)w(k)h(kt). All norms below are the actual
L²(0,∞) norms; finite residuals belong to that space.

## Exact positive survivor

For w(0)=1, finite Abel summation gives

D_N(w)=w(N)R_N+Σ_(k<N)(w(k)−w(k+1))R_k.

The coefficients sum to one. If w is positive and decreasing, all are
nonnegative. The terminal residual is indispensable. Moreover, whenever
||R_k||₂≤C for every k<N,

||w(N)⁻¹D_N(w)−R_N||₂ ≤ (w(N)⁻¹−1)C.

This is the exact total mass of the normalized earlier-prefix contribution.
The theorem does not assume global boundedness of the raw sequence.

For a triangular family w_N of such weights with w_N(N)→1,

**||D_N(w_N)||₂→0 if and only if ||R_N||₂→0.**

To prove the nontrivial implication, set e_N=w_N(N)⁻¹−1 and
s_N=w_N(N)⁻¹||D_N(w_N)||₂. The displayed estimate supplies both inequalities
between s_N and ||R_N||₂ with error at most e_N C, involving strict earlier
indices only. Existing Volterra induction first obtains one bound for every
raw norm from s_N→0 and e_N→0. The discrepancy then vanishes. Conversely,
raw convergence supplies that bound directly. Multiplication by w_N(N) or
its reciprocal preserves convergence to zero.

## Closed exclusion and scale floor

Choose w_N(k)=exp(−ε_N log k), with ε_N≥0; define w_N(0)=1, consistent
with Lean's log 0=0. These weights are positive, decreasing and at most one.
Consequently |μ(k)w_N(k)|≤1 without any arithmetic hypothesis.

If ε_N log N→0, the terminal weight tends to one, so successful power
damping would force raw convergence. The previously closed raw heat
obstruction rules that out. Thus

**There is no nonnegative schedule with ε_N log N→0 and ||D_N(w_N)||₂→0.**

The positive scale consequence is stronger than merely observing a failed
candidate: every successful nonnegative power schedule has some δ>0 such
that, for every M, some N≥M satisfies ε_N log N≥δ. At those cutoffs at
least 1−exp(−δ) of the Abel mass lies on earlier raw residuals.
This is a cofinal floor, not an eventual lower bound or a schedule-independent δ.
No separate assumption ε_N→0 was needed for this necessary condition.

## Lean certificate

Module `GaloisForLFunctions.RHTower.ChronologicalArithmeticAveraging`,
namespace `RHTower`. Public declarations cover the weighted residual,
finite Abel identity, discrepancy estimate, near-identity equivalence,
arithmetic weights and their bounds, total averaging mass, the closed
`chronologicalArithmeticDamping_no_small_scale`, and
`chronologicalArithmeticDamping_scale_floor`.

Scratch check: `lake env lean /tmp/ChronologicalArithmeticAveraging.lean`.
Final audit: `LEAN_NUM_THREADS=1 lake build --old
GaloisForLFunctions.RHTower.ChronologicalArithmeticAveraging`, exit 0;
only the requested leaf compiled, in 8.5 seconds. Its umbrella import is wired;
no umbrella or full build ran. Audit artifacts:
`/tmp/chronological_arithmetic_{manifest.json,axioms.lean,axioms.txt,axiom_summary.json,build.txt,lint.txt}`.

[Current source problem and limitations](../1-in-progress/chronological-arithmetic-averaging.md).
The finite convex-average experiments are exploratory evidence and do not
establish a sequence of vanishing full norms.
