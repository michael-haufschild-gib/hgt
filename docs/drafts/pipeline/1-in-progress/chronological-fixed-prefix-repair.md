# Fixed-prefix chronological repair — frozen test

Original [R] remains unchanged and open. This test asks whether finite bounded
repair can preserve early Möbius coefficients while reoptimizing the tail.
Earlier reset/deletion experiments did not reoptimize and cannot answer this.

**Protocol [D], frozen before results.** At N=128,256,512 fix a_k=μ(k) for
k≤m, with distinct m in {4,8,16,floor(sqrt(N)),N/4}. Optimize remaining
coefficients in [-C,C], C=1,2. Compare feasible vectors from active-set least
squares and cancellation of leading singular modes. Retain stronger-prefix
vectors as candidates for weaker prefixes and C=1 vectors for C=2. Also retain
zero-padded smaller-N vectors when the same fixed prefix applies. Score the
actual residual on training and independently shifted quadrature meshes,
including controlled end tails. Check selected vectors at 80-digit precision.
All computations run on the authorized Runpod; none enter Lean.

This is a finite diagnostic, not a convergence conjecture or certified
optimization. A worse constrained fit is only an upper bound unless accompanied
by a valid lower bound. In particular, solver failure is not mathematical
infeasibility. The known unconditional logarithmic floor forbids extrapolating
apparent finite power-rate decay indefinitely.

**Independent analytic question [E].** Does every uniformly bounded array with
full L² error tending to zero satisfy a_(k,N)→μ(k) for each fixed k? Proposed
route: separate the harmonic moment Σa_k/k from the exponentially convergent
Bose series, pass to compact coefficient limits, then use Lambert uniqueness.
This is not yet proved or formalized. If true, fixing any *finite* prefix has
no asymptotic cost, by replacing its vanishing coefficient deviations; choosing
a growing prefix still requires a quantitative estimate.

**[D] result, independently validated.** At N=512, m=128,
C=1, retained tail gives measured full error 4.3471e−9, versus 4.1182e−9
for the earlier unrestricted vector. A proportional exact prefix is feasible
at this scale; the earlier reset ablation did not reveal a necessary rewrite.

**Follow-up [D2], frozen before extension data.** Test the same quarter-prefix
constraint at N=1024,2048,4096 using the singular-mode construction, C=1,2.
The purpose is to seek the breakdown of the apparent power rate near the known
logarithmic floor. Compare with the bound using a numerically evaluated first
critical zero for guidance only. Validate retained vectors on shifted quadrature
and at 80 digits; resolve errors near floating-point cancellation before any
interpretation. This extension supplies neither a certified optimum nor a proof.

**Follow-up [D3], frozen before data.** At N=4096, keep only m=16 or m=128
coefficients fixed, with C=1. Compare with the quarter-prefix m=1024 result.
Use both exact singular-mode cancellation and balanced higher-mode residuals.
This tests repair-window width after the quarter-prefix fit's measured decay
slowed; it does not extrapolate a fixed-prefix test to a growing-prefix theorem.

**[D3] measured result.** At N=4096, C=1, retained errors are 3.50601e−10
for m=16 and 4.18541e−10 for m=128, versus 8.71476e−10 for m=1024.
Widening the adjustable tail improves these finite constructions. Independent
quadrature, 63-bit-mantissa profiles and 80-digit spot checks agree. The largest
logarithmic-frequency peaks are 14.10 (m=16) and 14.125 (m=128), near the first
zero ordinate 14.1347; no zero data entered fitting. The known Mellin invariant
is reproduced to relative errors below 6.1e−7. This is an expected spectral
constraint, not zero localization, optimality or an asymptotic theorem.

**Named missing estimate.** In the actual Hilbert space set
f_m=e^(−t)+Σ_(k≤m)μ(k)h(kt) and T_(m,N)x=Σ_(m<k≤N)x_k h(kt).
For an orthogonal projection P onto selected singular modes, exact cancellation
P(f_m+Tx)=0 gives the elementary upper bound
||f_m+Tx||≤||(I−P)f_m||+sqrt(N−m)||((I−P)T)|| when |x_k|≤1.
The open source problem is to prove *both* bounded-coordinate feasibility and
vanishing of this full remainder for one growing sequence of cutoffs and mode
ranks. Numerically feasible fixed ranks do not supply that joint estimate.
This identifies the missing proof; it is not a new formalized result.

All numerical outputs, checks and interpretation are in the compact
[computation report](../2-fully-proven/computations/chronological-fixed-prefix-2026-09-06/REPORT.md).

**Analytic construction attack: averaging cutoffs.** Positive averages of raw
Möbius residuals preserve the coefficient bound one. A tempting argument is to
choose a logarithmic averaging filter that cancels finitely many zero modes,
then use Gamma decay to control higher zeros. The missing dependence is decisive:
in a Perron/Mellin representation a zero contributes N^(ρ−s), with s varying
over the entire integration line, not only N^(ρ−1/2). Cancelling a finite list
of scalar phases does not cancel their moving L² profiles. This attempt does
not establish an estimate. Positive averaging is not retired; its full norm
control remains the original analytic difficulty.

**Analytic constraint now proved.** The [direct raw heat obstruction](../3-formalized/chronological-raw-heat-obstruction.md) excludes raw Möbius convergence and vanishing geometric-response damping. Every successful array must add a correction with cofinally positive L² norm. This permits the tested adjustable tails; it does not establish their all-scale feasibility or convergence. Coordinatewise rigidity [E] remains open.
