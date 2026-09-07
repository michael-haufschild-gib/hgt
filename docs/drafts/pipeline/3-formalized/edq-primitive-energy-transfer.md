# EDQ arithmetic primitive and critical energy transfer

Stage: 3-formalized. Dependency-closed paper proof and new-declaration Lean audit complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: bound the complete Möbius chronological current by a literal arithmetic primitive energy at the critical weight, without deleting cross terms or assuming an RH-strength estimate.

## Source identification

For the actual finite Möbius coefficients, write a_N(n) for the unweighted
deletion stream and A_N(K)=sum_(n<K) a_N(n). Summing each deletion stream
telescopes its modular residue. Thus A_N(K) is exactly the negative of the
corpus's bdMobiusModularApproximant N K at every K, including beyond N.
This is the full source, not just its expanding initial window.

For kernel b_s(n)=(n+1)^(-s), finite Abel summation gives
P_N(s,K)=A_N(K)b_s(K)+sum_(n<K) A_N(n+1)(b_s(n)-b_s(n+1)).
The primitive is bounded for each fixed N. At an actual zero, P_N(s,K)→0,
so the complete Abel series is zero, and
P_N(s,K)=A_N(K)b_s(K)-sum_(n>=K) A_N(n+1)(b_s(n)-b_s(n+1)).
All infinite series used here are norm summable.

## Critical Hardy–Schur transfer

For 1/2<sigma<1, the kernel increment is bounded by a constant depending
on s times (n+1)^(-sigma-1). The reflection-weight increment is bounded
by a constant depending on sigma times (k+1)^(2sigma-2).
Put B_n=abs(A_N(n+1))/(n+1). The normalized tail is bounded by the
positive triangular kernel
T_(k,n)=[k<=n](k+1)^(sigma-1)(n+1)^(-sigma).

With Schur weight w_n=(n+1)^(-1/2), its row and column bounds both reduce
to the positive gap delta=sigma-1/2. The row uses the convergent power
tail and the column the integrable power head. Weighted Cauchy–Schwarz
then bounds the full squared output by C_sigma times sum B_n^2.
Finite sums are bounded first; their limits are taken only after the
relevant norm summability or nonnegative monotone bound is established.

Consequently the actual full current at a right-half zero obeys
Re Q_N(s)<=C_s sum_(n>=1) A_N(n)^2/n^2. Reflection gives the analogous
absolute bound for off-line zeros. The arithmetic energy is at most twice the squared norm of the existing
full modular approximant carrier vector.
A cofinal logarithmic ceiling on this complete arithmetic energy would
therefore supply the current ceiling in EulerDeletionMobiusLogGrowth and RH.
That ceiling remains a producer to prove, not a premise discharged here.

## Corpus evidence and limits

EulerDeletionMobiusCurrentEscape and EulerDeletionMixedCurrentGram provide
the literal source, endpoint-zero theorem, and exact complete current energy.
BaezDuarteMobiusPrefixApproximation and StepFunctionCarrier provide the full
modular primitive and its weighted carrier norm. GaussSpikeMass supplies
the power-head estimate; PowerSeriesTailBound supplies the power-tail estimate;
WeightedSchurTest supplies the corpus pattern for a weighted finite-kernel bound.

The raw modular error norm is already proved not to converge to zero in
BaezDuarteMobiusCriticalTailObstruction. No such convergence is required by
the proposed logarithmic ceiling. No full energy ceiling has been found in
the inspected corpus. A pointwise Cauchy bound alone leaves a divergent
harmonic sum, so the critical weighted Schur step must remain intact.

## Formal certificate

Two leaves, both wired exactly once into the theorem-area umbrella:

- `formal/GaloisForLFunctions/RHTower/EulerDeletionPrimitiveHardy.lean` (233 lines): namespace `RHTower.DeletionPrimitiveHardy`; three definitions, three public theorems, six private helpers.
- `formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusPrimitiveEnergy.lean` (366 lines): namespace `RHTower.DeletionMobiusPrimitive`; four public definitions, eleven public theorems, eight private helpers.

The Hardy leaf provides `tailKernel`, `schurConstant`, and `tailTransform`.
`finite_tail_energy_le` bounds every rectangular finite section independently
of both cutoffs. `summable_tail_row` gives ordinary summability of each full
row for a nonnegative square-summable input. `tail_energy_summable_le` gives
summability and the complete infinite output-energy bound.

The application provides the actual `primitive`, `normalizedPrimitive`,
`primitiveEnergy`, and explicit `currentEnergyConstant`.

- `primitive_eq_modular`, `norm_primitive_le`: exact global identification with the negative modular Möbius approximant and its full-path bound at each cutoff.
- `summable_normalizedPrimitive_sq`: genuine summability of the full arithmetic input energy.
- `sourcePrefix_abel`, `sourcePrefix_abel_tail`: exact finite formula retaining the endpoint and exact full terminal-tail formula at each actual zero. The private Abel-series proof supplies norm summability before taking its limit.
- `scaled_sourcePrefix_le`: normalized actual source prefix bounded by its critical primitive input plus the complete positive Hardy tail.
- `sourceCurrent_le_primitiveEnergy`: at a right-half zero, the full current is at most `2*(2 Re(rho)-1)*(1+norm(rho)^2*(1+1/(Re(rho)-1/2))^2)*E_N`.
- `primitiveEnergy_le_two_modular_norm_sq`: the complete arithmetic energy is at most twice the squared norm of the existing full modular carrier vector.
- `exists_current_bound_by_primitiveEnergy`: every actual zero has a positive transfer constant, independent of channel cutoff, controlling the absolute real current by E_N. Reflection and the identically zero critical-line current are included.
- `riemannHypothesis_of_cofinally_log_bounded_primitiveEnergy`, `riemannHypothesis_of_cofinally_log_bounded_modular_norm`: source-only sufficient ceilings, allowing logarithmic growth on a cofinal subsequence. Neither ceiling is proved, and no converse from RH to either ceiling is claimed.

Final scratch checks used `LEAN_NUM_THREADS=1 lake env lean` on the two owned
scratch files; both exited 0 with no diagnostics. Targeted leaf audits used
`LEAN_NUM_THREADS=1 lake build --old` on each named leaf. Both exited 0; only
the respective new leaf rebuilt (3.8 seconds and 9.5 seconds). All other
dependencies were cached/replayed. No full or umbrella build occurred.

One new-only `#print axioms` scratch audit covered all 21 public declarations
across both leaves. It exited 0. Every declaration depends only on `propext`,
`Classical.choice`, and `Quot.sound`; dependency closure covers all 14 private
helpers. No added axioms, admissions, numerical premises, or external computation
certificates. The sufficient RH implications retain their explicit, unproved
source-ceiling antecedents.

No numerical experiment was needed or run. Any future justified numerical
experiment must follow the user's RunPod-only, multicore, bounded-runtime and
results-documentation requirements.

## Repository checks and cleanup

Repository lint ran once and failed solely on the unrelated unwired module
`GaloisForLFunctions.RHTower.MobiusDivisorMiddleChildHead`; existing file-size
warnings also remain. Both new EDQ leaves are wired exactly once. Scoped
source comparison, line counts, links, forbidden declarations, targeted build
contents, all 21 axiom reports, and owned-process checks passed. Final formatting
removed seven trailing spaces in the Hardy leaf only; proof tokens and line
numbers are unchanged, so no redundant proof build or axiom audit was run.
The search index was refreshed once; exact no-refresh search retrieves the
full-current transfer theorem. All five owned scratch Lean sources were removed,
and no owned Lean or Lake process remained. Logs are retained under
`/tmp/edq_primitive_hardy` (`.api.log`, `.check.log`, `.build.log`) and
`/tmp/edq_primitive` (`.api.log`, `.check.log`, `.build.log`, `.axioms.log`,
`.lint.log`, `.index.log`).
The arithmetic energy ceiling is still open. RH is neither proved nor falsified,
and no route is retired.
