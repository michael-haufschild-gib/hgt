# EDQ Möbius current growth beyond every logarithmic power

Stage: 3-formalized. Dependency-closed paper proof and new-declaration Lean audit complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: transport the corpus's arbitrary logarithmic harmonic Möbius saving to expanding source windows and the complete chronological current. RH remains open.

## Paper proof

Keep the literal coefficients, prefixes P_N(s,K), and all-cross current Q_N(s)
of EulerDeletionMobiusCurrentEscape. Write H_N for the ordinary harmonic
Möbius sum and a=2 Re(s)-1. The exact initial-window formula is
P_N(s,K)=H_N sum_(n=1..K) n^(-s)-1 for 1≤K≤N.
When Re(s)>0, each kernel has norm at most one, so
norm(P_N(s,K)+1)≤K abs(H_N).

The corpus proves (log N)^m H_N→0 for every natural m. Put
K_m(N)=floor((log N)^m). Eventually K_m(N)≤N; moreover, simultaneously
for every 1≤j≤K_m(N), norm(P_N(s,j)+1)≤1/2 and norm(P_N(s,j))≥1/2.
This is uniform control of a growing source window, not an exchange of
the two endpoint limits.

At an actual right-half zero a>0 and every reflection-weight increment is
nonnegative. The complete current dominates the finite Gram head, hence
Q_N(s).re≥((K_m(N)+1)^a-1)/4. Since K_m(N)+1≥(log N)^m,
choose m with ma≥q+1 to obtain Q_N(s).re≥((log N)^(q+1)-1)/4
eventually, for any fixed natural q. Therefore Q_N(s).re/(log N)^q→+∞.
Reflection reverses the full current with the same coefficients; its
absolute real part divided by (log N)^q tends to +∞ at every off-line zero.
Every current vanishes identically at critical-line points.

Thus critical-line location is equivalent to existence of a finite logarithmic
power ceiling on arbitrarily late current values. The exponent, constant, and
subsequence may depend on the zero. Universally this is an exact RH receiver.
The independent arithmetic ceiling is not proved or assumed here.

## Corpus basis and remaining producer

EulerDeletionMobiusCurrentEscape supplies the exact source prefix and full
reflection reversal. EulerDeletionMixedCurrentGram supplies the finite-head
bound on the complete current. Sieve/MoebiusHarmonicArbitraryLogRate supplies
the unconditional arbitrary logarithmic decay. BurnolPrimeLogSummability
supplies eventual logarithmic-power domination by a positive power.

MobiusDivisorAbelDiagonalBound estimates a different dilation-channel diagonal;
MobiusSignedSchurTransferPaper controls a safely damped probability source.
Neither inspected estimate supplies an upper bound for this complete growing
chronological current. No transfer identifying those sources has been proved.
The positive result is uniform persistence of the arithmetic unit defect on
growing windows and the resulting quantitative full-current escape. No route
is retired and no off-line zero is asserted to exist.

## Formal certificate

Leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusLogGrowth.lean`
(183 lines; eight public theorems, one definition, three private helpers).
Namespace: `RHTower.DeletionMobiusLogGrowth`.

- `logWindow`: the actual natural floor of a logarithmic source window.
- `sourcePrefix_error_le`: exact-source error bounded by K abs(H_N), uniformly throughout 1≤K≤N for every positive-real-part source parameter.
- `logWindow_le_eventually`: each fixed logarithmic window eventually lies in the exact divisor-inversion region.
- `sourcePrefix_logWindow_uniform`: one cutoff simultaneously gives error at most 1/2 and prefix norm at least 1/2 throughout the growing positive window.
- `sourceCurrent_logWindow_lower`: its telescoping quarter-weight lower bound on the complete actual current at a right-half zero.
- `sourceCurrent_div_log_pow_tendsto`, `abs_sourceCurrent_div_log_pow_tendsto`: the current, respectively absolute real current, divided by every fixed logarithmic power tends to positive infinity at right-half, respectively off-line, zeros.
- `sourceCurrent_cofinally_log_bounded_iff`: a logarithmic ceiling on arbitrarily late actual current values is equivalent to critical-line location at a zero.
- `riemannHypothesis_iff_mobius_current_cofinally_log_bounded`: exact equivalence with Mathlib's original RH. The exponent, real bound, and cofinal subsequence may depend on the zero.

Final scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_mobius_log.lean`,
exit 0, no diagnostics. Final leaf audit:
`LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionMobiusLogGrowth`,
exit 0; only the new leaf rebuilt (8.0 seconds). All dependencies cached/replayed.
One umbrella import added; no full or umbrella build.

New-only axiom audit: `lake env lean /tmp/edq_mobius_log_axioms.lean`, exit 0.
All nine public declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; their dependency closure covers all three private helpers.
No added axioms, admissions, numerical premises, or external computation certificates.

The logarithmic ceiling itself remains unproved. RH is neither proved nor
falsified, and no route is retired.

## Repository checks and cleanup

Repository lint ran once and failed solely on an unrelated unwired module:
`GaloisForLFunctions.RHTower.MobiusDivisorPositivePrimeSupply`.
Existing file-size warnings also remain. This new leaf is wired exactly once.
Scoped source equality, whitespace, links, declarations, new-axiom contents,
and absence of owned Lean/Lake processes passed. Search index refreshed once;
exact no-refresh search retrieves the new cofinal logarithmic RH criterion.
All three owned scratch Lean sources were removed. No owned Lean or Lake process
remained. Logs retained under `/tmp/edq_mobius_log` with `.api.log`, `.check.log`,
`.build.log`, `.axioms.log`, `.lint.log`, and `.index.log` suffixes.
