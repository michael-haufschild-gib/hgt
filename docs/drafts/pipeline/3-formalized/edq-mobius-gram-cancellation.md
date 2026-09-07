# EDQ complete Möbius Gram cancellation

Stage: 3-formalized. Dependency-closed paper proof, targeted Lean build, and new-only axiom audit complete.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: isolate the complete signed arithmetic term after proving a logarithmic diagonal ceiling for the actual modular carrier.

## Source and paper proof

Write G(m,n)=bdGram(1/m,1/n). The exact source identification in
BaezDuarteMobiusPrefixApproximation and the quadratic-form identity in
BaezDuarteGram give
norm(raw_N)^2 = D_N + X_N,
D_N = sum_(1<=m<=N) mu(m)^2 G(m,m),
X_N = sum_(1<=m,n<=N, m!=n) mu(m)mu(n)G(m,n).
The off-diagonal sum is over ordered pairs and retains every pair.
It is not replaced by the sum of absolute values.

The discrete series in BaezDuarteGramDiscrete gives a sharper diagonal bound
than the existing log(m)/m estimate. Every term is at most 1/m^2, using
(n+1) mod m <= n+1, and also at most 1/((n+1)(n+2)), using the residue
bound by m. Split each finite section at m: its head is at most 1/m,
and the remaining telescoping tail is at most 1/(m+1). Passing to the
already established Gram sum gives G(m,m)<=2/m. Since abs(mu(m))<=1,
0<=D_N<=2*harmonic(N)<=2*(1+log(N)). In particular D_N<=4*log(N)
eventually. This is an unconditional
source ceiling on the complete diagonal, independent of any selected zero.

EulerDeletionMobiusPrimitiveEnergy bounds each actual-zero absolute current
by a positive constant times norm(raw_N)^2. The current escapes beyond every
logarithmic power at an off-line zero. Thus the complete raw squared norm
has the same superlogarithmic escape. The diagonal ceiling then forces
X_N/(log N)^q to tend to positive infinity for every natural q at any
off-line zero. Use norm growth at normalization q+1 and log(N)>=1 to subtract the
complete diagonal while retaining growth at normalization q.

Consequently an independently proved cofinal polynomial-log upper ceiling
on X_N suffices for RH. A cofinal nonpositive X_N would be stronger than
needed. Neither sign nor logarithmic upper ceiling is asserted or assumed
as an unconditional fact. Positivity of the full Gram does not control its
signed off-diagonal sum from above. No converse from RH to this source
ceiling is claimed. No off-line zero is asserted to exist.

## Corpus novelty boundary

This is the raw modular Gram identified by the complete EDQ primitive,
not the different divisor-channel Gram or the normalized Euler-aperture
Hardy Gram. The existing diagonal estimate has a logarithmic loss; the new head/tail
proof removes that loss before aggregating the entries for literal Möbius coefficients and proves that any
hypothetical off-line obstruction must live in aggregate constructive
interference. No numerical experiment is needed for these deductions.

## Remaining producer

Prove a cofinal polynomial-log ceiling on the full signed off-diagonal
source sum, or prove a weaker direct EDQ current ceiling. Neither is yet
closed. The original unconditional RH proof/falsification goal stays active.

## Formalization

New leaf: `formal/GaloisForLFunctions/RHTower/EulerDeletionMobiusGramCancellation.lean`,
namespace `RHTower.DeletionMobiusGram`. Three source definitions and nine public
theorems; one private logarithmic-limit helper. It imports only the existing
primitive-energy application, the discrete Gram module, and Mathlib harmonic bounds.

- `entry`, `diagonal`, `cross`: actual signed Möbius entries and the complete diagonal/ordered cross decomposition.
- `modular_norm_sq_eq_diagonal_add_cross`: exact full carrier identity.
- `diagonal_nonneg`, `gram_self_le_two_div`: positivity and the new individual estimate without the previous logarithmic loss.
- `diagonal_le_two_mul_harmonic`, `diagonal_le_two_mul_one_add_log`, `diagonal_eventually_le_four_log`: complete unconditional diagonal budgets.
- `modular_norm_sq_div_log_pow_tendsto`, `cross_div_log_pow_tendsto`: every hypothetical off-line zero forces positive escape beyond every logarithmic power in the full raw squared norm and in its complete signed off-diagonal contribution.
- `riemannHypothesis_of_cofinally_log_bounded_cross`: a sufficient arithmetic cancellation criterion with its unproved source-ceiling antecedent explicit.

API checks passed. The complete scratch proof passed with one tactical-style
warning; replacing that redundant sequence-focus syntax changes no mathematics.
The targeted command `LEAN_NUM_THREADS=1 lake build --old
GaloisForLFunctions.RHTower.EulerDeletionMobiusGramCancellation` exited 0.
It built the new leaf in 8.2 seconds and refreshed its existing
EulerDeletionPrimitiveHardy dependency in 6.9 seconds; every other dependency
was cached or replayed. No full or umbrella build occurred. The cleaned new
leaf emitted no diagnostics. One new-only `lake env lean` scratch audit
covered all 12 new public declarations. Every dependency list is exactly
`propext`, `Classical.choice`, and `Quot.sound`; closure covers the one private
helper. No old declaration was reaudited. No added axioms, admissions,
numerical premises, or external computation certificates were used.

Repository formal lint ran once and passed; existing unrelated file-size
warnings remain. The module is wired exactly once in the theorem-area
umbrella, which was not built. Scoped whitespace checks passed. One index refresh completed (five changed files, zero removals); exact
no-refresh retrieval finds `cross_div_log_pow_tendsto`. Scoped checks verified
all 192 source lines against the final scratch, the single umbrella import,
links, all 12 axiom closures, forbidden-declaration absence, and exactly the
two expected leaf builds. No owned Lean or Lake process remained.

The three owned scratch Lean files were removed. Logs remain under
`/tmp/edq_gram` (`.api.log`, `.check.log`, `.build.log`, `.axioms.log`,
`.lint.log`, `.index.log`). No numerical experiment, remote computation,
subagent, commit, or push occurred. Future numerical experiments remain
subject to the user's RunPod-only, multicore, bounded-runtime and downloaded
results-documentation rules.

The source cross-sum ceiling remains open. RH is neither proved nor falsified;
no route is retired and the original goal remains active.
