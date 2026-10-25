# Escape records realize a faithful moving-origin boundary

- **ID:** escape-records-realize-a-faithful-moving-origin-boundary
- **Stage:** 2-fully-proven
- **Type:** CONJECTURE (Lean completion pending)
- **Parent:** [Q-III](../1-in-progress/q-iii-escape-state-classification.md)
- **Dependency:** [Resetting the moving origin](resetting-the-moving-origin-adds-a-faithful-step-module.md)

## Construction

For the actual prefix `A`, let `a=1-epsilon<1`. Escape means its pronic
energy `E(T)` tends to infinity. If `A(n)^2/n^a` were bounded, comparison with
the convergent power sum `sum n^(a-2)` would pay the receiver. Thus that ratio
is unbounded on escape.

Choose a sequence of prefix record locations `k_m` with record heights
`M_m=|A(k_m)|` and `M_m^2/k_m^a -> infinity`. Such records can be selected
from large values of the ratio: replace an index `n` by a location of the
maximum absolute prefix on `[0,n]`. Its height increases and its location
is at most `n`, so the ratio does not decrease. The resulting heights and
locations tend to infinity after extraction.

At records, `E(k_m)/M_m^2 -> 0`: all earlier prefix values have modulus at
most `M_m`; each fixed coordinate divided by `M_m` tends to zero; the
summable pronic weights dominate the normalized cells. This is a direct
head/tail argument.

Fix any positive `c`. Choose the first horizon `T_m` with
`E(T_m) >= M_m^2/c`. Eventually `T_m>=k_m`. The actual source has
`|A(n)|<=n`, hence each energy jump is at most one. Therefore
`E(T_m)/M_m^2 -> 1/c`, so `A(k_m)^2/E(T_m) -> c` and
`k_m^a/E(T_m) -> 0`.

Take a common cofactor Gram subsequence along these horizons. The already
proved source-power bound kills the recentered translation, and the fixed
step mixed terms vanish weakly. Thus the origin-reset translated rows have
own-normalized Gram

`[K(j,l) + c/max(j,l)]/(1+c)`.

For every `c>0` this is a faithful critical Wiener module with full Bohr
hull. It is a construction conditional only on the actual escape branch,
so the final statement must be admission-or-existence with no added analytic
premise. It does not assert this mixed kernel is an unshifted Möbius
`ActualCofactorLimit` and does not settle that classification.

## Verification obligations

- Search the corpus for an existing record-horizon boundary argument.
- Check exact energy conventions, the source increment bound, and the
  bounded-jump first-crossing estimate.
- Prove record extraction, cofinality and common Gram extraction along the
  constructed horizons without requiring strict monotonicity prematurely.
- Formalize the fixed bounded-row weak-orthogonality lemma and the faithful
  step module before claiming the final boundary construction.
- Audit whether the definition of moving-origin compactification accepts
  reset-only-origin rows; keep it separate from the unshifted source and
  from fully recentered translation.

No numerical experiment, actual escape instance, or zero configuration is
used or claimed.

## Source audit and first Lean drafts

The corpus already proves `abs_receiver_shift_sub_le` from actual centered
increments bounded by one; setting the old origin to zero gives
`|A(n)|<=n`. `TheMaxKernelFormOfTheDampingAutocorrelation` already proves the
pronic telescoping/max-kernel exchange and positivity. These are reused,
not claimed as new. `sum_Icc_rpow_neg_le` supplies the finite power-sum bound
needed to contradict admission from uniformly bounded sublinear square
prefixes.

The following components now passed the combined Lean scratch:

- `/tmp/qiii_receiver_energy_crossings_body.lean`: actual linear prefix
  bound, exact energy increment, jump bound one, and admission-or-existence
  of every positive energy level with overshoot below one.
- `/tmp/qiii_escape_prefix_records_body.lean`: sublinear square-prefix
  bounds imply admission; otherwise arbitrarily large such spikes occur at
  prefix records. Choice yields record origins with square heights tending
  to infinity and `k^a/A(k)^2 -> 0` for each `0<=a<1`.
- `/tmp/qiii_common_limit_along_horizons_body.lean`: common actual Gram
  extraction along any prescribed cofinal horizon sequence.
- `/tmp/qiii_step_gram_body.lean`: exact origin-step cofactor Gram limit.

The normalized record-energy limit, crossing-sequence assembly, bounded-row
weak orthogonality, faithful step/mixed modules and final admission-or-realization
theorem all passed the full boundary scratch with standard axioms. Canonical
leaves are installed and wired. Final direct standalone source checks remain in
[the completion ledger](../1-in-progress/q-iii-existing-findings-lean-completion.md). No actual
escape instance is assumed or constructed.

## Closed construction and horizon convention

To avoid a zero initial record height, cross the positive level
`M_m^2/c+1`. The first crossing `T_m` has overshoot below one, and the energy
used by `cofactorGram epsilon T_m` is `E(T_m+1)`, which differs by at most
one more unit. Hence

`M_m^2/c+1 <= E(T_m+1) < M_m^2/c+3`.

Dividing by `M_m^2 -> infinity` gives `E(T_m+1)/M_m^2 -> 1/c` and therefore
`M_m^2/E(T_m+1) -> c`. Multiplying by the already obtained
`k_m^a/M_m^2 -> 0` gives `k_m^a/E(T_m+1) -> 0`. Monotonicity of finite energy
and divergence of these levels imply `T_m -> infinity`. The record-energy
limit gives `E(k_m)<E(T_m)` eventually, so `k_m<T_m`; thus origins can be
chosen inside their observation horizons.

No sign extraction is needed: `A(k_m)/sqrt(E(T_m+1))` stays bounded in
absolute value, while its square tends to `c`. Each mixed step/receiver
pairing tends to zero, so the signed cross terms vanish even if record signs
alternate. Extract the actual cofactor Gram along the cofinal `T_m` family.
The recentered error and its fixed dilates vanish by the verified uniform
source-power budget with `a=1-epsilon`. This closes the paper construction
of the stated mixed kernel for every `c>0` on the escape branch.

The construction has a dependency-closed paper proof. Canonical source verification remains unfinished; the combined Lean proof
and transitive axiom audit passed. The general record/first-crossing device is not
claimed as a new general analysis theorem; its target is the exact actual
Möbius moving-origin boundary. The original unshifted classification remains
open.
