# CCM-FU: accumulated interaction charge

- Type: derived diagnostic for the unchanged uniform energy / RH target.
- Status: exact accounting and sharp two/three-coordinate boundary closed in
  Lean; frozen diagnostic completed. Accumulated-charge and full-head bounds open.
- Chain: actual divisor source → complete quadratic raw-energy order →
  O(M) Abel bound → CCM-FU → RH. Frontier map read only.

## Exact accounting: paper and Lean closed

For the full current field let `D(P)=sum_R |R| F_R(P)^2`. If `q` is an
unprocessed prime, write `G_R=F_(R union {q})` over labels avoiding `q`.
The literal merger gives

`D(P+q)-D(P)=2 sum_R |R| F_R G_R - sum_R G_R^2`.

The second term is the complete copied-child square energy `W_q`.
The first is the signed interaction charge `J_q`; no cofactor is omitted.
Thus every complete history satisfies `D_k=D_0+sum_(j<k)J_j-sum_(j<k)W_j`.
The equalities are proved in `RHTower.MobiusDivisorArityCharge`, for every
finite prime history, even with repeated insertions. A nonpositive
accumulated charge would budget all copied-child squares by the initial
arity energy. That sign is not assumed or proved.

Proof: split the full label cube into labels avoiding `q` and their
`q`-insertions. For an avoiding label of size `k`, its old contribution
is `k F_R^2+(k+1)G_R^2`; its new contribution is `k(F_R+G_R)^2`.
Subtracting gives `2k F_R G_R-G_R^2`. Summing and telescoping proves
the identity, retaining every cofactor. Nonnegativity of the final `D`
gives `sum W <= D_0+sum J`.

The actual support law also gives `D(P) <= floor(log_2 M) Q(P)` uniformly
in the entire processed core: a nonzero label has prime product below
`M`, hence `2^|R| < M`. The existing unconditional initial square bound
then yields `D_0 <= 722 M^2 floor(log_2 M)`. This is a proved logarithmic
loss, not the required uniform quadratic ceiling.

The arity weight can decrease when unweighted nonempty energy increases:
for two remaining coordinates it is `a^2+b^2+2c^2`, and the sum of its
two next increments is `-(a-c)^2-(b-c)^2`. Thus some next move is
nonincreasing. This is sharp as a dimension boundary: on three coordinates
the least next arity energy has sharp universal upper factor `4/3`.
Indeed, the sum of the three next energies equals four times the current
energy minus weighted squares of adjacent-label differences. All seven
nonempty coefficients equal to one attain the factor in every direction.
This is a generic signed-field theorem, not an actual divisor-source
counterexample. Both the positive factor bound and its optimality are
closed in Lean.

## Results and remaining mathematical obstacle

The eight saved complete histories all retained `D <= D_0` and negative
accumulated charge at every nonempty prefix in the floating screen.
Nevertheless every history contains positive `D` increments. The frozen
80-digit audit selected the first such increment: `M=512`, increasing
policy, index 16, prime 71. It gives `J=1.0837435393530826`,
`W=0.9873787519222513`, hence `Delta D=0.09636478743083128`, while raw
energy decreases from `35.86162828179455` to `35.82952133717677`.
Every signed cofactor is retained in the audit. These numerical observations
are not formal inequalities or all-cutoff evidence.

The unresolved task is an arithmetic bound for accumulated signed charge
through a complete interacting-prime order, with actual compensator
availability and exhaustion controlled. Even a nonpositive charge bound
alone would not finish this route: arity energy assigns weight zero to
the head and is identically zero after complete processing, whatever the
head value. A proof must recover a uniform bound for that signed head
and handle the initial logarithmic cost. Neither step is established here.
The raw selector and RH remain open; no route is retired.

The [computation archive](../../../2-fully-proven/computations/ccm-fu-arity-charge-2026-09-08/README.md)
records the frozen replay, independent audit, exact provenance and limitations.

## Formal validation

`MobiusDivisorArityCharge.lean` contains five definitions and fourteen
public theorems, with no added axioms or computational premises. All fourteen
new theorems were audited once: only `propext`, `Classical.choice`, and
`Quot.sound`. Scratch and installed-source `lake env lean` checks passed.
The final `lake build GaloisForLFunctions.RHTower.MobiusDivisorArityCharge`
compiled a byte-identical leaf in a cache-only audit package in 28 seconds;
existing dependencies were reused. The module is wired into `RHTower.lean`.
No umbrella or full build ran. Corpus index refreshed; formal lint passed.

## Frozen diagnostic protocol (executed unchanged)

- Replay the eight saved complete fixed-late-greedy histories at
  M=512,2048,8192,32768. No new policy, random seed or cutoff.
- Reconstruct source using the unchanged source generator. Check every
  replayed raw energy against the saved value. Derive `D`, `W`, `J` from
  all literal incidences, then regroup each selected successor directly.
- Record every prefix `D`, step `W`, step `J`, cumulative `W` and `J`.
  Test separately whether every `D` step is nonincreasing and whether
  cumulative `J` stays nonpositive. Positivity tolerance:
  `1e-10 max(1,D_0)`.
- A violation of either auxiliary comparison does not refute a uniform
  bound for `D`, the raw selector, or RH. A pass at four cutoffs proves
  none of these all-cutoff statements. The experiment is discriminating
  because raw energy and label counts do not determine the new charge.
- Four independent cutoff workers on the supplied RunPod; BLAS, OpenMP,
  MKL each one thread. Internal deadline 90 seconds, outer timeout
  100 seconds. Preserve completed cutoff records. No extension in this run.

## Frozen independent audit protocol (executed unchanged)

If accumulated `J` crosses zero, choose its first crossing at the smallest
cutoff, increasing policy first on a tie. Otherwise choose the first
positive `D` step in that order. If neither occurs, choose the first step
whose selected packet has a nonzero nonscalar child, at the smallest
cutoff and increasing policy first.

At the selected state reconstruct original time-sum coefficients with
independent factorization at 80 digits; verify full `D`, `W`, `J`, its
direct successor and every signed cofactor contribution. If selection
used an accumulated-charge crossing, also replay the entire selected
prefix at that precision. At most four workers, 90-second internal and
100-second outer limits. Preserve partial output if an audit exceeds its
limit; do not silently change the selection. Floating outputs are not
interval certificates and never become Lean premises.

All scripts and results go under the required computation archive. Remove
owned remote files and processes after verified download. No new primary
conjecture is introduced; scientific-method protocol was read first.
Broad corpus searches used `--any` for balancing, martingales, pair
cancellation, symmetric differences, degree energy and arity. The exact
pair expansion is already `subsetLabelEnergy_eq_pairs` in
`UniformPrimeSubsetEnergy`; it alone gives no signed bound.
