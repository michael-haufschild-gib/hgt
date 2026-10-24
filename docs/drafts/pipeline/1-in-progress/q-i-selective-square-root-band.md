# Q-I: selective cancellation at the square-root band

- **ID:** q-i-selective-square-root-band
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-2410/opus.md, §3 Q-I
- **Statement:** Find and unconditionally formalize a Beurling-selective, single-zeta estimate giving a fixed power saving at the square-root band, including its mathematical consequences and corpus applications.

## Goal

Resolve the fixed-strip question itself. A shrinking Vinogradov–Korobov band, a conditional
transfer theorem, an equivalent formulation, or a restricted no-go does not constitute a full
answer. The report identifies the target with `zetaZeroAbscissa < 1`. Audit that identification
against the actual declarations before applying it. Do not use the `hgtl7` skill or numerical
experiments. Preserve pre-existing worktree changes.

## Gates

- [x] Read the complete source report and task attachment; inspect repository instructions.
- [x] Search the Lean corpus before consulting mathlib.
- [ ] Establish a dependency-closed paper proof of an answer to Q-I.
- [ ] Formalize the exact answer and all derived corollaries without unproved analytic inputs.
- [ ] Apply the result in the relevant receiver, short-window, band, and source programmes.
- [ ] Check every new leaf with `lake --old env lean`; audit transitive axioms; wire umbrellas.
- [ ] Completion audit against the full original task, not intermediate milestones.

## Current evidence

- `CompletePronicVaughanCalibration.lean` gives the exact 25-entry signed Gram expansion,
  logarithmic source cancellation, a nonsummable logarithmic majorant, and a uniformly bounded
  difference between the interior and centered-source energies.
- The fifth Vaughan component is independent of both cutoffs and equals the negative pole
  density times the horizon, plus a bounded active correction. Thus individual Gram entries
  contain pole mass before cancellation. Any estimate of their absolute sizes must account for
  this source-defined linear term.
- Existing uncommitted files include work on the balanced statistic and Biarithmetic Geometry;
  those are separate work and must not be overwritten.

## Conjecture loop

1. **Audit the quantitative Class III target.** Determine the unavoidable leading pole part of
   the Vaughan Gram and whether the actual source already forces large negative mixed energy.
   Seek an exact positive decomposition identifying the residual estimate after pole removal.
2. **Test restricted-source estimates.** Use the resulting decomposition to locate a genuinely
   selective estimate, rather than a bound on an entry whose linear growth is forced.
3. **Transfer only proved savings.** Check implications across the receiver, Möbius windows,
   prime windows, and band compression. Record unresolved analytic inputs explicitly.

## No-go closure

No route retired. A failed conjecture requires a strongest non-trivial positive survivor,
paper proof, and Lean proof when dependency-closed. Failure of one estimate is not a negative
answer to Q-I.

## Paper proof: pole mass and normalized mixed cancellation

[PROVED HERE; Lean pending] Write `ρ = Re(1/ζ(1+ε)) > 0`, `a_n` for the active
correction, and `I_n` for the interior prefix. For every `ε > 0`, the source mean theorem
gives `I_n/n → 0`, since the centered divisor prefix is `o(n)` and `|a_n| ≤ 1/2`.
Cesàro averaging then gives `E_T^int/T → 0`. This uses absolute convergence at `1+ε`,
not a zero-free strip or even a quantitative PNT.

For every pair of Vaughan cutoffs, the last component is `p_4(n) = -ρn-a_n`. Hence
`G_44/T → ρ²`. More explicitly, `(ρn+a_n)² ≥ ρ²n²/2 - 1/4`, and
`n/(n+1) ≥ 1/2` for `n≥1`, so

`G_44 ≥ ρ²T/4 - 1/4`.

The full diagonal `D_T = Σ_i G_ii` dominates `G_44`, uniformly in cutoffs. Since
`E_T^int = D_T + R_T^mix`, it follows that `R_T^mix/D_T → -1`, uniformly over all
cutoff choices, even choices varying with `T`. Thus arbitrarily high *relative* cancellation
of the uncentered Vaughan diagonal is already unconditional. It does not establish bounded
energy: the unnormalized error is exactly `E_T^int`.

The positive survivor is an explicit scale calibration: the diagonal contains linear pole
mass and only the residual cancellation rate, rather than a fixed relative gap, can carry
the requested zero-free information. This is not a negative answer to Q-I.

### Exact obstruction for individual cross entries

[PROVED HERE; Lean pending] The sum of the pole row is the pronic pairing of `p_4`
with `I`. Divided by `T`, that pairing tends to zero by the same Cesàro argument.
Subtracting `G_44` therefore gives

`(G_40 + G_41 + G_42 + G_43)/T → -ρ²`.

This sum is exactly independent of both cutoffs. Hence no cutoff schedule can make every
one of these four entries `o(T)`. This refutes a specific proposed absolute-entry estimate;
it does not refute Q-I or prove that all Class III identities are insufficient. The strongest
positive survivor is the exact negative linear density together with uniform relative
cancellation and the exact residual identity.

The ratio here is `R_mix/D` for the uncentered Vaughan diagonal, whose pole contribution
has order `T`. It is not THIM's long-sawtooth/tail Cauchy–Schwarz ratio at order
`T^(1-2ε)`. The latter's strict gap remains open in the report's interior region.

Draft module: `formal/GaloisForLFunctions/BezoutValuationIncidence/TheVaughanDiagonalContainsLinearPoleMass.lean`.
Main names: `pmPronicVaughanDiagonal_linear_lower`,
`tendsto_pmPronicVaughanGram_pole_div_nat`,
`tendsto_pmPronicVaughanPoleMixed_div_nat`,
`not_all_pmPronicVaughan_pole_cross_entries_sublinear`,
`eventually_pmPronicVaughan_relative_cancellation`, and
`tendsto_pmPronicVaughan_mixed_div_diagonal`.
First complete leaf check is running; no successful kernel audit is claimed yet.

### Next conjecture after pole calibration

Center the individual finite-cutoff small Vaughan legs at their own linear densities. Their
remaining floor errors are bounded and therefore have finite pronic energy. Determine the
remaining large-leg cancellation without dropping its signed cross terms. Search already found
the Type-II short coefficient identity and finite-row receiver calculus; no new selective
residual estimate has yet been established. This is an attack direction, not a claimed theorem.

## External calibration

Guth–Maynard, [*New large value estimates for Dirichlet polynomials*](https://arxiv.org/abs/2405.20552),
states the `30/13` zero-density estimate and `17/30` short-interval consequence. Its stated
density exponent is positive for a fixed `σ<1`; that bound alone does not make the zero count
vanish. The existing corpus already incorporates these results. No external theorem is assumed
in the new pole-calibration proofs.

## Log

- 2026-10-25 — Created after reading the attachment and report, checking the worktree, and
  searching the corpus. Full Q-I remains open.
