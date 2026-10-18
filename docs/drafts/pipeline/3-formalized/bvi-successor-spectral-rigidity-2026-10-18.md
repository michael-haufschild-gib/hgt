# Successor spectral rigidity

- **ID:** bvi-successor-spectral-rigidity-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every finite sieve weight, successor energy vanishes exactly on constant responses; maximal negative successor correlation is exactly the parity mode after removal of the constant response.

## Scope and contribution standard

This card belongs to the user goal of 250 significant contributions to Bézout–Valuation
Incidence Mechanics. Count independent mathematical advances, not supporting lemmas,
reformulations, or packages of known facts. No RH work, numerical experiments, added
axioms, unproved analytic premises, or modifications to the field README.

Knowledge ledger: `logs/bvi-root-2026-10-18-knowledge.md`.

## Plan

1. Audit local corpus for diagonalization, inversion, and rigidity results.
2. Prove a complete classification on paper, including all endpoint cases.
3. Formalize new results inside `formal/GaloisForLFunctions/BezoutValuationIncidence`.
4. Audit target modules with `lake env lean`, inspect axioms in `/tmp`, wire umbrella,
   run formal lint, and record only verified contributions.

The `update_plan` tool is unavailable in this session; this card stores the plan.

## Corpus evidence

- The existing successor form diagonalizes as `B = Σ μ(e) Y(e)^2`, while
  the same-node form is `S = Σ φ(e) Y(e)^2`.
- Existing results show `φ(e) - μ(e) ≥ 1` for `e ≥ 2`, and `2 μ(e) ≤ φ(e)`.
- Existing research search identifies the Selberg coordinate normalization
  and the Möbius recovery of `c(1)`, but no coefficient-level energy-kernel
  classification in this field.
- Search results are discovery evidence; source-only matches must be checked by Lean.

## Paper proof [PROVED HERE]

Let `H = Y(1)`, `V = S - H²`, and `C = B - H²`.
For `e ≥ 2`, `-φ(e) ≤ μ(e) ≤ φ(e)/2`. Consequently `-V ≤ C ≤ V/2`,
or equivalently `V ≤ 2(S-B) ≤ 4V`, for all weights without a mean-zero premise.

Since `φ(e)-μ(e) ≥ 1` on `e ≥ 2`, equality `S=B` is equivalent to
`Y(e)=0` on `[2,N]`. The multiples transform is triangular: descending induction
on `d` identifies `Y(d)=c(d)/d` once all proper multiples have vanished. Hence
`S=B` exactly when `c(d)=0` on `[2,N]`, i.e. the sieve response is constant.

For the other endpoint, `φ(e)+μ(e)` vanishes only at `e=2`: for `e>2`,
evenness and positivity give `φ(e)≥2`, whereas `μ(e)≥-1`.
Thus `S+B=2H²` exactly when `Y(e)=0` on `[3,N]`; descending induction gives
`c(d)=0` on `[3,N]`. Removing the constant mean leaves the parity response.

The descending induction is valid above any cutoff `r+1`: if all coordinates vanish
there and `d` lies in that interval, every proper multiple `b` of `d` in `[1,N]`
satisfies `b>d` and hence `N-b<N-d`. Induction on `N-d` kills its coefficient.
The remaining diagonal term is `c(d)/d=0`; since `d≥r+1≥1`, this forces `c(d)=0`.
Conversely, if all coefficients above the cutoff vanish, every summand of every
coordinate above it vanishes because `e | d` with `d>0` implies `e≤d`.

Quantitatively, for every `e≥3`, positivity and evenness give `φ(e)≥2` and thus
`φ(e)+μ(e)≥φ(e)-1≥φ(e)/2`. Multiplying by `Y(e)²` and summing proves
`Σ_{e=3}^N φ(e)Y(e)² ≤ 2(S+B-2H²)`. Near equality in the negative spectral
bound therefore controls the entire variance outside the parity mode.

At `N=0` every sum is empty. At `N=1`, only the constant mode exists and both
classification tails are empty. At `N=2`, the plus-defect is identically zero,
exactly as the empty `[3,2]` tail asserts. These cases introduce no exceptions
or additional hypotheses.

For coefficients supported in `{1,2}`, the response is
`c(1)+c(2)·1_{2|k}` when `N≥2`, while `H=c(1)+c(2)/2`. Its centered response
changes sign at each successor. For coefficients supported in `{1}`, the response
is constant. Thus the coefficient classifications have the stated arithmetic meaning.

## Gates

- [x] Well-posed question; corpus search performed; arithmetic successor mechanism retained.
- [x] Dependency-closed paper proof, including `N=0,1,2`.
- [x] Lean target checks and axiom audit pass.
- [x] Module wired into the field umbrella, already imported by `MainTheorems`.
- [x] Formal lint run; no proof-debt findings or findings in the new module.
- [ ] Repository-wide lint passes: blocked by seven unrelated unwired BiScaleUncertainty modules.

## Lean implementation

Module: `GaloisForLFunctions.BezoutValuationIncidence.SuccessorEnergyRigidityAndParityStability`.

- `selbergMultiplesCoord_tail_zero_iff`: triangular tail recovery.
- `selberg_eq_bezout_iff_weight_tail_zero`: exact constant-energy kernel.
- `successor_covariance_bounds`, `successor_energy_variance_bounds`: unconditional bounds.
- `successor_anticorrelation_iff_weight_tail_zero`: exact parity endpoint classification.
- `variance_above_parity_le_anticorrelation_defect`: quantitative parity stability.

The complete scratch prototype and named module passed `lake --old env lean -j 1`.
The named-module audit emitted its `.olean` using `-o` and exited zero without warnings.
All eleven new theorems were audited with `#print axioms` in a `/tmp` scratch file:
only `propext`, `Classical.choice`, and `Quot.sound` occur. No added axioms or
computational oracle axioms occur. Mathlib declaration names were checked in `/tmp`.

`scripts/formal_tools.py index` completed and includes all twelve declarations.
`git diff --check` passed. The field README is unchanged. No umbrella build or full
build was run.

Global `scripts/formal_tools.py lint` exited one solely for unreachable modules under
`GaloisForLFunctions.BiScaleUncertainty`:
`ClampedPrimeLogResummation`, `CompactAutocorrelationPolarMoment`,
`FactorialBiNullPolarSign`, `FactorialRampDiagonalIdentity`, `SharpCycleDetectionOrder`,
`StrictCopyCycleCharge`, and `UnitCorrelationBump`. Existing large-file warnings also
remain. Those modules are outside this contribution's write scope.

## Contribution assessment

Count **one** significant contribution: a complete successor-energy kernel and negative-endpoint
rigidity classification, together with quantitative parity stability. Supporting transform,
diagonal, and bound lemmas are not counted separately. Novelty claim is relative to the
audited local corpus, not a claim of priority over the mathematical literature.

## Research boundary

These are finite-dimensional structural and rigidity theorems. They do not establish
cancellation of growing-horizon sawtooth errors or square-root precision. The README's
super-horizon incidence reach by itself must not be counted as that analytic estimate.
