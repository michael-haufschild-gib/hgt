# constraint-frame-relativity → stage 3 progress (2026-08-09)

Goal: unconditionally formalize every proven theorem in
`docs/drafts/pipeline/2-fully-proven/constraint-frame-relativity` (14 cards), wire into
`GaloisForLFunctions.HTGeometry`, write `<id>-formalized.md` companions, `git mv` to
`docs/drafts/pipeline/3-formalized/constraint-frame-relativity/`.

## New Lean area

`formal/GaloisForLFunctions/HTGeometry/ConstraintFrameRelativity/` — namespace
`HTGeometry.ConstraintFrameRelativity`.  (Distinct from the existing `ConstraintRelativity/`
folder, which serves a different card folder.)

## Modules GREEN so far

1. `ShellRamificationPower.lean` — `shellIndicator (r*m) (k^r) = shellIndicator m k` (RP.4),
   `mFree_iff_forall_factorization_lt`, squarefree descent (RB.2), `IsRPow`,
   `excess_witness` (`2^(rm)·3`).
2. `BernoulliBooleanGibbs.lean` — product Bernoulli weight/expectation on `Finset ι`,
   `bernoulliExp_prod` (= `Finset.prod_add` backwards), subset-occupation law,
   `bernoulliCov_linearStat` (diagonal covariance of linear statistics).
3. `SchurCapacity.lean` — `capA/capB/capC`, `schurCapacity`, variational `IsLeast`,
   two-row Cauchy–Binet `capA_mul_capC_sub_capB_sq`, positivity, `≤ π² A`.
4. `FiniteTiltResponse.lean` — `wexp/wcov`, `tiltExp/tiltCov`, `hasDerivAt_tiltExp` (RB.16),
   `hasDerivAt_tiltCov` (RB.19), `hasDerivAt_capacityOfMoments`,
   `hasDerivAt_tiltSchurCapacity` (RB.18), fugacity derivative (for RB.21).
5. `ShellExcessDirichlet.lean` — `powerImageStream`/`excessStream`, RP.7
   `lSeries_shell_eq_dilate_add_excess`, excess witness nonzero.

## Lean traps hit

- `convert h using 1` on `HasDerivAt` descends into instance arguments and produces
  `Real.instAddCommGroup = Real.normedAddCommGroup.toAddCommGroup` goals.  Use
  `HasDerivAt.congr_deriv` instead — always.
- `field_simp [someDef]` does not reliably unfold a `def`; use `simp only [theDef]` first.
- `rw [LSeries.term]` fails (match-based); use `LSeries.term_of_ne_zero` / `LSeries.term_zero`.
- `Complex.natCast_cpow_natCast_mul (n m : ℕ) (z) : (n:ℂ)^((m:ℂ)*z) = ((n:ℂ)^m)^z` is the
  reindexing lemma for `S_m(r s)`.
- `rcases h with a | b <;> simp [a, b]` is a name error; use `with h | h <;> simp [h]`.

## Remaining

Cards 1–14 of the task list; see TaskList.  Next: shell capacity depth bounds (RP.11–RP.18),
then the Boolean descent card, excess/octahedral, Kummer, Witt, escort, phase history,
anchor-defect incidence, jet factorization, Euler shell, monomial chart, source-law
nonreconstruction, static frame incompleteness, valuated Plücker–Gram.
