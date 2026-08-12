# CMR stage-3: 16/18 promoted; plan for the last 2 cards

Promoted 16.  New since the previous note:
- `marked-mellin-normalization-exchange-response`
  (`ConstraintMotiveRelativity/MarkedMellinExchange.lean`, all of §§1–5 including the `(MER.17)`
  Cauchy–Schwarz Fisher bound and the `(MER.18)`/`(MER.18a)` time jets; 29 decls axiom-clean).
- `finite-reporter-admission-hyperbolic-reduction-composition`
  (`ConstraintMotiveRelativity/FiniteReporterAdmission.lean`, §§0–5 including the new
  subspace Hahn–Banach lemma `exists_continuous_annihilator_of_notMem_closure`, the Chu mate,
  hyperbolic doubles, serial composition, prime-port instantiation; 29 decls axiom-clean).

## Remaining card 1: marked-euler-shell-mellin-gns-ht-recurrence-normalization-wall

Huge corpus reuse is available; DO NOT re-derive:
- `RHTower/HighExponentShellZeroFree.lean`: `shellIndicator` (= `a_m`, as
  `mFreeIndicator (m+1) - mFreeIndicator m`), `shellIndicator_eq_one_iff`,
  `shellIndicator_eq_zero_or_one`, `shellMultiplier` (= `H_m`), `LSeries_shellIndicator`
  (= `(ESG.22)` `S_m = ζ·H_m`), `shellMultiplier_ne_zero` (zero-free on `re s > 1/2`, `m ≥ 12`),
  `analyticAt_shellMultiplier`, `shellMultiplier_one_eq_ofReal_pos` (= `(ESG.23)`).
- `RHTower/HighExponentShellClockMeasure.lean`: `shellMass`, `summable_shellMass`, `shellMellin`,
  `shellMellin_pos`, `shellProbability`, `hasSum_shellProbability`, `shellIndicator_two_pow`.
- `RHTower/HighExponentShellClockMoments.lean`: `shellLogMoment`, `ofReal_shellLogMoment`,
  `shellClockVariance`.
- `RHTower/HighExponentShellHypertranscendence.lean`:
  `highExponentShellArithmetic_differentialIndependent`,
  `zetaShellArithmetic_differentialIndependent` (= §6 HT).

Still to write: §2 `(ESG.4)`–`(ESG.9)` (pure-power recovery under `L = -δ`, finite-`F` diagonal
model, restriction naturality); §3 `(ESG.10)`–`(ESG.13)` (moment object, weighted Vandermonde rank
`min(R+1,|F|)`, successor nonuniqueness by a Vandermonde kernel perturbation); §4 `(ESG.16)`–
`(ESG.19)` (coefficient faithfulness, `∫x^r dμ = (-1)^r S_m^{(r)}(σ)`, strict Hankel positivity,
`⟨Ω,U_tΩ⟩ = S_m(σ+it)/S_m(σ)`); §5 compact resolvent + recurrence + `‖-tDΩ‖² → ∞`; §7
`(ESG.24)`–`(ESG.25)` (`mσ = 1` forced, `∑_p (log p)²/p = ∞` — easy from
`Nat.Primes.not_summable_one_div`); §8 mixed-atom nonfaithfulness (perturb at `2^m·3`).

## Remaining card 2: helson-coefficient-fredholm-crossing-response

See the previous note: §§2–3, 5–6 are writable on `HTGeometry/SchattenOneBanach.lean`; §4 needs
new trace-class Riesz-projection perturbation theory and a Fredholm determinant.

## Practical notes

- `lake build <module>` for the audit; `lake env lean <file>` while iterating; `pkill -f "lake env
  lean"` afterwards.
- Namespace collisions are real: `hyperbolicForm` already existed in
  `PrimeAugmentationSymplectic.lean`; check with `rg` before naming.
- `↥S ⧸ T` needs `T : Submodule R ↥S` (use `Submodule.comap S.subtype T`), otherwise `HasQuotient`
  fails.
- `Module.evalEquiv`/`Module.IsReflexive` can fail instance search on `↥(Submodule …)` of a
  `→L[ℂ]` space; route through `Submodule.quotDualCoannihilatorToDual` and `Module.Finite.equiv`
  instead of `LinearEquiv.finiteDimensional`.
