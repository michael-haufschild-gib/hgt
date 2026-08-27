# Reflected bi-heat multiplicity-leading jet balance

- **ID:** RBH-MLJB
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + EXACT RECEIVER + COEFFICIENT-FREE REDUCTION
- **Parent:** RBH
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION] [EXACT RECEIVER] [COEFFICIENT-FREE]` At every actual Xi divisor, norms of two exact multiplicity-leading reflected bi-heat jets at fixed aperture `2` are equal iff divisor lies on critical wall; equality for all Xi divisors is exactly RH.

## Goal

Eliminate unknown completed leading coefficient and Xi multiplicity from RBH balance burden. Replace
asymptotic co-leading language by one exact fixed-aperture equality on actual nonzero jets.

This is exact RH receiver, not source-first proof of equality.

## Gates

- [x] 0 → 1 in-progress: fixed-aperture top-jet conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: norm identities, coefficient cancellation, pointwise and global iff
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claim

For `ρ : XiDivisorSupport`, let `m(ρ)` be exact Xi multiplicity and

`Aρ = (1/2) Λ^(m(ρ))(ρ) ≠ 0`.

At aperture `x=2`, exact first surviving jets obey

`|Lρ| = |Aρ| 2^((Re ρ-1)/2)`,

`|Rρ| = |Aρ| 2^(-Re ρ/2)`.

Therefore `|Lρ|=|Rρ|` iff `Re ρ=1/2`. Quantifying equality over all actual Xi divisor support is
equivalent to RH.

## Complete paper proof

Multiplicity tomography gives exact formulas for both `m(ρ)`-th derivatives; all lower derivatives
vanish and common completed derivative is nonzero. Norm of positive-real complex power is real power
with real exponent. Common positive factor `|Aρ|` cancels. Strict monotonicity of `2^t` makes equal
powers equivalent to equal exponents. Solving

`(Re ρ-1)/2 = -Re ρ/2`

gives `Re ρ=1/2`. Existing Xi-support endpoint converts universal pointwise wall law to RH and RH
gives converse.

## Hostile review and priority verdict

- Theorem is exact receiver equivalent to RH; it does not establish source balance.
- Novel reduction is coefficient-free and multiplicity-free: no simplicity assumption or
  normalization of unknown top derivative remains.
- Aperture `2` is arbitrary convenience; any fixed positive base unequal to `1` has same role.
- Functional-equation equality of completed coefficients does not imply this norm equality because
  aperture exponents remain different off wall.
- Primary literature audit included Hedenmalm's 2026 theta spectral interpretation
  arXiv:2606.17494 and Connes' heat expansion arXiv:2402.13082. Neither audited source states this
  reflected double-channel multiplicity-leading fixed-aperture iff or Lean formalization.

Verdict: real-power cancellation ingredients `[REDISCOVERED]`; exact RBH coefficient/multiplicity
elimination and global receiver `[NEW] [CLASSIFICATION]`, external priority provisional.

## No-go closure

- **Closed burden:** unknown multiplicity and common completed top coefficient cannot obstruct RBH
  endgame; both cancel at one fixed aperture.
- **Exact remaining source law:** force `|Lρ|=|Rρ|` at aperture `2` for every actual divisor before
  using divisor position.
- **Boundary:** proving that global equality by copywise or divisor-indexed normalization is exactly
  RH and is circular.
- **Positive survivor:** actual nonzero top-jet norm imbalance is faithful oriented horizontal
  coordinate even at arbitrary multiplicity.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ReflectedBiHeatMultiplicityLeadingJetBalance.lean`
- Common coefficient and nonvanishing: `reflectedBiHeatMultiplicityLeadingCoefficient`,
  `reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero`
- Exact norm laws: `norm_reflectedBiHeatLeftResponse_leadingJet_two`,
  `norm_reflectedBiHeatRightResponse_leadingJet_two`
- Pointwise iff: `reflectedBiHeatMultiplicityLeadingJetNorms_two_eq_iff`
- Global iff: `riemannHypothesis_iff_reflectedBiHeatMultiplicityLeadingJetNorms_two_eq`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityLeadingJetBalance`
  passed (`11454/11454`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from corpus multiplicity tomography and exact scale-order difference.
- 2026-08-27 — exact fixed-aperture norm formulas, pointwise wall classification, and global RH iff
  paper-proved and formalized.
