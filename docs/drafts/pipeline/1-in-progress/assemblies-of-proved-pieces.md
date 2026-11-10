# Assemblies of proved pieces

- **ID:** assemblies-review-1011
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, §2.1, “Assemblies of proved pieces”.
- **Statement:** Resolve every assembly in the source table, with unconditional Lean proofs and transitive axiom audits.

## Scope

| Tasks | Exact target | Status |
|---|---|---|
| A90 | RH iff positive definiteness of the prime-side lag function | Proof written; Lean audit pending |
| A72 | Count door on logarithmic windows with power-thin exceptions | Formalized and axiom-audited; `3-formalized/counts-on-exceptional-logarithmic-prime-windows.md` |
| A76 | Absolute and signed window criteria with exceptions | Both proofs written; Lean audits pending |
| A73 | Upper one-sided logarithmic-window criterion | Open |
| A71 | Uniform local tensor moments iff RH | Open |
| A56 | Explicit two-bump prime rung from a verified height | Open |
| A75 | S3 transfer implies the quasi-RH collapse | Open |
| A83 | Density-matched counter-configuration with bounded trace change | Open |
| A97 | Newtonian even multipoles, rulings, and prime-chain contact squares | Open |
| A98 | RH iff feasible weights exist at every aperture | Open |
| A99 | Completed-zeta quotient formula and exact regulator-defect criterion | Open |
| A78 | Cluster extension of separated windows | Open |
| A79, A81 | Matching aperture–height and block-index constants | Open |
| A80 | Eventual finite-scale positivity from RH or a verified height | Open |
| A82 | Li coefficients as comb forms of tails | Open |
| A92 | Prime-side resolution law, including both finite-mode statements | Open |
| A93 | Receiver exchange atlas | Open |
| A94 | Equality of finite-scale and aperture negative indices | Open |
| A95 | Separation-free finite-layer window length | Open |
| A96 | Exact first selective interval for the weight at 2 | Open |
| A100 | Trivial conductor aperture and exceptional square | Open |

## Proof requirements

Each row needs its stated mathematical content, a dependency-closed proof, correctly placed Lean declarations, umbrella imports, a direct `lake --old env lean` audit, and `#print axioms` containing only standard logical axioms. An unverified row is not assumed true. Refuted targets require the strongest positive survivor under the repository’s no-go closure rule.

## Dependency-closed assemblies

- **A72.** Every quadratic limit of natural-number counts is nonnegative. The identity `planeDefect p (1,1) = 2c_B(0)+2c_B(log p)` gives the floor required by `riemannHypothesis_iff_prime_logarithmic_windows_off_finset`. Conversely, under RH use the natural floor of the quadratic defect and empty exceptional sets. Source: `SurfaceOfSpecZ/ScaleLocality/CountsOnExceptionalLogarithmicWindows.lean`.
- **A90.** The central zero trace equals `weilLagFunction`. Combine the flow Castelnuovo–Severi equivalence with the zero-motive RH equivalence. For nonzero lags the prime formula is `exp(-|u|/2) primeDeviation(exp |u|)`; at zero it is `poleSharpConstant`. Evenness identifies both half-lines. Source: `InfiniteRankPurityTheory/ThePrimeLagIsPositiveDefiniteExactlyUnderRH.lean`.
- **A76.** An absolute bound gives the existing lower bound with the same exceptional set; the width theorem supplies the converse implication. Under the width bound the global absolute estimate permits empty exceptional sets. Source: `SurfaceOfSpecZ/ScaleLocality/ExceptionalAbsoluteWindows.lean`. Separately, `ExceptionalAbsolutePrimeWindowTransfer.lean` proves absolute prime avoidance; `ExceptionalSignedWindows.lean` combines it with the signed log-square receiver. At the abscissa `a=Θ−1/2`, the reduction `a≤max(σ,a+β−1)`, `β<1`, forces `a≤σ`.

## Local tensor target

For A71 preserve the corpus’s uniformity: constants may depend on the tensor order; the growth exponent may not. The local target is `∃ A, ∀ k≥1, ∃ C_k, ∀ U, ∃ T≥U, Σ_{p in window(T)} log p · (2c_B(log p))^(2k) ≤ C_k exp(A T)`. Windows may depend on `k`. One summand and `R(T)=o(T)` give a prime bound of exponent `|A|/k`; the logarithmic-window width theorem and `k→∞` give RH. This avoids imposing a stronger, unintended bound exponential in `k` on the moment constants.

## Further exactness checks

- **A56:** `boxSpline 1 3` has support radius **4**, so a two-bump packet at separation `log p` has aperture `4 + (log p)/2`. `VerifiedHeightRungs.WindowEntries.windowHeight` is explicit. The verified-height rung must use this radius.
- **A99:** The raw `scatteringWeilEnergy` changes the jump kernel, the mass coefficient, and the prime operator. Its difference from the Weil form is therefore the jump tail **plus** `(2 gammaHardyPhaseRate(0) − scatteringMassCoefficient N)‖f‖²` **minus** the omitted prime form. The positive jump tail alone is not the full raw defect. `scatteringSecondHeightDefect_eq` already retains the prime correction after removing the Robin mass drift; the requested regulator criterion must retain these terms or explicitly correct the regulator.
