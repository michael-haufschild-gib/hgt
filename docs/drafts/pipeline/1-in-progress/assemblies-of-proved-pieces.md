# Assemblies of proved pieces

- **ID:** assemblies-review-1011
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/obstacles-summary.md`, §2.1, “Assemblies of proved pieces”.
- **Statement:** Resolve every assembly in the source table, with unconditional Lean proofs and transitive axiom audits.

## Scope

| Tasks | Exact target | Status |
|---|---|---|
| A90 | RH iff positive definiteness of the prime-side lag function | Formalized and axiom-audited; `3-formalized/the-prime-lag-is-positive-definite-exactly-under-rh.md` |
| A72 | Count door on logarithmic windows with power-thin exceptions | Formalized and axiom-audited; `3-formalized/counts-on-exceptional-logarithmic-prime-windows.md` |
| A76 | Absolute and signed window criteria with exceptions | Absolute logarithmic criterion audited; signed transfer and log-square audits pending |
| A73 | Upper one-sided logarithmic-window criterion | Negative-trace filter and prime-transfer proofs written; Lean audits pending |
| A71 | Uniform local tensor moments iff RH | Proof written; Lean audit pending |
| A56 | Explicit two-bump prime rung from a verified height | Explicit unbounded rung proof written; Lean audit pending |
| A75 | S3 transfer implies the quasi-RH collapse | Proof written with the exact floor cutoff; Lean audit pending |
| A83 | Density-matched counter-configuration with bounded trace change | Open |
| A97 | Newtonian even multipoles, rulings, and prime-chain contact squares | Open |
| A98 | RH iff feasible weights exist at every aperture | Formalized and axiom-audited; `3-formalized/feasible-weights-at-every-aperture-are-rh.md` |
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
- **A98.** A finite family of compactly supported tests has a common aperture. Choose a feasible weight at that aperture. Every nonnegative prime-blind mixture then has nonnegative Weil form, and its prime terms cancel. Thus its archimedean form is nonnegative. The unconditional prime-blind RH criterion supplies RH. Conversely RH supplies the von Mangoldt weight at every aperture. No compatibility of the chosen weights is needed.
- **A73.** Negate the trace coefficients before applying the positive quartet filter. Nonvanishing, conjugate symmetry, and logarithmic leakage bounds survive. The resulting finite spectrum has dense negative excursions, contradicting a floor for the negative trace. Prime-gap transfer gives width reduction `a≤max(σ,a−1/3)` at the abscissa, hence `a≤σ`. This yields the upper power criterion and its RH specialization on logarithmic prime windows.
- **A75.** Formalize the transfer as a uniform bound on a log-square prime window whenever heavy identity returns are absent for primes up to `⌊T^A⌋` and heights `[T₁, exp(ηT)]`. A strip of depth `h<1/2` gives `log t≥c y^d`, `d=1/2−h>0`. Choose `A=2/d`: then `y≥T^A/2` gives `c y^d≥c2^{-d}T²>ηT` eventually. Thus the return-free hypothesis holds on every late window; the proposed transfer and the signed window criterion give RH. The theorem proves the implication from the transfer, not the transfer itself.

## Local tensor target

For A71 preserve the corpus’s uniformity: constants may depend on the tensor order; the growth exponent may not. The local target is `∃ A, ∀ k≥1, ∃ C_k, ∀ U, ∃ T≥U, Σ_{p in window(T)} log p · (2c_B(log p))^(2k) ≤ C_k exp(A T)`. Windows may depend on `k`. One summand and `R(T)=o(T)` give a prime bound of exponent `|A|/k`; the logarithmic-window width theorem and `k→∞` give RH. This avoids imposing a stronger, unintended bound exponential in `k` on the moment constants.

## Further exactness checks

- **A56:** `boxSpline 1 3` has support radius **4**, so a two-bump packet at separation `log p` has aperture `4 + (log p)/2`. `VerifiedHeightRungs.WindowEntries.windowHeight` is explicit. The verified-height rung must use this radius.
  An explicit inverse rung is the largest `n≤⌊T⌋` with `windowHeightOfOne(4+log(n)/2)≤T`, or zero if none exists. It tends to infinity: for each fixed `n`, every `T≥max(n,windowHeightOfOne(4+log(n)/2))` admits `n`. Every prime up to the rung fits in its aperture, without any monotonicity assumption on the height formula.
- **A99:** The raw `scatteringWeilEnergy` changes the jump kernel, the mass coefficient, and the prime operator. Its difference from the Weil form is therefore the jump tail **plus** `(2 gammaHardyPhaseRate(0) − scatteringMassCoefficient N)‖f‖²` **minus** the omitted prime form. The positive jump tail alone is not the full raw defect. `scatteringSecondHeightDefect_eq` already retains the prime correction after removing the Robin mass drift; the requested regulator criterion must retain these terms or explicitly correct the regulator.

## Finite-mode sign resolution

For A92, a sharper candidate is available. For a real trace `F=Re Σ a_j exp(iγ_j t)` with nonzero frequencies and `F` not identically zero, compose the positive shift operators `1+τ_{π/|γ_j|}`. Their product annihilates every mode and has support diameter `D=Σ π/|γ_j|`. If `F≥0` on an interval longer than `D`, every summand in each shifted identity is nonnegative; its unshifted summand vanishes on an open interval. Analytic uniqueness then forces `F≡0`, contradiction. Thus `L≤D≤nπ/Γ`. Repeated frequencies can be discarded. The nonzero-real-trace condition is essential when opposite frequencies are allowed. Lean proof pending.

For A95, apply this to the finite top layer. On the compact phase torus, absence of a nonnegative trace on a fixed interval of length `>D` gives a uniform negative excursion; lower layers are negligible after normalization. The excursion amplitude may depend on the layer, but the length is bounded using only its size and the lowest ordinate.

The weighted L1 clause of A92 needs an exactness audit: `F≥−K` directly gives `∫w|F|≤2K∫w+|∫wF|`, hence the Fourier bound with coefficient **2** on the floor. The proposed coefficient 1 is suspect. A candidate obstruction uses `F=cos t+cos(2t)≥−9/8` and three equal narrow translated bumps centered at `0,2π/3,4π/3`: their first two Fourier modes vanish, while their weighted absolute trace approaches 4 against floor cost `27/8`. Formalize the obstruction and the sharp surviving bound before retiring the stated coefficient.
