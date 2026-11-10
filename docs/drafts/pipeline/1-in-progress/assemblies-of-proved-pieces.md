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
| A76 | Absolute and signed window criteria with exceptions | Formalized and axiom-audited; `3-formalized/absolute-and-signed-exceptional-prime-windows.md` |
| A73 | Upper one-sided logarithmic-window criterion | Negative-trace filter and prime-transfer proofs written; Lean audits pending |
| A71 | Uniform local tensor moments iff RH | Formalized and axiom-audited; `3-formalized/local-tensor-moments-on-prime-windows-are-rh.md` |
| A56 | Explicit two-bump prime rung from a verified height | Formalized and axiom-audited; `3-formalized/verified-heights-give-explicit-prime-two-bump-rungs.md` |
| A75 | S3 transfer implies the quasi-RH collapse | Proof written with the exact floor cutoff; Lean audit pending |
| A83 | Density-matched counter-configuration with bounded trace change | Exact critical-projection count proof written; trace superposition, sparse count comparison, and audits pending |
| A97 | Newtonian even multipoles, rulings, and prime-chain contact squares | Proofs written in `TheJetsAreEvenNewtonianMultipoles` and `TheContactsOfAPrimeAreChainSquares`; audits pending |
| A98 | RH iff feasible weights exist at every aperture | Formalized and axiom-audited; `3-formalized/feasible-weights-at-every-aperture-are-rh.md` |
| A99 | Completed-zeta quotient formula and exact regulator-defect criterion | Open |
| A78 | Cluster extension of separated windows | Open |
| A79, A81 | Matching aperture–height and block-index constants | Open |
| A80 | Eventual finite-scale positivity from RH or a verified height | Open |
| A82 | Li coefficients as comb forms of tails | Open |
| A92 | Prime-side resolution law, including both finite-mode statements | Sign and weighted coefficient-two bounds formalized and axiom-audited; counterexample and prime-side assembly pending |
| A93 | Receiver exchange atlas | Open |
| A94 | Equality of finite-scale and aperture negative indices | Open |
| A95 | Separation-free finite-layer window length | Finite-mode window theorem formalized and axiom-audited; top-layer specialization pending |
| A96 | Exact first selective interval for the weight at 2 | Open |
| A100 | Trivial conductor aperture and exceptional square | Existing `TheTrivialApertureAndTheExceptionalSquare` supplies the assembly and stronger aperture bound; audit pending |

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

For A92, compose the positive shift operators `1+τ_{π/γ_j}` for `γ_j ≥ Γ > 0`. Their product annihilates every mode and has support diameter `D=Σ π/γ_j`. If `F≥0` on an interval longer than `D`, every summand in each shifted identity is nonnegative; its unshifted summand vanishes on an open interval. Analytic uniqueness gives `F≡0`. Thus a nonzero trace satisfies `L≤D≤nπ/Γ`; without a nonvanishing premise, this is the short-interval-or-zero classification. Formalized in `HalfPeriodSignResolution.lean`; direct audit passed with standard axioms only. Card: `3-formalized/half-period-deletion-bounds-sign-intervals.md`.

For A95, apply this to the finite top layer. On the compact phase torus, absence of a nonnegative trace on a fixed interval of length `>D` gives a uniform negative excursion; lower layers are negligible after normalization. The excursion amplitude may depend on the layer, but the length is bounded using only its size and the lowest ordinate.

For distinct positive frequencies, nonvanishing survives every phase rotation: the positive-frequency Bohr coefficient of twice the real trace is its original nonzero coefficient; conjugate frequencies are negative and cannot cancel it. The open sets where some time in the fixed interval has trace below `−ε` form a directed cover of the compact phase torus. A single `ε>0` therefore works for every phase. `tendsto_normTrace_sub_topTrace` supplies the lower-layer remainder without a gap below the top real part.

The weighted L1 clause of A92 needs an exactness audit: `F≥−K` directly gives `∫w|F|≤2K∫w+|∫wF|`, hence the Fourier bound with coefficient **2** on the floor. This bound is formalized and axiom-audited in `WeightedTraceFloors.lean`. The proposed coefficient 1 is suspect. A candidate obstruction uses `F=cos t+cos(2t)≥−9/8` and three equal narrow translated bumps centered at `0,2π/3,4π/3`: their first two Fourier modes vanish, while their weighted absolute trace approaches 4 against floor cost `27/8`. Formalize the obstruction and sharpness before retiring the stated coefficient.

## Further assembly inputs

- **A97:** `CHMDPrimeChainVariance.exists_pow_mul_of_same_chain` and `same_chain_of_pow_mul` identify distinct positive integers on one prime chain with a prime-power quotient. Thus the prime contact form is `log p` times `Σ_b(Σ_{ordCompl[p]n=b}c_n)²−Σ_nc_n²`. `hasSum_jetLevel` supplies the even axial Newtonian expansion once the Euclidean distance on an axis is identified; the weight-zero kernel at zero is `1/n`, and its normalized limit at infinity is `1`.
- **A82:** `SuzukiCorFourSix.suzukiLiWeilForm_eq_xiLiPaired` already identifies the Bombieri–Lagarias test with `2λ_n`. The missing bridge is the comb limit for its Laguerre tail. These tests jump at zero and have unbounded support; the compact C² sampling theorem alone does not supply that bridge.
- **A80/A94:** `TheInequalityAtFiniteScaleIsDecidedOnBlockAverages` controls arbitrary divisors by block means with an arbitrarily small mass error. Exact positivity additionally needs a positive window gap and convergence on the finite block space. At a zero eigenvalue, convergence alone cannot identify the eventual negative index; the critical correction must be determined.
- **A78:** `OnlyDeepOrdinatesNeedSeparation` bounds leakage from every other deep exponent by a separated inverse-square sum. A cluster extension must control cancellation inside the selected cluster, not merely multiply the far-leakage count by its cardinality.
- **A100:** `AbsoluteGeometryOfSpecZ/TheTrivialApertureAndTheExceptionalSquare.lean` identifies real-packet positivity with complex window positivity and gives the exceptional real-pair decomposition. Its improved sufficient condition is `primeMass a + primeMass(a/2) + archConstant χ ≤ log q`; the mass ratio tends to `2e^a`. This existing work is being audited separately in the shared workspace; no duplicate proof is needed.
- **A83:** Project every zeta zero horizontally to `Re s=1/2`, adding multiplicities at equal ordinates. `TheCriticalProjectionPreservesTheCounts.lean` proves preservation of every window count and temperedness from the unchanged local count. This supplies the exact-density background without assuming RH. The remaining assembly adds its bounded spline trace to the sparse off-line construction and checks that the latter does not change the density asymptotic.
  The sparse tower's local count is at most `32k+40` on the unit intervals meeting level `k`. Its recursion gives `log Γ_(k+1)≥(Θ/7)T_k`, while `T_k≥exp((k+1)²)` for `k≥1`. Thus its local count is `o(log t)` and its cumulative count is `o(T log T)`. Adding this tower preserves the leading zeta density; it does not preserve every finite-window count.
