# CLG/TTF: remaining compact determinant incidence

**Classification:** `[BRIDGE]`. The inner endpoint `0≤x≤8/95` remains a target, not a proved source-positivity result. RH remains unproved.

**Full chain:** literal theta source → every signed center-mixed Hankel section nonnegative → Fourier-current sign → Xi Bezoutian orientation → RH.

## Exact remaining identity

`HTGeometry.evenCompactRawDet u a w = HTGeometry.evenCompactRawPolynomial u a w`.

The left side is the complete signed four-by-four source determinant with last-entry correction `10^12 Q(3Q−6/19)`, divided by `100^12`. Here `Q=u²/24+a/16−3/8`. The right side retains 2460 monomials in twenty-one gap degrees. Its definition is checked; its equality to the determinant is not.

Every following substitution is checked:

1. All twenty-one identities `R_n(u,u(1+v/4))=P_n(u²,v)`.
2. Every step of `H_21=0`, `H_n=P_n+A H_(n+1)`, where `A(r,t)=191/10−12r/5+t(1/10+16r/15)`.
3. All twelve drift-graded block identities and all twenty-one coefficient identities landing `H_0` in the independently positive polynomial `T`.
4. The exact unit-to-raw determinant transport from the seven complete source-moment identities.

The existing `T≥1/1000` theorem and actual source-coordinate/correction theorems cannot prove the inner endpoint until the displayed raw identity is closed.

The determinant and raw table now have exact lifts to `Polynomial ℝ` in the gap variable. All seven source-polynomial evaluation identities and degree bounds are proved, and both complete polynomials have degree at most twenty. All twenty-one target-table coefficient identities are also proved without expanding their scalar grades. The remaining identity therefore reduces to the determinant coefficient identities and final polynomial extensionality. The determinant coefficient identities at gap degrees `0,1,2,3,12,13,14,15,16,17,18,19,20` are proved. Degrees `4–11` remain open. The lifts copy existing algebraic expressions, and separate evaluation theorems verify them; no external coefficient computation is used.

The complete determinant also has an exact weighted reflection at degree twenty. Its coefficient at `20−n` equals coefficient `n` of the reflected determinant for `n≤20`. The correction has gap degree at most two, so its first six reflected coefficients vanish. The leading determinant coefficient follows from the weighted source degrees `2,3,…,8`; coefficients one and sixteen through nineteen use exact finite product formulas. Explicitly unrolled product coefficients through index ten avoid expanding source expressions while summation indices remain symbolic.

The seven source polynomials have 41 independently proved normalized coefficients and complete bounds annihilating higher coefficients. The complete determinant has an exact seven-term cofactor decomposition. The leading cofactor’s coefficients zero through four and all three coefficients of the full correction are checked. All seven cubic contributions and their exact determinant sum are proved. At degree four, contributions zero through four are proved; contributions five and six and the final sum remain open. All normalization remains inside Lean and retains the exact source equality; external computations supply no premise.

## Checked formal boundary

The 159 installed inner modules comprise 98 source/model/positive-polynomial/grading/Horner modules and 61 gap-polynomial modules. Thirteen determinant coefficients and all twenty-one target-table coefficients are closed. Every new module was checked separately with foreground `lake env lean`, copied from checked staging bytes and verified to have exactly one theorem-area umbrella import and its required olean. No umbrella or full build was run.

The seventeen new cubic/quartic/certificate theorems received one axiom audit each. All use only `propext`, `Classical.choice`, and `Quot.sound`. Their names are recorded in `checked-modules.json`; the earlier groups of 94 and nineteen capstones, and earlier source/grading/Horner audits, were not repeated.

Repository-wide static formal lint currently flags five unrelated unwired RHTower modules, listed in `checked-modules.json`. No new CLG/TTF module is among those errors. Foreign source files and wiring were preserved.

## Proof-size constraint

Do not repeat the monolithic determinant checks or raise their limits. The raw `unfold; ring1` attempt reached a measured 57.4 GB physical footprint while Lean abstracted the proof term. Resident memory alone hid this cost. It was interrupted and its process exited. A `dsimp only; ring1` variant reached 12.6 GB within about a minute and was also interrupted. Neither produced a checked determinant theorem.

The remaining raw gap coefficients must stay separately bounded. The generic cofactor degree bound uses explicit product, power, sum and difference bounds; automatic degree inference on abstract polynomial inputs was too expensive. Direct formulas for product coefficients zero and one, followed by a separate source-coefficient normalization, close gap degree one with a measured 1.6 GB physical footprint. The degree-two candidate reaches expensive proof-term traversal at 4.4 GB; isolating its final scalar proof with the corpus’s `as_aux_lemma` pattern reaches kernel checking at 6.4 GB but did not complete within the three-minute limit. Both degree-two processes were interrupted and exited. The source-cache form closes degrees twelve through fifteen within the same 500000-heartbeat budget. Degree twelve completed module serialization after reaching a measured 12.0 GB physical footprint in `CollectAxioms`/`FoldConsts`; lower reversed degrees must be split before checking, rather than extending that whole-coefficient proof form. The checked seven-term cofactor split now closes degree two. Direct `grind only` after full coefficient expansion also exhausted the unchanged heartbeat budget; the checked replacement uses independently normalized cofactor identities. Do not rerun superseded whole-coefficient proof forms or raise their limits. A resource failure is not a mathematical counterexample.

`pending-lean/` preserves the unsuccessful raw proof forms, the untested degree-four cofactor/assembly and degree-five/reversed-degree-ten/eleven candidates, and the untested determinant/source capstones. Superseded degree-two, degree-three and degree-fifteen candidates are removed; their checked replacements are installed. These are research candidates outside the formal corpus; do not install or wire them before successful checks. If the raw identity closes, the pending capstones target determinant reserve `10^21 M(x)^8`, inner strictness for every `C≥10^12`, and canonical weighted strictness outside the remaining explicit middle interval. Those conclusions are not yet established.

## Computation boundary

The [scientific-method guide](../../../../meta/scientific-method.md) governs future experiments. No further coefficient-generation or numerical scan is scheduled. Existing tables are proof candidates, not admitted computational facts. Any new experiment must address an uncertain mathematical question whose possible outcomes would change the approach, run briefly on Runpod with multicore code, and retain downloaded results. All owned Runpod working directories are removed.

The bulk coefficient queue is stopped. Pending degree-four contributions five and six use the validated certificate-retaining form; their assembly remains untested. The remaining degree-five and reversed degree-ten/eleven whole-coefficient drafts must not be run unchanged. Required checked oleans and pending drafts are retained. Owned scratch files and processes are cleaned at the checkpoint.

## Research priority and proof engineering

This is a finite source-incidence bridge. Its completion would establish the proposed compact inner source comparison, not RH, the remaining middle comparison, the integrated rank-seven sign, or all-order positivity. Closing further scalar coefficients must not be described as resolving those hard mathematical obligations.

The original normalization helpers discard the equality proof returned by `Conv.mkConvGoalFor`; the following scalar theorem repeats normalization. `PolynomialODEEvenCompactGapCertifiedNormalizer` retains the normalized value and exact equality in `CompactGapNormalForm`. Its checked use in `PolynomialODEEvenCompactGapCofactorTerm4Slice4` performs one normalization and proves source incidence by the certificate projection. The redundant normalization is removed; no measured wall-clock speedup is claimed. No heartbeat limit was raised. Further work should prioritize a noncircular all-order source-sign producer from the corpus; finite coefficient closure is a secondary bridge.
