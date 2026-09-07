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

The determinant and raw table now have exact lifts to `Polynomial ℝ` in the gap variable. All seven source-polynomial evaluation identities and degree bounds are proved, and both complete polynomials have degree at most twenty. The remaining identity therefore reduces to twenty-one coefficient identities. The determinant coefficient identities at gap degrees `0,1,16,17,18,19,20` are proved. Degrees `2–15` remain open. The lifts copy existing algebraic expressions, and separate evaluation theorems verify them; no external coefficient computation is used.

The complete determinant also has an exact weighted reflection at degree twenty. Its coefficient at `20−n` equals coefficient `n` of the reflected determinant for `n≤20`. The correction has gap degree at most two, so its first six reflected coefficients vanish. The leading determinant coefficient follows from the weighted source degrees `2,3,…,8`; coefficients one and sixteen through nineteen use exact finite product formulas. Explicitly unrolled product coefficients through index five avoid expanding source expressions while summation indices remain symbolic.

## Checked formal boundary

The original 98 installed inner modules comprise 38 source/model/positive-polynomial/integer-normalization modules, 21 gap grades, 22 Horner stages including terminal zero, and 17 structural/block-grading/landing modules. The fifteen gap-polynomial modules bring the checked total to 113: exact lifts and source coefficients, determinant/table evaluation and degree bounds, finite convolution formulas, weighted top-coefficient and reflection laws, the reflected determinant, and seven determinant coefficient identities. Each new module was checked separately with foreground `lake env lean`, copied from checked staging bytes and verified to have exactly one theorem-area umbrella import and its required olean. No umbrella or full build was run.

The nineteen new gap-polynomial capstones received one axiom audit each. All use only `propext`, `Classical.choice`, and `Quot.sound`; their names are recorded in `checked-modules.json`. Earlier source, grading and Horner capstones retain their completed audits and were not re-audited.

Repository-wide static lint currently flags three unrelated unwired RHTower modules: `ConstrainedWeilPolarDerivativeTest`, `RetainedPrimeDivisorConvolution`, and `RetainedPrimeMobiusEulerIdentity`. No owned module is among those errors. Their files and umbrella wiring were left to their respective work.

## Proof-size constraint

Do not repeat the monolithic determinant checks or raise their limits. The raw `unfold; ring1` attempt reached a measured 57.4 GB physical footprint while Lean abstracted the proof term. Resident memory alone hid this cost. It was interrupted and its process exited. A `dsimp only; ring1` variant reached 12.6 GB within about a minute and was also interrupted. Neither produced a checked determinant theorem.

The remaining raw gap coefficients must stay separately bounded. The generic cofactor degree bound uses explicit product, power, sum and difference bounds; automatic degree inference on abstract polynomial inputs was too expensive. Direct formulas for product coefficients zero and one, followed by a separate source-coefficient normalization, close gap degree one with a measured 1.6 GB physical footprint. The degree-two candidate reaches expensive proof-term traversal at 4.4 GB; isolating its final scalar proof with the corpus’s `as_aux_lemma` pattern reaches kernel checking at 6.4 GB but did not complete within the three-minute limit. Both degree-two processes were interrupted and exited. Degree fifteen reaches the 500000-heartbeat `whnf` limit. These candidates need smaller coefficient/cofactor identities; do not rerun them unchanged or raise limits. A resource failure is not a mathematical counterexample.

`pending-lean/` preserves the unsuccessful raw proof forms, the two incomplete degree-two proof forms, the degree-fifteen candidate, untested degree-three-through-five candidates, and the untested determinant/source capstones. These are research candidates outside the formal corpus; do not install or wire them before successful checks. If the raw identity closes, the pending capstones target determinant reserve `10^21 M(x)^8`, inner strictness for every `C≥10^12`, and canonical weighted strictness outside the remaining explicit middle interval. Those conclusions are not yet established.

## Computation boundary

The [scientific-method guide](../../../../meta/scientific-method.md) governs future experiments. No further coefficient-generation or numerical scan is scheduled. Existing tables are proof candidates, not admitted computational facts. Any new experiment must address an uncertain mathematical question whose possible outcomes would change the approach, run briefly on Runpod with multicore code, and retain downloaded results. All owned Runpod working directories are removed.

The active proof split first isolates normalized source coefficients, then cofactor coefficients. New checks use fresh `/tmp/clg_even_inner_slice_stage` staging and one foreground Lean process. Completed previous scratch files remain removed; checked modules and pending proof candidates are retained in the repository.
