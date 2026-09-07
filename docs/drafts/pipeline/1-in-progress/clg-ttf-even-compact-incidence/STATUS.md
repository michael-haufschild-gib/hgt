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

The determinant and raw table now have exact lifts to `Polynomial ℝ` in the gap variable. All seven source-polynomial evaluation identities and degree bounds are proved, and both complete polynomials have degree at most twenty. The remaining identity therefore reduces to twenty-one coefficient identities. The constant coefficient is proved; the other coefficients remain open. The lifts copy existing algebraic expressions, and separate evaluation theorems verify them; no external coefficient computation is used.

## Checked formal boundary

The original 98 installed inner modules comprise 38 source/model/positive-polynomial/integer-normalization modules, 21 gap grades, 22 Horner stages including terminal zero, and 17 structural/block-grading/landing modules. `PolynomialODEEvenCompactGapLift`, `PolynomialODEEvenCompactGapDet`, and `PolynomialODEEvenCompactGapCoefficient0` bring the checked total to 101. Each was checked separately with foreground `lake env lean`, copied from checked staging bytes and wired into its theorem-area umbrella. No umbrella or full build was run.

The new capstones `evenCompactHorner0_eq_unitPolynomial`, `evenCompactRawPolynomial_relative_eq`, `evenCompactRelativeDet_gap_eq_horner`, and `evenCompactUnitDet_square_eq_raw` each received one axiom audit. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. Earlier capstones were not re-audited.

Repository-wide static lint currently flags three unrelated unwired RHTower modules: `MobiusDivisorCoupledTwoSourceCone`, `PartialSubsetEnergyOrder`, and `ThreePlaneSourceMargin`. No owned module is among those errors. Their files and umbrella wiring were left to their respective work.

## Proof-size constraint

Do not repeat the monolithic determinant checks or raise their limits. The raw `unfold; ring1` attempt reached a measured 57.4 GB physical footprint while Lean abstracted the proof term. Resident memory alone hid this cost. It was interrupted and its process exited. A `dsimp only; ring1` variant reached 12.6 GB within about a minute and was also interrupted. Neither produced a checked determinant theorem.

The remaining raw gap coefficients must be proved as separately checked named identities. The generic cofactor degree bound is proved by explicit product, power, sum and difference bounds; automatic degree inference on abstract polynomial inputs was too expensive. The corpus uses `as_aux_lemma` to isolate intermediate jet proofs in `PolynomialODEEvenSeamJets`; each individual coefficient identity must also stay small. A resource failure is not a mathematical counterexample.

`pending-lean/` preserves the two unsuccessful raw proof forms and the untested determinant/source capstones. These are research candidates outside the formal corpus; do not install or wire them before successful checks. If the raw identity closes, the pending capstones target determinant reserve `10^21 M(x)^8`, inner strictness for every `C≥10^12`, and canonical weighted strictness outside the remaining explicit middle interval. Those conclusions are not yet established.

## Computation boundary

The [scientific-method guide](../../../../meta/scientific-method.md) governs future experiments. No further coefficient-generation or numerical scan is scheduled. Existing tables are proof candidates, not admitted computational facts. Any new experiment must address an uncertain mathematical question whose possible outcomes would change the approach, run briefly on Runpod with multicore code, and retain downloaded results. All owned Runpod working directories are removed.
