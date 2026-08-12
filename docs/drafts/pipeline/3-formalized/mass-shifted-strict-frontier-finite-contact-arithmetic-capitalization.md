# Mass-shifted strict-frontier finite-contact arithmetic capitalization

- **ID:** `mass-shifted-strict-frontier-finite-contact-arithmetic-capitalization`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** Every occupied physical strict frontier has a finite first Padé normal contact; order one is the negative first omitted remainder, while every order at least two is a nonzero admission-selected bilinear rational–Gamma-minus–von-Mangoldt source with the alternating sign forced by the positive chamber.

## Goal

Replace the residual “flatter than quadratic” branch by its complete finite-contact arithmetic
classification.  This does not bound contact order uniformly across frontiers; it identifies the
remaining global obstruction as contact-degree escape rather than infinite local flatness.

## Gates

- [x] 0 → 1 in-progress: exact claim, source-pure producer, falsifiers, and corpus dependencies identified
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: exact Lean theorem, targeted build and axiom gate green
- [ ] 3 → 4 publication-ready: standalone proof and independent priority review

## Approach

At strict frontier `y = tau_(n+1)`, put `m=n+2` and take canonical terminal-normalized null vector
`c` of singular block `H_(m+1)(y)`.  Infinite Xi divisor excludes equality with finite flat
quadrature at every moment, hence selects finite first defect `delta_(2m+d)`.  Right-chamber
positivity forces `(-1)^d delta_(2m+d)>0`.  If `d=1`, defect is first omitted monic remainder.
If `d>=2`, choose null lifts `P X^(d-2)` and `P`; corpus all-contact producer gives literal
arithmetic source `(2m+d) delta_(2m+d)` before aggregation.

## Conjecture → proof/fail ledger

1. `[FALSIFIED]` Strict terminal frontier forces odd contact.  Terminal failure means failure of
   positive definiteness, so an isolated even-order singularity may itself be supremal while both
   punctured sides remain positive definite.
2. `[PAPER-PROVED]` Infinite-order local flatness is impossible and every surviving
   higher contact is a literal bilinear arithmetic source.
3. `[LEAN-PROVED]` Exact Schur factorization and arbitrary-order newborn-norm residue; moving
   admission contributes no hidden leading correction.
4. `[OPEN CORE]` Quotient by wall numerator and decide whether contact degree can escape cofinally
   or explicit all-order source prices are globally nonsummable.

## External audit

Positive-measure total positivity and matrix-model Hankel theory keep determinants strictly
positive; singular/indefinite Padé and Toda theory allow zero/pole strata but do not identify the
shifted-Xi admission-selected rational–Gamma-minus–von-Mangoldt normal coordinate.  Exact priority
remains `[NOVELTY UNVERIFIED]`.

## Dependency-closed paper proof `[PROVED HERE]`

Let `y=tau_(n+1)` be an occupied strict frontier, `m=n+2`, and let `c` be canonical
terminal-normalized degree-`m` admission vector at `y`.  Strict-frontier classification gives
`H_m(y)>0`, `H_(m+1)(y)>=0` singular, and `H_(m+1)(y)c=0`; terminal normalization gives
`c_last=1`.  Occupancy and strictness imply `y>0`.

The shifted-Xi support has infinitely many distinct divisor coordinates.  Therefore its moment
germ cannot equal finite flat quadrature germ at every order.  Well-order first nonzero flat-shadow
defect.  There is a finite `d>0` such that

```text
delta_k=0  for k<2m+d,       delta_(2m+d) != 0.
```

For every `u>0`, `y+u` lies strictly beyond degree-`m-1` terminal frontier, hence
`H_(m+1)(y+u)>0`.  Exact moving-null Padé contact series and right nonnegativity force

```text
(-1)^d delta_(2m+d) > 0.
```

If `d=1`, first-defect identity gives `delta_(2m+1)=R_m(y)`; thus `R_m(y)<0`.

Suppose `d>=2`.  Put `P=P_c`, `A=P X^(d-2)`, and `B=P`.  Admission-sensitive bilinear producer
forms both lifts before rational–Gamma/von-Mangoldt aggregation.  Its exact all-contact law is

```text
ArithmeticSource_y(A,B) = (2m+d) delta_(2m+d).
```

Since `2m+d>0`, its alternating sign is strictly positive.  This exhausts all finite `d>0` and
proves the claim.  No RH premise, generic positivity extension, finite observer, or fixed reporter
is used.  QED.

## Log

- 2026-08-12 — card opened after strict-frontier odd-contact conjecture failed; finite all-contact arithmetic survivor frozen.
- 2026-08-12 — dependency-closed paper proof completed; moved to Stage 2.
- 2026-08-13 — exact all-contact local law and premise-free cofinal phase formalized in
  `XiShiftedStrictFrontierAllContactArithmeticSource.lean`; direct Lean and axiom audit green.
- 2026-08-13 — exact Schur determinant/admission-norm factorization and arbitrary-order strict-
  frontier norm residue formalized; conjectural binomial price upgraded to `[LEAN-PROVED]`.
