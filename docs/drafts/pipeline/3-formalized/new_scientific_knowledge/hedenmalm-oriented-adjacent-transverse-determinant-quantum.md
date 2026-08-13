# Hedenmalm oriented-adjacent transverse determinant quantum

- **ID:** `hedenmalm-oriented-adjacent-transverse-determinant-quantum`
- **Stage:** `3-formalized`
- **Status:** `[OWN CONJECTURE LEAN-PROVED] [AXIOM-AUDITED] [NO 75% CLAIM]`
- **Parents:** `hedenmalm-adjacent-feature-krein-index-separator.md`,
  `hedenmalm-critical-feature-holomorphic-sector-coercivity.md`

## Frozen claim

Let `z=x+iy`, `|y|<1/2`, choose an integer center `t` with `|x-t|<=1/2`, and orient the second
feature toward `x`: use `t+1` when `t<=x`, and `t-1` when `x<=t`.  For the corresponding pair of
critical-feature evaluations `a,b`, write

```text
Delta = Re(a) Im(b) - Im(a) Re(b).
```

Then, for `y!=0`,

```text
(96/145)^2 <= Delta^2/y^2,                              (TD1)
reflectedPairBlockDet(a,b)/y^2 <= -4(96/145)^2.         (TD2)
```

Unlike bare negative index, `(TD1)` gives a uniform quantitative transverse determinant after the
forced inverse-square Green normalization, including arbitrarily submicroscopic `|y|`.  Critical-line
multiplicity still gives determinant zero before normalization.

## Paper proof

Put `u=x-t` and choose `s=1` for `u>=0`, `s=-1` for `u<=0`.  Exact adjacent-feature algebra gives

```text
|Delta|/|y| = 8 [1-y^2-u(u-s)] /
  (|1+(z-t)^2|^2 |1+(z-(t+s))^2|^2).
```

Orientation gives `u(u-s)<=0`, hence numerator bracket is greater than `3/4`.  Also
`|u|<=1/2`, `|u-s|<=1`, and direct norm-square expansion gives denominator at most
`(29/16)*5=145/16`.  Therefore `|Delta|/|y| >= 96/145`; squaring proves `(TD1)`, and
`reflectedPairBlockDet=-4 Delta^2` proves `(TD2)`.

## Hostile audit

1. Orientation chooses between two predeclared adjacent source blocks; no new feature center is
   fitted to a zero.
2. Division by `y^2` is singular and cannot be replaced by a bounded holomorphic source operator.
3. Determinant of a sum is not sum of determinants.  Exact prime--Gamma formulas for the four
   matrix entries do not yet give a dyadic arithmetic bound for sum of normalized block determinants.
4. No density conclusion is permitted without that exterior-square/rank--trace source estimate.

## Gates

- [x] corpus collision search
- [x] exact paper proof and rational constant
- [x] Lean determinant quantum
- [x] Xi nearest-integer oriented specialization
- [x] targeted build, forbidden scan, axiom audit, umbrella wiring
- [ ] source-native exterior-square dyadic budget

## Lean certificate

Module `HedenmalmOrientedAdjacentTransverseDeterminantQuantum.lean` proves both oriented local
branches, their disjunctive two-reporter theorem, the normalized reflected-block determinant
quantum, and actual strict-right Xi-copy specialization.  Targeted build completed over 12,950
jobs.  Key declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`; forbidden
declaration scan is clean.  Module is wired into the `RHTower` umbrella.
