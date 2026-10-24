# The exact Ramanujan correction of the product-residue profile

- **ID:** goldbach-product-residue-ramanujan
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite bridge; no novelty claim
- **Parent:** [flat prime-dilation dispersion](../../2-fully-proven/goldbach-flat-prime-dilation-dispersion.md)
- **Module:** `formal/GaloisForLFunctions/goldbach/ProductResidueRamanujan.lean`

## Exact statement

For every positive integer q and residue r modulo q, let
ν_q(r)=#{(a,b) modulo q:ab=r}. Then

    ν_q(r)/q = Σ_(d|q) c_d(r)/d.

Here c_d is the actual finite Ramanujan character sum. The equality
includes r=0, q=1, and all nonunit residues. Both the integer-exponential
and CGL reduced-residue conventions are identified in Lean.

For every actual function f:Z/qZ→ℂ, finite pairing gives

    (1/q) Σ_(a,b mod q) f(ab)
      = Σ_(d|q) (1/d) Σ_(r mod q) c_d(r) f(r).

No periodic mean, equidistribution estimate, or supplied Fourier
identity is a premise. This is the exact complete-residue correction
used in the two mixed terms of the flat dispersion calculation.

## Paper proof [PROVED HERE]

The already formalized product-residue Fourier identity is

    ν_q(r)=Σ_(a mod q) gcd(q,a) e_q(−ar).

Group the actual frequencies by d=q/gcd(q,a). For each divisor d of q,
the frequencies are exactly a=(q/d)u with u a unit modulo d. Their
common multiplier is q/d, and their character sum is c_d(−r).
Ramanujan sums are even, so this is c_d(r). Dividing by the positive
integer q proves the first identity. Finite regrouping after multiplying
by f(r), and the actual multiplication-fibre pairing identity, prove
the second.

The identification of conventions rewrites the CGL sum as a sum over
integer representatives 0≤u<d. The exact equivalence
`IsUnit (u : ZMod d) ↔ Nat.Coprime u d` gives the same support; the
standard additive character's exponential formula gives the same term.
There is no asymptotic step.

## Corpus reuse and certificate

- `goldbach/ProductResidueProfile.lean` supplies the actual count,
  its gcd Fourier spectrum, and the multiplication-fibre pairing.
- `RHTower/EstermannRamanujanMainTerm.lean` supplies exact finite
  grouping by reduced modulus and evenness of Ramanujan sums.
- The CGL reduced-residue convention is the one already used by
  the Kloosterman and Bézout–valuation incidence modules.

The five unconditional roots in `GaloisForLFunctions.Goldbach` are:

- `estermannRamanujanSum_eq_cgl`
- `productFrequencyGcd_eq_quotient`
- `productResidueCount_eq_ramanujanDivisorSum`
- `productResidueCount_eq_cglRamanujanDivisorSum`
- `productResidue_ramanujan_pairing`

Direct final check from `formal/`:

```text
lake --old env lean GaloisForLFunctions/goldbach/ProductResidueRamanujan.lean
```

Exit 0, no errors or warnings. All five transitive `#print axioms`
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
No added axiom, proof hole, analytic premise, or raised elaboration
limit occurs. Log: `/tmp/hgt-goldbach-product-ramanujan-audit.log`.
Audit directives were removed after verification. The completed module
is imported by `goldbach/Main.lean`; no umbrella build was run.
Exact corpus lookup finds the CGL-form final root. Forbidden-marker and
targeted whitespace checks pass; all 35 local links in the three correction
documents resolve. The proof-audit log is retained.

## Remaining obligation

A complete-residue identity does not estimate finite curved regions.
The determinant row count, both mixed endpoint estimates, the masked
conductor kernel, and the full flat dispersion theorem remain separate
Lean obligations. Signed Möbius cancellation and Goldbach remain open.

## Log

- 2026-10-24 — Completed the exact finite correction and both character
  conventions; direct leaf check and all five closure audits passed.
