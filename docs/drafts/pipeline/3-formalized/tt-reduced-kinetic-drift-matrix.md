# Complete reduced kinetic drift matrix (C81)

- **ID:** tt-reduced-kinetic-drift-matrix
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route TT; tt-kinetic-contraction-source
- **Statement:** Every coefficient of the complete kinetic source has an exact polynomial drift factor, including at zero clock and zero drift; all160 moment drift cells and their whole-row reconstructions are audited.

## Goal

Expose the complete signed coefficients needed for the finite-clock source
inequality. This is an exact representation result. No source-value or
Bernstein-control sign is asserted.

## Gates

- [x] Source-pure target and full literal source retained.
- [x] Dependency-closed algebraic proof below, [PROVED HERE].
- [x] Seven direct production leaf audits,295 imported declaration audits.
- [ ] Standalone publication.

## Proof

Specialize the complete cleared slope at drift zero. For nonzero clock its
original source factorization makes this specialization zero. Polynomial
extension across zero clock proves the same identity for every clock.
Evaluate the entire degree19 kinetic polynomial at drift zero and use
polynomial extensionality. Each kinetic coefficient therefore has zero
constant drift coefficient. Its `Polynomial.divX` is an exact quotient;
coefficient b of the quotient is original coefficient b+1.

Consequently, for all complex h,v,z, with no nonzero or sign premise,

`clearSlope(h,v,z) = v * sum_(j<20) reducedCoefficient(h,j)(v) * z^j`.

Taking real parts and applying the already audited finite Bernstein identity
produces the complete reduced controls and their exact difference formula.
The moment table uses all35 kinetic coefficients from C80, extracts all160
drift cells, and proves every whole-row degree bound and reconstruction.
The two-index convolution is the ordinary polynomial product identity in
both variables; all signs remain.

## Lean certificate

Namespace `HTGeometry.ThetaRatioKineticContraction`.

- `ThetaCuspRatioKineticDriftMoments2/4/6/8/10`:160 exact scalar cell identities,
  35 degree bounds and35 evaluated expansions.
- `ThetaCuspRatioKineticDriftTensor`:35 arbitrary-row reconstructions,
  exact product convolution and linear operations.
- `ThetaCuspRatioKineticReducedDrift`: full drift removal, complete reduced
  source expansion, full reduced controls and difference identity.

Capstones: `completeKineticSlope_reduced_expansion`,
`reduced_source_control_difference`, `kineticDriftCell_mul`.
All seven leaves pass `lake --old env lean -o ... <module>.lean`, warning-free,
and are wired once into RHTower. No full or umbrella build was run.
`/tmp/TTC81ProductionAudit.lean` audits all295 declarations; log
`/tmp/tt_c81_production_axioms.log` contains only `propext`, `Classical.choice`,
and `Quot.sound`. Manifest: `/tmp/tt_c81_production_manifest.json`.

The complete central cof2 cell (kinetic8, drift5) also passes against these
production imports, with standard axioms, in the active scratch pilot
`/tmp/TTC81CofactorCentralCell.lean`. It is a normalization pilot, not a sign.

Formal lint terminal1: fifteen unrelated missing theorem-area imports;
exact list in `/tmp/tt_c81_lint.log`. No C81 error. Scoped forbidden-declaration,
raised-limit, whitespace and wiring checks pass. Forty-one superseded owned
scratch files/caches removed; cleanup manifest `/tmp/tt_c81_cleanup_manifest.json`.

## Learning and remaining frontier

Raw natural/integer casts must be unfolded before hom mapping. A final
`norm_num [Nat.rawCast,Int.rawCast]` is also needed after coefficient extraction:
otherwise negative-integer polynomial coefficients can survive as atoms inside
an apparently scalar normal form. The trace identified this exactly; cleanup
made the previously failing whole central cofactor pass without raised limits.
An explicit outer-minus cofactor identity must precede product expansion.

C83 later found unevaluated coefficients of `Polynomial.X` in some C81
witnesses. All C81 equalities and support bounds remain valid. The corrected
C82 block/cofactor producers explicitly simplify `Polynomial.coeff_X` before
multiplication; the earlier selected trace did not establish literal
normalization of every C81 witness.

No hard finite-clock sign gap was closed. Next: all complete cofactor/block
cells, then the actual reduced-control inequalities (or another full-value
certificate). A negative control alone would reject that certificate, not
source positivity. Full source quadratic, fourth Schur gap, compact/adverse-ray
join, integrated/all-rank closure and RH remain open.

## Log

- 2026-10-06 — all seven production leaves and295 declarations audited.
