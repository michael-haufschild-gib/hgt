# Actual character seam flux controlled by inversion phase energy

- **Stage:** 3-formalized
- **Type:** POSITIVE QUANTITATIVE SOURCE BOUNDARY LAW
- **Goal:** Control the literal paired circular-boundary character flux by the actual inversion-transfer loss and original physical derivative energy, retaining coherent channel interference.

## Corpus evidence and positive conjecture

Revalidated both cycle46 source hashes unchanged. Explicit OR boundary-impedance/two-projections/angle-gap/Hardy-gluing/spectral-concentration query returned23 declarations in9 modules. Broader single-term OR gluing/impedance/uncertainty, plus projection-angle and Schur-complement phrases, returned728 declarations in179 modules. Artifacts: `/tmp/selberg_gluing49_corpus.json`, `/tmp/selberg_gluing49_wide.json`. Read `TwoProjectionDeficiency` (a genuine angle estimate requires its explicit angle bound), `ProjectionCornerCommutator` (exact complementary projection corners), and the actual source unit-circle current transport. `SelbergScatteringSpectralConcentration` concerns an independent Xi approximate-family input and is not a supplied Maass source estimate.

The complementary-corner algebra suggests a sharper source statement. Let P=P_r and Q=Q_-r be the actual upper and lower character projectors. Conjecture: the actual diagonal transfer loss satisfies

`||v||²-||C_rr v||² = ||(P-Q)v||² + ||(I-Q)(I-P)v||²`.

Paper proof: `(P-Q)v=(I-Q)Pv-Q(I-P)v`. These two outputs are orthogonal under Q. Split `(I-P)v` into Q and I-Q pieces, then compare with the proved two-stage transfer-loss decomposition. Every term is an actual original projector, and the retained last square supplies the exact difference between transfer loss and projection mismatch.

On the original circular seam, inversion sends source values by the actual unitary U and reverses the radial derivative. Hence the sum of an upper-character radial flux at paired points is exactly `Re <(P-Q)v,w>`, where v is the original source value and w its original radial derivative. Cauchy–Schwarz and the exact identity above give

`|paired flux|² <= (||v||²-||C_rr v||²) * ||w||²`.

The radial derivative should satisfy `||w||² <= |z|²*gradientDensity(z)`, giving the full physical-gradient bound on the unit circle. The transfer loss is already the actual complete triple phase-displacement energy. This retains the coherent source at the varying arc height; no fixed-height Fourier orthogonality is substituted on the curved seam.

## Gates

- [x] Source revalidation, broad corpus discovery, and dependency-closed paper candidate.
- [x] Exact complementary-corner transfer-loss decomposition and flux bound.
- [x] Actual source derivative transport and paired character flux identity.
- [x] Physical radial derivative estimate and quantitative unit-circle phase/gradient law.
- [x] Scratch/source checks, single-module final builds, axioms, index/wiring/lint, cleanup.

## Positive strengthening and complete paper proof

All conjectures above are now proved. The projection identity holds for every actual character pair r,s, with upper projector P_s and lower projector Q_-r. It supplies the exact double-complement remainder, not merely a norm contraction. Pairing the mismatch with any original derivative vector gives the quantitative coherent flux bound by Cauchy–Schwarz.

The new `sourceDerivative` is the complete vector of original quotient-field derivatives. `sourceDerivative_eq_dir` identifies it with the Fréchet derivative of the canonical source vector. The existing original Möbius chain rule transports it with the reciprocal-square Jacobian. Inversion sends the radial tangent to the negative radial tangent at the image point; the complete derivative vector therefore changes by minus the actual regular unitary. Applying this at S^-1 z avoids assuming equality of the two inverse deck motions on arbitrary vectors. Actual lower-character conjugacy then proves the paired radial-flux identity.

The radial estimate exposes a stronger exact identity:

`||D_v F||² + ||D_(i*v) F||² = |v|² * gradientDensity`.

Paper proof: write v=x+i*y, expand the two real-linear directional derivatives as x*D_x+y*D_y and -y*D_x+x*D_y, and cancel their mixed inner products. The two coordinate derivative norms are exactly the original gradient density. Consequently the seam inequality retains the entire positive term `transferLoss * ||D_(i*z) F||²` on its left side.

The actual character-mass derivative equals twice `Re <P_r F,D_v F>`, proved by the original chart's Fréchet chain rule and orthogonal-projection self-adjointness. Thus the flux is attached to literal projected mass, not a new independent boundary datum. On the unit circle, S^-1 pairs (x,y) with (-x,y), and |z|²=1. Substituting the already audited full triple phase-displacement identity proves the literal arithmetic phase/physical-gradient bound.

The original circle normal density uses tangent `(-x/y,-1)=-(1/y)*(x,y)`. Its current is exactly `-(2/y)*radialFlux`, including the arc-length Jacobian. Hence the squared paired outward current is at most `4/y² * transferLoss * gradientDensity`. On the actual modular arc, x belongs to [-1/2,1/2] and y²=1-x²>=3/4, giving the proved level-independent bound

`pairedNormalCurrent² <= (16/3) * transferLoss * gradientDensity`.

This is a boundary estimate for the original source at every level. The coefficient16/3 is a bound for its squared normal current, not a claimed spectral quarter constant.

## Lean and audit certificate — cycle47, 2026-09-09

- `formal/GaloisForLFunctions/RHTower/SelbergMaassProjectionFlux.lean`: eight public theorems.
- `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterSeamFlux.lean`:21 public declarations, including the original derivative/current definitions and the exact physical boundary laws.
- Both complete scratch files and exact source checks passed using `lake env lean`. Only the projection module's needed olean was emitted for the dependent scratch import.
- Final builds were serialized: `lake build GaloisForLFunctions.RHTower.SelbergMaassProjectionFlux` rebuilt only its target (11s), then `lake build GaloisForLFunctions.RHTower.SelbergMaassCharacterSeamFlux` rebuilt only its target (4.7s).
- The post-build `/tmp` axiom audit covers every public declaration. All29 depend only on standard `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or admission occurs. Source hashes remained unchanged.
- Both modules are wired once into `RHTower.lean`. The refreshed search index contains31 entries including two local instances; all29 public declarations also occur under the exact module in `LEAN_API.md`. Repository formal lint passed with existing large-file warnings.
- Every task-owned Lean/build/index/lint handle is terminal; a final process check found no task-owned Lean worker. No build overlap, full/umbrella build, numerical experiment, commit, or push occurred in this cycle.
- Artifacts: `/tmp/selberg_seam49_manifest.json`, `/tmp/selberg_seam49_audit.json`, `/tmp/selberg_seam49_coverage.json`, and the scratch/source/build/axiom/index/lint files under the same prefix.

## Next positive test

Attach these literal character currents to the integrated characterwise core–cusp energy identity, retaining the original Bessel boundary forms, all Fourier modes, and the angular remainder. Test whether the actual arithmetic phase coupling controls the resulting complete quarter deficit. The required bulk comparison is to be proved from that original source; it is not an input hypothesis.

The full-domain coefficient-four comparison remains unproved and is never an input hypothesis.
