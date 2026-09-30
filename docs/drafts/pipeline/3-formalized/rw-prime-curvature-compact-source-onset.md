# Exact compact-source onset at the prime-curvature boundary

- **ID:** RW-PRIME-CURVATURE-COMPACT-ONSET
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); publication novelty audit remains provisional
- **Source:** RW; literal prime rates and established exact six-sample curvature form.
- **Statement:** At aperture `a=log 2`, actual prime Gamma-two at `log 2` is nonnegative on every compact interior source, regardless of the two pole constraints. Its zero set consists exactly of sources whose real component vanishes at all six stencil points. Immediately above this aperture, throughout `log 2<a<log(5/2)`, exactly pole-constrained compact sources of arbitrarily small form norm and complete `|Q|` attain the strictly negative sharp stencil.

## Dependency-closed paper proof

At multiplicative scale `A=2`, the index cutoff is exactly `{2,3,4}` in both orientations. All four rows `q∈{2,1,2/3,1/2}` have the same accepted targets and rates as at `A=21/10`: accepted targets lie in the closed interval `[1/2,2]`, rejected targets lie outside it. Thus the already proved exact six-sample quadratic applies at the boundary.

Write `l=log 2`, `m=log 3`, and the established sample differences as `A=f(log 1)-f(log 2)`, `B=f(log(2/3))-f(log 2)`, `C=f(log(1/2))-f(log 2)`, `D=f(log(4/3))-f(log 2)`, `E=f(log(3/2))-f(log 2)`. For a compact interior source `g`, the real normalized reader is `f(x)=Re(g(x))/(e^{x/2}+e^{-x/2})`. Its endpoint values at `x=±log 2` vanish because its topological support lies strictly inside the aperture. Therefore `C=0` and `f(log 2)=0`.

The exact curvature reduces to

`(7lm/72)(D-2B)² + (5lm/72)E² + alpha A² + beta B² + b AB`,

where `alpha=31l²/36-5lm/54`, `beta=53m²/162-7lm/27`, `b=10lm/27`.

The strict logarithmic comparisons `3l<2m` and `5m<8l` follow from `2³<3²` and `3⁵<2⁸`, respectively. They give `alpha>(7/10)l²` and

`beta-(25/72)l² = (m-3l/2)(53m/162+25l/108)>0`.

Also `b²/4<(64/729)l⁴`. Hence

`alpha beta-b²/4 > (35/144-64/729)l⁴ > 0`.

The remaining two-variable block is positive definite: complete its square as

`alpha(A+bB/(2alpha))² + (beta-b²/(4alpha))B²`.

Every displayed coefficient is strictly positive. Curvature vanishes exactly when `B=A=D=E=0`; together with both endpoint zero values, this means every one of the six samples vanishes. This concerns the real component of the normalized source. It does not force imaginary sample values or the full complex source to vanish.

For every strictly larger scale in the plateau, all six points lie strictly inside the source aperture. The exact constrained finite-interpolation theorem realizes the sharp negative stencil with arbitrarily small actual form norm and `|Q|`. Thus the compact-source sign changes at the endpoint because of support geometry, although the literal observable curvature quadratic stays fixed.

## Survivor and limits

Endpoint visibility and form-domain capacity identify an exact onset of local compact-source instability. This is a source-domain sign classification and an aperture threshold, not a sign statement for the complete Weil form. Nonnegative boundary curvature does not establish positivity of its ground floor; negative curvature above the boundary does not produce negative Weil energy.

## Audit

- Search before code: `prime curvature boundary log two endpoint`, filtered to `CCMPrimePole`; verify actual source and toolchain names before using candidates.
- Lean must retain closed endpoint indicators and classify the real source component precisely.
- No numerical experiment, added axiom, full build or raised heartbeat is allowed.

## Complete Lean certificate

`formal/GaloisForLFunctions/RHTower/CCMPrimePoleCurvatureCompactOnset.lean` formalizes the exact
closed endpoint. `aperture_indices_eq` and `gammaTwo_eq_fixed` identify the literal cutoff and
all four curvature rows with the established six-sample quadratic. `boundary_blockDet_pos`,
`boundarySchur_pos`, and `curvatureAtTwo_eq_boundary_squares` prove the strict logarithmic
comparisons, positive block determinant and complete positive-square decomposition.
`source_endpoints_zero` derives both endpoint values from strict interior support.

`compact_source_gammaTwo_nonneg` applies to every complex compact interior source, with no pole
constraint. `compact_source_gammaTwo_eq_zero_iff` identifies exactly the real component at all
six physical sample points. The intrinsic capstone
`RHTower.PrimeCurvatureCompactOnset.compact_source_curvature_onset` combines this boundary
classification with the actual sharp negative extremizers at every `2 < A < 5/2`, retaining
both exact pole constraints, arbitrary small form norm and arbitrary small complete `|Q|`.
Its statement has no unproved mathematical hypothesis parameters.

Targeted `lake --old build +GaloisForLFunctions.RHTower.CCMPrimePoleCurvatureCompactOnset:olean`
passed. Final `lake env lean GaloisForLFunctions/RHTower/CCMPrimePoleCurvatureCompactOnset.lean`
passed exit 0 without warnings. All 16 public declarations were axiom-audited in `/tmp`; only
`propext`, `Classical.choice`, and `Quot.sound` occur, including private dependencies transitively.
The new leaf is wired into `RHTower.lean`. Authoritative formal lint reports no issue on this
leaf, while unrelated concurrent reachability gaps remain in the workspace.

- 2026-09-29 — every endpoint, kernel and strict-aperture clause formalized and audited; moved to Stage 3.
- Public searches for `Weil prime curvature log 2` and `Gamma Bochner von Mangoldt curvature` found no matching boundary classification. Inspected primary research pages [TFPT Prime Front](https://www.fixpoint-theory.com/prime-front) and [CliffordNN paper source](https://github.com/tracyphasespace/riemann-lean/blob/main/Papers/CliffordNN_TwoThirds_Aug2026.md) contain no inspected exact theorem of this form. Their distinct positivity/numerical claims are not used as proof inputs. Universal absence from literature or training data remains uncertified.
