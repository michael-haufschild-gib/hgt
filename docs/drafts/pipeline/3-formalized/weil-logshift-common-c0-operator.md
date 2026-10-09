# Common C₀ operator and stable affine recovery receiver

Status: FORMALIZED. Dependency-closed paper proof and four public Lean theorems verified.

## Corpus question

Can the common factorial normalization on a finite-dimensional regular locus be promoted from scalar sums to a bounded linear operator into continuous functions vanishing at infinity, with a stable affine-family specialization?

Only local Lean sources were used. The lexical corpus query `factorial regular submodule continuous linear vanishing potential` found the existing uniform normalization, actual regular submodule, coefficient criterion, and individual `C₀` construction. Local mathlib checks cover the induced supremum norm on `C₀`, bounded linear-map construction, and affine composition.

## Dependency-closed paper proof

For summable coefficients v, the existing potential `pairedLogPotentialC0 v hv` has supremum norm at most U sum_n |v(n)|, where U=2 riemannAutocorr(0)>0. This follows from the global paired-kernel bound, the triangle inequality for the absolutely convergent sum, and the induced supremum norm.

Given any linear coefficient family R:E→(Nat→Real) with E finite dimensional, let L be its actual regular submodule, the preimage of the factorial-majorant sequence submodule. The established uniform theorem chooses m,B>0,D>=0 such that every a in L has summable normalized coefficients w_a(n)=exp(-Bn)R(a)(n)/(n!)^m, and sum |w_a(n)|<=D norm(a).

Define S(a) to be the actual paired-kernel potential of w_a. It belongs to `C₀`. Additivity and real homogeneity follow from the pointwise linear coefficient map and summability, which permits addition and scalar multiplication through the sums. Thus S is a linear map on L. Its norm bound is norm(Sa)<=UD norm(a), so it is a continuous linear map with operator norm at most UD. No value or linearity claim is made outside L.

For an affine coefficient family F, homogenize to H(a,t)=F.linear(a)+t F(0). Apply the linear result on the actual regular submodule of E×Real. Every regular amplitude a maps into it as (a,1). Restricting S gives a common `C₀` receiver Phi on the regular affine fibre, with norm(Phi a)<=C(1+norm a). For regular a,b, subtract their lifts: (a,1)-(b,1)=(a-b,0). Hence norm(Phi a-Phi b)<=C norm(a-b). This bound is uniform over the whole real shift line because the target norm is the supremum norm. Empty regular fibres require no extra case or hypothesis.

For native bounded-history families, divide the origin moment affine map coordinatewise by the strictly positive origin kernel. The resulting affine coefficient map is exactly the recovered-deviation sequence. The coefficient criterion identifies its regular amplitudes with histories regular at some shift. The affine receiver therefore yields a common normalized native moment sum in `C₀`, with the same affine norm bound and difference bound.

## Intended artifacts

- `WeilLogShiftC0PotentialOperator.lean`: supremum-norm estimate and common continuous linear operator on the actual regular submodule.
- `WeilLogShiftC0RecoveryReceiver.lean`: common affine coefficient receiver and native bounded-history receiver with quantitative stability.

## Verification log

Pending local API scratch check, direct leaf compile/export, axiom audit, umbrella imports, index refresh, and formal lint. No unproved analytic assumptions, numerical experiments, or external sources.

Initial direct leaf checks passed for both files. Statement review then strengthened every operator/receiver evaluation contract to `HasSum`, making convergence part of the public theorem. This excludes reliance on Lean's default `tsum` value for a nonsummable series. Rechecking the strengthened leaves next.

Both strengthened leaves now compile/export cleanly. Public operator and both receiver theorems use `HasSum`. The receiver `forall` binders explicitly name their regular subtypes; otherwise Lean inferred the ambient E from the coefficient expression before seeing the receiver application. Native evaluation uses `HasSum.congr_fun` (the installed API has no `HasSum.congr`). Axiom audit is running.

## Final checkpoint

- Both strengthened leaves passed direct `lake --old env lean` compile/export with clean logs. Fresh oleans verified.
- All four public theorem axiom audits contain exactly `propext`, `Classical.choice`, `Quot.sound`.
- Both umbrella imports unique; index refresh exited 0; all four theorems indexed exactly once in their expected modules.
- Fresh formal lint exited 1 with six unrelated errors: unreachable `RHTower.BaezDuarteLogDualEnergy`, `HTGeometry.PaperTriangularExponentExtension`, `HTGeometry.PaperVeroneseFullNormalSpace`, `HTGeometry.PaperVeroneseIndependentFaces`, `HTGeometry.QKrawtchoukCompanionTriangular`, and a `sorry` in `RHTower/BaezDuarteLogDualEnergy.lean:392`, theorem `exists_bdDualEnergy_polyLogDual_le`. No errors or proof debt in either owned leaf; their dependency audits exclude `sorryAx`.
- No full builds, external sources, numerical experiments, added axioms, or heartbeat changes.

Public results: `norm_pairedLogPotentialC0_le`, `exists_weilLogShift_uniform_c0_operator`, `exists_weilLogShift_uniform_affine_c0_receiver`, and `exists_weilLogShift_uniform_history_c0_receiver`.

Exact new insight: finite-dimensional regular coefficient families have a single normalization realized by a bounded linear map into `C₀`. Native affine regular fibres inherit actual convergent moment receivers and the supremum-norm stability estimate `norm(Phi a - Phi b) <= C norm(a-b)`. Every public evaluation contract contains `HasSum`.

Next conjecture, not yet audited or formalized: a common nonnegative envelope g in `C₀` should control the operator pointwise by `abs(S a y) <= norm(a) g(y)`. A finite basis of the actual regular subspace suggests g(y) is a fixed coordinate-norm constant times the sum of absolute basis images. The affine lift would then bound both values and amplitude differences by this same vanishing profile, yielding uniform decay over bounded regular amplitude sets. Check the local corpus before implementing.


Subsequent formalized strengthening: [common vanishing profile](weil-logshift-common-vanishing-profile.md). One nonnegative C0 profile controls all regular amplitudes and their differences, yielding simultaneous uniform decay for bounded amplitude sets and bounded amplitude separations.
