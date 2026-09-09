# HB original cutoff orbit, reverse kernel, and requested broad corpus searches

Goal ACTIVE and RH UNPROVED. Latest frontier-map instruction READ ONLY. No agents authorized. No numerical computations. One owned foreground Lean/Lake at a time; no full or umbrella builds; check axioms only newly created/changed declarations.

## Closed and installed
Ten NEW modules under `formal/GaloisForLFunctions/RHTower/`, all prefix `ThetaCuspHawking`: BMCuspOrbitIndex, BMCuspHeightOrbitFinite, BMCuspHeightRowPeriodization, BMCuspNonparabolicHeight, BMNativeCutoffOrbitSeparation, BMCuspWindowAbsoluteRegrouping, BMCuspPowerPeriodization, BMLowCuspPower, BMLowCuspPowerMean, BMNativeCutoffMellinAdmission. 681 source lines; 43 public theorems.

Each passed scratch `lake env lean`, then individual canonical `lake build <module>` in isolated workspace with existing dependency artifacts. All ten final builds warning-free. Scratch-only axiom probe checked exactly43 new public theorems; every closure uses only propext, Classical.choice, Quot.sound. Axiom process97275 exit0. Installed10 sources+20olean/ilean with exact byte comparison and final SHA256 verification. Ten imports added once to RHTower umbrella; no umbrella build. Owned scratch `/tmp/hb-cutoff-orbit.84xi32pe` removed after all sessions terminal. No owned live Lean/Lake process left. Do not rebuild or re-audit this completed batch.

Formal proof card: `docs/drafts/pipeline/3-formalized/hb-native-cutoff-orbit-kernel.md`. Active next proof: `docs/drafts/pipeline/1-in-progress/hb-native-cutoff-orbit-mellin.md`. Physical chain card `hb-qnm-parameter-continuation.md` updated. STATUS F20i-y extended with route-independent distinction between pointwise finite sums and summability of integral norms. Frontier map unchanged.

## Exact new mathematical results
Original cuspWindow partitions EVERY real coordinate; cuspOrbitEquiv identifies gammaSetHalf x integers with original PSL2Z, using actual unique translation/halfRep factorization. For h=0 at y<=2, every fixed-point orbit has finite support (original height bound max(y,1/y), compact rectangle [-1,1]x[2,max], proper discontinuity), hence full sum and norm sum admitted despite no upper compact support. Exact P_h(z)=sum_halfrows h(Im gamma_v z)=h(y)+full nonparabolic sum. Nonidentity halfrows have c>0 and transformed height<=1/y. Thus full nonparabolic correction vanishes at ALL horizontal coordinates when y>=1/2.

Original native h_q=eta(y)*A_(q-1/2)(y)^2/2 matches squareCutoffSeed definitionally. Global native residual equals original squareResidual when y>=1/2; its exact horizontal mean there is (1-eta)*A^2/2+4*sum amplitude^2. All lower images retained.

Original nonnegative translation window preserves row norm: sum_n norm(seed_h(T^n gamma_v z))=norm(h(Im gamma_v z)). Row summability therefore admits full projective orbit even for profiles reaching0. Full coprime row sum=2*halfrow sum. Actual Eisenstein convergence then gives Lambda(2s)*P_(y^s)=scalar(s-1/2) for Re s>1, with original normalization.

lowCuspPower s y=if y<=1/2 then y^s else0 has admitted full row/orbit sums Re s>1. On y>=2, Lambda(2s)*P_low=scalar(s-1/2)-Lambda(2s)*y^s. Actual horizontal mean is Lambda(2s-1)*y^(1-s), derived from original scalar constant term, not assigned as definition.

Native h_q globally continuous and norm<=C*y^2 for ALL real y, C=(norm Lambda(2q-1)+norm Lambda(2q))^2/2. Strict Xi strip derives both positive exponents q,1-q; no sourcebound supplied. Actual reflected Mellin moment integral_2∞ y^(-s-1)h_q(y) absolutely admitted for Re s>2 using C*y^(1-Re s).

## Precise remaining hard target
For Re s>2, prove Lambda(2s)*integral_0^(1/2) y^(s-2)*Cnp_q(y)=Lambda(2s-1)*integral_2∞ y^(-s-1)*h_q(y). Cnp is actual full nonparabolic cutoff horizontal mean. Equivalently unfold pairing in both directions: integral_strip low_s*P_h dmu = integral_fd P_low_s*P_h dmu = integral_strip h*P_low_s dmu. Reverse mean and RHS height moment proved, but BOTH strip product admissions and norm-integral/sum interchanges NOT yet proved. Do not claim Mellin value or promote whole active card.

Proposed analytic proof not yet Lean: sigma=Re s>2. Norm P_h<=C*real positive P_(y^2), norm P_low_s<=P_low_sigma via original nonnegative window and real height powers. Horizontal norm-density bounds suggested by actual means: const*(y^sigma+y^(sigma-3)) near0 and const*y^(1-sigma) at∞. Need measurable sum/indicator construction, positivity bridge for real cpow row sums, nonzero Lambda(2sigma) (zero-free right half-plane), Tonelli/Fubini using exact hyperbolicstrip chart. Then existing hasSum_fdUnfoldTerm_half/summable_fdUnfoldTerm and actual modularity give both unfoldings. Pointwise finite orbit support alone insufficient. Whole Fourier–Bessel Mellin evaluation, original source continuation to physical s=q/2, outgoing joint inverse, physical adjoint left residue, nonvanishing, independent extinction, RH still open.

## Verification scope
Index refreshed once. Repository `lint --check-generated` exit1: unreachable unrelated `GaloisForLFunctions.HTGeometry.FokasLenellsRawMixedPrimitive`; stale formal/LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md. That Fokas file appeared during concurrent work. No error reported in new ten leaves and no proof-debt violation reported. Global gate NOT passed; documented in proof card. Do not chase other threads' live modules or repeatedly rerun global checks. Scoped git diff --check passed. New proof card relative links resolved. Frontier git diff remained empty.

## Latest user search request satisfied
Ran `python3 scripts/formal_tools.py research Fokas`, THEN same tool `research Higgs`; then fetched ALL matches with --per-module0 --limit10000 --explore0 --json --no-refresh. Fokas1572 declarations98 modules; Higgs285 declarations26 modules. Broad single-term searches, no AND narrowing. Read complete inventory.

Read actual `RHTower/FokasLenellsDirectResolvent.lean`: directSolution_existsUnique at147, norm directCauchyOperator<=4/9, inverse<=9/5 for regularized scattering symbol after explicit rescaling of Schwartz potential. This is Riemann–Hilbert, not Riemann Hypothesis. HB operator/domain/data identification and preservation of original source still needed. Other indexed candidates include SpectralVolterra actual spectral ODE construction with factorial convergence, AnalyticRH holomorphic slices and actual Hardy boundary realization.

Read actual HTGeometry/HiggsCausalOrbit: exact quaternionic radial/orthogonal orbit decomposition, no physical time/gravity identification. CausalRayPolarityNonselection: positive null outer squares for H and its spin flip, equal scalar weight, adjugate/mutually annihilating, explicit distinct north-pole example at71. HiggsSpinorNullCone and GomesHiggsResidualCircle are other strong matches. These give mathematical identities, not a proved identification with HB response/polarity. Findings documented on physical chain card.

## API pitfalls already resolved
Use bare gammaSetMatrix (not EisensteinSeries.gammaSetMatrix). summable_prod_of_nonneg exists; summable_prod_iff and summable_prod_iff_of_nonneg absent. Summable.ofReal absent. tsum_eq_zero absent: prove pointwisezero then simp. Explicit height functions in rewrite avoid typeclass heartbeat loops; no increased heartbeat used. Real.smoothTransition.contDiff may need (n:=1). For y∈Ioi2 use `change (2:ℝ)<y at hy` before linarith. Fin2 simplification needs Matrix.cons_val_one AND cons_val_zero.

Previous closed batch in mem:hawking_bm_native_square_residual_unfolding_2026_09_08; do not re-audit its8modules22theorems.