# Gomes arXiv corpus experiment: tenth completed batch

Goal remains active and unbounded. User wants as many direct corpus applications as possible of arXiv 2607.24901, latest 2509.25276v7, and 2404.10461. Only search/read Lean, not pipeline cards/docs. New theorems carry no supplied mathematical proof hypotheses/axioms; natural universally quantified data and closed iff classifications are used. No numerical/decision computation tactics in new proofs. One foreground Lean process, scratch `lake env lean`, exact final target `lake build`, never umbrella/full builds; no commits/subagents. Session init was completed earlier.

## Verified state
52 new theorems across 7 modules. Cumulative experiment: 509 theorems / 58 modules (prior 457/51). All seven target builds passed; all 67 audited declarations closed with only Classical.choice, Quot.sound, propext. These 67 include 52 theorems, 10 definitions, new model type, its 3 constructors and recursor. All new imports wired into HTGeometry.lean. No own stale Lean/lake processes.
All source files are formal/GaloisForLFunctions/HTGeometry/ with namespace GaloisForLFunctions.HTGeometry:
- GomesMomentModels: 3 theorems/1 def plus inductive.
- GomesMomentQuotientGeometry: 8/3.
- GomesMomentHeightExpansion: 7/0.
- GomesProjectiveFlux: 8/1.
- GomesMomentComplexFrameEnergy: 9/3.
- GomesMomentNormalizedFlux: 6/1.
- GomesMomentFluxReconstruction: 11/1.
Artifacts /tmp/hgt-gomes/tenth/: modules.json, counts.json, build-status.json, AxiomAudit.lean, axioms.log, axiom-audit.json, progress.json with source SHA256s, lint.log, next-models-search.txt. Prior ninth batch's nine source hashes revalidated unchanged at turn start.
Global lint failed only on unrelated untracked/unwired RHTower.FokasLenellsSecondTimeSymbols plus stale LEAN_API.md and LEAN_OVERVIEW.md. That unrelated Lean source was authoritatively modified after the index command ended. Do not wire another task's unfinished file.

## Results
GomesMomentModel has data-only constructors .arcsine, .gamma(logShape:Real), .fock(B:Fin k -> Matrix(Fin(d+1))(Fin(d+1)) C). .moments returns existing normalizedCentralBinom, gammaShapeMoment(exp r), completed free-Fock moments. No constructor carries a positivity proof. gomesMomentModel_positive, _norm_pos, _recurOff_pos discharge all conditions internally.
Consecutive quotient Q_(n+1)/Q_n has imaginary part exactly source imaginary part times weight K_n*h_n/normSq(Q_n), where K is existing positive Christoffel kernel. Possible denominator zeros are confined to the real axis using existing MomentRealRootedness. Imaginary part positive/negative/zero iff source imaginary part has corresponding sign, including Lean's quotient convention at real zeros. Weight at level0=1; weight at n+1>1 iff denominator nonzero. Absolute imaginary height never contracts, and beyond first level strictly expands iff source nonreal. Quotient conjugation symmetry and DifferentiableOn C on {z|z.im!=0} proved.
Internal flux(v)=Re(v^H iJ v)=2 Im(v0 conj(v1))=2 normSq(v1) Im(v0/v1). Positive flux iff projective chart lies in upper half-plane, even degenerate charts. Scalar rescaling multiplies flux by normSq(c). All projective coordinates forget exactly every nonzero scalar; full flux tensor stabilizer is exactly normSq(c)=1. Jacobi step flux balance and Riccati imaginary-part law are unconditional.
Complex frame F_n=[[Q_(n+1),R_(n+1)],[Q_n,R_n]]: actual recurrence advance, determinant=-h_n/h_0, invertible at every complex z. Wave_v(k)=Q_k*v0+R_k*v1; E_n=sum_(k<=n) normSq(wave_v(k))/h_k. E nonnegative; E_(n+1)>0 iff v!=0. Exact balance flux(F_n*v)/h_n+flux(v)/h_0=2 Im(z)*E_n.
Normalized flux D_n=h_n^-1 F_n^H(iJ)F_n+h_0^-1(iJ) is Hermitian and has quadratic value cast(2 Im(z)*E_n). D_n PSD iff Im(z)>=0; D_n PD iff Im(z)>0 and n!=0.
Explicit Gram G_n=sum weighted rank-one observations of row(Q_k,R_k) has quadratic value cast(E_n). Existing corpus quadratic determination reconstructs full tensor D_n=2 Im(z)*G_n. G_n PSD always; G_n PD iff n!=0. Scalar c*G_n PSD iff c>=0, PD iff c>0 and n!=0. D_n=0 iff Im(z)=0. -D_n PD iff Im(z)<0 and n!=0. This closes the whole-frame extension of ninth batch's two-step observation result.

## Important implementation/evidence lessons
The private audit parser inherited from previous batches incorrectly counted a header comment line beginning `theorem upgrades ...` as a declaration. Fixed /tmp/hgt-gomes/tenth/prepare_audit.py to lex away nested block comments, line comments and strings before declaration/namespace regexes. Correct count is 52, not the temporary pre-audit 53. Added explicit type/constructor/recursor audit entries. Existing formal research index correctly ignored that header; search for upgrades in the module returned zero. Reuse this corrected audit preparation, not old parser.
Matrix.mulVec_mulVec orientation: B*(A*v)=(B*A)*v, so expanding product action uses `rw [← Matrix.mulVec_mulVec]`.
Matrix.vecHead/vecTail are actual definitions in Mathlib/Data/Fin/VecNotation.lean. Fin2 mulVec simp can leave these; include Matrix.vecHead,Matrix.vecTail or use explicit helper vector identities. Do not expect `change` to simplify 1*v+0*v definitionally.
Complex.div_im, normSq_pos, normSq_eq_zero verified. No Complex.div_mul_conj. Convert complex order on real casts explicitly using Complex.zero_lt_real/zero_le_real. `simp` may already turn product=0 into a disjunction; inspect before applying mul_eq_zero.
Matrix.sum_mulVec is in Data/Matrix/Basic, dotProduct_sum/root dotProduct_smul in Data/Matrix/Mul. Matrix.smul_mulVec, vecMulVec verified. Matrix.isUnit_iff_isUnit_det verified.
Matrix.PosDef/PosSemidef.of_dotProduct_mulVec_pos/nonneg, dotProduct_mulVec_pos/nonneg verified. For Hermitian congruence, no method Matrix.IsHermitian.conjTranspose_mul_mul; can unfold Hermitian then simp [Matrix.conjTranspose_mul,Matrix.mul_assoc] with H^H=H.
Polynomial.differentiableAt_aeval exists in Analysis/Calculus/Deriv/Polynomial; explicit import used. `Polynomial.aeval_algebraMap_apply` verified. monicOrthoC_ofReal is not imported by ComplexSecondKind alone.

## Sources already read (do not reread)
ComplexChristoffelDarboux.lean 1-165: root namespace HTGeometry, monicOrthoC, monicOrthoC_conj, christoffelDarbouxC_conj, kernelSum_mul_im. ComplexSecondKind.lean 1-86: secondKindC and recurrence, monicOrthoC_succ_succ, mixed CD, monicOrthoC_wronskian. MomentRealRootedness.lean95-122: monicOrtho_aeval_ne_zero (h:PositiveMomentForm s) n {z} (hz:z.im!=0). NevanlinnaRealMatrix.lean1-40: real evaluation bridges; did not need to import heavy module.
MatrixQuadraticFormDetermination.lean whole (<100 lines): matrix_eq_of_quadraticForm_eq M N h; matrixQuadraticForm_conjTranspose; skew-Hermitian classification. Reused existing polarization; do not duplicate it. Its existing norm_num call was not copied into new proofs.

## Next frontier
All 34 positiveMomentForm search declarations were retrieved across both pages, per-module cap0, exploration0; saved next-models-search.txt. More concrete applications include reciprocalTailClock/Stieltjes perturbations; Fock coordinate/vector moments; explicit lognormal positiveRecurrenceSeparationMoments; coordinate-dilated arcsine; completedPrimeGammaFarRightMoment; Gamma semilocal moments; and broad FavardJacobiMomentRealization (favard_positiveMomentForm at328, exists_positiveMomentForm_of_jacobiData at423). These source bodies have NOT yet been read.
An especially broad next step: a data-only Favard constructor with arbitrary real diagonal sequence and exponentiated lower sequence, plus exact reconstruction of existing normalized moment sources from their recurrence coefficients. It could extend the seven-module geometry to many sources without adding proof premises. Adding a constructor to GomesMomentModels requires updating its moments and positivity proofs and auditing dependent targets in a batch; use current state and source searches before design. Goal is not exhausted or blocked.