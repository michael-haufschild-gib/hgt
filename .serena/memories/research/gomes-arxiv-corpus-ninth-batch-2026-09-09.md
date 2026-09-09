# Gomes arXiv corpus experiment: ninth completed batch

User goal remains active: apply/formalize as many results/viewpoints as possible from arXiv 2607.24901, 2509.25276 (latest v7, withdrawn old equivalence), and 2404.10461 throughout Lean corpus. Search directly with scripts/formal_tools.py research; do not read pipeline cards/docs. No added hypotheses/axioms, no numerical or decision computations. Natural universally quantified data and closed iff classifications are used. One foreground Lean process, scratch lake env lean, exact target lake build only for final audits, wire own modules only, no full/umbrella builds, no commits or subagents.

## Verified batch
59 theorems, 10 definitions, 9 new modules, all in GaloisForLFunctions.HTGeometry and wired into HTGeometry.lean:
- GomesJacobiInvariantForms: 11 theorems/4 defs.
- GomesJacobiPositiveMetric: 6/1.
- GomesJacobiReconstruction: 5/0.
- GomesMomentFrameTransport: 3/1.
- GomesArcsineFrameGeometry: 8/0.
- GomesGammaFrameGeometry: 8/0.
- GomesJacobiTwoStepFlux: 4/1.
- GomesCompletedFockFrameGeometry: 11/2.
- GomesMomentTwoStepFlux: 3/1.
Cumulative experiment: 457 theorems across 51 modules (prior 398/42).

All nine exact target builds passed, all 69 declarations independently #print axioms audited. Only Classical.choice, Quot.sound, propext; no added axioms or sorry. No own stale Lean/lake processes at checkpoint. Artifacts /tmp/hgt-gomes/ninth/: modules.json, build-status.json, counts.json, AxiomAudit.lean, axioms.log, axiom-audit.json, progress.json with source SHA256s, lint.log. Global formal lint failed solely on unrelated untracked/unwired HTGeometry.FokasLenellsRawTwistKernels; no generated-freshness errors at snapshot. Do not wire another task's unfinished source.

## Results
Jacobi T(a,b,x)=[[x-a,-b],[1,0]]. For the entire real x-family, T^t B T=bB iff B=cJ. Complex Hermitian common forms are exactly real multiples of iJ; full complex spectral family retains only zero. No common positive metric. Exact complex defect T(z)^H(iJ)T(z)-b(iJ)=2 Im(z) diag(1,0), PSD iff Im(z)>=0.
Fixed real step admits positive metric iff (x-a)^2<4b. Every such metric is c[[1,-(x-a)/2],[-(x-a)/2,b]] with c>0; full classification, including construction and boundary.
Full-family constant intertwiner P T(a,b,x)=T(c,d,x)P iff P=0 or a=c,b=d,P=kI. Common conformal area-form spaces agree for all coefficients; concrete a versus a+1 has identical area menu and character but no nonzero intertwiner. Distinguish form-space information from determinant character, which itself remembers b.
Moment frame is entrywise evaluation of existing momentTransfer; determinant is evaluated momentWronskian, area character the same. Actual arcsine and Gamma(exp r) moment systems have closed positive off-diagonal coefficients, exact frame advance, negative determinant/norm-ratio area, sharp metric boundary, complex flux sign, and coefficient reconstruction between levels.
Two-step Gram G=T1^H diag(1,0) T1+d diag(1,0), factorized as L^H diag(d,1)L with L=[[1,0],[z-a,-b]]. G PD iff b!=0 and d>0. Two-step flux defect=2 Im(z) G, PD iff Im(z)>0,b!=0,d>0. Independent of both diagonal coefficients. Closed upper-half-plane iff applications to all three actual families.
Completed free-Fock family: arbitrary B:Fin k -> Matrix(Fin(d+1))(Fin(d+1)) C, generators indexed Option(Fin k): none=I, some i=B_i+B_i^H. Proves Hermitian and trivial common kernel internally, then existing freeFockTraceMoment_positiveMomentForm applies without proof premises. This explicitly changes/completes input family. Eleven theorems provide same recurrence geometry plus positivity construction; two-step application separate.

## Sources / APIs
Existing moment APIs live in root namespace HTGeometry despite file paths. SecondKindMomentPolynomials read 1-325; defines recurDiag,recurOff,secondKind,momentWronskian,momentTransfer. momentWronskian_eq h n = C(-(h_n/h_0)); monicOrtho_succ_succ_eval h n x, secondKind_succ_succ_eval s n x. PositiveMomentForm.pos_of_ne_zero p hp is the positivity field (NOT .pos). monicOrtho_ne_zero s n. MomentInnerProduct read18-80,86-123.
ArcsineHankelPositiveDefinite read1-132: normalizedCentralBinom_positiveMomentForm closed. PoleUnitGammaBase read210-245 and gammaShapeMoment definition at34: product_i<n(r+i); use gammaShapeMoment_positiveMomentForm(Real.exp_pos r).
FreeFockMatrixSemicircle read843-873,678-693,800-809: HasTrivialCommonKernel A := forall x, (forall k i, sum_p A k i p*x p=0)->x=0. Identity component solves by simp. freeFockTraceMoment at686, .positiveMomentForm at860. No need reread same excerpts.
Matrix.PosDef.conjTranspose_mul_mul_same takes Function.Injective B.mulVec. posDef_diagonal_iff available. Complex.zero_le_real / zero_lt_real explicitly convert order of real casts before simp; default simp may push casts into products/powers and block conversion. Use pow_two when taking re/im after real-square casts. Fin2 matrix.mulVec simplification leaves vecHead/vecTail; change explicit v 0/v 1 equations before linear_combination. Avoid rewriting B=cG inside a coefficient B00: use congrArg to prove inverse-scale identity first.

Next research frontier: iterated flux and complex evaluated moment frames; derive actual Weyl/Herglotz rational quotient geometry from positivity rather than assumed spectral hypotheses. Prior research must be searched before new Lean. Goal remains active; this is a verified batch checkpoint, not exhaustion of papers/corpus.