Verified progress increment; whole indefinite corpus goal remains ACTIVE. This continuation explicitly read objective file /Users/michael/.codex/attachments/ac1d8777-936c-4edc-9c8e-fc7e0b037fde/pasted-text-1.txt at start. User restriction remains ONLY local Lean for mathematical evidence; no web, external papers/training novelty judgments/numerical experiments. No web used.
Card docs/drafts/pipeline/3-formalized/finite-weil-covariance-information-deficit.md.

3newleaves,9decls=7theorems+2defs:
1 HTGeometry/FiniteLawProductEntropy.lean, namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law:
kl_eq_zero_iff_of_dominated {P Q:Law alpha} hdom: P.kl Q=0 iff P=Q. Existing Law.tv_sq_le_kl =>TV0=>sumabs0=>coord equality.
prod_eq_uniform_factor_mul_exp_kl [Nonempty alpha](P:Law alpha)(hP:forall x,0<Px): productP = (card alpha real inverse)^card * exp(-(card real * (uniform alpha).kl P)). Derived by unfolding kl/crossE/uniform entropy, Real.log_prod/log_pow/log_inv then exp_log. This is UNIFORM->P KL, not P->uniform entropy deficit.
2 RHTower/WeilLogShiftPowerCovarianceEntropy.lean (ROOT namespace RHTower):
def finiteWeilCanonicalJointQuadraticTiltIndexLaw r k a b d: Law(Fin(r+1)), from explicit weight positivity/normalization.
def finiteWeilPowerCovarianceUniformBenchmark r = (prod_i prod_{j in Ioi i} (j.real-i.real)^2/(r+1))*((r+1 real)^-1)^(r+1).
finiteWeilPowerCovarianceUniformBenchmark_pos allr (empty products include0).
finiteWeilCanonicalJointQuadraticTilt_powerCovarianceMatrix_det_entropy allr,k,a,b,d: actual r-square power-cov determinant = benchmark * exp(-((r+1 real)*(Law.uniform Fin(r+1)).kl(IndexLaw...))). No helper assumptions.
3 RHTower/WeilLogShiftPowerCovarianceMaximum.lean:
..._powerCovarianceMatrix_det_le_uniform: det <=benchmark.
..._powerCovarianceMatrix_det_eq_uniform_iff: equality iff foralli actualWeight_i=(r+1 real)^-1.
..._powerCovarianceMatrix_det_le_tv: det <=benchmark*exp(-N*tv(uniform,IndexLaw)^2), using existing Law.tv_sq_le_kl.
No assertion that quadratic family attains uniform weights at eachr,k. Benchmark sharp over probability laws on support; actual equality criterion exact.

Verification:3nativebuilds terminal0 EMPTY logs/freshobjects. Final /tmp/hgt-covariance-information-final-audit.lean imports Maximum, session54456 terminal0;22APIchecks;9axiomreports incl2defs onlypropext/Classical.choice/Quot.sound; /tmp/hgt-covariance-information-audit.py axioms parser9/9;metadata4freshprojectedges,umbrellaswired,whitespaceclean. AllownednativejobsTERMINAL. Latestlint1FOREIGN unreachablemodule RHTower.WeilDecayClassRHCriterion +367sizewarnings; supersedesprior7foreignsnapshot. No unrelated sourceedited. No publication indexrefresh.

APIlessons: Law is abbrev private lawSet subtype, with custom FunLike. simpa only[Fintype.card_fin] (even unfolding IndexLaw) did NOT reduce P application in product. Fixed via local heval(i):IndexLaw...i=Weight_i:=rfl; then simpa only[card_fin,heval] usinggenericprodidentity. Finset.mem_Ioi.mp needs first have hijFin:i<j then cast toNat; otherwise expectedNat inst LocallyFiniteOrderTop Nat fails. Real.exp_eq_one_iff has EXPLICIT x: use (Real.exp_eq_one_iff _).mp. Upper bound have he needs explicit Nnonneg in mul_nonneg to infer multiplication factor. Avoid unnecessary <;> with field_simp onegoal (cleaned linter).

Corpus prior: product entropy lexicalHTGeometry cached59/59 acrossoffset0,20,40 names processed; actual finiteLawAPI/Comparison read, Compress.Prefix.kl_uniform is reverse direction P||uniform =entropy deficit, coldGibbs logproduct notgenericprob product. Focusedsourcechecks no proposedidentityroots. Relevantproofbasisexists Law.kl_nonneg, entropy_uniform, tv_sq_le_kl, paperAtomicLaw_klDiv (read butNOTneeded/used currentnewmodules).

NEXTCONJECTURES NOTSTARTED (needlocalcorpussearch/paper/cardbeforecode):
A. Gaussian-regime actual tilted moment control plus escape of uniform law on expanding indexgrid may force TV(U,W)->1, hence normalizeddet <=exp(-N*(1-o(1))). Pointspacing1/sqrt(N), uniform boundedwindow cardinalO(sqrtN) uniformly in center; actualsecondmomentbounded allows Markov/tightness. Stronger uniformKL->infinity possible via varyingfixedwindows and binarydata processing, not proved. Existing fixedmomentGaussianlimit alone is NOT being claimed to control growinguniformlogweights.
B. Existing finite polynomial interpolation and strictlypositivebaseweights may explicitly realize uniform, or EVERY positive targetlaw, by scalar polynomial tilt degree<=r: interpolate log(targetweight/baseweight). Would establish benchmarkattainment in polynomial family, distinct from unproved quadratic-familyattainability. No newcodeorsearch yet for either.
Goal NOTCOMPLETE. Previous turn classification: verified progress.