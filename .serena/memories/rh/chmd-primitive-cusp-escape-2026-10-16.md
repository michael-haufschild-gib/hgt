# CHMD primitive cusp escape and noncompact source projection (2026-10-16)

Persistent unconditional RH goal remains ACTIVE, unbounded. Read the attachment each new goal turn:
`/Users/michael/.codex/attachments/2c5020c9-b71c-40b8-ba6c-e8fb1100e229/pasted-text-1.txt`.
Corpus-only, no web/old research Markdown/novelty audits/numerical experiments/subagents. One owned Lean process, leaf --old builds only, final plain lake env lean, no heartbeat increases.

## Completed structural contribution
Conjecture: the primitive compact-core Doob graph may have compact projection to its theta-cosh mass space, enabling a discrete first-mode argument.
Result: false, with an unconditional explicit primitive escape sequence.
Positive survivor: actual compact-core vectors p_n with source norms1, graph norms≤2, pairwise orthogonal source coordinates, signed energies→0, COMPLETE jump norms²→1, graph norms²→2.
No strictly increasing source subsequence is Cauchy; primitive graph ball source image is not compact; no positive uniform signed margin can hold.

Mechanism:
- f = evenShift(g,4) - cosh(1)*g, g = WeilOneSided.narrowBump0.
- Both hyperbolic half-moments vanish by exact evenShift laws.
- f0 = -cosh1 ≠0 (g support[-1/4,1/4]).
- f_T(x)=f(x-T) remains primitive; cosh moment transports as C_f*cosh(T/2)+S_f*sinh(T/2).
- Complete Markov energy M(f_T)=M(f), from exact simultaneous-translation invariance of the Weil autocorrelation.
- Inverse Doob test v_T=f_T/Θ enters existing CHMDDoobGraph compactLift.
- Its actual source mass is I(T)=∫ f_T² cosh(x/2)/Θ(x)dx→∞. Θ→0 and cosh≥1 imply inverse weight→∞ uniformly over translated fixed compact support; ∫f²>0.
- Normalize p_T = ||source(liftT)||^-1 • liftT. Signed energy exactly M(f)/I(T), no assumption on sign M(f).
- Source mass1, full edge mass=energy+1, graph norm²=energy+2.
- Choose T_n=A+(2R+1)n beyond uniform graph bound, with f support in[-R,R]. Source coordinates have disjoint supports, hence orthonormal.

Scope: no primitive nonnegativity, no RH, no selfadjoint operator, no spectral Weyl residual or exact essential spectrum. No maximal-domain=compact-core equality. This is an exact primitive sequence and source-level compactness obstruction, not an RH receiver.

## New wired leaves
1. formal/GaloisForLFunctions/RHTower/CHMDTranslatedPrimitiveSource.lean
namespace RHTower.CHMDTranslation, 216 lines,25 declarations.
SHA f526232c72ec226a07393b183a390e2f8ec75a2555b086448ebc0fee7570c878
translate, markovEnergy_translate40, profile, profile_moments, profile_zero, profile_ne_zero,
profile_translate_primitive111,
inverseWeight=cosh(x/2)/riemannKernelReal x,
inverseMass f=∫f²*inverseWeight,
inverseMass_pos, inverseMass_translate, inverseWeight_atTop,
support_interval, inverseMass_translate_atTop181.

2. formal/GaloisForLFunctions/RHTower/CHMDPrimitiveCuspEscape.lean
namespace RHTower.CHMDEscape,254 lines,34 declarations.
SHA 7e4e23004fc307db07c785cd06c3d24933ffbf56dd58174d280c4929d7fefd8d
source p=p.val.fst; Primitive p = real inner(sourcep,source(constantLift1))=0.
test t=phiDoobInv(translate profile t), lift t=compactLift(testt).
lift_source_ae, lift_energy, lift_mass, lift_primitive.
normalized t, normalized_source_norm, normalized_energy, normalized_energy_zero,
normalized_jump_one, normalized_graph_norm_sq_two, eventually_normalized_bounded.
separated_lift_inner, separated_normalized_inner.
exists_primitive_escape177: full unconditional existential sequence.
no_cauchy_subsequence217.
primitiveBallImage=source image {p|p∈compactCore ∧ Primitivep ∧ ||p||≤2}.
not_isCompact_primitiveBallImage235.
no_positive_primitive_margin244.

## Validation
Both leaf --old builds exit0.
Both FINAL PLAIN lake env lean source audits exit0, empty output. Second plain check preceded successful leaf build; unchanged source hash verified.
Separate25-name /tmp have:=@Name probe exit0.
ALL59 declarations #print axioms via/tmp: only propext,Classical.choice,Quot.sound.
Each import exactly once in RHTower.lean.
Whitespace passed. Index exit0.
GLOBAL LINT EXIT1, solely six other unwired concurrent modules:
DeningerHasseHilbertOperators
DeningerHasseHilbertPairing
DeningerMeyerHasseHilbertAdmission
DeningerMeyerHasseHilbertDensity
DeningerMeyerHasseHilbertTopology
DeningerMeyerHasseMoments
(all under GaloisForLFunctions.RHTower; untracked, not modified by this task).
No new CHMD lint error. Do not claim global lint passed.
Previous PaperThetaCutMeyerCurrent lint exception was observed wired at this turn init.

All12 owned temp files removed, absence verified. All owned search/Lean/index/lint sessions terminal. NO owned live process.

## Persistence
Topic card MOVED from1-in-progress to:
docs/drafts/pipeline/3-formalized/chmd-primitive-cusp-escape-2026-10-16.md
Failed compact-projection route with full positive salvage:
docs/drafts/pipeline/5-failed/chmd-primitive-compact-projection-2026-10-16.md
Main CHMD card appended result, audit exceptions, cleanup:
docs/drafts/pipeline/1-in-progress/chmd-convolution-defect-elimination-2026-10-15.md

## Lean lessons
- Open scoped InnerProductSpace for explicit ⟪x,y⟫_ℝ. RealInnerProductSpace only supplies bare inner notation in this toolchain.
- Qualify CHMDTranslation.translate in simp lists; global _root_.translate causes ambiguity.
- ContDiffBump.contDiff has implicit finite smoothness n. Provide expected ContDiff ℝ2; do not use untyped .of_le.
- ContDiff.const_mul absent here: use contDiff_const.mul hg.
- HasCompactSupport constant multiplication: use .mul_left/.mul_right, not .const_mul.
- Explicit intermediate HasCompactSupport(fun x=>f x^2), with g:=fun y:ℝ=>y^2, avoids 200k isDefEq timeout. No heartbeat override.
- Give μ:=volume to independent integral_add_right_eq_self binds.
- Unfold inverseMass explicitly in simp-only.
- Function.comp_def needed for inverse-mass filter compositions.
- Do not split a method after a trailing dot across lines; use intermediate typed hcont then hcont.integrable_of_hasCompactSupport.
- Generic name probes need explicit universe zeros.
- Redirect leaf-build logs: large cached warnings replay.
- Serena ignores Lean paths; use rg/apply_patch fallback. update_plan unavailable; plan persisted in card.

## Frontier
Do not redo full graph closure, prime-chain variance, arithmetic tail selection/order obstruction, or primitive cusp escape.
Primitive-sector cosh domination/nonnegativity remains open. It must work at the exact critical source-norm boundary, not via a positive uniform margin or compactness of this source projection. The escape construction is compatible with either sign of fixed Markov energy and does not settle RH.
