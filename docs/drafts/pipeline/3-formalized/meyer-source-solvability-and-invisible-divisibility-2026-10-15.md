# Meyer source solvability and invisible-sector divisibility

Status: conjectures 2 and 3 formalized and audited. Conjecture 1 remains open.

Objective: an unconditional structural advance beyond finite Xi source realization, combining literal Meyer source calculus with another corpus route. Exclude bounds, RH equivalences, and conditional receivers.

Completed plan:
1. Search actual Lean corpus for source division, spectral synthesis, and independent route mechanisms.
2. Conjecture; derive a dependency-closed paper proof or record the precise failure and positive survivor.
3. Formalize the strongest justified structural statement. Audit leaf modules directly with `lake --old env lean`, inspect axioms in a temporary file, wire finished leaves, run lint, clean owned scratch files.

Starting evidence:
- `DeningerMeyerXiSpectralInclusion.lean`: global injectivity still requires literal source synthesis.
- `DeningerMeyerCausalDivision.lean`: all-weight target admits division when the corresponding Mellin moment vanishes.
- `DeningerMeyerXiCausalChains.lean` and `DeningerMeyerFiniteXiCausalSplitting.lean`: actual finite Xi chains and generator-invariant source sections exist.
- `DeningerMeyerHedenmalmSourceRealization.lean`: these chains realize Hedenmalm divided chains; one common actual boundary accounts for their generator defects.

Conjecture 1: the literal Meyer cap is saturated under Euler division at nontrivial Xi zeros when its Mellin moment vanishes. Consequence sought: eliminate polynomial-torsion classes invisible to all Xi jets. This requires a genuine cap inverse, not only a target inverse or an assumed synthesis property.

Restrictions: no external search, novelty audit, old research-note reading, numerical computation, extra axioms, admitted proofs, heartbeat increases, or full/umbrella builds.

Conjecture 1 audit: unresolved, not refuted. Existing target division does not prove cap division. Do not infer absence of invisible homogeneous modes. Search also found the already-proved Mobius commutator regularity theorem, so Fourier regularity is not a new contribution here.

Conjecture 2 / paper proof: finite-rank source solvability.
Let Q be literal strong Meyer cohomology, A its logarithmic generator, E_S its full finite Xi jet packet, J_S its causal section, P_S = J_S E_S. Corpus proves E_S J_S = 1 and A J_S = J_S T_S, E_S A = T_S E_S.

1. If xi(r) is nonzero, replace a forcing representative g by g - M(g)(r)/xi(r) Z(fXi). This has zero Mellin moment at r and the same cohomology class. Causal division gives a preimage under A-r.
2. If r belongs to S and E_S u = 0, every representative g has M(g)(r)=0. Causal division gives v with (A-r)v=u. Replace v by (1-P_S)v. Commutation of P_S with A proves that this still solves the equation and has zero full packet. Step 1 admits the same repair for nonzero xi(r).
3. For any finite list L of complex shifts, take S to be precisely its Xi zeros. Induction gives surjectivity of W_L(A)=product(A-r) on ker(E_S). Repeated roots are allowed, with no limit or completeness argument.
4. For every finite packet endomorphism B, the range of W_L(A)+J_S B E_S is exactly the inverse image under E_S of the range of W_L(T_S)+B. Necessity is intertwining. For sufficiency, solve the finite packet equation, lift its solution with J_S, and solve the residual forcing in ker(E_S) by step 3.
5. Taking B=1-W_L(T_S) gives an explicit source-native finite-rank correction that is surjective on all actual cohomology, unconditionally. A linear right parametrix for W_L(A) with defect P_S can also be chosen using the proved residual surjectivity.

This removes the analytic forcing obstruction for arbitrary finite products and arbitrary finite packet couplings. It does not eliminate homogeneous ghosts, prove a two-sided resolvent, assert a bounded/continuous inverse, establish spectral completeness, or prove RH. Cross-route ingredients: causal all-weight division, exact arithmetic Xi cap, Hedenmalm multiplicity chains, and finite Xi source projectors.

Conjecture 3 / paper proof: all-jet invisibility survives division.
For tau != r, multiplication by s-r is an analytic unit at tau. Therefore the analytic order of the Mellin transform is unchanged there; vanishing of the full tau packet for (A-r)v forces it for v. If xi(r) is nonzero, every actual Xi point is of this kind. If xi(r)=0, repair only its singleton packet using the causal projector; its other Xi packets vanish by the same unit argument. Hence A-r is surjective on the submodule invisible to every Xi jet, for every complex r. Iterating gives unconditional divisibility of this submodule by every finite product of shifts. This identifies the unresolved invisible sector as having no polynomial forcing obstruction; it does not prove that sector vanishes.

Lean progress: all three leaves passed direct foreground `lake --old env lean -o ... <leaf>.lean` audits and are wired once into `RHTower.lean`:
- `DeningerMeyerFiniteXiCausalSolvability.lean`: actual residual source solvability for arbitrary finite products.
- `DeningerMeyerFiniteRankSourceSolvability.lean`: exact finite obstruction model, unconditional finite-rank regularization, right parametrix, and cokernel equivalence.
- `DeningerMeyerInvisibleSourceDivisibility.lean`: identification with the existing comparison kernel and its divisibility under every finite product of shifts.

Repository lint completed with one unrelated reachability error: `GaloisForLFunctions.RHTower.CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion`. No diagnostic concerns these three leaves. No full build or umbrella build was run.

Final audit: a separate `/tmp` file compiled successfully with `lake --old env lean`. It verified the used mathlib names and printed axioms for eleven principal results. Every result depends only on `propext`, `Classical.choice`, and `Quot.sound`; no added axiom or admitted proof occurs. All three exported leaf oleans are current. Each new module is imported exactly once by the theorem-area umbrella. Temporary search outputs, lint log, and name/axiom scratch file were removed after inspection.

Principal results:
- `deningerMeyerGeneratorWord_packet_kernel_surjective`: every finite generator word is surjective on the complement of its full resonant Xi packet.
- `deningerMeyerCoupledSourceOperator_range` and `deningerMeyerCoupledSourceCokernelEquiv`: arbitrary resonant packet couplings have exactly the finite obstruction operator `W(T_S)+B`.
- `deningerMeyerRegularizedSourceWord_surjective`: the explicit correction `J_S (1-W(T_S)) E_S` admits every actual cohomological forcing.
- `deningerMeyerGeneratorWord_exists_rightParametrix`: a linear solution operator satisfies `W(A) R = 1-P_S` and `E_S R = 0`.
- `deningerMeyerInvisibleGeneratorWord_surjective`: the kernel of the existing Meyer-to-compact-open-Xi comparison admits division by every finite product of shifts, including repetitions.

Structural consequence: global source synthesis is not a prerequisite for these inhomogeneous source equations. Any invisible homogeneous sector has arbitrary-depth preimages and supplies no additional finite-word cokernel. Its vanishing, cap Euler saturation, and continuous solution operators remain unproved here.
