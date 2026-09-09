# Actual theta dilation Gram kernel

RH goal remains ACTIVE and unproved. User constraints: frontier map read-only; analytical work only, no numerical computations; every turn states full proof chain, hardest obstacle, and attack; broad OR corpus discovery; one owned foreground Lean process, collect terminal exit; scratch/source lake env lean FILE, final named leaf builds only; no umbrella builds; no new no-go modules. Latest result proves a positive conjecture, not an occurrence receiver.

## Closed Lean result
New modules:
- formal/GaloisForLFunctions/RHTower/SelbergThetaDilationRows.lean (599 lines, 16 public declarations)
- formal/GaloisForLFunctions/RHTower/SelbergThetaDilationGram.lean (364 lines, 5 public declarations)
Namespaces RHTower.SelbergThetaDilationRows and RHTower.SelbergThetaDilationGram. Both wired once in RHTower.lean.

For g=SelbergThetaDilationTransform.profile rho and f_L(y)=exp(log(y)/2)g(log(y)+L), source rho L is literal complete periodize(cuspHeightSeed f_L). Source has all weighted power bounds, actual native MemLp2, absolute product unfolding, and exact horizontal mean f_L(y)+sum_c phi(c) integral f_L(y/(c²(y²+t²)))dt.

SelbergThetaDilationGram.source_pairing_gram, vector_inner, vector_norm_sq prove for every complex rho and real L,M:
< Q(L),Q(M) > = autocorrelation rho (M-L)+SelbergThetaTotientHankel.kernel rho (L+M),
||Q(L)||² = Re(K(0)+H(2L)).
vector is the actual native Lp element, vector_coe identifies its original full modular representative. No Xi-zero, occurrence, convergence, or spectral-location assumption.

Proof: direct half-row equivalence Unit+positive primitive pairs, then c:PNat, reduced residues a mod c, integer translates. Full mean has exact phi(c) factor. Log-height and horizontal rescaling give logRow=exp(-shift/2)conj(g(t+L))g(M-t-shift), shift=2log c+log(1+x²). Absolute majorant C c^-4 [normg(t+L)exp(-3(t+L)/2)](1+x²)^-2 gives Fubini and integrated phi(c)-row norm summability c^-3. Parabolic term gives K, full reflected rows H. No omitted spatial modes.

## Audit
Both scratch and source checks clean. Named leaf builds passed: Rows40s (+needed HalfRowIntegralInterchange6.1s), Gram8.1s; only those built, other dependencies reused. All21 public declaration axiom checks only propext, Classical.choice, Quot.sound; no computational axiom. Index regenerated. Global formal lint PASSED with existing warnings (the unrelated earlier reachability failure is no longer present). Logs /tmp/sqb35_{source_check,leaf_build,gram_source_check,gram_leaf_build,axioms,index,lint}.log. Scratch /tmp/sqb35_profiles.lean and /tmp/sqb35_gram.lean. All owned tool processes finished, no live Lean process.

Report docs/drafts/pipeline/3-formalized/sqb-theta-native-gram.md. Loop card updated section4 eq9 and verification boundary. Frontier and universal-law-field/STATUS unchanged (result route-specific). No commits/pushes.

## Hardest remaining obstacle
Full chain actualtheta -> normalized native approximate vectors at full Xi target -> occurrence -> real-preimage -> critical line -> RH. The pointwise native Gram transport is now closed: do not redo it. Integrated packet identity G(w), original graph/differential forcing, and especially actual source-derived w_R with G(w_R)>0 and G(w_R''-kappa²w_R)/G(w_R)->0 remain unproved. Existing paired Gaussian leading cancellation did not solve this; do not repeat that no-go. Mean-pole holomorphic continuation (prior TotientHankel module) does not establish actual integral boundary convergence. First-order NativePairing.centeredVector is a different family from these dilation vectors.

Useful verified APIs: MeasureTheory.L2.inner_def (NOT Lp.inner_def); RCLike.inner_apply' gives conj(x)*y; RCLike.re_to_complex needed with inner_self_eq_norm_sq. Integrable.integral_prod_left integrates SECOND coordinate, integral_prod_right FIRST. Explicit Function.uncurry simplification / using! resolves eta mismatch. For real product measure integral_prod_mul, rw Measure.volume_eq_prod first. Primitive row geometry ring! handles reducible cast diamonds. Generic integral_image_eq_integral_abs_deriv_smul and integrableOn_image_iff_integrableOn_abs_deriv_smul with exp/injective/range_exp provide unconditional whole-line substitution. MeasurableSet.univ exact name. Profile_integrable rho0 needs function eta expansion before simplifying fourierIntegrand.

Broad searches this turn: Gram/pairing/unfolding/periodization; unfold/primitive/strip; logarithmic/Mellin/substitution/exponential; forcing/residual/current/balance. Stored /tmp/sqb35_*_search.json. Positive current search found existing sourceVariance gauge_source_balance and MaassAverageCurrents radialResidual_mean_decomposition; no new residual cancellation inferred.