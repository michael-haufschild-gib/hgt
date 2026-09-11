# FZZ-P all-count original charge integral CLOSED — 2026-09-11
Active unlimited goal remains unconditional closed Lean RH via FZZ-P. RH UNPROVED; goal ACTIVE. Latest goal turn made VERIFIED PROGRESS, not blocked. No subagents, commits, numerical computations or #print axioms. User banned further #print axioms explicitly. One owned foreground Lean at a time; scratch lake env lean /tmp/file.lean, cwd formal; lake build exact leaf only final audit; no full/umbrella builds. Other tasks concurrently edit shared docs/umbrella; preserve them.

## New complete leaf
formal/GaloisForLFunctions/RHTower/FZZCigarScreeningChargeMoments.lean (~246 lines).
Imports neutral-screening determinant, HTGeometry.CauchyBinet, Integral.Pi.
W_z(w)=prod_i (norm(w-z_i)^6)^-1.
D=closedBall 0 (exp R) minus union_i ball(z_i)(exp(-T)).
M_ab=integral_D w^a conj(w^b) W_z(w).
For all fixed count m, integrated count n, positions z, real R,T:
integral_{D^n} |det Vandermonde(w)|² prod_i W_z(w_i)=n! det(M).re.
Original literal neutral K4 when m=n: its entire one-charge-family integral is
|det Vandermonde(z)|² n! det(M).re.
All interactions, every moment and both position cutoffs retained. Empty domains, count zero, coincident fixed positions included. No integral/counterterm/count continuation or physical Ward is inferred.

Five public data-only theorems and line numbers at final audit:
129 fzzScreeningChargeMoment_integrable
178 fzzScreeningChargeKernel_integrable
193 fzzScreeningChargeKernel_integral
228 fzzNeutralCubicScreeningKernel_charge_integrable
238 fzzNeutralCubicScreeningKernel_charge_integral.
All L1 obligations proved from original compact-away-from-fixed-collisions domain. Generic determinant integration helper private with hypotheses discharged in actual source application.

Proof: two determinant permutation expansion; each expanded product L1 via Integrable.fintype_prod before finite sum interchange; integral_fintype_prod_eq_prod; for each first permutation, second sum is signed row-permuted moment determinant. Sign²=1; count permutations n!. Connect conjugate weighted determinant with det_mul_column and RingHom.map_det; Complex.mul_conj'; exact Vandermonde/cross-product identities connect full neutral kernel.

## Verification — ALL HANDLES TERMINAL, NO OWNED LEAN
Final clean scratch /tmp/fzzp_charge_family_moments.lean: session87702 exit0, empty log.
Final exact leaf build session37475 exit0, built newleaf101s.
Global formal lint session96649 exit0, formal lint passed (unrelated large-file warnings).
Logs /tmp/fzzp-charge-family-moments-{scratch,build,lint}.log.
Wired into formal/GaloisForLFunctions/RHTower.lean after NeutralScreeningDeterminant.
Scoped git diff --check passed. Final ps scan showed no owned scratch/build/Lean.
Earlier scratch sessions6824,51888,4869,94612 terminal; do not poll/restart.
Research98991,78002,89928 terminal too.

Lean pitfalls resolved:
- Expand sums explicitly rw [det row,det row,Finset.sum_mul]; simp_rw[mul_sum], otherwise simplifier reverses binder order.
- integral Pi needs explicitly applied eta-expanded family via have hint(σ τ):=integral_fintype_prod_eq_prod (μ:=...) (fun i x=>...); simp_rw[hint].
- ContinuousOn.integrableOn_compact compact-proof continuous-proof (compact first).
- current continuousOn_finsetProd and integral_finsetSum names.
- Explicit IntegrableOn and fzzScreeningChargeMeasure unfolding needed.
- h.re uses RCLike.re; change to explicit Complex.re in a have hr, then simp only[Complex.ofReal_re,...].
- For neutral source integrability change bare function to lambda before simp_rw pointwise factor theorem.
- det_mul_column weights index i (despite swapped docs); det_mul_row weights j.

## Docs
Card docs/drafts/pipeline/1-in-progress/fzz-p-higher-screening-collisions.md:
#closed-all-count-original-charge-integration ~1001: exact full proof, 5 theorem status/build/lint.
Initial n2 target retained historical heading Original charge-family integration: initial target.
Added checked allcount gate.
#next-continuation-attack-roots-to-coefficients records next actual integral attack.
Source-normalization discrepancy at end, below.
Frontier rh-current-frontier-map.md FZZ section ~1794 pointwise result now links closed integral paragraph1798.
STATUS existing convergent-integral-vs-continuation rule line47 extended route-independent Must prove every expanded term admitted, exact permutation multiplicity, all interactions. Finite cutoff does not justify removal or dimension continuation. No route-specific new rule.
Keep goal chain: full fixed source/count continuation + normalization → mixed replica-momentum Ward in independently fixed phase frame → balanced vacuum-delay saturation → passivity → RH.
Physical count s'=1/(k-2), so k4 count1/2, not integer matrix dimension. Physical coupling/nonzero modes/replica insertion and independent phase remain open.

## Next actual hard attack (no new scratch yet)
Source appendix B zero-dual identity n integrated roots and n+1 fixed nodes. Conjecture derive it from original variables using roots→coefficients map; do NOT assume Gamma product.
P_w(t)=prod_j(t-w_j), n nonleading coefficients c.
dP/dw_j=-prod_{k!=j}(t-w_k).
Evaluate derivatives at roots: E(w) J(w)=-diag(prod_{k!=j}(w_j-w_k)), E=Vandermonde.
Thus norm complex det J squared equals norm Vandermonde². Real Jacobian equals that square.
For distinct roots generic ordered fibre has n! permutations. Need full finite-to-one change of variables, not direct application of injective Jacobian theorem.
Suggested measurable chamber strict increasing real parts. Permuted chambers n!, complement real-part-ties null; coefficient image of null complement null by local Lipschitz/equal dimension. FTA gives surjectivity, symmetric polynomial/root multiset uniqueness gives chamber injectivity. Must actually prove every step and Jacobian.
For distinct fixed nodes t_0..t_n, d_i=prod_{j!=i}(t_i-t_j), u_i=P(t_i)/d_i.
Installed Lagrange.leadingCoeff_eq_sum gives sum u_i=1. Affine coefficient→u map contributes full fixed-node Vandermonde²; weight constant pair exponent 2p_i+2p_j+2.
Remaining integral complex Dirichlet on affine hyperplane, parameters alpha_i=p_i+1>0 and sum alpha<1. Successive original beta convolution should give Gamma product after full admission.
Then need original root cutoffs transported and all singular counterterms before p=-3 continuation. Fractional count still distinct.

Authoritative corpus read:
Mathlib/MeasureTheory/Function/Jacobian.lean1176-1236:
lintegral_image_eq_lintegral_abs_det_fderiv_mul requires MeasurableSet s, ∀x∈s HasFDerivWithinAt, InjOn f s.
integrableOn_image_iff_integrableOn_abs_det_fderiv_smul similarly; integral_image... and openPartialHomeomorph version.
Mathlib/LinearAlgebra/Lagrange.lean490-515:
coeff_eq_sum (hvs:Set.InjOn v s)(hP:P.degree<#s):
 P.coeff(#s-1)=sum_i∈s P.eval(v i)/prod_j∈s.erase i(v i-v j).
leadingCoeff_eq_sum(hvs)(hP:#s=P.degree+1): leadingCoeff=sum same.
FZZCigarPlaneScreeningBeta.lean298-326,341-413 read:
private plane_kernel_integrable/integral for 0<a,b<1,1<a+b; exact whole plane norm^(-2a)*norm(z-1)^(-2b).
Public fzzScreeningBeta_chart_iff a b covers entire convergence chamber; public original beta integral/L1 via explicit exp chart.
Correct file is FZZCigarPlaneScreeningBeta.lean (not guessed longer names).

## Research current turn
/tmp/fzzp-charge-family-permutation-methods.json gen875038 partial; semantic backend unavailable, rerank timeout, malformed filtering, pending coverage. All20 candidates+20methods inspected, no ideas/ingredient.
Useful det_eq_sum_perm_row, Matrix.det_permute and Pi integrals. Source/domain proofs needed.
/tmp/fzzp-charge-continuation-shift-methods.json gen875157 partial semantic/source; noerrors. All20+20+ingredient inspected. Gamma recurrence no original integral.
/tmp/fzzp-root-coefficient-jacobian-methods.json gen875179 partial semantic/rerank/source; rerank deadline. All20+20+ingredient inspected. WeightedVandermonde no measure transform.
Lasttwo inventories 56893files complete, 47312Lean+9581prose; most compiler snapshots pending, not proof coverage.
All handles terminal.
Broad rigidity/interpolation June–Sep2026 searches returned:
https://arxiv.org/html/2609.06258v1 Dimitric/Vuckovic/Zigic Sep5 thm3.4: derivative-order interpolation assumes already smooth function and gap ratio, no count producer.
https://arxiv.org/html/2606.22671v1 Arutyunov/Korgin Jun21 thm2.10,5.1: dual basis finite dimensional interpolation. Helps identify affine monic-value coordinates; no fractional count.
Both read primary, compact source comparisons in card.

## Important primary source discovery
https://arxiv.org/html/2208.00016 v3 appendixB extracted current HTML saved /tmp/fzzp-duality-source.html.
Normalized measure d2n w = prod d2w/(pi^n*n!).
Identity(71) (PDFB.2) is complex Vandermonde n↔m duality, N=n+m+1 fixed insertions.
Setting free n-1, N=n, p_j=-1-b² gives I=gamma(-b²)^n/gamma(-n b²)*D_n^(-1-2b²).
Therefore recursion multiplier MUST be gamma(-n b²)/gamma(-b²)^n.
HTML eq75 shows only first power denominator. VERIFIED PDF https://arxiv.org/pdf/2208.00016 B.6 page21 (zero-index21) textlines2314-2336 also first power. Web screenshot failed cache; parsedPDF clear. This is source normalization discrepancy, not merely HTML conversion. Do not import first-power formula.
Earlier cited https://arxiv.org/pdf/0707.1664 v2 page3 (zero-index2) eq1.14 explicitly gamma(-b²)^n denominator, consistent. Its main eq1.13 original duality and appendixB equations read; appendixB explicitly without proofs. Outside convergence chamber contour continuation referenced, not original cutoff matching.
Source1999 https://arxiv.org/html/hep-th/9906010 opened; broadintro/reflection seen but no integral proof reliedon.
Keep per-source summaries compact, cite primary links near claims.
Previous detailed memory mem:rh/fzz_cubic_marked_value_closed_2026_09_11 covers all earlier closed markedFP=-141pi/8, ratio47/224, unmarkedFP=-84pi and exact Cauchy retained residual.
