# HB quartic physical compact-core Green identity

Goal remains active: full theta → Xi → spin-two → physical causal/left-QNM → original common Hawking-clock extinction → RH. Extinction/RH NOT proved. This turn is progress, not blocked. No subagents.

## Verified change
Existing leaf formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSquareCuspJets.lean is now 815 lines, SHA256 04bf62862b8754bf3f1a01ad6e4832c7a59c66567171c4cd31a2a3cf8ab08110. Four new public declarations in RHTower.D4BMSquareCuspJets:
- quarticContactField_modular (line660): all six actual full quartic differential expressions invariant under PSL2Z.
- quarticContactCoreCutoff (670): actual CoreField gamma_(n+1) P, smooth/modular/compact properties derived.
- quarticContactCoreCutoff_physical_green (735): for independent source q and physical target r, both original modular integrands are integrable and integral psi_r Delta(gamma_N P_q)=mu_r integral psi_r gamma_N P_q, mu_r=physicalAngularParameter r^2-1/4.
- quarticContactCoreCutoff_laplacian (787): on original closed fd, Delta(gamma_N P)=gamma_N Delta P+2y² gamma_N' P_y+y² gamma_N''P.

Proof: structural induction on actual AngularExpression with xi_scalar_modular, chartLaplacian_invariant and chart-coordinate equivalence. Construct source core. Use conjugated physicalCoreCutoff r (3*n+2); its whole germ equals full physicalTestField r on support of source core and its Laplacian. Both source expressions vanish as germs above 3(n+1). CoreField.completed_green (requires JointCoreTestData import) yields exact bilinear test identity by two conjugated Hilbert inner products. No full physical test L² eigenvector premise. All modular seams handled by actual core Green theorem.

Scratch lake env lean /tmp/hb-quartic-green.lean passed. Exact isolated cached lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareCuspJets passed without warnings, 7.3s, 2jobs, 12cachedroots. Source and five leaf artifacts copied byte-identically canonical. Existing umbrella import once. API regenerated (3changed), four new names once. Eight local doc links and scoped whitespace pass. Whole formal_tools lint exit1 ONLY reports concurrently appearing untracked ThetaCuspHawkingBMOnsetPulseTransform and XiAffineCollisionControl unreachable from RHTower; neither owned or edited here. The subsequent Mellin extension audit reran whole lint and got exit0 with existing large-file warnings after those two imports were added elsewhere in the shared worktree. Current whole gate passed at that later check; see mem:hb_quartic_finite_cutoff_mellin_2026_09_11.md.

## Exact next mathematical bridge (paper, not Lean)
Active card docs/drafts/pipeline/1-in-progress/hb-source-contact-spin-two-balance.md section Constructed compact-core physical Green identity. chi(y)=smoothTransition(y-2), gamma_N(y)=1-chi(y/N), existing M(w)=3^w/w-integral_2^3 chi(y)y^(w-1).
For N>=2, w!=0:
 integral_2^infinity gamma_N chi y^(w-1)=(N^w-1)M(w),
 -integral_0^infinity gamma_N' y^w=w N^w M(w).
At w=0 FIRST formula replaced by log N, not zero. Finite support, split transitions or substitute y=Nv, integrate parts. Original cutoff convention retained.
Full source f0=A y^rho+B y^(1-rho). r_i=2-i+(2i-2)rho, q_i=binom(2,i)A^i B^(2-i)/2, j_i=(c-2r_i(r_i-1))q_i/8, t_i=-r_i(r_i-1)(r_i(r_i-1)-2)q_i. Quartic exponent k_m=4-m+(2m-4)rho. Ordered pair i+l=m coefficients: Q²=sum q_i q_l; J²=sum j_i j_l; Gamma=sum r_i r_l j_i j_l; JRQ=sum j_i t_l; H=2sum j_i j_l+a sum q_i q_l; DeltaH=k_m(k_m-1) H_m. All six coefficient identities on paper, not Lean attached.
Actual same-q physical test principal D y^(1-eta), eta=rho/2, D!=0, other Weyl coefficient C=Lambda(rho)=0 (existing PhysicalAngularCutoffCalibration). w_m=k_m-eta nonzero via Imrho!=0 and halfinteger slope. mu=eta(eta-1); gap=k(k-1)-mu=w(k-1+eta).
I_N(P)=integral psi gamma_N P=N(P)+D sum p_m N^w_m M(w_m)+o(1), where N(P)=integral psi(P-chiP0)-D sum p_m M(w_m). Exact compact Green + integration by parts of cutoff commutator gives same scale terms for I_N(DeltaP)-mu I_N(P). Integrate gamma_N' B over endpoints N,4N (strictly outside derivative support); flux remainder tends zero uniformly and gamma derivative bounds yield o(1). Cancellation gives N(DeltaP)=mu N(P). Need formal principal expansion, finite-transition Mellin identities and limit transport. Compact theorem alone does NOT prove native identity, physical action sign, or extinction.

## Search use and limits
Latest four deep --retrieval-views all searches: two unfiltered modular/core Green searches completed retrieval; unfiltered scaled Mellin search partial due malformed model JSON + reranking deadline; narrower ThetaCuspHawkingBM Mellin query completed without errors. Inventory complete ~56,949 files, 732,524 declarations, but semantic coverage unmeasured and many compiler states pending. Do not claim exhaustive/compiler-verified search. Source-checked cutoffBulkMoment_eq_nativeMellin, nativeCutoffLowPower_value, scaledCuspCutoff_deriv/second/derivative_bounds. Generated ingredient set rejected: lower power value requires Rew>0, not true for all five exponents; unfolding theorem is wrong pairing. Finite separated-transition proof avoids chamber assumption.
Broad recent arxiv duality search found 2609.11417v1 (10Sep2026), sections3.3–4: constrained-domain-preserving modified translation need not commute with Hamiltonian because field-dependent defect terms remain. Method applicability test only, no HB theorem imported. Details/citation in active card.

Other shared edits include many other agents' leaves/scripts/umbrellas. Preserve them. No #print axioms, numerical computations, full/umbrella builds. All owned Lean/search processes terminal at time of memory write. Cleanup current owned scratch/audit files before ending or carry forward explicitly.
