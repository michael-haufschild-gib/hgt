# HB original future-horizon regularity — 0913al

RH remains UNPROVED; unbounded goal ACTIVE. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Closed this turn

Two new exact-source leaves passed scratch `lake env lean` and isolated exact `lake build Module` audits under Lean 4.32.2, LEAN_NUM_THREADS=2, default proof budgets. No computations, #print axioms, Git, launch.sh, umbrella/full builds or subagents. New artifacts atomically installed; both imports appended to formal/GaloisForLFunctions/RHTower.lean (currently lines17733–17734). All owned scratch/search/audit files removed and owned Lean/Lake count verified zero.

1. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMRetardedHorizonGeometry.lean (~284 lines), namespace RHTower.D4BMRetardedHorizonGeometry. Exact audit26s, only this source built (2654 cached/setup jobs). Imports prior RetardedTriangleGeometry + JointSourceTimeField + JointSourceHorizonFactor + interval integration by parts. Reuses existing sinhc rather than duplicating removable-singularity machinery.
- expc(t)=exp(t/2)*sinhc(t/2), globally smooth/positive; t*expc(t)=exp(t)-1.
- compactUnit z=(1-z)/(1+z); radialUnit y=compactUnit(exp(2y)).
- compactInvariant image E rho z=1+2*(if image then (E-rho)*(z-1/E) else (E-1)*(z-rho/E))/((1+rho)*(1+z)). `invariant_compact`53 identifies actual invariant(v-x+y,x,±y) for E=expv,rho=exp2x,z=exp2y.
- compactForcing retains physical complex power, full J/K and fixed timeOnset. `timeOriginalForcing_compact`101: original source at tau=(a+b)/2,y=(a-b)/2 equals exp(a-b)*compactForcing at source(a,z=exp(a-b)).
- sourceLower=(if image then1else rho)*exp(-p*(1-alpha)); sourceZ=lower+(1-lower)*beta.
- horizonFactor=p*expc(p*(1-alpha))*(1-rho*exp(-p*(1-alpha)))/((1+rho)*(1+sourceZ)); strictly positive for p>0, |rho|<1/2, alpha≤1, beta∈[0,1], including edges.
- horizonChart(v)=(1-expv)/(2*(1+expv)), bounds(-1/2,1/2), smooth, value0 atv0.
- horizonRadius image z=2arsinh(cos(z2)*sin(z3)*sqrt(H)) with p=expz0,rho=horizonChartz1,alpha=sin²z2,beta=sin²z3. `horizonRadius_smooth`220 global; `horizonRadius_eq`251 identifies actual arcosh(max1 invariant) at prior angleMap(alpha/beta), including full closed square.
- `integral_source_coordinate`270: for ANY F:ℝ→ℂ and a,B, integral_a^B exp(a-b)*F(exp(a-b))db = integral_exp(a-B)^1 F(z)dz. Uses antitone substitution, no continuity/integrability premise needed for this change of variables.

2. formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalHorizonRegularity.lean (414 lines), namespace RHTower.D4BMOriginalHorizonRegularity. Exact audit22s, [2/2], only this new source built. Imports geometry and prior OriginalRetardedIdentity. Originally scratch integral/regularity pieces were merged; there is NO OriginalHorizonIntegral module or namespace.
- compactSample/compactCircle: full original half-square and gradient energy at actual compact direct/image circle.
- compactAction = 1/4 integral_a0^p integral_z(rho*exp(a-p))^1 compactCircle(false) minus1/4 integral_a0^p integral_zexp(a-p)^1 compactCircle(true).
- `originalPotential_eq_compactAction`71: actual originalPotential(q,branch,amp,p,p+width,X,k)=compactAction(...p,exp(-width),X,k), all p,width NNReal.
- `compactAction_eq_unitAction`119 exact fixed-square rescaling.
- `extendedIntegrand_smooth`: global smooth full source in (Fin4 physical chart × Fin3 integration chart), keeps gradient energy, onset, Jacobians and1/4.
- extendedAction uses unitCube_integral_smooth and gamma=(angleMap alpha,angleMap beta,theta), DIRECT MINUS IMAGE.
- `extendedAction_eq_compactAction`315 exact full-source identification.
- horizonPotential349=extendedAction at[logp,log((1-2rho)/(1+2rho)),X,k].
- `horizonPotential_smooth`353: joint ContDiffAt ℝ∞ on p>0, |rho|<1/2, all angular coordinates, INCLUDING rho0.
- `horizonPotential_eq_compactAction`371.
- `originalPotential_eq_horizonPotential`377: original p,p+width equals extension at p,exp(-width) when p>0 and exp(-width)<1/2.
- `originalPotential_horizon_limit`385: at fixed NNRealp>0, originalPotential p r X k tends as r→∞ to horizonPotential p0Xk. No regularity, source-ID or boundary-value assumption is supplied.

## Own facts and actual next obstacles

Own log docs/drafts/pipeline/1-in-progress/hb-own-research-facts.md now F01–F103/N01–N04. FactsF100–103 grouped before no-gos, final proof-status remains RH unproved. F98 upgraded to Lean, F101 geometry/source cancellation, F103 actual horizon limit. No new no-go this turn.
Main card docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md updated current state and exact proofs (frontier map untouched/read-only; STATUS untouched because no new route-independent necessity established).

Two POSITIVE analytical results exposed, NOT YET LEAN:
F100/maincard3774 'Horizon transport of the actual normal derivative': with W(p,rho), old partial_r=-rho partial_rho, old partial_p=partial_p_new+rho partial_rho. Original wave gives W_p_rho+W_rho+rho W_rho_rho+Delta_H W/(1+rho)^2=-Fcompact/4. At rho0, U=W_rho obeys U_p+U=-Delta_H W-Fcompact/4. Fcompact is complete original source density. Existing smooth extension justifies continuity to boundary. No vanishing.
F102/maincard3809 'Complete stream current in regular ingoing coordinates': directly transforms existing BMMixedRadialActionCurrent.stream_complete_action_current ALL FOUR components. R=physical radius, f=R²-1, p=t+tortoiseR. Ingoing stream master M_P=R²fP_RR+R²(P_pR+P_Rp)+2R P_R-2R P_p+A(P), C_P=A(P)-M_P; D_P=partialX P1-partialY P0. Keep ordered mixed derivatives. Original static P_R=P_Ringoing+P_p/f and P_RR=PRR+(PpR+PRp)/f+Ppp/f²-2R Pp/f². Current determinant-one transformation Jp=Jt+JR/f gives:
Jp=1/R² sum(P_R C_Q-Q_R C_P).
JR=1/R² sum((fP_R+P_p)C_Q-(fQ_R+Q_p)C_P).
JX=-Y²/R²*[f(P1_R DQ_R-Q1_R DP_R)+P1_R DQ_p+P1_p DQ_R-Q1_R DP_p-Q1_p DP_R].
JY=+Y²/R²*same index0.
All inverse-f poles cancel without a field equation or angular integration. AtR1, JR=sum(P_p C_Q-Q_p C_P), all sources/angular fluxes retained. Formalize these exact identities, attach ACTUAL reconstructed causal and left fields, then evaluate complete physical boundary pairing. Do NOT redo lift-only horizon results or field regularity. Full original causal tensor/left-QNM incidence, onset/cusp boundary terms and fixed-Hawking-clock extinction remain open. Preserve raw B+Lk=T and all four correction-pairing terms.

## Checks / process discipline

Final global scripts/formal_tools.py lint ran once. Only error remains unrelated pre-existing unreachable GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionCoprime; both new modules wired and no lint errors for them. Many pre-existing large-file warnings. Do not edit that other work or claim global lint pass. No owned Lean/Lake process remains. All /tmp/*0913al* owned artifacts explicitly removed, audit stage removed after package symlink unlink. Exact repo oleans remain installed.

## Lean efficiency lessons

- THIS ContDiff.div requires same base/output field (f:E→𝕜); cannot use it for real differentiation of complex-valued functions. For compact coefficient, prove REAL quotient smooth then compose Complex.ofRealCLM and push_cast. Generic complex inv/mul can pick NonUnitalNormedRing vs Complex normed-add-group diamonds; avoid by using real coefficients. Constant division helper from prior OriginalSpacetimeRegularity works.
- Needed all four minus-instance attributes, including RCLike.innerProductSpace, as prior OriginalSpacetimeRegularity.
- Explicitly type intermediate maps and use have before composition to avoid greedy elaboration. ContinuousAt.comp at vector-valued fixed point chose Matrix.vecCons incorrectly; supply (f:=fun rho:ℝ=>![p,rho,X,k]) (x:=0) explicitly.
- Instantiate source-transform pointwise on both triangles and use integral_congr/exact. Rewriting generic circle_transform under original retarded integral repeatedly did not match. Final local h(image,B), pointwise exact with explicit p/width and arithmetic rewrites, then congrArg₂ combines triangles.
- angleMap_continuous is NOT a fun_prop attribute; compose it explicitly with continuous_fst/snd.
- NNReal coercion in horizon bound: change to exp(-(r-p)) before simp neg_sub.
- All proof code uses default heartbeats. No #print axioms or old proof rechecks.
- If staging future exact audits, copy lakefile/manifest/toolchain, append roots=[exactleaf] under lean_lib, symlink packages, recursively hardlink cached project dep artifacts, copy only new root source. WAIT for prepare process completion before lake build. Atomic artifact install must compare exact staged/repo source and copy via temp+os.replace, never mutate hardlinks. No umbrella builds.

## Searches this turn

Broad horizon, deep OR compactification/Jacobian/smooth extension, deep removable exponential factor, deep characteristic/normal derivative/current mechanisms. Inspected candidate_lemmas/source_arguments/proof_ideas/ingredient_sets. Most source_only; deep results partial, fresh metadata pending in some snapshots. Actual selected candidates verified in Lean. Recent broad arxiv memory/compactification/regularization/transport searches mostly yielded old irrelevant work. Primary arxiv2608.18589 opened (19Aug2026/rev10Sep2026): exprel removes0/0 in CGC quadrupole formula, no computation/quadrature adopted. Our positive removable factor reused corpus sinhc and was proved analytically in Lean.