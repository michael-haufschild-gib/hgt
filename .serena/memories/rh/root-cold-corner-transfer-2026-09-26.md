# Root RH checkpoint — actual theta negative cold/degree diagonal Lean-closed

## Rules and goal
Active goal is unconditional Lean proof/falsification of RH, NOT achieved. On continuation read `/Users/michael/.codex/attachments/57626bac-f4cf-4d94-bed5-5e4426c73652/pasted-text-1.txt`. No git commands, no numerical experiments, one foreground Lean process, scratch checks and named leaf builds only; no umbrella/full build. No subagents authorized. All owned processes have exited at this checkpoint. Methods already read: docs/meta/stroke-of-genius-method.md, scientific-method.md. Corpus search before new topics; direct documented command, inspect partial/coverage; method search is deep mechanism query, --mode method invalid. Preserve other workers' files/logs.

## Completed new result
Phi=thetaCuspFullSource, A_j=j+1/2, M_j(lambda)=integral_0^inf x^(2j)exp(lambda*x^2)Phi(x), q_j=(M_(j+1)/M_j)/A_j, S_j=q_j-2q_(j+1)+q_(j+2).
For every u>0, L_n=(n+1/2)/u: L_n^4 S_n(-L_n) -> (d^3/dy^3)log(Phi(sqrt y)) at y=u. Full literal-theta transfer is now Lean-closed. At u=9 profile<0, so S_n(-(n+1/2)/9)<0 eventually, without input hypotheses. Closed theorem directly refutes forall lambda<=0 forall j, S_j(lambda)>=0. NOT a refutation of degree-zero GABTC or RH.
Strongest positive survivor is full signed profile limit, not merely negative existence.

## New proof leaves and verification
SourceFallingEulerMomentShift.lean (namespace RHTower.ColdGamma, 8 public theorems): ordinary-source integration by parts, bounded continuous source concentration, exact two/three falling-Euler finite difference algebra.
ThetaColdDegreeEulerJets.lean (namespace RHTower.ThetaColdCorner, 12): bounded/continuous literal jets H1=xPhi'/2, H2=(x^2Phi''-xPhi')/4, H3=(x^3Phi'''-3x^2Phi''+3xPhi')/8, source differences k1–3, log derivative identity. Uses weighted_iteratedDeriv_thetaCuspFullSource_le; no square-root regularity problem at zero.
ThetaColdDegreeCornerLimit.lean (same namespace, 19): F_j=B_j(Phi), exact ratio q=F_(j+1)/(LF_j), scaled differences, diagonal concentration, full signed limit, eventually_negative_theta_diagonal (line199), not_all_degree_aperture_curvature_nonnegative (line211). Full limit line169.
Named builds all pass; scratch audits for all39 public theorem names pass, exactly standard axioms propext/Classical.choice/Quot.sound. Audit files /tmp/rh-theta-cold-diagonal-axioms.lean/.log. Build logs /tmp/rh-source-euler-shift-build.log, /tmp/rh-theta-euler-jets-build.log, /tmp/rh-theta-cold-diagonal-build.log. Umbrella wired19445–19447; index regenerated.
Global lint /tmp/rh-theta-cold-diagonal-lint.log failed SOLELY six unrelated unwired modules: ThetaCuspChargeContourShift, ThetaCuspChargeFarField, ThetaCuspChargeLineIntegral, ThetaCuspChargeSaddleGeometry, ThetaCuspChargeSaddleWindow, ThetaCuspChargeWindowLaw. None edited; do not wire others' drafts. No owned running Lean/search/index/lint jobs.

## Proof algebra
Source average B_j(H)=integral x^(2j)e^(-Lx²)H/G_Lj. E=x/2*d/dx; A Delta B_j(H)=B_j(EH). H_(k+1)=(E-k)H_k; (A)_k Delta^k F=B_j(Hk). Concentration variance+bias=(A/L-u)^2+A/L², bounded continuous H implies B_j(H)->H(sqrt u).
Jk=L^k Delta^k F. Exact L^4S=[F0²J3-3F0J1J2+2J1³+L^-1(F0J1J3+J1²J2-2F0J2²)]/(F0F1F2). Jk->Hk(sqrt u)/u^k; limit identifies third log derivative.
Prior leaves (do not redo): GaussianMomentColdDegreeCorner23audits, ThetaColdDegreeCornerLogJet4, ColdGammaShapeConcentration17; previous arc/dyadic/finiteprefix formal closures in own maincard.

## Own cards/facts
Moved root-owned corner card stage2 -> `docs/drafts/pipeline/3-formalized/rh-cold-degree-corner-2026-09-26.md` with dependency-closed paper proof and sixleaf table. Old stage2 file removed after ownership check. New failed card `docs/drafts/pipeline/5-failed/rh-global-all-degree-aperture-convexity-root-2026-09-26.md` records exact kill and strongest positive survivor paper+Lean status. Main own card `docs/drafts/pipeline/1-in-progress/rh-reflection-source-sign-2026-09-26.md`; own facts sibling `...-facts.md` nowF1–F40. Stale pending statuses F28/30/31/32/33 updated to completedF35–38. F39 route gate, F40 auxiliary Hankel mismatch. Do not edit other workers' logs.

## Next research priority audit
Global all-degree aperture convexity is retired; avoid more endpoint positivity or easy classification refinements. GABTC parent lines293–327 explicitly only proves one Hankel block atL0; separate degree>=2/all-order upgrade open. Thus degree-zero GABTC is not automatically next priority.
Current TH frontier docs/reports/rh-current-frontier-map.md lines98–103: actual fifth moment jointly with lower-moment deviations, joint cutoff/order j~N², exact fullsource sign. STATUS21/22/24/26 no-go: local zero geometry+RVM+all individual moment positivity; monotone/logconcave/exacttheta tail; all-order linear upper rawmoment recurrence; all insufficient. Specific actual modular identities needed.
Relevant open card (OTHER owner read only) docs/drafts/pipeline/1-in-progress/k-rvm-finite-sixth-moment-bracket.md ~693lines. Inspect slices: 350–410 exact gate, 462–500 retained score defect/affine gate, 609–650 Gaussian tangent cone and jointmomentwall. `362880 q D3=dDelta+G`; strictGram residual positive but must paynegativeG. Universal fifthmomentfloors lose840/11 at Gaussian boundary and cannot closeactualgate. New countermodels preserve allorderlinear recurrence. Merelyrepackaging equivalences isn't progress.
Source audit ThetaGammaPrimeArchStrictHankelRay (73lines) shows auxiliary positive sequence GammaRealConnectionJet+thetaCuspHigherLikelihoodSpectralMoment, NOT canonical moment identification. RH theorem remains adjoining-cone classifier. Do not mistake search positiveHankel hits forcanonicalproducer.

## Completed searches this turn
/tmp/rh-root-next-cross-moment-deep-20260926.json; /tmp/rh-root-canonical-source-global-deep-20260926.json; /tmp/rh-root-aperture-newman-deep-20260926.json. All terminal. Partial retrieval/deadlines, full source inventory~59535, compiler mostlypending/stale; candidates/source_arguments/ingredients inspected. No ready canonical incidence. The Newman/aperture query returned generic unrelatedhits; NO theorem connecting negative heat and canonical Hankel proved or claimed. Earlier Euler-shift/log-third queries partial, directsourceused. Do not endlessly broaden same search; freeze next source-specific conjecture after direct relevantcard audit.

## Lean/edit gotchas
Have explicit h:= innerfunction for HasDerivAt.comp; continuous .rexp; (ENat.coe_lt_top m).le; abs_of_nonneg typed. Pi.*_apply simplify before ring. Whitespace |c| * C. convert!/using! resolvesinstances. Some field_simp fullycloses. In finite difference algebra provide all b_j explicit. Audit imports allbefore#print. Python triple SINGLEquotedstrings breakon derivative '''; use shell heredoc or triple double. Shellglob RHTower/*.lean exceedsargv; rg directory --glob '*.lean'.
