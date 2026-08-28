# C5 combined bridge no-go (2026-08-28)

New exact counterexample:
F(t)=exp(-(t^2+t^4/10+t^6/2)),
s(x)=F(sqrt x)=exp(-(x+x^2/10+x^3/2)),
P(t)=F(t)F(-t)=exp(-q(t)),
q(t)=2t^2+t^4/5+t^6.

Properties, all closed in Lean:
- first Laguerre = (1/5+3x) exp(-2(x+x^2/10+x^3/2));
- on x>=0 its log second derivative is -9/(1/5+3x)^2-2(1/5+3x)<0;
- Riccati margin 2q'q''-q''' = t/25*(680-2360t^2+7296t^4+1920t^6+9000t^8)>=0, hence correlation angle concave on every [0,T];
- P''(0)P^(6)(0)-P^(4)(0)^2=92544/25>0, so generic cusp theorem gives C5>0 near zero;
- at t=sqrt(1/2), with r=exp(47/40)-1, C5/P^2=24r^2-(613/16)r-3481/100<0. Exact proof uses exp(47/40)<81/25 from exp_bound at 47/80, giving 1<r<56/25.

Conclusion: strict second-level Laguerre concavity + global Riccati/angle concavity + positive coalesced C5 chamber still do not imply global C5. The surviving burden is genuinely completed-theta-specific, requiring nonlocal atom-likelihood control of the normalized logistic defect.

Lean module:
formal/GaloisForLFunctions/HilbertMetric/SecondLevelConcavityRiccatiFifthRootNoGo.lean
Capstone:
exists_secondLevelStrict_angleConcave_localC5Pos_kernel_with_globalC5Failure
Umbrella:
formal/GaloisForLFunctions/HilbertMetric.lean
Research card updated:
docs/drafts/pipeline/1-in-progress/theta-center-mixed-odd-four-point-cusp.md
Frontier map was read-only and not edited by this work.

Audit:
- lake env lean leaf: pass
- lake build GaloisForLFunctions.HilbertMetric.SecondLevelConcavityRiccatiFifthRootNoGo: pass
- #print axioms core theorems: propext, Classical.choice, Quot.sound only
- no forbidden proof tokens
- repo lint currently fails only on unrelated concurrently-added unreachable RHTower/HTGeometry modules.