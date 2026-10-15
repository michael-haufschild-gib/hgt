# EWU: negative-double-pole branch eliminated

New formal module: `formal/GaloisForLFunctions/RHTower/EvenSectorDoublePoleExclusion.lean`, wired into `RHTower.lean`.

Main theorem `RHTower.EvenSector.canonical_or_negative_superpole`: for every real beta and source lambda with `WeilPositiveEvenAt beta lambda`, either lambda(n)=vonMangoldt(n) for all n>=2, or for some real sigma>1 the series `max(-lambda(n),0)/n^sigma` is not Summable. No additional convergence, Abel-limit, sign or lower-floor premise occurs in this classification. Super-pole means a divergence alternative, not an assertion of meromorphic continuation or an actual pole. Full EWU remains open.

Mechanism: define the exact actual-source cosine kernel `C(t)=beta*farJ^2*(exp(-t/2)+exp(t/2))+farCosineArch(t)-farSum(lambda,t/2)`. Note the prime coefficient is ONE. With e_t the unnormalized even far bump, `Q(g+c e_t)=q+4c C(t)+2c^2(q+C(2t))`, q=C(0). Positivity gives `2 C(t)^2<=q(q+C(2t))`. Repeated squaring prohibits a polynomial factor at the exponential boundary. Absolute Dirichlet convergence at every exponent >1 supplies every exponential type >1/2. The exact far-window Abel identity then gives the no-negative-double-pole input automatically, and existing Abel pinning forces the canonical source. Existing convergence of the positive part turns the result into the unconditional canonical-or-negative-divergence classification.

Useful declarations: `farCosineKernel_doubling`, `cosine_doubling_exponential_type`, `no_negative_double_pole_of_weilPositiveEvenAt`, `canonical_or_negative_superpole`. The old frontier alternative involving a separate negative-double-pole branch is superseded by this theorem. The remaining branch is negative-part divergence at some sigma>1.

Paper proof and failed-conjecture record: `docs/drafts/pipeline/3-formalized/ewu-double-pole-exclusion-2026-10-15.md`. C1–C5 are unsuccessful mechanisms with open blindness/positivity requirements, not universal impossibility theorems.

Validation: targeted `lake --old build` passed; final `lake env lean GaloisForLFunctions/RHTower/EvenSectorDoublePoleExclusion.lean` passed with no output. Five critical `#print axioms` checks in /tmp yielded only propext, Classical.choice, Quot.sound. Index refreshed, exact corpus search locates the capstone. Global `scripts/formal_tools.py lint` blocked only by the pre-existing unrelated unwired CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion module; no new EWU error. No full/umbrella build, heartbeat increase, numerical experiment, web search, novelty audit, commit or push.
