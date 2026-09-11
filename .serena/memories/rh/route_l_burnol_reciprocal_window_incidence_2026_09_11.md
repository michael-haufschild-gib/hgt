# Route L C33: actual reciprocal-window incidence — closed

RH remains unproved; goal active. Chain: complete original source → cyclic/fixed physical reader agreement at original anchor → conormal vanishing → RH. Previous C32: `mem:rh/route_l_adiabatic_gaussian_boundary_parity_2026_09_11`.

New module `formal/GaloisForLFunctions/RHTower/BurnolCoPoissonReciprocalWindowIncidence.lean`, 13 exported theorems, 3 internal lemmas, 3 definitions. Wired after BurnolCoPoissonReciprocalSeedLanding in RHTower. Card `docs/drafts/pipeline/3-formalized/route-l-burnol-reciprocal-window-incidence.md` (L-C33); frontier + route-neutral STATUS updated.

## Actual mathematical progress
For L>0, f_L is existing actual Sonin/co-Poisson source of reciprocal seed on [exp(-L),1]. Ff_L is actual co-Poisson indicator seed [1,exp L]. Proved arbitrary indicator-window absolute Mellin integrability throughout 0<Re(w)<1 via near C*t^(-Re w) and far C*t^(-Re w-1) bounds, then exact integral ζ(w)*(d^(1-w)-c^(1-w))/(1-w).
Literal completed Fourier evaluation at unchanged w is G(w)ζ(w)*(exp(L(1-w))-1)/(1-w). No reflection of the zeta argument was used.
At actual Xi divisor rho, exact m=burnolCoPoissonXiConormalOrder rho, all lower completed Fourier jets vanish and leading jet is nonzero. Original/partner leading formulas:
J_L = G(rho) ζ^(m)(rho) (exp(L*rho)-1)/rho;
K_L = G(rho) ζ^(m)(rho) (exp(L*(1-rho))-1)/(1-rho).
Same original nonzero zeta conormal and Gamma factor retained. Completed doubled-window quotients centered by exp(-L/2) give E=exp(L*(rho-1/2)) and E^-1 at same rho.
At L=log n, their squared-norm difference is deningerBurnolActualConormalRadialReflectionDefect n rho. Final theorem deningerCofinalRelativeBocksteinIncidence_sourceValue_eq_actualFourierWindow substitutes this difference into complete incidence source value with original p,q,hpq,r,m and nonzero cross-prime witness retained. Zero-set exactly critical line; no vanishing, RH, physical cyclic agreement, or equal complex phases proved/assumed.

## Audit (all terminal)
- /tmp/route_l_burnol_reciprocal_incidence.lean final scratch session58856 exit0 emptylog; all tree theorem bodies exactly match. Only imports/examples/header differ.
- Targeted lake build GaloisForLFunctions.RHTower.BurnolCoPoissonReciprocalWindowIncidence session53580 exit0; ONLY leaf built (63s),11272 cached/leaf jobs. Existing dependency diagnostics replayed; no leaf diagnostics. /tmp/route_l_burnol_reciprocal_build.log.
- /tmp/route_l_burnol_reciprocal_axioms.lean session49683 exit0. 13/13 exported theorem audits exactly propext, Classical.choice, Quot.sound, covering all 3 used private lemmas transitively. No new axiom/sorry. /tmp/route_l_burnol_reciprocal_axioms.log.
- python3 scripts/lean_dupcheck.py <new file> exit0,19 declarations,0 collisions. Direct executable failed permission126; python invocation correct.
- scripts/formal_tools.py index session13671 exit0,5 shared changedfiles; LEAN_API/GAPS/OVERVIEW regenerated.
- scripts/formal_tools.py lint session74831 exit0, formal lint passed (shared earlier C32 unfinished modules had meanwhile changed). No umbrella/full builds, no numerical experiments. No commit/push performed here.

## Research
Three deep/method searches completed, all20candidates+20source arguments inspected each. First2 /tmp/route_l_burnol_incidence_c33_deep.json and /tmp/route_l_burnol_jet_c33_deep.json: generation823361 semantic2196271/2337495 partial, no ideas/ingredients. Third /tmp/route_l_burnol_gram_c33_deep.json: gen824048 semantic2192666/2347598 partial, deadline/filter-and-judge/source_refresh unfinished, no ideas/ingredients.
Third search actual parity methods: BurnolCoPoissonParityChannels.lean read1–175: genuine selfadjoint Fourier± projectors, source quotient commuting. BurnolCoPoissonCosineClosedExactJetDetection.lean read1–end: right-half closed source lower jets killed and actual first-live jet nonzero. BurnolLiteralApertureJetSystem.lean read1–105: Riesz index strictly below multiplicity; cannot use these annihilated tests on leading mth jet. Generic unitary Gram invariance/common inverse-Cholesky requires its own isometry/common-frame input, not provided for physical nonlinear jet ratios.
Broad recent arXiv: reciprocity,sewing,transmission. Primary https://arxiv.org/abs/2609.04169 (Vu et al) Theorem6 HTMLproof read: weighted D1 X=(D2 Y)^T, not raw D1=D2^T; positive compliance gives contraction via Schur complement. No theorem adopted as Lean input. https://arxiv.org/abs/2609.08820 abstract plus initialHTML only, no specific result adopted. https://arxiv.org/abs/2608.07054 empirical optical interleaving abstract, irrelevant proof-wise.

## Next obstacle / attack
Actual Fourier partner-to-physical comparison is now closed; it retains rather than annihilates radial defect. Need source-derived equality of radial readouts / agreement with cyclic reader. Test REAL polarized source pairing that measures squared-norm difference, preserving both actual normalization factors and complete corrections. Do not assume that Hilbert Fourier orthogonality survives point-conormal evaluation. Do not demand complex-character equality: inverse characters can have different phases even on wall. No fixedness, stationarity, common-frame/isometry premise, or counterterm defined to cancel the desired scalar may be silently inserted.

## Useful scratch fixes
(inv_le_inv₀ (by linarith : 0<1+t) ht0).2 (by linarith). Integral cpow endpoint uses rw [show -w+1=1-w by ring] (congr2/ring made spurious diagnostics). For actual Fourier coeFn, first prove reciprocal SEED equals indicator[1,exp L] and rewrite only that seed in the a.e. equality: simplification of exp(-L) throughout the a.e. equality also changed the source vector's parameter and caused a genuine type mismatch.
