Route E remains open: no signed covariance upper bound, no bounded-return subsequence, no RH or simplicity proof. Goal active.

Closed new leaf formal/GaloisForLFunctions/RHTower/MobiusProductFibreVariation.lean (namespace RHTower.MobiusProductFibre). Imports MobiusLaplaceGammaHankelWall, SquarefreeLowerDensity, mathlib Liouville. Physical indices 1..N, all ordered pairs, no coprimality restriction.
- pair_sign: mu(m)mu(n)=lambda(mn)mu(m)^2mu(n)^2.
- signedFibre_eq_sign_mul_unsigned; abs_signedFibre_eq_unsigned: exact product q has one sign lambda(q).
- energy_eq_signed_fibres and energy_eq_liouville_weighted_fibres: original finite Gamma--Hankel energy = Gamma(r) sum q<=N^2 lambda(q)W_N(q;r).
- variation_power_lower: full absolute product variation >= (2^(-r)/16) N^(2-r) for N>=1,r>=0, using existing quarter_le_card_squarefree.
- tendsto_variation_atTop for 0<=r<2.
- squarefree_pair_isSquare_iff: if m,n squarefree, IsSquare(mn) iff m=n. Proof squarefree divisor of k² divides k; both <=k forces equality.
- diagonal_eq_square_fibres: D_N exactly square-product fibres.
- covariance_eq_nonsquare_fibres: C_N exactly Gamma(r) sum nonsquare q lambda(q)W_N(q;r).
- gamma_mul_variation_eq_diagonal_add_cross and tendsto_crossVariation_atTop: even after removing entire bounded diagonal, absolute nonsquare variation -> infinity for each 1<r<2.
These classify the actual source and exclude internal-fibre cancellation and absolute fibre summation. They do NOT imply divergence of signed covariance or exclude cross-product cancellation, bounded returns, or RH.

Verification terminal:
lake env lean /tmp/route_e_product_fibre.lean session29849 exit0 no diagnostics. Earlier scratch29217 failed only wrong multiplication-order lemma; fixed using mul_le_mul_iff_right₀ hg. Production differs only added documentation.
lake build GaloisForLFunctions.RHTower.MobiusProductFibreVariation session68213 exit0, 99s new leaf, new leaf no diagnostics, dependency informational tactic suggestions.
RHTower umbrella import wired near6209.
index session65402 exit0, generated API/GAPS/OVERVIEW and search refreshed.
lint session38546 exit0, /tmp/route-e-product-fibre-lint.log says formal lint passed, existing file-size warnings.
No own Lean/search processes remain. No full/umbrella builds, no numerical experiments, no #print axioms. No commit/push. Dirty shared worktree has unrelated concurrent changes, preserve all.

Docs:
Initial in-progress route-e-product-fibre-cancellation.md MOVED to docs/drafts/pipeline/5-failed/mobius-product-fibre-absolute-summation.md. Full positive survivor, paper+Lean status and scope there; no old-path references found.
Parent docs/drafts/pipeline/1-in-progress/route-e-literal-renewal-energy-attack.md has Attempts9-10; frontier updated with exact nonsquare target; STATUS top route-independent condition: cannot cancel inside groups whose label already determines every nonzero sign.

Attempt10 paper only:
For prime p, A_N^p(x)=sum n<=N,p∤n mu(n)e^-nx, M=floor(N/p), B=A_N^p-A_M^p.
F_N=H+B, H=A_M^p(x)-A_M^p(px).
Complete cell Q=(m+n)^-r-(pm+n)^-r-(m+pn)^-r+(pm+pn)^-r.
Gamma Q integral x^(r-1)(e^-mx-e^-pmx)(e^-nx-e^-pnx), so Q>0 and Q<=K pointwise. Each squarefree cofactor pair still carries lambda(mn). Pointwise kernel ordering does not give signed quadratic-form ordering. Actual E_N=||H||²+2<H,B>+||B||² retains boundary (N/p,N]; no bound for either missing term. These are paper identities, not new Lean producer.
Next hard attack must derive a collective many-prime incidence bound with retained physical weights and cutoff boundary. Do not add more one-prime reconstruction receivers or replace integer prefixes by complete-prime products (already divergent in Gamma norms).

Corpus searches used /tmp/route-e-gcd-pair-search.json, product-fibre-search, squarefree-mass-search, prime-fibre-remainder-search, prime-cell-method-search. Deep coverage partial, inspect statements/source_arguments/ingredient_sets. Product ingredientset finiteSignedCharge_product plus finite modular shear norm was not_verified and lacks identification/bound. Actual mu/lambda and squarefree-density sources supplied closed proof. MobiusCoprimeSquarefreeProductSignCount retains unknown signed imbalance. LiouvilleSignedCofactorDilation retains nondivisible residual. MobiusMertensPrimeRemovalTentLaw supplies actual coefficient prime-free difference, exact Mertens interval window, no interval bound. MobiusMultiplicativeRectangleCubature bounds admitted rectangles but no actual covering/uncovered residual estimate. Prime-cell deep search returned no ingredientset; exterior envelope only valid x>=fixed delta, continuation criterion assumes energy.

Broad recent arXiv coloring sources read:
https://arxiv.org/html/2607.25973v1 Or Zamir fixed-k coloring algorithm, needs low-degree structure or large sets restricted to disjoint palettes; no arithmetic mapping, no algorithms run.
https://arxiv.org/html/2607.20752v1 Shi-Dong (July22, manuscriptAug24) digit color equal-carry lemmas for arithmetic progressions and finite-field norm construction; no actual Möbius sign/weight restriction.
Other broad coagulation/disintegration mostly older/irrelevant. No source supplied RH bound.
