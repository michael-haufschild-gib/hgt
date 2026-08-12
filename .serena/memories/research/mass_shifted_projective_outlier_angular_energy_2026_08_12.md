# Mass-shifted projective outlier/angular energy (2026-08-12)

Formal module: `formal/GaloisForLFunctions/RHTower/AngularPolynomialLaguerreEnergy.lean`, wired in `RHTower.lean`.

Unconditional exact findings:
- For `q_Q(theta)=Q(cos theta)`, actual full-period integration by parts proves
  `2∫|q_Q'|² = ∫[cos theta Q Q' + sin² theta L1[Q]]`, where `L1[Q]=(Q')²-QQ''`.
- For real-split Q, corpus `laguerreL1_linear_mul` / `laguerreL1_eval_nonneg` makes the Laguerre term a nonnegative root-deletion density.
- For root multiset r, empirical mean and eta>=0:
  `eta² * outlierCount <= multisetQuadraticSpread r n`.
- For canonical admissions:
  `eta²*k_eta <= projectiveGaussRootSpread` and
  `2(2n+1)eta²*k_eta <= projectiveJacobiRetainedInventory`.
Thus retained adaptive mixed/completed arithmetic source literally pays constrained-zero outlier count.
- If empirical spread v=G/n tends to zero, eta=v^(1/4) gives eta->0 and k/n<=sqrt(v)->0 (paper consequence).

Analytic avenue:
Borwein–Erdelyi 1995 sharp constrained Lp Bernstein law has p=2 derivative energy scale O(n(k+1)) for factor h(cos theta)q(theta), h degree n-k with zeros outside unit disk and q degree k. This is the exact o(n²) scale once k=o(n).
Remaining precise bridge: prove shrinking central clustered-root arc has negligible normalized mass via Remez domination and transfer two exterior constrained-zero estimates through original arcsine/Cayley measure. Universal one-line variance Bernstein inequality is no longer needed and is not claimed.

Docs:
- Stage3: `docs/drafts/pipeline/3-formalized/mass-shifted-projective-outlier-angular-energy.md`
- Stage1 updated: `docs/drafts/pipeline/1-in-progress/mass-shifted-hard-edge-root-spread-bandwidth-rigidity.md`
- Report equations (9.3.634)-(9.3.638).

Verification:
- direct `lake env lean GaloisForLFunctions/RHTower/AngularPolynomialLaguerreEnergy.lean` passed.
- targeted `lake build GaloisForLFunctions.RHTower.AngularPolynomialLaguerreEnergy` passed [11791/11791].
- eight capstone axiom audits: only propext, Classical.choice, Quot.sound.
- forbidden token and diff whitespace scans clean; no stale Lean.
RH remains open.