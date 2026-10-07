# Next conjecture: exact discrete polar mass with overlapping Riemann profiles

Status: OPEN source conjecture, paper mechanism below; no Lean implementation. Original universal WP02 lower inequality remains OPEN. This candidate must pass a fresh novelty/utility and full paper audit before formalization.

## Literal candidate

Let b>=2 be an integer, ell=log(b), L>=2, and M>=0. Put psi_L=truncatedRiemannKernel L and

    f_i(u)=sum_(j=0)^M c_ij psi_L(u-j*ell).

Allow arbitrary finite complex coefficient rows and nonnegative mixture weights alpha_i. Impose the actual half-pole condition paperFT(f_i)(i/2)=0; full polar tests are included. Let K=M+ceil(2L/ell)+1, large enough to include every nonzero sampled correlation. Conjecture the exact physical-mass identity

    sum_i alpha_i integral |f_i(u)|^2 du
      +sum_(m=1)^K cosh(m*ell/2) sum_i alpha_i atomCoeff(f_i)(b^m) = 0.

Unlike separated Fejer window recovery, this statement retains every overlap of the actual Riemann profiles, and recovers physical L2 mass. It implies a weighted absolute-trace bound and a strictly negative sampled atom for every nonzero positive mixture in this source class. No archimedean sign or RH premise is allowed. This is not a proposed bound on all polar tests.

## Paper mechanism to audit

Define complex coefficient covariance C_d=sum_i alpha_i sum_(j-k=d) c_ij conj(c_ik), and sampled profile autocorrelation H_r=weilTest(psi_L,psi_L)(r*ell). Both sequences have finite support. The exact sample sequence V_m=sum_i alpha_i weilTest(f_i,f_i)(m*ell) is C*H, retaining every overlap.

Finite exponential evaluation is multiplicative under convolution. Hence

    sum_m V_m exp(m*ell/2)
      =(sum_d C_d exp(d*ell/2))*(sum_r H_r exp(r*ell/2)).

The first factor is sum_i alpha_i P_i(+) conj(P_i(-)), where P_i(+/-)=sum_j c_ij exp(+/-j*ell/2). The actual profile factor paperFT(psi_L)(i/2) is nonzero, by positivity of the truncated Riemann kernel on a fixed central interval. Thus source half-pole vanishing forces P_i(-)=0 and the product vanishes. Taking real parts, using conjugate symmetry V_-m=conj(V_m), and pairing positive/negative m gives the displayed identity. The zero sample is exactly the physical mass, and atomCoeff at b^m is 2 Re(V_m), with no 1/sqrt(n) or 2*pi factor inside atomCoeff.

[OPEN CORE] Verify the exact finite convolution, complete support range, actual profile multiplier, all exponential/pole normalizations, and physical mass positivity. Check whether this exact law is already present in the corpus. Do not count a rephrased no-go or a general finite-convolution wrapper as scientific novelty.

## Evidence and relation to the main problem

Cycle 13 deep search on discrete exponential polar moments completed non-partial with a complete 68,482-file inventory, predominantly pending/stale compiler data, and incomplete background refresh. All candidate lemmas, source arguments and generated ingredient sets inspected. It recovered the existing private `sum_geometric_autocorr` and `sum_geometric_logValue` in WeilWorkDeficitGeometricRadicalObstruction, plus owned exposing-tail bounds. The generated truncation-error recipe does not prove this exact discrete moment law. No absence claim follows.

The existing module already proves an outer-support invariant and injective complete power-sampling for broad truncated Riemann profiles on integer-base grids. Those no-go consequences are prior research. Intended additional content here is exact norm recovery and stability despite overlap, at the literal source used to approach the exposing endpoint. The covariance algebra is classical; external scientific novelty remains unestablished.

An arbitrary opposite-ray family need not have this common-profile/grid representation. Matching all positive integer atoms is stronger than matching b-powers, and a mass identity alone is not a signed Gamma-energy lower bound. The next audit must explain whether this identity constrains the actual vanishing tail budget or only supplies another restricted source diagnostic. Keep the original endpoint and every residual unchanged.

## Big-picture falsification and utility gate

The source factorization also predicts repeated half-pole zeros: the multiplier P(exp(i*z*ell)) is periodic under z -> z+2*pi*k/ell. If its half-pole vanishes, every real-period translate of that half-pole vanishes. Generic polar tests are constrained at only the original two points. This extra infinite zero pattern may explain the entire discrete mass law; verify it from the literal factorization, rather than treating geometric-grid rigidity as evidence for the full cone.

Before investing in another Lean leaf, determine whether physical-mass recovery materially constrains the existing near-radical opposite-ray candidate and its vanishing tail budget. If its only contribution is a quantitative restatement of this extra spectral restriction, classify it as a bridge/rediscovery and return to the all-integer signed residual. The successful overlapping short-step completion, the fixed local-seed capacity floor, and coarse-grid rigidity together point to the unresolved joint arithmetic/Gamma estimate; none removes that estimate.

## Cycle 14 utility verdict

DEPRIORITIZED as a source diagnostic; no false universal consequence and no Lean implementation claimed. The actual translate transform in `WeilFullConeBochnerMeasure` factors as the profile transform times `sum_j c_j exp(i*z*j*ell)`. At z=i/2 the profile multiplier is nonzero. At z=i/2+2*pi*k/ell every coefficient exponential is unchanged because j,k are integers. Thus the filter vanishes on the entire repeated half-pole lattice. The discrete mass identity measures precisely this stronger constraint. Its finite-convolution paper mechanism remains a valid positive survivor, but does not bound signed Gamma energy, supply a tail-sized approximation to the opposite exposing ray, or apply to arbitrary polar tests. The existing geometric outer-support rigidity already supplies a related qualitative obstruction. Do not spend another formalization cycle on a wrapper without a new endpoint application.

Fresh unrestricted searches returned actual ground-form reductions and exact moment realizations, but no paid signed estimate among inspected hits. Both searches were partial (reranking disconnection/Qdrant deadline), so no absence or novelty claim follows. Return to literal source production beyond even common-profile filters.
