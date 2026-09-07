# Actual BM quadratic angular source and correction

User currently requires rh-current-frontier-map.md READ ONLY. No edits to it from this work. RH goal remains active, unproved/unfalsified. Full chain: literal theta cusp → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → independent fixed Hawking-clock extinction → RH.

Proof card: docs/drafts/pipeline/3-formalized/hb-quadratic-angular-source-and-correction.md. Current source card: docs/drafts/pipeline/1-in-progress/hb-actual-einstein-metric-jet-source.md. Route-independent requirement appended to existing F20i-i in universal-law-field/STATUS.md.

Three new audited leaves:
- formal/GaloisForLFunctions/HTGeometry/CoordinateEinsteinComplexQuadratic.lean: 9 public theorems. Differentiates actual first Einstein variation, identifies finite second contraction with actual complex Hessian. Final leaf build 5.1s.
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuadraticAngularSource.lean: 2 public theorems, actual all-complex/all-y angular source. Final leaf build 221s.
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMQuadraticAngularCorrection.lean: 3 public theorems, explicit complete correction jet and actual corrected nonlinear path. Final leaf build 24s.

Let f=r²−1, B_t=sB, B_r=sB/(rf). Same scalar S supplies fundamental scalar and coexact vector (Sy,−Sx), independent amplitudes aS,aV. Scalar PDE Syy=(s+1)(s+2)S/y²−Sxx. Pair convention (Txx−Tyy,Txy).
H=(S*(2Sxx−(s+1)(s+2)S/y²−2Sy/y),S*(Sxy+Sx/y)); G=(Sx²−Sy²,SxSy); R(T)=(2T.2,−T.1/2).
C=s²((s+1)²−4r²)/(8r⁴), D=s²(3s²+12s+11)/(2r⁴), F=s²(s+1)/r³.
Actual quadratic angular Einstein source Q=B²[aS² C(2H+G)+aSaV F R(H+G)+aV² D G]. Arbitrary r,y,s complex with r,y,f nonzero. VV loses every second/third S derivative; SV is rotated Hessian of S². Actual Hessian /2 normalization, not a supplied source map.
Correction nonzero metric entries: k_tt=−2f aS² B² C S²; k_tA=f aSaV B² s(s+1)/(2r³) S(coexact S)_A, symmetric. Full product/inverse two-jet, not only values. Its actual linear angular Einstein image is −B²[2aS² C(H+G)+aSaV F R(H+G)]. Actual g+εh+ε²k angular ε² coefficient therefore equals B²(aV²D−aS²C)G.

Scope limits: only two angular tensor components evaluated. Other Einstein components, global correction field realization, nonlinear gauge, horizon/boundary admission, causal turn-on, constrained master reduction, physical left test, retained spin-two/AIME identification and fixed-clock extinction remain open. Crucially original affine-source pairing still includes Lk unless actual left test kills it on the physical domain INCLUDING boundary terms. Corrected-jet identity does not permit dropping Lk from original causal cut. Literal infinite cusp specialization of this new combined-source formula not yet added. These are intermediate chart theorems, not unconditional RH closure.

Next useful work: evaluate remaining actual Einstein components and construct physically admitted correction/response, then actual left pairing. Do not substitute another generic Bianchi/curvature/Green identity for this obstacle. Existing scalar reconstructed-metric boundary charge remains nonzero; reduced-master A=0 boundary cannot be conflated with reconstructed scalar metric falloff.

RunPod experiment: docs/drafts/pipeline/2-fully-proven/computations/hb-quadratic-angular-source-2026-09-07/. Frozen protocol, exact symbolic full nonlinear expansion, 3 workers, 9.91 seconds, y=1 only after derivatives. 96 background/linear checks. Outputs/code checksummed after download. Initial Python3.8 functools.cache incompatibility fixed to lru_cache(None), log preserved. Remote /tmp/hb-quadratic.OB3sO2 removed. Experiment only guided formulas; no results admitted to Lean.

Validation: exact-source cache-only package compiled only new leaves; one owned foreground Lean/Lake process at a time. Fourteen new public theorem axioms checked ONCE, all only propext/Classical.choice/Quot.sound. No old audits, full/umbrella/dependency builds. Each leaf wired once; only new olean/ilean installed after byte checks. Index current. Final lint --check-generated had sole unrelated concurrent missing umbrella import HTGeometry.SmoothBlockWindow, plus141 existing large-file warnings. Other task preserved. Exact 95-entry non-symlink local /tmp/hb-quadratic-lean.4jjRVf removed; all owned processes terminal.

Lean performance notes: to identify actual Hessian, explicitly align derivative point q+(0:ℂ)•v with q before unification; otherwise giant unfolding. Rewrite sparse K before finite-sum expansion; include angular in simp. Normalize ←pow_two, ←sub_eq_add_neg before field_simp so inverses of r*r−1 resolve. Pair proofs use dsimp then ring, not broad simp. In correction eq_sum use apply Prod.ext <;> (dsimp [...] <;> ring): dsimp closes one branch; semicolon sequencing instead causes No goals to be solved. Existing source proof expensive; avoid rerunning it.
