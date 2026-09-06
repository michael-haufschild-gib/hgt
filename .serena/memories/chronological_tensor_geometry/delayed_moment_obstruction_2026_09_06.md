# Delayed geometric moment obstruction: current hard-proof checkpoint

Goal active; user insists every turn attack hardest mathematics, no more standard operator infrastructure. No novelty/priority established. No subagents, commits or numerical jobs this turn.

## New paper theorem
`docs/drafts/pipeline/2-fully-proven/chronological-delayed-moment-obstruction.md` contains a dependency-closed analytic proof, no numerical input. Same actual A=R[u,c²,c³]⊂B=R[u,c], base wedge K0={0≤c≤1,c≤u≤3c}. Actual homogeneous quotient costs β_k=1/((k+1)2^(k+1)), from positive-node Lagrange coefficient duality for T_(k+1)(r−2).
For N=2^(j+4), m=N+1, ξ=cos(π/m), cardinal l1 at ξ among cos(iπ/m), set α=−2m²/(2m−ξ), ε=1/(16m³), h=1−ε/2, V=(1−ε)T_m+εαl1. It preserves the penultimate coefficient after r−2 translation. Homogenize F=c^m V(u/c−2); K_m=K0∩{|F|≤h}. All lower-degree Chebyshev nodes protected. With L=4m+1,a=h/(1+εL), q0=a^(1/m), q0K0⊂Km⊂K0. Thus exact Δ_k=β_k for k<N and aβ_N≤Δ_N≤hβ_N. Prefix through Δ_N remains strictly log-convex. Km→K0; explicitly nonconvex (both top endpoints included but (2+ξ,1) excluded).

Squared normalized γ agrees with b_k=4^-k/(k+1)^2 below N. For d=N/2, monic Q_d=2·16^-d T_d(8x−1) has Lγ(Q²)≤4·16^-N−4^-N/(32m^5)<0. Elementary induction proves 4^N>128m^5. Base b=double integral of (st/4)^k on unit square. Hence all nonzero polynomial squares of degree <2d remain strictly positive, first failure degree exactly d, first failing Hankel matrix inertia (d,1,0). Unbounded first-failure degree with identical thermal −Γζ response; moment representability not open at K0. No all-tail log-convexity or convex-domain counterexample claimed.

Original cubic Jacobi degree17 numerical witness remains UNPROVED. New family is a structural realization theorem, not its sign proof. Prior papers exponential rate and uniform spectral disc remain paper-only; retain original card `chronological-recovery-moment-problem.md`.

## Key proof simplification
l1(x)=[1+2Σ(k=1..m−1)cos(kπ/m)T_k(x)−T_m(x)]/m. Finite cosine kernel D_m(t)=Σ(k=0..m−1)cos(kt)+(cos(mt)−1)/2 satisfies 2sin(t/2)D=sin(mt)cos(t/2), D(0)=m, D(qπ/m)=0 for 0<q<2m, D even. Product-to-sum identifies cardinal values and norm ≤2. Highest coefficients −2^(m−1)/m and −ξ2^(m−1)/m give translated coefficient. This replaces derivative-quotient estimates in paper.

## Lean completed
New leaf `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor/RecoverySurgeryGrid.lean`, 524 lines, 40 declarations (33 theorems,7 defs). Final individual `lake build GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryGrid` PASS no warnings. All 40 #print axioms audit PASS, only propext/Classical.choice/Quot.sound. Import wired HTGeometry; index refreshed. Total 107 leaves/1134 declarations=843theorems291defs.
Formalized exact cosine expansion, bound2, rational-angle grid separation, V degree≤m, selected node V<−1, ε/α estimates, global perturbation bound, unconditional `recoverySurgery_lower_grid (n)(l:Fin(n+1))(i:Fin(l.val+2))`. Here n=m−2 (paper n=N−1). Main preserves all lower-degree grids with no external hypotheses. Scratch `/tmp/chronological_chebyshev_grid.lean` passed; source equivalent plus header/comments and removed examples. Full geometric theorem NOT yet formalized.
Axiom scratch `/tmp/chronological_recovery_surgery_grid_axioms.lean`, output `.txt`; summary `/tmp/chronological-recovery-surgery-grid-audit-summary.txt`. No owned Lean process remains. Global lint currently fails on concurrent OTHER researcher's unwired RHTower.CCMRestrictedWeilPoleDiagonalSharpConstant; no chronological module flagged. Do not edit their work/processes; earlier ps confirms separate active researcher building it.

## Next substantive proof
1. Preserved penultimate coefficient via last two terms of cosine expansion and translated-coefficient formula. `Polynomial.Chebyshev.leadingCoeff_T R (n:Z)`=2^(n.natAbs−1), `natDegree_T R n`=natAbs; verified in this toolchain. Beware unrestricted simp expands Chebyshev recurrence; use simp only.
2. Actual compact domain and protected-node coefficient duality yield first N quotient norms, and homothetic core yields bound at N.
3. Exact negative square using base polynomial integral and symbolic exponential-vs-polynomial bound; no prescribed-sequence substitute.

Compact high-level notes `docs/drafts/pipeline/1-in-progress/excursion-intervention-geometry.md` fully updated. One foreground Lean process per agent, scratch lake env lean, final leaf lake build only, no full/umbrella builds, no numerical certificates. Math numerics only Runpod if needed; none needed for this theorem. Preserve shared tree. Plan tool unavailable.