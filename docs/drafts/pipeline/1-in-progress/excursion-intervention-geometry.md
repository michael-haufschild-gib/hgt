# Chronological tensor geometry — working knowledge

**Status:** 20 final leaf builds passed; all 230 declarations axiom-audited (173 theorems, 57 definitions); latest global lint passes with existing large-file warnings. New-field novelty and priority remain unestablished. Goal remains active.

**Aim:** a coherent theory of ordered tensor observation, with complete paper proofs and unconditional Lean proofs. The paper, detailed derivations, and novelty references are in `docs/drafts/pipeline/3-formalized/chronological-tensor-geometry.md`. This file carries high-level state, not a diary.

## Primitive and scope

For a chord matching D on ordered endpoints, `P_D(x)=∏_(i,j∈D)(x_j−x_i)`. A linear combination P is observed with total variation budget `V=Σ|x_(i+1)−x_i|≤1`; capacity is `sup|P|`. Translation disappears in gap coordinates. Alternating tensors evaluated on affine probes `(1,x_i)` give these chord products. They are, up to orientation sign, classical two-row Specht polynomials of shape (r,r): [Moustrou–Riener–Verdure, Definition 8](https://arxiv.org/pdf/1912.05266).

Lean foundations allow arbitrary finite windows, a larger class than perfect endpoint matchings. They construct the bounded supremum, a mathlib seminorm, and observational kernel. No knot-isotopy or spacetime-curvature claim is made.

**Enclosure currently formalized:** multiply P by `S^k`, with S the existing probe's net displacement. Fresh outer endpoints with freely variable padding gaps are a separate nesting operation; do not silently identify them. The current operation agrees with that nesting on the zero-padding probes.

## Established mathematics

- Four endpoints: `D=uw`, `N=v(u+v+w)`, crossing `=D+N`; `cap(AD+BN)=max(|A|/4,|B|)`. Monotone probes suffice throughout this plane.
- Six endpoints: `D=ace`, `R=(a+b+c+d+e)(b+c+d)c`. Individually `cap(27D)=cap(R)=1`, but `cap(27D+R)=K≈1.132005672`, with exact maximizer `q=(50−√313)/81`. Models identifies actual capacity suprema, rather than merely proving loose inequalities.
- Curved support: response curve `φ(q)=(q(1−q)²/4,q²)`. For `1/3≤q≤√2−1`, supporting coefficients `(8q,(3q−1)(1−q))` have capacity `q²(1−q²)`. Actual derivative determinant is `(1−3q²)/2>0`. The `AD+R` plateau ends exactly at `A=12+8√2`, with two different maximizing motions at the transition.
- Reversal: monotone capacity of `27D−R` is 1; unit probe `(1/3,0,−1/3,0,1/3)` gives `−28/27`. Signed optimum remains unknown. A remote candidate ≈1.04387639 fits profile `27z(1−z)²/4+28z³/27`, stationary equation `841z²−972z+243=0`; global optimality unproved.
- Fusion: normalized n-fold product of `27D+R` has exact capacity `K^n`; each of its `2^n` normalized diagram summands has capacity 1. General arbitrary-form fusion is still open here.
- Growing-degree survival: `P_n=n^(3n)∏(27D_i−R_i)` has monotone capacity 1. Its enclosed rational probe has magnitude `(28/27)^n/3^k`. Taking `n=54(k+1)` gives at least 3 by Bernoulli. Existing Enclosure theorems concern these explicit response formulas; a general finite-window presentation of the block product still needs to be connected to the new abstract depth invariant.
- Fixed-form stabilization: with `M=monotoneCapacity` and `L=d·Σ|coefficients|`, `M≤C_k≤max(M,L/k)` for k≥1. Product telescoping, orientation, and `z^k(1+k(1−z))≤1` prove the estimate. `M=0` implies P=0 via a univariate polynomial vanishing on an interval. Thus every fixed form stabilizes exactly in finite depth.
- Degree-only bound: for d≥2, `C_(d(d−1)+k)=M`. Jordan decomposition plus classical Chebyshev extrapolation gives `|P(g)|≤M S^d T_d(V/S)`; `T_d(x)≤x^(d²)` completes the bound. This is an upper bound, not yet a sharpness theorem.
- **Exact cubic depth:** `|S(27D−R)|≤V⁴`. Small S uses the rational bound `|27D−R|≤8V³/7`; the remaining sign cases reduce to a quartic comparison. Consequently `C_k=1 iff k≥1`. Convexity extends positive-depth capacity B to the cone `AD−BR`, `0≤A≤27B`. The attempted extension to the entire coefficient plane failed: for A>27B, monotone capacity need not be A/27 because of cancellation.
- **Finite enclosure curvature:** `C_(k+1)²≤C_k C_(k+2)`. A plateau occurs iff C_k=M; before that, descent is strict. Define `κ_k=C_k−2C_(k+1)+C_(k+2)` and N=minimal stabilizing depth. Then `κ_k>0 iff k<N`, and `κ_k=0 iff N≤k`. Exact reconstruction: `C_k=M+Σ_(j<N)(j+1)κ_(k+j)`. Also `C_k−C_(k+1)=Σ_(j<N)κ_(k+j)`. CurvatureDepth checks all definitions, support, and finite telescoping identities.

## Current research choices

1. **Genuine outer nesting / padding:** adding free outer gaps replaces a fixed inner response by `t^d P(h)` and its enclosing displacement by `1−t+t|S(h)|`. For k nested outer chords, the candidate exact capacity reduction is `sup_h,t |P(h)| t^d(1−t+t|S(h)|)^k`. Padding.lean is scratch-checked: adding an unused gap preserves signed and monotone capacity, can only increase enclosed capacity/depth, and preserves the universal degree sealing bound. For the cubic, |(p+S)P|≤|p|(8/7)V³+V⁴≤(|p|+V)⁴; this extends exact one-enclosure behavior to a freely variable padding gap (scratch audit next). The full nested-chord reduction still needs its formal bridge. All outer padding windows share the innermost new gap: each factor is bounded by |S|+totalPaddingCost, and concentrating padding of the correct sign in that common gap attains all bounds simultaneously.
2. **Sharp degree depth:** homogenized Chebyshev `H_d(x,y)=(x+y)^d T_d((x−y)/(x+y))` has monotone capacity 1. On signed unit probes with displacement z, enclosed response is `z^(d+k)T_d(1/z)`. Its derivative at z=1 is `k−d(d−1)`, so depths below d(d−1) fail. Need a finite-window representation, zero-displacement treatment, and Lean derivative/existence proof. Sharpness for actual perfect matchings is separate.
3. Full signed six-endpoint ball, arbitrary fusion, and order-map contraction laws remain open. Prioritize results specific to chronology over further generic polynomial-norm machinery.

## Novelty boundaries and rejected ideas

Polynomial norm balls are established: [García et al.](https://arxiv.org/html/2408.01741v1), [Pérez-García–Villanueva](https://doi.org/10.1016/j.jat.2004.01.001). Extrapolation is classical: [Révész](https://arxiv.org/pdf/math/0703386). Finite stabilization uses the familiar Lipschitz/error-bound mechanism of [exact penalty theory](https://web.uvic.ca/~janeye/hosted/papers/ExactPenaltyFinal.pdf). Log-convexity and second-difference inversion are also known mechanisms. These ingredients alone do not constitute a new field.

Rejected novelty routes: phase-swap braids already in corpus; first-return renewal already [1302.7286](https://arxiv.org/abs/1302.7286) and [1702.04032](https://arxiv.org/abs/1702.04032); noncommutative realization already [Ball–Groenewald–Malakorn](https://doi.org/10.1137/S0363012904443750); switching-only tensor spaces overlap [Lotter–Preiß](https://arxiv.org/html/2607.04712v1). These are overlap findings, not impossibility theorems. Irreducible Casimir inclusion–exclusion and graph entropy remain comparison leads, not claimed inventions.

User's remembered ball-to-ring result remains unidentified. Inspected near matches: AbelianHiggsMechanism's unit-circle vacua and ObserverKernelTubeVolume's annular tubes. Corpus anchors: KnotTheory/ChordData, KnotTheory/RMatrix, ConstraintIdealExcursion, NoncommutativeDiscreteDevelopment (other researchers' work; preserve).

## Verification and resources

Lean directory: `formal/GaloisForLFunctions/HTGeometry/ChronologicalTensor`; all 20 leaves wired into HTGeometry. No full/umbrella builds. Single foreground Lean process; development via `lake env lean /tmp/...`, final audits via exact leaf `lake build`. All declarations use only `propext`, `Classical.choice`, `Quot.sound`; no numerical certificates or prohibited proof tactics.

Three remote searches completed with 24 workers and one BLAS/OpenMP thread each. Local source/results/reports/figure: `docs/drafts/pipeline/2-fully-proven/computations/chronological-chord-capacity`; remote directory `/root/chronological-chord-capacity`. The normalized-basis inequality failed numerically from degree three; the cubic failure and one-enclosure lead now have independent symbolic Lean proofs. Exact signed optimum remains a lead.

Shared tree contains other researchers' edits and commits. No commit/push initiated here. Plan tool unavailable; this document carries research state. Keep it compact.
