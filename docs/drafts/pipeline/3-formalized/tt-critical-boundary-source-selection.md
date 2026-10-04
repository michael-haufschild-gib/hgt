# TT actual-source selection of the critical boundary direction

- **ID:** tt-critical-boundary-source-selection (C66–C68)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/tt-actual-odd-border-primitive.md
- **Statement:** The actual complete modular orbit has q→1/12 and k(q−1/12)→−7/72, where q=(u−3J)/(u k(9−u²)); both compactified transverse coordinates decay faster than every inverse power of k.

## Goal and scope

C65 falsified third-slope positivity on the known coarse pointwise cone. Its exact compactification h=1/k, r=k²(9−u²), t=k(1−3J/u) exposed the expanding mode r−12t. These theorems identify how the actual source approaches the critical direction t/r=1/12. They assume no source-sign, asymptotic-model, or RH premise.

The actual global third-slope sign, full source quadratic, transported fourth Schur gap, controlled join, and all-rank closure remain open. Fixed-r,t boundary sign laws cannot be applied uniformly along this moving actual orbit.

## Dependency-closed paper proof

Let T=9−u², q=(u−3J)/(u kT), h=1/k. The corpus supplies the actual differential equations, 0<u<3, k>5/4, 0<J≤u/3, J<1, J′>0, monotonicity of k,u,J and k²T<361/25.

Positive J(1) and monotonicity give a positive lower bound on k′ for x≥1, hence k→∞. The kinetic bound implies T→0 and kT→0. Exact substitution in F=J′ gives

    F=T*(k²−2k/3−4/9−(2/3)u²*k*(k+2/3)*q).

Thus 0≤q<3/(2u²); because u≥u(1)>0 on the tail, q is uniformly bounded. Direct differentiation of the actual source, with every term retained, gives

    q′=(k/u)*(36*(q−1/12)+e),
    e=3/k+4/(3k²)−5Tq+(2/3)u²q/k−(2/9)u²q/k²
      +(2/3)u²*(1+1/(3k))*q²T.

Bounded q and u²q, together with T,h→0, imply e→0. Also k/u≥1/3. A bounded complete solution of this outward scalar equation must tend to 1/12: if it lies above any fixed upper band, comparison keeps it above its starting value and forces a positive linear increase forever, contradicting its bound; apply the same argument to its negative below a lower band. This proves q→1/12 without assuming convergence.

Now u²→9 and kT→0 imply k e→7/2. The exact inverse-ratio velocity is

    h′=−2h(1+h/3)J→0.

For any real a define f_a=q−1/12−a h and

    R_a=36a+k e−a u h′→36a+7/2.

The full source equation becomes

    f_a′=(k/u)*(36 f_a+h R_a).

If a>−7/72, R_a is eventually positive. Any later f_a>0 would trigger the same outward escape and contradict boundedness. Hence q≤1/12+a/k eventually. For a<−7/72, the opposite argument gives q≥1/12+a/k eventually. These moving barriers squeeze k(q−1/12) to −7/72 without assuming that rescaled quantity is bounded.

For every natural n, differentiate W_n=k^(n+2)T exactly:

    W_n′=k^(n+1)T*(2(n+2)(k+1/3)J−2u k²).

Since J≤u/3, u≥u(1)>0 and k→∞, the bracket is eventually at most −k. Thus W_n′≤−W_n on a complete tail. The signed scalar Gronwall inequality gives W_n→0. Consequently k^n r→0 for every n. The exact identity t=q r and q→1/12 imply k^n t→0 as well. These all-order statements control the joint approach to the boundary; they do not assert a slope sign.

## Lean certificates

Namespace `RHTower.ThetaCuspModularRatio`:

- `boundaryRatio_compact` identifies q with compactified t/r.
- `boundaryRatio_tendsto` proves the unconditional critical-direction limit.
- `boundaryError_scaled_tendsto` proves k e→7/2.
- `boundaryRatio_eventually_le_barrier` and `boundaryRatio_eventually_ge_barrier` prove the moving barriers.
- `boundaryRatio_firstOrder_tendsto` proves the unconditional first-order limit.
- `kineticGap_superpolynomialDecay` and `compactifiedDeficit_superpolynomialDecay` prove both all-order transverse decay laws.

The comparison core is `HTGeometry.BoundedUnstableSelection.no_bounded_escape` and `tendsto_equilibrium`. All six scratch leaves passed direct `lake env lean` audits, with imported dependencies and only `propext`, `Classical.choice`, `Quot.sound`. Production copies are `ThetaCuspRatioBoundaryEscape`, `ThetaCuspRatioBoundaryDynamics`, `ThetaCuspRatioBoundarySelection`, `ThetaCuspRatioBoundaryResidual`, `ThetaCuspRatioBoundaryFirstOrder`, `ThetaCuspRatioKineticFlatness`; all six production leaves passed direct audits, are wired into the umbrella and indexed. The final imported audit confirms all four actual capstones have no premises and only the three standard foundational axioms.

## Log

- 2026-10-04 — C66 critical-direction theorem and C67 first-order theorem proved and checked. C68 all-order kinetic-gap decay opened to control the simultaneous actual boundary limit.
- 2026-10-04 — C68 proved and checked for both compactified transverse coordinates, at every algebraic order. Production audits running serially.

- 2026-10-04 — Production integration complete. Final imported type/axiom audit exit0; superseded scratch sources/caches removed. No full or umbrella build, no proof-limit raises, no external mathematical computation.
