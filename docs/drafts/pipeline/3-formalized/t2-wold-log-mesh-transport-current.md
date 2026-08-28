# Ordered-prime Wold log-mesh transport current

- **ID:** T2-WOLD-AE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · T2 ordered-prime shell defect
- **Statement:** The centered Wold residual edge molecule converges on the ordered prime-log mesh in the Lipschitz-free/Arens--Eells transport norm; its exact dual norm is the already finite series `sum |R_N| (log p_(N+1)-log p_N)`, attained by a canonical source-sign potential, and Fourier evaluation is the physical residual Hardy boundary kernel.

## Goal

Construct the source-marked nonscalar carrier demanded by T2 after compact-open scalar descent and absolute critical graph closure were proved impossible.  Claim uses only ordered prime shells, centered Wold residual, and its unconditional square-root-log damping.  It does not assume a divisor, RH, critical-gap energy, or analytic continuation across the half-density wall.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem package in `XiHeatCassiniWoldLogMeshTransportCurrent`, target build green, axiom audit standard
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen claim

Write `h_N = log p_N`, `delta_N = h_(N+1)-h_N`, and let `R_N` be the centered ordered Wold residual.  Define

`T(phi) = sum_N R_N (phi_N-phi_(N+1))`

for complex node observables satisfying the adjacent Lipschitz law

`norm(phi_N-phi_(N+1)) <= K delta_N`.

Prove:

1. `T(phi)` is absolutely summable and `norm(T(phi)) <= K V`, where
   `V = sum_N |R_N| delta_N < infinity`.
2. The recursively defined source-sign potential `Phi_0 = 0`,
   `Phi_(N+1) = Phi_N - sign(R_N) delta_N` is globally one-Lipschitz for prime-log distance:
   `|Phi_M-Phi_N| <= |h_M-h_N|`.
3. `T(Phi) = V`; hence the transport bound is exact, not merely an upper estimate.
4. Evaluating `T` on the negative prime characters `phi_N(z)=exp(-i h_N z)` gives exactly the existing Wold residual lower-Hardy kernel on the closed lower half-plane, and on real `z` gives the physical boundary phase kernel.
5. For every edge `N`, a unit-Lipschitz step observable isolates exactly `R_N delta_N`.  Therefore `T` vanishes on every unit-Lipschitz observable if and only if every centered Wold residual coefficient vanishes.

No quantitative Gevrey constant, upper-half continuation, or scalar compact-open descent is included.

## Approach

Use `summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap` as the transport-cost theorem.  Adjacent Lipschitz control gives a termwise absolute majorant.  Source-sign recursion makes every edge contribution equal `|R_N| delta_N`.  Global Lipschitz control follows by induction and exact telescoping of ordered log heights.  Fourier landing is definitional after identifying the current atom with `xiHeatCassiniWoldResidualComplexPhaseConnectionAtom`.

## Proof

**[PROVED HERE]** Let `V_N = |R_N| delta_N`.  Corpus theorem
`summable_abs_xiHeatCassiniOrderedWoldResidual_mul_primeLogGap` gives `sum V_N < infinity`.
For any adjacent `K`-Lipschitz observable, multiplicativity of the complex norm gives

`norm(R_N (phi_N-phi_(N+1))) <= K V_N`.

Comparison proves absolute summability; triangle inequality for the infinite sum gives
`norm(T(phi)) <= K sum V_N`.

Define `Phi_(N+1)=Phi_N-sign(R_N)delta_N`.  Since the sign has modulus one,
`|Phi_(N+1)-Phi_N|=delta_N`.  Induction over ordered edges and the triangle inequality give, for
`N <= M`,

`|Phi_M-Phi_N| <= sum_(j=N)^(M-1) delta_j = h_M-h_N`.

Swapping endpoints proves the global prime-log Lipschitz law.  On each edge,

`R_N (Phi_N-Phi_(N+1)) = R_N sign(R_N) delta_N = |R_N| delta_N`.

Termwise summation therefore gives `T(Phi)=sum V_N`, so the upper bound is exact.  Substitution of
`phi_N(z)=exp(-i h_N z)` makes each current atom definitionally equal to the existing complex
residual phase-connection atom; its sum is the lower-Hardy kernel, and restriction to real `z`
is the physical boundary kernel.

For fixed `N`, define the step probe `E^N_j=delta_N` for `j <= N` and `E^N_j=0` for
`j>N`.  Every adjacent difference is zero except at edge `N`, where it is `delta_N`, so `E^N`
is unit-Lipschitz.  The corresponding current atom is zero off edge `N` and equals
`R_N delta_N` on edge `N`; hence `T(E^N)=R_N delta_N`.  Strict positivity of consecutive
prime-log gaps recovers `R_N` from this value.  Thus annihilation of all unit-Lipschitz probes is
equivalent to coefficientwise vanishing of the centered Wold residual.  No open premise remains.

## Hostile audit

- **Circularity:** none; no Xi zero, RH, critical energy, or continuation premise occurs.
- **Known no-go conflict:** none.  Carrier is nonscalar and source-marked; it does not claim compact-open continuity or absolute convergence at upper height `1/2`.
- **Degeneracy:** exact norm attainment prevents the construction from being a renamed convergence bound.  Edge probes additionally prove coefficient-faithfulness: the whole current vanishes on the unit-Lipschitz ball exactly when every `R_N` vanishes.  Even if some `R_N` vanishes, sign convention leaves a legal unit-slope potential and the corresponding edge contributes zero.
- **False strengthening rejected:** replacing transport norm by coefficient total variation, or demanding upper-half exponential moments, conflicts with the critical graph/half-density no-go.
- **Literature audit (2026-08-28):** searches for prime-gap/Mertens/Wold combinations with Arens--Eells, Lipschitz-free, Wasserstein, and logarithmic edge currents found the general molecule/duality framework but no prime-log Wold residual instance or exact Fourier landing.  General comparison source: Albiac--Ansorena--Cuth--Doucha, *Lipschitz free p-spaces for 0<p<1*, arXiv:1811.01265, especially molecules and duality at `p=1`.

## No-go closure

- **Exact killing theorem/mechanism:** Absolute critical residual variation plus critical mesh energy is inconsistent: critical zeta multiplicity survives as a nonzero radial residual pole.  Compact-open scalar reporters erase multiplicity-matched escaping bubbles.
- **Strongest positive survivor:** source-marked ordered edge molecule with finite exact transport norm, a canonical norming potential, and unit-Lipschitz probes separating every source coefficient.
- **New insight:** T2's viable carrier is a coefficient-faithful transport current on prime-log edges, not an absolutely summable coefficient measure and not a scalar compact-open reporter.  Its Fourier transform recovers the physical Hardy boundary kernel while retaining and individually recovering edge provenance.
- **Status:** dependency-closed paper proof and Lean formalization complete.  Main declarations:
  `norm_xiHeatCassiniWoldResidualLogMeshCurrent_le`,
  `xiHeatCassiniWoldResidualLogMeshNormingPotential_lipschitz`,
  `xiHeatCassiniWoldResidualLogMeshCurrent_normingObservable_eq`, and
  `xiHeatCassiniWoldResidualLogMeshCurrent_negativePhase_eq`,
  `xiHeatCassiniWoldResidualLogMeshCurrent_edgeProbe_eq`, and
  `forall_unitLipschitz_woldResidualLogMeshCurrent_eq_zero_iff`.

## Log

- 2026-08-28 — created directly in Stage 1 after corpus audit, two no-go checks, and external literature search.
- 2026-08-28 — `[PROVED HERE]`; promoted through Stage 2 to Stage 3 after direct source check,
  target-only `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldLogMeshTransportCurrent`,
  umbrella wiring, and axiom audit `[propext, Classical.choice, Quot.sound]`.
- 2026-08-28 — strengthened by exact unit-Lipschitz edge probes and the coefficient-faithfulness
  equivalence; target build remained green.
