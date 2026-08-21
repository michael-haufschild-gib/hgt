# Optimal-design weighted static-Choi first-return law

- **ID:** `optimal-design-weighted-static-choi-first-return-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Date:** 2026-08-21

## Exact result

For any finite normalized target dictionary, replica order `r`, static Choi orbit, and common
initial-return cut, a determinant-optimal probability design on actual target endpoints bounds the
complete post-cut capture event with one factor

\[
 m_r=\dim_{\mathbb C}\operatorname{span}\{\phi_c^{\otimes r}:c\in C\}.
\]

Target count is absent. Every surviving source sheet retains its original restricted Gaussian mass.
For maximally projective spectrum `E`, one-target Gaussian replica moment satisfies

\[
 \mathbb E_X F(\Omega_E(TX),\phi)^r
 \le {r!\over d^r}+A_{r,\delta}(E,\phi)+e^{-(T\delta)^2/2},
\]

where `A` is exact target-weighted strictly-near replica-action mass. If `w*` is canonical
determinant-optimal endpoint design, then no narrow hit occurs after initial return cell and before
`T` whenever

\[
 m_r\left[{r!\over d^r}+\sum_cw_c^*A_{r,\delta}(E,\phi_c)
      +e^{-(T\delta)^2/2}\right]
 < c_G {\epsilon_w-\epsilon_n\over 2T\,v_E}(1-\epsilon_w^2)^r.
\]

This is linear in source mass, not squared. It is sharper than label-union and worst-spectrum
crowding bounds. An arbitrary, possibly infinite or adaptive target class transfers through one
finite projective net with only net radius added to narrow capture error.

## Lean certificates

- `RHTower.StaticChoiOptimalDesignFirstReturnLaw`
- `RHTower.StaticChoiOptimalDesignAdaptiveNetFirstReturnLaw`
- `RHTower.StaticChoiOptimalDesignWeightedCrowdingFirstReturnLaw`
- `RHTower.NearestNeighborGaussianSameDrawGrowthPlateauRecurrenceLaw`

Headline declarations:

- `no_forward_pureChoiCircuitReturn_of_canonicalOptimalDesignWeightedCrowding`
- `no_forward_adaptivePureChoiCircuitReturn_of_gaussianReplicaCrowdingNet`
- `nearestNeighborPath_sameDraw_growth_firstCircuitReturn_of_canonicalWeightedCrowding`

All targeted source checks and module builds pass. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Exact remaining Brown frontier

The theorem does not establish that ordinary fixed-`q` Gaussian local draws satisfy displayed budget
at Brown scale. Remaining mathematical problem is quenched growing-replica lower-tail bound for

\[
 m_r\sum_cw_c^*A_{r,\delta}(E_H,\phi_{H,c}),
\]

uniform over Brown time/depth schedule and intersected with already-proved laboratory-growth event.
For continuous gates, one additionally needs entropy-efficient projective circuit net; abstract net
transfer itself is closed. Minimum spectral gap, raw target count, global Haar mixing, and worst
action degree are not active invariant.

## Gates

- [x] Dependency-closed paper proof
- [x] Lean formalization
- [x] Umbrella wiring
- [x] Targeted build and axiom audit
- [ ] External novelty audit
- [ ] Ordinary fixed-`q` quenched weighted-action estimate
- [ ] Brown-scale continuous-circuit net instantiation
