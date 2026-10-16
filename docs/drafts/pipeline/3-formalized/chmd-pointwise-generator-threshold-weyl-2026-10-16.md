# CHMD pointwise generator and the threshold Weyl sequence of the arithmetic resolvent

- **ID:** chmd-generator-weyl-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CHMD route; continuation of chmd-polar-transfer-arithmetic-resolvent-2026-10-16 (cards listed "no selfadjoint generator theorem with explicit action, no spectral Weyl residual, no exact essential spectrum")
- **Statement:** (1) pointwise harmonic identity of `Θ` (symmetrized prime shift sum = polar rate + archimedean correction); (2) on compact `C²` tests the arithmetic Doob form has the explicit generator `v ↦ 𝒲₀(Θv)/cosh(·/2)` where `𝒲₀` is the pole-free Weil operator, valid against every vector of the completed graph, and `R v = v/2 − R(𝒲₀(Θv)/cosh)/2`; (3) the escape vectors form an orthonormal Weyl sequence of the resolvent at `1/2`, so `1/2 ∈ spectrum ℝ R` and the threshold is essential.
- **Status:** STATUS MUST-1543, MUST-1544. Four leaves (1463 lines, 95 declarations), all axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audits clean; `lake build --old` of each leaf green; wired once each into `GaloisForLFunctions/RHTower.lean`; index refreshed. Global lint exit 1 solely for other agents' untracked unwired modules (EvenSector*, OddWeil*, PaperThetaCutFactorConvolution, HTGeometry/AnalyticMonicRootGerm, HTGeometry/HeatEscapeSimpleRoots).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `theta_harmonic_identity`, `inner_edge_compactLift`, `genTotal_eq_weilOp`, `sourcePair_compactLift`, `resolvent_compactLift_source`, `norm_resolvent_sub_half_le`, `resolvent_defect_tendsto_zero`, `exists_weyl_sequence`, `half_mem_spectrum_resolvent`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
The Doob-graph cards had the arithmetic form only as a closed quadratic form (`‖edge‖² − mass`) with no explicit
operator action and no spectral information beyond "no positive primitive margin". Now: the generator acts on compact
tests as an explicit integro-difference operator (every prime power and the archimedean Lévy density visible), and the
critical value is a point of the essential spectrum of the bounded arithmetic resolvent.

## Paper proof
*Harmonic identity.* The corpus's complete theta source equation (one-sided, from `L[Θ] = ξ(1/2+w)` and the
logarithmic derivative) reads `−cΘ(x) + ∫_0^∞[ν(u)Θ(x) − ω(u)Θ(x+u)]du + ∫_0^∞ 2cosh(u/2)Θ(x+u)du − Σ_n a_nΘ(x+log n) = xΘ(x)`,
`c = (γ+log π)/2`, `a_n = Λ(n)/√n`. Adding the equation at `−x` (Θ even) kills `xΘ(x)`; the two polar half-line
integrals combine into `∫_ℝ 2cosh(u/2)Θ(x+u)du = cosh(x/2)` (cosh-addition, `∫Θcosh = 1/2`, `∫Θsinh = 0`), giving
`Σ_n a_n(Θ(x±log n)) = cosh(x/2) − 2cΘ(x) + ∫_0^∞ symArch(x,u)du`, `symArch = 2νΘ(x) − ω(Θ(x+u)+Θ(x−u))`.

*Edge pairing.* For compact `C²` `v,w`, `⟨edge v, edge w⟩_κ = ∫(Δv)(Δw)dκ` with `κ = arch + Σ prime_n`;
integrability of the product follows by polarization from the corpus's square integrability. Each edge of
displacement `s` gives `∫Θ(x)Θ(x+s)(v(x)−v(x+s))(w(x)−w(x+s))dx = ∫ w(y)Θ(y) J_s v(y) dy` by splitting at the two
endpoints and translating the second (`J_s v(y) = Θ(y+s)(v(y)−v(y+s)) + Θ(y−s)(v(y)−v(y−s))`). The archimedean
`t`-integral is exchanged with the `y`-integral by Fubini: `|J_t v(y)| ≤ 2‖Θ‖_∞ L t` (Lipschitz) and
`∫_0^∞ ω(t)t dt < ∞` (`ω(t)t ≤ (1+2t)e^{−t/2}/2`). The prime sum is exchanged by `Σ_n a_n sup_{|y|≤R}(Θ(y±log n)) ≲ Σ a_n/n² < ∞`.
So `⟨edge v, edge w⟩ = ∫ wΘ(J_arch v + J_prime v)`.

*Generator.* `ω J_t v(y) = [2νf(y) − ω(f(y+t)+f(y−t))] − v(y)symArch(y,t)` with `f = Θv` (both brackets integrable),
and `Σ a_n J_{log n} v(y) = v(y)·Σ a_n(Θ(y±log n)) − Σ a_n(f(y±log n))`; with the harmonic identity,
`J v − cosh(·/2)v = 𝒲₀ f`. Bounds: `|J_arch v| ≤ K_A` uniformly; `|J_prime v| ≤ 2‖v‖_∞ Σ a_n(Θ(y±log n)) ≤ 2‖v‖_∞(cosh(y/2)+K_P)`
(harmonic identity plus the corpus bound on the gamma source term); hence `G v = 𝒲₀f/cosh` is bounded and
`|𝒲₀f(z)| ≤ K(1+cosh(z/2))`. The signed pairing `sourcePair(v,q) = ⟨Gv,q⟩_μ` holds on compact `q` and extends by
continuity (compact tests dense in the graph). Riesz: `⟨Riesz(v), q⟩_graph = ⟨v,q⟩_μ` and `⟨v,q⟩_graph = 2⟨v,q⟩_μ + ⟨Gv,q⟩_μ`
give `Riesz(v) = v/2 − Riesz(Gv)/2`, so `Rv = v/2 − R(Gv)/2` and `‖(R−1/2)v‖ ≤ ‖Gv‖/2` (`‖R‖ ≤ 1`).

*Weyl sequence.* With `v_T = (profile)(·−T)/Θ`, `𝒲₀(Θ v_T)(y) = 𝒲₀(profile)(y−T)` (translation covariance), so
`‖G v_T‖²_μ = ∫(𝒲₀profile)(y−T)²Θ(y)/cosh(y/2)dy ≤ A + B cosh²(T/2)` using `cosh((y−T)/2) ≤ 2cosh(y/2)cosh(T/2)`.
The mass `‖v_T‖²_μ = ∫profile²·cosh((x+T)/2)/Θ(x+T) ≥ (∫profile²)·exp(πe^{2(T−R)})/(E_U e^{9(T+R)/2})` by the theta
envelope `Θ(s) ≤ E_U e^{9s/2}e^{−πe^{2s}}`. The ratio is `≤ C exp(9(T+R)/2 + T − πe^{2(T−R)}) → 0` (quadratic lower bound
of the exponential). Separated normalized translates are orthonormal (corpus); `(1/2)·1 − R` invertible would give
`1 = ‖e_n‖ ≤ ‖b‖‖(R − 1/2)e_n‖ → 0`.

## Lean modules (namespace `RHTower.CHMDPolar`)
1. `RHTower/CHMDThetaHarmonicIdentity.lean` (194 lines) — `archDiagonalDensity`, `symArchTerm`, `archConstantReal`,
   `primeKernelSum`, `integrableOn_symArchTerm`, `summable_primeKernelSum`, `polar_halfLine_sum`,
   `oneSided_source_equation`, `theta_harmonic_identity`.
2. `RHTower/CHMDPointwiseGenerator.lean` (589 lines) — `symJump`, `genArch`, `genPrime`, `genTotal`, sup/Lipschitz bounds,
   `archLevyDensity_mul_le`, `integrableOn_archMoment`, measurability, polarization integrability, `integral_shift_product`,
   `integral_prime_mul_eq`, `integrable_archPair`, `integral_arch_mul_eq`, `integral_genPrime_eq_tsum`,
   `exists_genArch_bound`, `abs_genPrime_le`, `exists_primeKernelSum_bound`, `inner_edge_compactLift`.
3. `RHTower/CHMDGeneratorWeilOperator.lean` (290 lines) — `weilOp`, `archIntegrand_eq`, `genTotal_eq_weilOp`, `genImage`,
   `genImage_eq_weilOp`, `exists_weilOp_bound`, `memLp_genImage`, `genImageL`, `sourcePair_compactLift_eq`,
   `sourcePair_compactLift`, `inner_smul_graph`, `rieszLift_compactLift_source`, `resolvent_compactLift_source`,
   `norm_resolvent_sub_half_le`.
4. `RHTower/CHMDThresholdWeylSequence.lean` (390 lines) — `weilOp_translate`, `genImage_test`, `exists_weilOp_profile_bound`,
   `cosh_sub_le`, `exists_genImage_test_bound`, `profile_sq_integral_pos`, `inverseWeight_lower`,
   `inverseMass_translate_lower`, `norm_resolvent_sub_half_normalized_le`, `exists_ratio_bound`, `bound_tendsto_zero`,
   `resolvent_defect_tendsto_zero`, `exists_weyl_sequence`, `half_mem_spectrum_resolvent`.

## Limits
No sign of the Weil form and no RH. Not proved: `σ_ess(R) = [0,1/2]` (whether the essential spectrum reaches below `1/2`
unconditionally), the bound-state count of `R` above `1/2` against nonreal Xi orbits, or any statement about `(1/2, 1]`.

## Log
- 2026-10-16 — built on the polar-transfer modules; four leaves compiled, built with `lake build --old`, audited with
  plain `lake env lean`, 95 declarations axiom-checked, wired, index refreshed.
