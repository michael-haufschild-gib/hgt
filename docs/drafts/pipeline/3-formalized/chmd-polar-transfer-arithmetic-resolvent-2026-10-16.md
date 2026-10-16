# CHMD polar transfer and the bounded arithmetic Weil operator

- **ID:** chmd-polar-transfer-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, CHMD "Needs" (dominate negative theta-cosh mass jointly with all prime and archimedean channels; no selfadjoint realization / primitive spectral gap in the Doob-graph cards)
- **Statement:** On the complete arithmetic Doob graph (`μ = Θ cosh(x/2)dx`, archimedean density plus all prime-power lines) the complete Weil form of `Θv` equals the arithmetic jump energy minus the polar jump energy `∫∫ cosh((x−y)/2)Θ(x)Θ(y)(v(x)−v(y))²`; the theta–cosh mass is the diagonal of the polar jump form. The complete Weil form is the quadratic form of the bounded selfadjoint operator `T = R − 2R² + 2|1⟩⟨1| − 2|R tanh(·/2)⟩⟨R tanh(·/2)|` on `L²(μ)`, `R = (1+L)⁻¹` the arithmetic resolvent.
- **Status:** STATUS MUST-1541, MUST-1542. Three leaves, 100 declarations, all `#print axioms` = propext/Classical.choice/Quot.sound; final plain `lake env lean` audits clean; `lake build --old` of each leaf green; wired once each into `GaloisForLFunctions/RHTower.lean`; index refreshed. Global lint exit 1 solely for the unrelated concurrent unwired module `RHTower/CHMDTranslatedRelativeGraph` (another agent's untracked file); no diagnostic on the three leaves.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `polarEnergy_eq`, `weilForm_eq_edge_sub_polar`, `weilForm_compactLift`, `weilForm_critical`, `weilForm_normalized_tendsto_zero`, `resolvent_isPositive`, `resolvent_oneL`, `resolvent_critical`, `inner_weilOperator`, `weilOperator_isPositive_iff`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
The CHMD cards state the signed Doob energy as "jump norm² minus theta–cosh mass norm²" and ask to dominate the
negative mass jointly by all prime and archimedean channels, and record that no selfadjoint realization exists.
Both are removed: the mass is not a killing term but the diagonal of a second jump Dirichlet form with the
rank-two polar kernel `2cosh((x−y)/2) = 2cosh(x/2)cosh(y/2) − 2sinh(x/2)sinh(y/2)`, whose generator on `L²(μ)`
is `1 − 2|1⟩⟨1| + 2|tanh(·/2)⟩⟨tanh(·/2)|`. The complete Weil form is `J_arith − J_polar`, a comparison of two
Markovian forms with the same invariant measure, and it is the quadratic form of a bounded selfadjoint operator.

## Paper proof
Let `a = Θ cosh(·/2)` (the mass density), `b = Θ sinh(·/2)`, `τ = tanh(·/2)`. Then `∫a = 1/2`
(corpus `integral_riemannKernelReal_cosh_half`), `∫b = 0` (odd), `|b| ≤ a`, and
`cosh((x−y)/2)Θ(x)Θ(y) = a(x)a(y) − b(x)b(y)`. For `v ∈ L²(μ)` (so `av², av, bv², bv ∈ L¹`), expanding
`(v(x)−v(y))² = v(x)² + v(y)² − 2v(x)v(y)` gives six product integrals (Fubini):
`J_polar(v) = ‖v‖²_μ − 2⟨v,1⟩²_μ + 2⟨v,τ⟩²_μ`.
The pole term of `f = Θv` is `Re P(f) = 2(∫f cosh(·/2))² − 2(∫ f sinh(·/2))² = 2⟨v,1⟩² − 2⟨v,τ⟩²`
(corpus `phiDoob_pole`), and `M(f) = Re W(f,f) − Re P(f)` (`markovEnergy_eq_W_sub`), with
`M(f) = ‖edge v‖² − ‖v‖²_μ` on the graph (`sourceEnergy_compactLift`). Hence
`Re W(Θv,Θv) = ‖edge v‖² − ‖v‖²_μ + 2⟨v,1⟩² − 2⟨v,τ⟩² = ‖edge v‖² − J_polar(v)`.
Both sides are continuous on the completed graph; compact `C²` tests are dense (`dense_compactTests`).

Critical modes `c = Θ(·−a)/Θ + Θ(·+a)/Θ − 2cosh(a/2)` are even, so `⟨c,τ⟩ = 0`; with `sourceEnergy c = 0` and
`⟨c,1⟩ = 0` the Weil form vanishes on them. Along the cusp escape both pairings vanish (the profile has both
hyperbolic half-moments zero and `sinhHalfMoment(translate f t) = C sinh(t/2) + S cosh(t/2)`), so the Weil form is
the signed energy there and tends to zero.

Resolvent: the graph is complete for `⟨p,q⟩_graph = ⟨p,q⟩_μ + ⟨edge p, edge q⟩`. Riesz gives `Riesz w` with
`⟨Riesz w, q⟩_graph = ⟨w, q⟩_μ`; put `Rw = source(Riesz w)`. Then `⟨Rw,w'⟩ = ⟨Riesz w, Riesz w'⟩_graph`
(symmetric, positive), `‖Riesz w‖² = ⟨Rw,w⟩ ≤ ‖Rw‖‖w‖ ≤ ‖Riesz w‖‖w‖` gives `‖R‖ ≤ 1`; the constant lift has no
edge so `R1 = 1`; `⟨edge c, edge q⟩ = ⟨c,q⟩_μ` for critical modes gives `Riesz c = c/2`. For `p = Riesz w`,
`‖p‖²_graph = ⟨w,Rw⟩`, so `sourceEnergy p = ⟨w,Rw⟩ − 2‖Rw‖²` and
`weilForm p = ⟨w,Rw⟩ − 2‖Rw‖² + 2⟨w,1⟩² − 2⟨Rτ,w⟩² = ⟨Tw,w⟩`. If `p ⊥ range(Riesz)` then `⟨w,p⟩_μ = 0` for all
`w`, so `source p = 0` and `p = 0` (injective source projection): the range is dense, and `T ≥ 0` iff the Weil
form is nonnegative on the completed graph.

## Lean modules (namespace `RHTower.CHMDPolar`)
1. `RHTower/CHMDPolarJumpForm.lean` (185 lines) — `polarWeight`, `polarEnergy`, `sinhDensity`, `tanhHalf`,
   `polarWeight_eq`, `integral_massDensity`, `integral_sinhDensity`, `integrable_sinhDensity`, `integral_mass`,
   `integrable_mass_iff`, `polarEnergy_nonneg`, `polarEnergy_eq`.
2. `RHTower/CHMDPolarTransfer.lean` (289 lines) — `oneL`, `tanhL`, `inner_toLp_right`, `inner_oneL`, `inner_tanhL`,
   `norm_sq_eq_integral`, `weilForm`, `weilForm_eq_edge_sub_polar`, `weilForm_le_edge`, `continuous_weilForm`,
   `compactLift_source_ae`, `phiDoobCoshMass_eq_integral_mass`, `phiDoobSinhMass_eq_integral_mass`,
   `weilForm_compactLift`, `W_re_eq_edge_sub_polar`, `massDensity_neg`, `tanhHalf_neg`, `ratio_neg_arg`,
   `criticalFunction_neg`, `integral_eq_zero_of_odd`, `critical_inner_tanhL`, `weilForm_critical`,
   `sinhHalfMoment_translate`, `escape_inner_tanhL`, `weilForm_normalized`, `weilForm_normalized_tendsto_zero`,
   `weilForm_compactLift_nonneg_of_riemannHypothesis`, `weilForm_nonneg_of_riemannHypothesis`,
   `polarEnergy_le_edge_of_riemannHypothesis`.
3. `RHTower/CHMDArithmeticResolvent.lean` (349 lines) — `graph_inner`, `graph_norm_sq`, `norm_source_le_graph`,
   `sourceFunctional`, `rieszLift`, `inner_rieszLift`, `rieszLift_unique`, `rieszLift_add`, `rieszLift_smul`,
   `resolventFun`, `inner_resolventFun`, `resolventFun_self`, `norm_resolventFun_le`, `resolventLinear`,
   `resolvent`, `resolvent_apply`, `norm_resolvent_le`, `resolvent_symm`, `inner_resolvent_self`,
   `resolvent_isPositive`, `isSelfAdjoint_resolvent`, `rieszLift_oneL`, `resolvent_oneL`, `rieszLift_critical`,
   `resolvent_critical`, `graph_norm_sq_rieszLift`, `edge_norm_sq_rieszLift`, `sourceEnergy_rieszLift`, `rankOne`,
   `rankOne_apply`, `weilOperator`, `weilOperator_apply`, `inner_resolvent_oneL`, `inner_resolvent_tanhL`,
   `inner_weilOperator`, `weilOperator_symm`, `isSelfAdjoint_weilOperator`, `norm_oneL_sq`, `inner_tanhL_oneL`,
   `weilOperator_oneL`, `weilOperator_critical`, `rieszLinear`, `dense_range_rieszLift`,
   `weilForm_nonneg_of_weilOperator_isPositive`, `weilOperator_isPositive_iff`,
   `W_re_nonneg_of_weilOperator_isPositive`, `weilOperator_isPositive_of_riemannHypothesis`.

## Limits
No sign of the Weil form, no spectral gap, no essential spectrum of `R` or `T`, and no RH is proved. `T ≥ 0` is
Weil positivity on the completed graph; the equivalence with RH itself is not restated here (the corpus Weil
criterion `riemannHypothesis_iff_weilPositiveFull_vonMangoldt` quantifies over complex tests). The polar
domination `J_polar ≤ J_arith` is the whole sign question in Doob coordinates: the kernel difference
`k(|t|)/2 − cosh(t/2)` is the `√x`-normalized prime fluctuation measure.

## Log
- 2026-10-16 — created from the corpus modules CHMDDoobSourceGraph / CHMDThetaCriticalModes /
  CHMDPrimitiveCuspEscape / CHMDCriticalBandReduction / WeilPhiDoobPrimeAtoms; three leaves compiled, built with
  `lake build --old`, audited with plain `lake env lean`, 100 declarations axiom-checked, wired, index refreshed.
