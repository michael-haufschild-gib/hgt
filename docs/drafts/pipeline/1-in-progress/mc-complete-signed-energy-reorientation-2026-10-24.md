# MC: complete signed interior history after the new corpus advances

- **ID:** mc-complete-signed-energy-reorientation-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; open arithmetic estimate, no new theorem claimed
- **Source:** `docs/reports/rh-current-frontier-map.md`, route MC; Lean declarations below.
- **Statement:** Bound the complete compensated interior history pairing uniformly in the horizon at positive dampings accumulating at zero.

## Current hard target

Use the existing, literal arithmetic quantities

```
E(ε,T) = pmPowerDampedDivisorDiscreteEnergy ε T
M(ε,T) = pmBezoutInteriorMartingaleSum ε T
c(ε)   = pmInteriorLogCounterterm ε
H(T)   = pmCompensatedHarmonicSum T
J(ε,T) = 2*M(ε,T) + 2*c(ε)*H(T).
```

The immediate open statement is

```
∀ η > 0, ∃ ε ∈ (0, min η (1/2)), ∃ B, ∀ T, J(ε,T) ≤ B.
```

The constants may depend on ε, never on T. This is an existing RH-strength target, not a new equivalence or a new theorem. Its arithmetic content must be proved without an admission, zero-location, or cancellation premise.

The history pairing is explicitly

```
M(ε,T) = Σ_{1≤n<T} (τ_ε(n+1) − density_ε) I_ε(n)
                         * (1/(n+1) − 1/(T+1)),
```

where `I_ε = pmBezoutInteriorPrefix ε`. Both density and compensated endpoint belong to the target.

## Closed obligations: do not repeat

1. `LiouvilleTriangularHeadOscillation.frequently_gt_and_frequently_lt` closes the old actual-source Mellin/Landau connection and both oscillation signs. The October 4 pole-separation continuation is superseded by that result and `LiouvilleHyperbolaCutoffOscillation`.
2. `RoughPrimeBoundaryUniformDampingDefectSign.eventually_pmPowerDamped_renormalizedDefect_nonpos_uniform` gives all-prefix defect nonpositivity, eventually in cutoff, uniformly for `0≤ε≤1`. This does not bound the complete energy.
3. `UniformRenormalizedInteriorEnergyRemainder` proves bounded compensated diagonal and predecessor-peak remainders for every ε>0. In particular, `exists_pmBezoutInterior_compensated_energy_bound` proves `|J(ε,T)−E(ε,T)|≤C_ε` for every T.
4. `TheReceiverEquivalenceAndZeroWidthLaw.exists_compensated_pmBezoutInteriorMartingale_bound_iff` already identifies bounded J with bounded E. Its strict-contraction equivalents are also already proved. They supply no unconditional small-damping bound.
5. `SignedModulusSumOfTheInteriorMartingale` evaluates the signed jump-orbit mean through Selberg multiples coordinates and Ramanujan weights, proves radical invariance, and proves absolute summability of the double-modulus drift for ε>0. Evaluating that mean again would not address the remaining fluctuations.
6. `CompletePronicVaughanCalibration.pmInteriorPronicEnergy_eq_vaughanGram` retains all five components and all 25 signed Gram entries. Its available logarithmic majorant is proved nonsummable below half damping.

## Exact obstruction in the present estimates

`PronicPotentialSelfCancellationAndInteriorGradientConservation` shows that replacing the history pairing by a forward difference returns the energy itself. Substitution into the full budget cancels E identically; the surviving gradient/local-impulse conservation law is not an upper bound for E.

`SignedModulusSumOfTheInteriorMartingale.eventually_abs_compensated_interiorMartingale_le_growth_of_pos` proves

```
|J(ε,T)| ≤ C_ε T^(1−2ε) exp(−vkKappa*vkScale(T)/270)
```

for each fixed `0<ε<1/2`, eventually in T. Its proof transfers the existing energy growth estimate using coefficient-one tracking. It does not obtain a strict contraction from signed history cancellation.

`BirthDelayedInteriorJumpCenteringAndUniformPairBounds` controls a centered atom pair by `1/d + 2/gcd(d,e)`, uniformly in the finite horizons. The bound retains a constant contribution for coprime pairs. Taking absolute values before the signed modulus sums therefore does not provide the required global bound.

`BilinearCountertermRemainderAndDefectDriftObstructions` keeps the principal counterterm, low-product sum, high-product remainder and inherited cutoff history together. Its semiprime identity and positive successor reserve rule out deleting these terms on the strength of defect nonpositivity.

## Focused next attack

Work directly on the signed jump-progressions of the literal history pairing. Use the already evaluated orbit means to remove their canonical drift, then keep the birth-delayed residual, initial-value correction and linear density correction in one signed expression. The missing estimate concerns this combined fluctuation across growing moduli and all horizons, not the orbit mean.

An acceptable intermediate success is a source-derived strict inequality

```
J(ε,T) ≤ (1−δ_ε)*E(ε,T) + C_ε,   δ_ε>0,   for every T,
```

at dampings accumulating at zero. The existing coefficient-one comparison then gives a bound for E. The strict inequality itself is unproved; introducing it as a premise would not be progress. Keep the complete Vaughan Gram available to check that any regrouping retains all mixed terms. Do not replace this target by separate component norms or a stronger pointwise damping-derivative assumption.

## Assessment and verification

- This batch reoriented the route and removed obsolete obligations. It proved no new mathematical estimate and did not advance the numerical cancellation exponent.
- The next mathematical advance must bound the joint signed fluctuation above, or expose a concrete obstruction with a nontrivial positive survivor. Another receiver equivalence, orbit-mean evaluation, or local gradient identity does not count.
- Read the actual Lean statements and proof bodies, including the coefficient-one energy transfer and the exact self-cancellation. No fresh compilation or axiom audit is claimed; no Lean files changed.
- No web search, external comparison, novelty check, mathematical numerical experiment, or subagent used.

## Search and working log

- 2026-10-24 — Corpus searches for complete pronic Vaughan Gram, joint counterterm/high-product remainder, signed damping work and compensated interior contraction. Inspected candidate lemmas, source arguments and their Lean source. Semantic queries completed with `partial=false`, no reported errors. No claim of exhaustive absence.
- 2026-10-24 — Read `TheAveragedBudgetIsExactlyAdmission`: damping-averaged relative loss is exactly admission; a pointwise budget is stronger in general. This prevents adding an unnecessary pointwise obligation to MC.
- 2026-10-24 — Selected the compensated interior history fluctuation as the next attack. Goal remains unmet and active; no unconditional RH proof or falsification obtained.

## Signed residual attack after reorientation

The replacement goal in attachment `421946d1-022c-4288-ba56-539c94bebf22/pasted-text-1.txt` requires an unconditional RH proof and an actual significant source estimate. It excludes further criteria, numerical improvements and no-go results as deliverables. Read that attachment, the current MC ledger and the applicable killed-route entries before resuming. No web or novelty checks.

### Attempt: sum the conditionally centered pair bounds

For jump modulus d and interior modulus e, the source definition is

```
R(d,e,k) = anchoredInteriorSawtoothAtom e (d−1+d*k)
           − 1_{e/d≤k}*(interiorJumpOrbitMean d e − (e−1)/(2e)).
```

The bound in `abs_birthDelayedInteriorJumpResidual_compensated_le` has a coprime contribution `2`, even after the initial segment is handled. The signed orbit-mean series is summable, but that theorem is about the mean, not R. Transferring its summability to R would be an unjustified step. No bound for the complete signed residual was obtained this way.

### Attempt: cancel the two modulus orientations before estimating

Pointwise antisymmetry is not available. Directly from the source definitions, for d≥2 at the first jump,

```
R(d,d+1,0) = −(d−1)/(d+1),
R(d+1,d,0) = 0.
```

Indeed, the first modulus has not reached its birth threshold and neither endpoint is divisible by d+1. In the reverse orientation birth has occurred, the observed predecessor is d, and the deleted endpoint and coprime orbit mean both vanish. This only rejects pointwise antisymmetry; it says nothing against cancellation of the complete Möbius sum.

For the complete pairing, inspected the proof of `UniversalSawtoothInteriorMartingaleAndPostStepCalculus.sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_bezout_interior`. Polarization and reciprocal summation by parts retain the symmetric pronic Gram term and terminal value. The horizon-free version is the already inspected self-cancellation law. Thus this argument has not supplied a strict contraction either. No new no-go module is being pursued.

### Remaining positive attack

The signed orbit means have already been evaluated; the full fluctuation has not. Keep both modulus orientations, their different birth thresholds, the density correction and the endpoint in the same arithmetic sum. A proof must use the actual Möbius coefficients across growing moduli to bound that sum, rather than infer its sign from pair centering or a coefficient-independent kernel inequality. The exact full-energy target above is unchanged.

### Batch status

- Completed source inspection and mathematical checks of the two proposed cancellation steps; neither closes the source estimate.
- No new unconditional source bound, Lean theorem, or RH proof obtained. No Lean files edited or compiled.
- Corpus semantic searches for birth-delayed signed residuals, reciprocal sawtooth pairing, joint interior estimates and LCM grouping completed with `partial=false` and no reported errors. Search hits were checked against their Lean statements/proofs where used.
- All owned search processes reached exit 0. Temporary search output removed after recording this state. Goal remains active.

## Complete-source curvature attempt

The preceding turn did not improve the source estimate. This batch inspected the natural-cutoff cofactor decomposition, the all-lag window covariance bound, the actual adjacent-correlation power-rate proof, and the damping generator/second-tangent proofs. None of the retrieved closure statements discharges the small-damping source input: the retrieved RH statements retain admission, convexity or budget premises. This is a statement about inspected hits, not an exhaustive absence claim.

The all-lag estimate `abs_window_lag_covariance_sub_le` is uniform in the lag, but retains `(2*N^2−1)*sieveVariance N c`. Its covariance is the complete-period covariance. Substituting it for the moving-prefix signed pairing would still require paying that error and preserving the source's initial phase. No such transfer was proved. The adjacent theorem's positive power rate proves the already-paid predecessor-peak remainder; it does not estimate the interior history.

### Conjecture being attacked

For the actual arithmetic source, prove the sign of the complete second-damping work

```
Σ_{1≤n≤T} (B_ε(n)^2 + A_ε(n)*F_ε(n))/(n*(n+1)) ≥ 0,
```

where B and F are the first and second damping tangents already defined in Lean. The existing `riemannHypothesis_of_second_tangent_pairing_ge` closes RH if this arithmetic inequality is proved for every T and `0<ε≤1/2`. The conjecture is the sign, not another criterion theorem. No assumption of the sign is permitted in an RH proof.

### Exact generator calculation and remaining mathematical work

Let L be the existing `arithmeticDampingGenerator`, let `v_ε(n)=A_ε(n)/n` on positive states, let `m(ε)=dampedReadout ε`, and put `w(n)=n/(n+1)`. The source evolution in `DampingWorkAsArithmeticMarkovBoundaryFlux` is

```
v' = L v − m,       L(constant)=0.
```

Consequently the full sign to prove is

```
Σ_{1≤n≤T} w(n)*((L v(n)−m)^2 + v(n)*(L(L v)(n)−m')) ≥ 0.
```

This keeps the density's second derivative. It is the same source sign as the existing second-tangent formula, not an established estimate.

The attempted mechanism is a positive-square expansion of the iterated arithmetic jump form. For the bilinear jump form Γ and its iterate Γ₂, the algebraic identity for the homogeneous contribution is

```
(L v)^2 + v*L^2 v = (1/2)*L^2(v^2) − 2*L Γ(v) + 2*Γ₂(v).
```

After centering, the additional terms are `−2*m*L v + m^2 − m'*v`. Thus a curvature sign by itself would leave both weighted fluxes and the density terms. The pronic weight is not asserted stationary in the Lean source. A prime-coordinate or divisor-state square identity cannot be silently transferred through prefix averaging to this norm.

The next proof obligation within this attempt is to control these flux and density terms jointly with the actual-source iterated jump form. No sign for that combination has been established. Do not formalize a generic curvature lemma as if it closed this obligation; do not strengthen the target to a separate sign for each cell or each flux.

### Verification and progress assessment

- New explicit proof attempt: complete second-damping source sign via arithmetic generator curvature, with both fluxes and both density contributions retained.
- No significant obstacle closed and no new unconditional estimate proved. No Lean edits, build, or axiom-audit claim.
- The listed corpus searches completed normally; no web search, novelty check, subagent or mathematical numerical experiment was used.
- Goal remains the full unconditional Lean proof of RH. The generator attempt remains open; it has not been retired or replaced by an auxiliary theorem.
