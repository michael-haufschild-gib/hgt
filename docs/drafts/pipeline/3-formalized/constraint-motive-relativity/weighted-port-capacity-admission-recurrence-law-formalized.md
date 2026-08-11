# Weighted port capacity, admission, and recurrence law — Lean certificate

- **ID:** `cmr-weighted-port-capacity-admission-recurrence-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `weighted-port-capacity-admission-recurrence-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean modules

All in `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/`, namespace
`HTGeometry.ConstraintMotiveRelativity`, all imported by the area umbrella
`GaloisForLFunctions.HTGeometry`:

1. `WeightedPortCapacity.lean` — §2, the exact capacity–cost reciprocity.
2. `PortAdmissionCapacity.lean` — §3, capacity is admission and closedness.
3. `PortRecurrenceJets.lean` — §4, the recurrent orbit and the jet admission hierarchy.
4. `PrimePortCapacityHierarchy.lean` — Corollary 3.1 and the §5 specializations.

The prime module reuses two corpus results rather than rebuilding them:
`RHTower.summable_prime_invNatLogSq` (from `RHTower/GammaDampedPrimeLogCauchyDomain.lean`) and
`HTGeometry.summable_log_pow_div_nat_rpow` (from `HTGeometry/ZetaVerticalAlmostPeriodic.lean`),
together with mathlib's `Nat.Primes.not_summable_one_div`.

## Formal statement chain

### §2 — exact capacity–cost reciprocity (Theorem 1)

1. `portCap`, `portEnergy`, `portValue` — `(CA.1)`–`(CA.3)` on a finite aperture: capacity
   `C_F = ∑_{p ∈ F} ‖a p‖²/w p`, filling energy `∑_{p ∈ F} w p ‖x p‖²`, port value `∑_{p∈F} c p x p`.
2. **`portValue_normSq_le`** — weighted Cauchy–Schwarz: `‖λ(x)‖² ≤ E_F(x) · C_F`.
3. `portMinimizer`, `portValue_portMinimizer`, `portEnergy_portMinimizer` — `(CA.5)`: the explicit
   vector `x_p = z · conj(c p)/(w p · C_F)` realizes the value `z` at energy `‖z‖²/C_F`.
4. **`isLeast_portEnergy`** — `(CA.4)`: `‖z‖²/C_F` is the least filling energy of the value `z`.
5. **`portCap_mul_minEnergy`** — `(CA.6)`: `C_F · E_F^min(z) = ‖z‖²`.

### §3 — capacity is admission (Theorem 2, Corollary 2.1)

6. `SourceL2`, `srcBasis`, `srcEmb`, `srcEmb_apply`, `norm_srcEmb_sq`, `norm_sq_eq_tsum`,
   `memℓp_two_iff` — the source chart and its coordinate mass.
7. `portLin`, `portKer` — the algebraic port `(CA.2)` on finitely supported vectors and its
   constraint realized inside the chart.
8. **`summable_of_continuous_port`** — a continuous extension bounds every finite capacity by
   `‖L‖²`: testing against the capacity-optimal aperture vector gives `C_F ≤ ‖L‖ √C_F`.
9. `portVec`, `portCL`, `portCL_srcEmb`, **`norm_portCL_sq`** — the Riesz vector of a
   square-summable family extends the port continuously with `‖λ‖² = C₀`.
10. **`port_admission_iff`** — `(CA.7)`: the algebraic port extends continuously **iff** `C₀ < ∞`.
11. `isClosed_ker_portCL` and **`quot_ker_portCL_equiv`** — in the admitted case the constraint is
    closed and of codimension one.
12. **`portKer_orthogonal_eq_bot`**, **`portKer_topologicalClosure_eq_top`**, `dense_portKer` — the
    divergent branch: a vector orthogonal to the constraint has coordinates `α · conj(c p)`, and
    square-summability forces `α = 0`, so the constraint is dense and Hausdorff reduction of the
    port vanishes.
13. **`exists_aperture_capacity_gt`**, **`exists_aperture_minEnergy_lt`** and
    **`tendsto_atTop_iff_tendsto_inv_zero`** — Corollary 2.1, `(CA.8)`: divergent capacity produces
    apertures of arbitrarily large capacity, equivalently of arbitrarily small unit-port filling
    energy `1/C_F`, and the two limits are literally reciprocal.

### §4 — the recurrent orbit and the jet hierarchy (Theorem 3)

14. `portPhase`, `portCoef`, `portOrbit` — the orbit `Φ t = (p ↦ c p e^{-itθ p})` in the chart.
15. `norm_portOrbit_sub_sq` and **`norm_portOrbit_shift`** — the orbit is an isometric flow:
    `‖Φ(t+s) − Φ(s)‖ = ‖Φ(t) − Φ(0)‖`.
16. `singleCLM`, `coordCLM`, `portTrunc`, `norm_portOrbit_sub_trunc_sq` and
    **`tendstoUniformly_portTrunc`** — the finite-aperture truncations converge to the orbit
    uniformly in time, with error exactly the tail capacity.
17. **`continuous_portOrbit`** — the orbit is norm-continuous.
18. **`totallyBounded_range_portOrbit`** and **`isCompact_closure_range_portOrbit`** — the orbit is
    totally bounded (the truncation lands in the continuous image of a compact coordinate box) and
    has compact closure.
19. **`portOrbit_recurrent`** — the orbit is recurrent: for every `ε > 0` and every `T` there is
    `t > T` with `‖Φ(t) − Φ(0)‖ < ε`.  Pigeonhole on the net of a totally bounded set plus the
    shift isometry, so no subsequence extraction is needed.
20. `jetCoef`, `norm_jetCoef_sq` — the `n`-jet coefficient `(-iθ p)^n c p`, whose mass is
    `θ p^{2n}‖c p‖²`, i.e. the `n`-th jet capacity `(CA.3)`.
21. `hasDerivAt_portCoef`, `hasDerivAt_portTrunc` and **`hasDerivAt_portOrbit`** — the orbit
    differentiates term by term; the uniform truncation supplies the hypothesis of
    `hasDerivAt_of_tendstoUniformlyOn`.
22. **`summable_jetCoef_one_of_differentiableAt`** — the converse: the coordinate readouts pin the
    derivative coefficients, so a differentiable orbit has finite first jet capacity.
23. **`contDiff_portOrbit_iff`** — `(CA.9)`: the orbit is `C^n` **iff** every jet capacity up to
    order `n` is finite.
24. **`iteratedDeriv_portOrbit`** — the `n`-th derivative is the orbit of the `n`-twisted family,
    and `norm_portOrbit_sq` gives its squared norm `C_n` at every time.

### Corollary 3.1 and §5 — the prime specializations

25. `primeLog`, `chartCoef`, **`norm_chartCoef_sq`**, **`norm_jetCoef_chartCoef_sq`** — the
    weighted prime chart `c p = a p/√(w p)` and its jet capacities
    `C_n = ∑ ‖a p‖² (log p)^{2n}/w p`, which is exactly `(CA.3)`.
26. `singularWeight`, `singularCoef`, **`summable_singularCapacity`** and
    **`not_summable_singularJetOne`** — `(CA.10)`–`(CA.11)`: with `a = 1` and `w p = p (log p)²`,
    `C₀ = ∑ 1/(p (log p)²) < ∞` while `C₁ = ∑ 1/p = ∞`.
27. **`singular_time_law`** — Corollary 3.1: that port orbit is norm-continuous, totally bounded
    with compact closure, and recurrent, and is not `C¹`.  Global recurrence and infinitesimal
    dynamics occupy different admission strata.
28. **`not_summable_unweightedCapacity`** — §5.1: `a = w = 1` has `C₀ = ∞`.
29. **`not_summable_eulerHalfDensityCapacity`** — §5.2: `a p = (log p)/√p`, `w = 1` has
    `C₀ = ∑ (log p)²/p = ∞`, since `log p ≥ log 2 > 0` on every prime.
30. **`summable_shiftedDensityCapacity_iff`** — §5.3: `a p = (log p) p^{-σ}`, `w = 1` has finite
    capacity **iff** `σ > 1/2`.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/WeightedPortCapacity.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PortAdmissionCapacity.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PortRecurrenceJets.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/PrimePortCapacityHierarchy.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.PrimePortCapacityHierarchy
```

Green with no warnings.  `#print axioms` on `isLeast_portEnergy`, `portCap_mul_minEnergy`,
`port_admission_iff`, `norm_portCL_sq`, `quot_ker_portCL_equiv`,
`portKer_topologicalClosure_eq_top`, `exists_aperture_minEnergy_lt`,
`tendsto_atTop_iff_tendsto_inv_zero`, `continuous_portOrbit`, `totallyBounded_range_portOrbit`,
`isCompact_closure_range_portOrbit`, `portOrbit_recurrent`, `hasDerivAt_portOrbit`,
`contDiff_portOrbit_iff`, `iteratedDeriv_portOrbit`, `summable_singularCapacity`,
`not_summable_singularJetOne`, `singular_time_law`, `not_summable_unweightedCapacity`,
`not_summable_eulerHalfDensityCapacity` and `summable_shiftedDensityCapacity_iff` reports only
`propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The weighted chart `H_w` of `(CA.1)` is realized through the isometry `x ↦ (√(w p) x p)` onto flat
`ℓ²`, which is the Riesz identification the card's own proofs of Theorems 2 and 3 use ("after Riesz
identification, the orbit is the diagonal unitary orbit of the vector `(a_p/√w_p) ∈ ℓ²`").  The
weighted formulation therefore appears in the Lean development at the two places where it carries
information: §2, which is stated with explicit weights, and §5, where `chartCoef` converts a
weighted port into its flat coefficient family and `norm_jetCoef_chartCoef_sq` recovers `(CA.3)`
verbatim.

Recurrence is stated in the exact form the card's proof establishes — the orbit returns to within
`ε` of its start at arbitrarily late times — rather than through a Bohr almost-periodicity
interface.  The corpus Bohr–Bochner layer (`HTGeometry/BohrBochnerEquivalence.lean`) concerns
translation orbits of scalar functions in the uniform metric, a different object, and is not used.

The `(CA.14)` remark that the two-frequency orbit is dense in a torus is classical background for
the intuition and is not part of any statement of this card.

`§6`–`§10` are programme scope and no-go bookkeeping and claim no further theorem.
