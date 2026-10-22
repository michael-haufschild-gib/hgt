# Sonin semilocal Witten-area response universality law

- **ID:** `sonin-semilocal-witten-area-response-universality-law`
- **Law:** LAW500
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proof and direct Lean check complete)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
  `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SoninSemilocalWittenAreaResponseUniversalityLaw.lean`

## Theorem

For every positive Sonin aperture `a`, let `Tₐ` be the central prolate compression and let

```text
Vₐ = Re tr(Tₐ - Tₐ²)
```

be its local free-fermion number variance.  Then:

1. `0 ≤ Vₐ ≤ 4a²`;
2. `‖Tₐ‖²_HS + Vₐ = 4a²`;
3. the complete zero-mode-subtracted Witten partition

   ```text
   ‖Tₐ‖²_HS + ‖Tₐ,ext‖²_HS + 2Vₐ
   ```

   is exactly `8a²`; and
4. every prime-power semilocal geometric trace response is bounded by

   ```text
   sqrt(Wₐ) * sqrt(1024 Wₐ),
   ```

   where `Wₐ` is that same exact Witten partition.

Thus signal-processing aperture area is simultaneously an occupation simplex, a supersymmetric
Hamiltonian partition, and the universal response budget.  Arithmetic prime-power scale cannot
alter that budget.

## Theorem-generated derivation

Whole-corpus same-folder theorem-leaf pairing exposed:

- `SoninProlateCommutatorEnergy.re_opTrace_centralProlateImpurity_eq_transition_hsNormSq`;
- `SoninProlateCommutatorEnergy.hsNormSq_centralProlateBlock_add_re_opTrace_impurity_eq_four_mul_sq`;
- `SoninProlateCommutatorEnergy.hsNormSq_centralSoninProjectionCorrection_eq_compressions_add_two_mul_re_opTrace_prolateImpurity`;
- `SoninTimeBandHilbertSchmidt.hsNormSq_centralSoninProjectionCorrection_eq_eight_mul_sq`;
- `SoninSemilocalTraceObstruction.norm_soninSemilocalGeometricTraceResponse_le_compressions_add_two_mul_transition`.

No target law was predicted before these theorem surfaces were read.

## Dependency-closed paper proof

The trace identity identifies `Vₐ` with the Hilbert--Schmidt square of the transition corner, so
`Vₐ ≥ 0`.  The occupation budget gives `‖Tₐ‖²_HS + Vₐ = 4a²`; nonnegativity of
`‖Tₐ‖²_HS` gives `Vₐ ≤ 4a²`.

The correction-partition theorem identifies the full Witten expression with the Hilbert--Schmidt
square of the central Sonin projection correction.  The time-band area theorem evaluates that
square as `8a²`, giving the exact full partition.

Finally, the semilocal response theorem bounds every prime-power response by the same expression
with the transition-corner square in place of `Vₐ`.  Replacing that square by the exact trace
identity yields the Witten-area response bound without loss or a new constant.

No numerical computation is used.  Every dependency is an existing Lean theorem.

## Strict corpus delta

`SoninProlateCommutatorEnergy` proves the occupation and Witten partitions but does not connect
them to the semilocal prime-power response.  `SoninSemilocalTraceObstruction` proves the response
bound in transition-corner coordinates and separately evaluates a scalar area bound, but it does
not expose the free-fermion trace as the exact response budget or state the variance interval.
No corpus declaration simultaneously gives the variance simplex, exact `8a²` Witten partition,
and its universal semilocal response control.

## Lean result

`formal/GaloisForLFunctions/RHTower/SoninSemilocalWittenAreaResponseUniversalityLaw.lean`
defines the exact variance and Witten budget and proves:

- `centralSoninFreeFermionVariance_mem_areaInterval`;
- `centralSoninWittenAreaBudget_eq_eight_mul_sq`;
- `norm_soninSemilocalGeometricTraceResponse_le_wittenAreaBudget`;
- `soninSemilocal_wittenArea_responseUniversality`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/SoninSemilocalWittenAreaResponseUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after the dependency-closed Lean proof passed.

- Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators: semilocal adelic operators*
  (arXiv:2310.18423), develops semilocal prolate operators, Sonin spaces, and the semilocal trace
  formula, but does not state this free-fermion variance simplex or its exact response budget.
- Classical time--band limiting literature supplies the prolate/Shannon area mechanism, while
  determinantal/free-fermion literature supplies `tr(T-T²)` as number variance.  These are
  component mechanisms, not the exact central-Sonin `4a²`/`8a²` partition coupled to the
  prime-power response bound.
- Targeted searches for prolate Witten partitions, semilocal free-fermion response bounds, and
  `T-T²` aperture-area laws found no matching conjunction.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is not claimed for
`tr(T-T²)` as a variance, for prolate time--band limiting, or for semilocal trace formulas
separately; it is limited to the exact variance interval, Witten-area partition, and uniform
semilocal response law proved here.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
