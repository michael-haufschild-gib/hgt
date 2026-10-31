# Logarithmic defect reserve at prescribed growing overlap

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `../1-in-progress/three-frontier-questions-full-solutions.md`, Q1.
- **Statement:** Absolute `a,C>0` such that, for every `0<α<1/16`, eventually
  `W_N(c,x) ≥ a c⁻⁷[D_N(x)−C log(2c)‖x‖²]` for every vector and
  `1≤c≤(log log N)^α`.

## Proof

The explicit polynomial reserve gives `W≥b c⁻⁷D−B c⁹‖x‖²` once
`N≥Hc⁸`. Set `a=min(b/2,1/2)`, `δ=a/c⁷`, and
`L=conductorLogarithmicLoss tiltedUnitSpline c`. Consider
`S=W−δ[(log N)I−P]+δ(L+1)I`.

Its conductor energies are at least `δ`. A nonpositive unit vector of `S`
satisfies `D≤(B/a+log 8+4)c¹⁶`, by the row comparison between `D` and
renormalized prime energy. Thus it has the same exponential conductor
cutoff as the unshifted form.

The residual of `S` is exactly the complete Weil residual plus `δ` times
the prime residual. Since `δ≤1`, the uniform quartic conductor bound from
`complete-weil-positivity-at-growing-iterated-log-overlap.md` applies with
a new absolute constant. The common spectral argument then makes `S`
positive definite. The reverse row comparison yields the stated reserve.

## Lean

Module: [TheCompleteWeilLogarithmicReserveSurvivesGrowingOverlap.lean](../../../../formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/TheCompleteWeilLogarithmicReserveSurvivesGrowingOverlap.lean).

- `exists_logarithmicReserve_negative_conductor_cutoff`: uniform shifted confinement.
- `logarithmicReserve_conductor_floor`: the exact scalar floor.
- `exists_logarithmicReserve_uniform_conductor_residual_bound`: the common residual rate.
- `exists_logarithmicReserveMatrix_posDef_iteratedLog`: positivity of the shifted matrix.
- `exists_completeWeil_logarithmic_defect_reserve_iteratedLog`: the actual all-vector reserve.

Direct `lake --old env lean` check passed. All five transitive axiom audits
contain exactly `propext`, `Classical.choice`, `Quot.sound`. The module is
imported by the CACT umbrella. The complete agreement-shell identity and
RH-complete overlap remain open.
