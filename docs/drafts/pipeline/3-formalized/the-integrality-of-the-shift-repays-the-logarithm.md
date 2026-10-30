# The integrality of the shift repays the logarithm

- **ID:** ssh-lattice-gain
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Let `φ ∈ C²` be supported in `[0,1]`, `M = ∫φ² > 0`, `G` its autocorrelation,
  `F_c(h) = ∫_{h/c}^1 G(u)/u du`. Then for `c > 0`:
  (1) `∫_0^c F_c(h) dh = c(∫φ)²/2`, so the continuum shell completion
  `E^cont(c) = log(1/(2πc)) + β/M + cq − (2/M)∫_0^c F_c` equals `log(1/(2πc)) + β/M`, tends to `−∞`
  and is negative for `c > e^{β/M}/(2π)`;
  (2) the lattice gain `E(c) − E^cont(c) = log(2πc) − β/M + E(c) ≥ log(2πc) − β/M`, and
  `E(c) − E^cont(c) − log(2πc) → −β/M`;
  (3) for every conductor `m`, `Σ_{h=1}^m c_m(h) = [m = 1]`, the continuum conductor energy is the
  nonpolar reference energy `log(1/(2πc)) + β/M + log m + τ(m) − γ → −∞`, and
  `E_m(c) − E_m^cont(c) − log(2πc) → −β/M − log m − τ(m) + γ`.

## Paper proof

(1) Substitute `h = cs`: `∫_0^c F_c = c∫_0^1 F(s) ds`, `F(s) = ∫_s^1 G/u`. With the regular part
`H(u) = (G(0) − G(u))/u` (continuous), `F(s) = −M log s − ∫_s^1 H`. Integration by parts with
`d/ds(∫_s^1 H) = −H(s)` gives `∫_0^1∫_s^1 H = ∫_0^1 sH(s) ds`, and `∫_0^1 log s = −1`. So
`∫_0^1 F = M − ∫_0^1 sH = ∫_0^1 G = (∫φ)²/2` (the autocorrelation is even, supported in `[−1,1]`,
with total mass `(∫φ)²`). Then `(2/M)∫_0^c F_c = cq`, the pole shift.
(2) Subtract; `E(c) ≥ 0` and `E(c) → 0` are the positive Fourier integral and marginality of the
completed shell energy.
(3) `c_m(h) = Σ_{d∣(m,h)} μ(m/d)d`, and `d ∣ m` divides exactly `m/d` of `1, …, m`, so
`Σ_{h≤m} c_m(h) = mΣ_{d∣m}μ(m/d) = m[m = 1]`. Replacing `Σ_h c_m(h)F_c(h)` by the period mean of
`c_m` times `∫_0^c F_c` removes the shell correction for `m ≥ 2` and the pole shift for `m = 1`.
Nonnegativity and marginality of `E_m(c)` give the gain.

## Scope

The cell `0 < h < 1` omitted by the lattice carries `M log c` of shell weight: the logarithmic
repayment of the complete Weil form is the unit gap of the integers. A model with continuous shifts
keeps only the pole charge and loses positivity at large overlap.

## Lean proof

`SuccessorShellArithmetic/TheIntegralityOfTheShiftRepaysTheLogarithm.lean`:

- `continuumShellSum_eq`, `continuumShellEnergy_eq`, `tendsto_continuumShellEnergy_atBot`,
  `continuumShellEnergy_neg`
- `latticeGain_eq_shell_deficit`, `latticeGain_eq`, `latticeGain_ge`, `tendsto_latticeGain_sub_log`
- `sum_ramanujanLagCoefficient_period`, `continuumConductorEnergy_eq`,
  `tendsto_continuumConductorEnergy_atBot`, `conductorLatticeGain_ge`,
  `tendsto_conductorLatticeGain_sub_log`

`lake --old env lean` passes; axioms `propext`, `Classical.choice`, `Quot.sound`.
