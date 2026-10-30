# Logarithmic reserve by shifting the prime energy

- **ID:** ssh-shifted-reserve
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/review-3010/obstacles-summary.md` §2.3 Q1
- **Statement:** For the tilted unit spline there are absolute `a,C>0` such that, for
  every `c≥1`, eventually in `N`, every vector satisfies
  `W_{N,c}(x) ≥ a c⁻⁷(D_N(x) − C log(2c)‖x‖²)`.

## Proof

Write `R_N=(log N)I−P_N`, `λ_m=γ+log m+tameDifferent(m)`, and
`M=∫φ²`. The two proved row bounds give
`R_N−(log 8+4)I ≤ D_N ≤ R_N+(log 4+4)I`.

**Scalar conductor bound.** For positive integers `h,m`, the divisor formula gives
`|c_m(h)|≤Σ_{d|h}d≤h²`. The elementary totient bound is `m≤2φ(m)²`:
for odd primes `p`, `p≤(p−1)²`; at `p=2` the factor is `2`, appearing only once
in the Euler product; higher prime powers only improve these inequalities.
For `1≤h<c`, Cauchy–Schwarz gives `|G(u)|≤M`, hence
`|∫_{h/c}¹G(u)/u du|≤Mc`. There are at most `c` shifts, so
`|shellCorrection(c,m)|≤2c⁴/φ(m)`.

If `m≥8c⁸`, this is at most `1`, and the completed-energy identity gives
`E_m(c)≥λ_m−log c+b−1`, where `b=β(φ)/M−log(2π)−γ`.
If `m<8c⁸`, the proved bound `tameDifferent(m)≤log m` gives
`λ_m≤γ+2log 8+16log c`. Together with `E_m(c)≥0`, these imply
`E_m(c)≥δ(λ_m−L(c))` for every `0<δ≤1`, where
`L(c)=|γ|+|b|+2log 8+16log(2c)+1`.

**Shifted operator.** The proved polynomial reserve is
`W_N≥β(c)D_N−B(c)I`, with
`β(c)=min(growingMassConstant,1/2)/(4c⁷)>0`.
Put `δ=β(c)/2`, `A_N=W_N−δR_N`.
Then
`A_N≥(1/2)W_N−(B(c)+β(c)(log 8+4))I/2`.
Every bounded-energy unit vector of `A_N` therefore has bounded `W_N` energy.
The existing finite Ramanujan coordinate certificate applies to that sublevel.
The norm quasimodes of `W_N` and `P_N` give norm quasimodes of `A_N` with
energies `E_m(c)−δλ_m≥−δL(c)`.

**Spectral transfer.** If `A_N` had an eigenvalue below `−δ(L(c)+1)` at arbitrarily
large horizons, its unit eigenvector would carry at least `1/18` of squared
coordinates on one fixed finite conductor set. For each member, self-adjointness
and the quasimode residual bound give coordinate square at most
`residual²/δ²`. Their finite sum tends to zero, a contradiction.
Thus `W_N≥δR_N−δ(L(c)+1)I` eventually. The upper row bound now gives
`W_N≥δ(D_N−(L(c)+log 4+5)I)`.
Since `log(2c)≥log 2>0`, this is the stated reserve with constants independent
of `c` and `N`.

## Exact scope

The horizon depends on `c` and is not effective. No interchange of
`∀c, eventually N` with a prescribed growing-overlap schedule is used.
The proof keeps the complete matrix, including both poles, Gamma and all prime shells.

## Lean verification

- [x] Totient and conductor-uniform shell bounds; Lean check and standard-axiom audit passed.
- [x] General finite-coordinate spectral transfer; Lean check and standard-axiom audit passed.
- [x] Application to `W_N−δR_N`.
- [x] Exact all-vector reserve, umbrella imports, standard-axiom closure.

Declarations:

- `RenormalizedArithmeticPotentialTheory.completedConductorEnergy_ge_logarithmic_reserve`
  in `TheConductorEnergyKeepsALogarithmicReserve` — checked.
- `CriticalArithmeticCorrelationTheory.eventually_matrix_energy_ge_of_ramanujan_certificates`
  in `FiniteRamanujanCoordinatesTransferSpectralFloors` — checked.
- `CriticalArithmeticCorrelationTheory.exists_completeWeil_logarithmic_defect_reserve`
  in `ShiftingThePrimeEnergyGivesALogarithmicDefectReserve` — checked directly with
  `lake --old env lean`. Both capstone transitive axiom sets are exactly
  `propext`, `Classical.choice`, `Quot.sound`.

The last declaration has exactly `∃a,C>0, ∀c≥1, eventually N, ∀x`.
